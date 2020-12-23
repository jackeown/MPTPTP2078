%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:43 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 707 expanded)
%              Number of leaves         :   18 ( 233 expanded)
%              Depth                    :   16
%              Number of atoms          :  263 (2005 expanded)
%              Number of equality atoms :   16 (  89 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(A))
                 => ( r2_hidden(D,B)
                  <=> r2_hidden(D,C) ) )
             => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_28,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_39,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(A_21,B_22)
      | ~ m1_subset_1(A_21,k1_zfmisc_1(B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_46,plain,(
    r1_tarski('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_39])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( r2_hidden(B_9,A_8)
      | ~ m1_subset_1(B_9,A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_217,plain,(
    ! [C_59,B_60,A_61] :
      ( r2_hidden(C_59,B_60)
      | ~ r2_hidden(C_59,A_61)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_324,plain,(
    ! [B_76,B_77,A_78] :
      ( r2_hidden(B_76,B_77)
      | ~ r1_tarski(A_78,B_77)
      | ~ m1_subset_1(B_76,A_78)
      | v1_xboole_0(A_78) ) ),
    inference(resolution,[status(thm)],[c_16,c_217])).

tff(c_335,plain,(
    ! [B_76] :
      ( r2_hidden(B_76,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(B_76,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_46,c_324])).

tff(c_811,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_335])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_47,plain,(
    r1_tarski('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_39])).

tff(c_334,plain,(
    ! [B_76] :
      ( r2_hidden(B_76,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(B_76,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_47,c_324])).

tff(c_337,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_334])).

tff(c_341,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_335])).

tff(c_24,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_138,plain,(
    ! [C_43,B_44,A_45] :
      ( ~ v1_xboole_0(C_43)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(C_43))
      | ~ r2_hidden(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_164,plain,(
    ! [B_49,A_50,A_51] :
      ( ~ v1_xboole_0(B_49)
      | ~ r2_hidden(A_50,A_51)
      | ~ r1_tarski(A_51,B_49) ) ),
    inference(resolution,[status(thm)],[c_24,c_138])).

tff(c_174,plain,(
    ! [B_52,A_53,B_54] :
      ( ~ v1_xboole_0(B_52)
      | ~ r1_tarski(A_53,B_52)
      | r1_tarski(A_53,B_54) ) ),
    inference(resolution,[status(thm)],[c_6,c_164])).

tff(c_183,plain,(
    ! [B_7,B_54] :
      ( ~ v1_xboole_0(B_7)
      | r1_tarski(B_7,B_54) ) ),
    inference(resolution,[status(thm)],[c_12,c_174])).

tff(c_184,plain,(
    ! [B_55,B_56] :
      ( ~ v1_xboole_0(B_55)
      | r1_tarski(B_55,B_56) ) ),
    inference(resolution,[status(thm)],[c_12,c_174])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_199,plain,(
    ! [B_58,B_57] :
      ( B_58 = B_57
      | ~ r1_tarski(B_57,B_58)
      | ~ v1_xboole_0(B_58) ) ),
    inference(resolution,[status(thm)],[c_184,c_8])).

tff(c_212,plain,(
    ! [B_7,B_54] :
      ( B_7 = B_54
      | ~ v1_xboole_0(B_54)
      | ~ v1_xboole_0(B_7) ) ),
    inference(resolution,[status(thm)],[c_183,c_199])).

tff(c_345,plain,(
    ! [B_79] :
      ( B_79 = '#skF_3'
      | ~ v1_xboole_0(B_79) ) ),
    inference(resolution,[status(thm)],[c_337,c_212])).

tff(c_348,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_341,c_345])).

tff(c_355,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_348])).

tff(c_357,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_335])).

tff(c_100,plain,(
    ! [A_36,B_37] :
      ( r2_hidden('#skF_1'(A_36,B_37),A_36)
      | r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( m1_subset_1(B_9,A_8)
      | ~ r2_hidden(B_9,A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_110,plain,(
    ! [A_36,B_37] :
      ( m1_subset_1('#skF_1'(A_36,B_37),A_36)
      | v1_xboole_0(A_36)
      | r1_tarski(A_36,B_37) ) ),
    inference(resolution,[status(thm)],[c_100,c_14])).

tff(c_150,plain,(
    ! [A_45] :
      ( ~ v1_xboole_0(k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_45,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_138])).

tff(c_152,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_364,plain,(
    ! [B_81] :
      ( r2_hidden(B_81,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(B_81,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_335])).

tff(c_375,plain,(
    ! [B_81] :
      ( m1_subset_1(B_81,k1_zfmisc_1('#skF_2'))
      | v1_xboole_0(k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(B_81,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_364,c_14])).

tff(c_395,plain,(
    ! [B_86] :
      ( m1_subset_1(B_86,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(B_86,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_375])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_421,plain,(
    ! [B_86] :
      ( r1_tarski(B_86,'#skF_2')
      | ~ m1_subset_1(B_86,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_395,c_22])).

tff(c_124,plain,(
    ! [D_40] :
      ( r2_hidden(D_40,'#skF_3')
      | ~ r2_hidden(D_40,'#skF_4')
      | ~ m1_subset_1(D_40,k1_zfmisc_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_133,plain,(
    ! [A_10] :
      ( r2_hidden(A_10,'#skF_3')
      | ~ r2_hidden(A_10,'#skF_4')
      | ~ r1_tarski(A_10,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_124])).

tff(c_171,plain,(
    ! [B_49,A_10] :
      ( ~ v1_xboole_0(B_49)
      | ~ r1_tarski('#skF_3',B_49)
      | ~ r2_hidden(A_10,'#skF_4')
      | ~ r1_tarski(A_10,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_133,c_164])).

tff(c_597,plain,(
    ! [A_98] :
      ( ~ r2_hidden(A_98,'#skF_4')
      | ~ r1_tarski(A_98,'#skF_2') ) ),
    inference(splitLeft,[status(thm)],[c_171])).

tff(c_609,plain,(
    ! [B_9] :
      ( ~ r1_tarski(B_9,'#skF_2')
      | ~ m1_subset_1(B_9,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_597])).

tff(c_615,plain,(
    ! [B_99] :
      ( ~ r1_tarski(B_99,'#skF_2')
      | ~ m1_subset_1(B_99,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_357,c_609])).

tff(c_635,plain,(
    ! [B_100] : ~ m1_subset_1(B_100,'#skF_4') ),
    inference(resolution,[status(thm)],[c_421,c_615])).

tff(c_639,plain,(
    ! [B_37] :
      ( v1_xboole_0('#skF_4')
      | r1_tarski('#skF_4',B_37) ) ),
    inference(resolution,[status(thm)],[c_110,c_635])).

tff(c_649,plain,(
    ! [B_101] : r1_tarski('#skF_4',B_101) ),
    inference(negUnitSimplification,[status(thm)],[c_357,c_639])).

tff(c_198,plain,(
    ! [B_56,B_55] :
      ( B_56 = B_55
      | ~ r1_tarski(B_56,B_55)
      | ~ v1_xboole_0(B_55) ) ),
    inference(resolution,[status(thm)],[c_184,c_8])).

tff(c_672,plain,(
    ! [B_102] :
      ( B_102 = '#skF_4'
      | ~ v1_xboole_0(B_102) ) ),
    inference(resolution,[status(thm)],[c_649,c_198])).

tff(c_675,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_337,c_672])).

tff(c_679,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_675])).

tff(c_681,plain,(
    ! [B_103] :
      ( ~ v1_xboole_0(B_103)
      | ~ r1_tarski('#skF_3',B_103) ) ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_696,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_681])).

tff(c_705,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_696])).

tff(c_707,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_334])).

tff(c_708,plain,(
    ! [B_104] :
      ( r2_hidden(B_104,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(B_104,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_334])).

tff(c_719,plain,(
    ! [B_104] :
      ( m1_subset_1(B_104,k1_zfmisc_1('#skF_2'))
      | v1_xboole_0(k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(B_104,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_708,c_14])).

tff(c_726,plain,(
    ! [B_105] :
      ( m1_subset_1(B_105,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(B_105,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_719])).

tff(c_36,plain,(
    ! [D_19] :
      ( r2_hidden(D_19,'#skF_4')
      | ~ r2_hidden(D_19,'#skF_3')
      | ~ m1_subset_1(D_19,k1_zfmisc_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_881,plain,(
    ! [B_114] :
      ( r2_hidden(B_114,'#skF_4')
      | ~ r2_hidden(B_114,'#skF_3')
      | ~ m1_subset_1(B_114,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_726,c_36])).

tff(c_899,plain,(
    ! [B_9] :
      ( r2_hidden(B_9,'#skF_4')
      | ~ m1_subset_1(B_9,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_16,c_881])).

tff(c_907,plain,(
    ! [B_115] :
      ( r2_hidden(B_115,'#skF_4')
      | ~ m1_subset_1(B_115,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_707,c_899])).

tff(c_148,plain,(
    ! [B_11,A_45,A_10] :
      ( ~ v1_xboole_0(B_11)
      | ~ r2_hidden(A_45,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(resolution,[status(thm)],[c_24,c_138])).

tff(c_920,plain,(
    ! [B_11,B_115] :
      ( ~ v1_xboole_0(B_11)
      | ~ r1_tarski('#skF_4',B_11)
      | ~ m1_subset_1(B_115,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_907,c_148])).

tff(c_941,plain,(
    ! [B_120] : ~ m1_subset_1(B_120,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_920])).

tff(c_945,plain,(
    ! [B_37] :
      ( v1_xboole_0('#skF_3')
      | r1_tarski('#skF_3',B_37) ) ),
    inference(resolution,[status(thm)],[c_110,c_941])).

tff(c_955,plain,(
    ! [B_121] : r1_tarski('#skF_3',B_121) ),
    inference(negUnitSimplification,[status(thm)],[c_707,c_945])).

tff(c_979,plain,(
    ! [B_122] :
      ( B_122 = '#skF_3'
      | ~ v1_xboole_0(B_122) ) ),
    inference(resolution,[status(thm)],[c_955,c_198])).

tff(c_982,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_811,c_979])).

tff(c_986,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_982])).

tff(c_988,plain,(
    ! [B_123] :
      ( ~ v1_xboole_0(B_123)
      | ~ r1_tarski('#skF_4',B_123) ) ),
    inference(splitRight,[status(thm)],[c_920])).

tff(c_1003,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_988])).

tff(c_1012,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_811,c_1003])).

tff(c_1014,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_335])).

tff(c_752,plain,(
    ! [B_105] :
      ( r1_tarski(B_105,'#skF_2')
      | ~ m1_subset_1(B_105,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_726,c_22])).

tff(c_59,plain,(
    ! [D_27] :
      ( r2_hidden(D_27,'#skF_4')
      | ~ r2_hidden(D_27,'#skF_3')
      | ~ m1_subset_1(D_27,k1_zfmisc_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_228,plain,(
    ! [A_64] :
      ( r2_hidden(A_64,'#skF_4')
      | ~ r2_hidden(A_64,'#skF_3')
      | ~ r1_tarski(A_64,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_59])).

tff(c_242,plain,(
    ! [B_9] :
      ( r2_hidden(B_9,'#skF_4')
      | ~ r1_tarski(B_9,'#skF_2')
      | ~ m1_subset_1(B_9,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_16,c_228])).

tff(c_1393,plain,(
    ! [B_143] :
      ( r2_hidden(B_143,'#skF_4')
      | ~ r1_tarski(B_143,'#skF_2')
      | ~ m1_subset_1(B_143,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_707,c_242])).

tff(c_1404,plain,(
    ! [B_143] :
      ( m1_subset_1(B_143,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ r1_tarski(B_143,'#skF_2')
      | ~ m1_subset_1(B_143,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1393,c_14])).

tff(c_1643,plain,(
    ! [B_161] :
      ( m1_subset_1(B_161,'#skF_4')
      | ~ r1_tarski(B_161,'#skF_2')
      | ~ m1_subset_1(B_161,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1014,c_1404])).

tff(c_1686,plain,(
    ! [B_166] :
      ( m1_subset_1(B_166,'#skF_4')
      | ~ m1_subset_1(B_166,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_752,c_1643])).

tff(c_1690,plain,(
    ! [B_37] :
      ( m1_subset_1('#skF_1'('#skF_3',B_37),'#skF_4')
      | v1_xboole_0('#skF_3')
      | r1_tarski('#skF_3',B_37) ) ),
    inference(resolution,[status(thm)],[c_110,c_1686])).

tff(c_1742,plain,(
    ! [B_169] :
      ( m1_subset_1('#skF_1'('#skF_3',B_169),'#skF_4')
      | r1_tarski('#skF_3',B_169) ) ),
    inference(negUnitSimplification,[status(thm)],[c_707,c_1690])).

tff(c_90,plain,(
    ! [B_34,A_35] :
      ( r2_hidden(B_34,A_35)
      | ~ m1_subset_1(B_34,A_35)
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_98,plain,(
    ! [A_1,A_35] :
      ( r1_tarski(A_1,A_35)
      | ~ m1_subset_1('#skF_1'(A_1,A_35),A_35)
      | v1_xboole_0(A_35) ) ),
    inference(resolution,[status(thm)],[c_90,c_4])).

tff(c_1746,plain,
    ( v1_xboole_0('#skF_4')
    | r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_1742,c_98])).

tff(c_1752,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1014,c_1746])).

tff(c_1769,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1752,c_8])).

tff(c_1781,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_1769])).

tff(c_1015,plain,(
    ! [B_124] :
      ( r2_hidden(B_124,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(B_124,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_335])).

tff(c_1026,plain,(
    ! [B_124] :
      ( m1_subset_1(B_124,k1_zfmisc_1('#skF_2'))
      | v1_xboole_0(k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(B_124,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1015,c_14])).

tff(c_1033,plain,(
    ! [B_125] :
      ( m1_subset_1(B_125,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(B_125,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_1026])).

tff(c_1059,plain,(
    ! [B_125] :
      ( r1_tarski(B_125,'#skF_2')
      | ~ m1_subset_1(B_125,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1033,c_22])).

tff(c_153,plain,(
    ! [A_46] :
      ( r2_hidden(A_46,'#skF_3')
      | ~ r2_hidden(A_46,'#skF_4')
      | ~ r1_tarski(A_46,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_124])).

tff(c_162,plain,(
    ! [A_46] :
      ( m1_subset_1(A_46,'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_46,'#skF_4')
      | ~ r1_tarski(A_46,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_153,c_14])).

tff(c_1787,plain,(
    ! [A_170] :
      ( m1_subset_1(A_170,'#skF_3')
      | ~ r2_hidden(A_170,'#skF_4')
      | ~ r1_tarski(A_170,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_707,c_162])).

tff(c_1802,plain,(
    ! [B_9] :
      ( m1_subset_1(B_9,'#skF_3')
      | ~ r1_tarski(B_9,'#skF_2')
      | ~ m1_subset_1(B_9,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_1787])).

tff(c_2097,plain,(
    ! [B_191] :
      ( m1_subset_1(B_191,'#skF_3')
      | ~ r1_tarski(B_191,'#skF_2')
      | ~ m1_subset_1(B_191,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1014,c_1802])).

tff(c_2122,plain,(
    ! [B_192] :
      ( m1_subset_1(B_192,'#skF_3')
      | ~ m1_subset_1(B_192,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1059,c_2097])).

tff(c_2135,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1('#skF_1'(A_1,'#skF_3'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2122,c_98])).

tff(c_2164,plain,(
    ! [A_195] :
      ( r1_tarski(A_195,'#skF_3')
      | ~ m1_subset_1('#skF_1'(A_195,'#skF_3'),'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_707,c_2135])).

tff(c_2172,plain,
    ( v1_xboole_0('#skF_4')
    | r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_110,c_2164])).

tff(c_2181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1781,c_1014,c_1781,c_2172])).

tff(c_2185,plain,(
    ! [A_196] : ~ r2_hidden(A_196,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_2194,plain,(
    ! [B_2] : r1_tarski('#skF_4',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_2185])).

tff(c_2183,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_151,plain,(
    ! [A_45] :
      ( ~ v1_xboole_0(k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_45,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_138])).

tff(c_2201,plain,(
    ! [A_197] : ~ r2_hidden(A_197,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2183,c_151])).

tff(c_2218,plain,(
    ! [B_199] : r1_tarski('#skF_3',B_199) ),
    inference(resolution,[status(thm)],[c_6,c_2201])).

tff(c_2275,plain,(
    ! [B_203] :
      ( B_203 = '#skF_3'
      | ~ r1_tarski(B_203,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2218,c_8])).

tff(c_2283,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2194,c_2275])).

tff(c_2293,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_2283])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:48:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.38/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.60  
% 3.38/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.60  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.38/1.60  
% 3.38/1.60  %Foreground sorts:
% 3.38/1.60  
% 3.38/1.60  
% 3.38/1.60  %Background operators:
% 3.38/1.60  
% 3.38/1.60  
% 3.38/1.60  %Foreground operators:
% 3.38/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.38/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.38/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.38/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.38/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.38/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.38/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.38/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.38/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.38/1.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.38/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.38/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.38/1.60  
% 3.69/1.63  tff(f_77, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_setfam_1)).
% 3.69/1.63  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.69/1.63  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.69/1.63  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.69/1.63  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.69/1.63  tff(f_62, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.69/1.63  tff(c_28, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.69/1.63  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.69/1.63  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.69/1.63  tff(c_39, plain, (![A_21, B_22]: (r1_tarski(A_21, B_22) | ~m1_subset_1(A_21, k1_zfmisc_1(B_22)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.69/1.63  tff(c_46, plain, (r1_tarski('#skF_4', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_39])).
% 3.69/1.63  tff(c_16, plain, (![B_9, A_8]: (r2_hidden(B_9, A_8) | ~m1_subset_1(B_9, A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.69/1.63  tff(c_217, plain, (![C_59, B_60, A_61]: (r2_hidden(C_59, B_60) | ~r2_hidden(C_59, A_61) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.69/1.63  tff(c_324, plain, (![B_76, B_77, A_78]: (r2_hidden(B_76, B_77) | ~r1_tarski(A_78, B_77) | ~m1_subset_1(B_76, A_78) | v1_xboole_0(A_78))), inference(resolution, [status(thm)], [c_16, c_217])).
% 3.69/1.63  tff(c_335, plain, (![B_76]: (r2_hidden(B_76, k1_zfmisc_1('#skF_2')) | ~m1_subset_1(B_76, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_46, c_324])).
% 3.69/1.63  tff(c_811, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_335])).
% 3.69/1.63  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.69/1.63  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.69/1.63  tff(c_47, plain, (r1_tarski('#skF_3', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_39])).
% 3.69/1.63  tff(c_334, plain, (![B_76]: (r2_hidden(B_76, k1_zfmisc_1('#skF_2')) | ~m1_subset_1(B_76, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_47, c_324])).
% 3.69/1.63  tff(c_337, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_334])).
% 3.69/1.63  tff(c_341, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_335])).
% 3.69/1.63  tff(c_24, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.69/1.63  tff(c_138, plain, (![C_43, B_44, A_45]: (~v1_xboole_0(C_43) | ~m1_subset_1(B_44, k1_zfmisc_1(C_43)) | ~r2_hidden(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.69/1.63  tff(c_164, plain, (![B_49, A_50, A_51]: (~v1_xboole_0(B_49) | ~r2_hidden(A_50, A_51) | ~r1_tarski(A_51, B_49))), inference(resolution, [status(thm)], [c_24, c_138])).
% 3.69/1.63  tff(c_174, plain, (![B_52, A_53, B_54]: (~v1_xboole_0(B_52) | ~r1_tarski(A_53, B_52) | r1_tarski(A_53, B_54))), inference(resolution, [status(thm)], [c_6, c_164])).
% 3.69/1.63  tff(c_183, plain, (![B_7, B_54]: (~v1_xboole_0(B_7) | r1_tarski(B_7, B_54))), inference(resolution, [status(thm)], [c_12, c_174])).
% 3.69/1.63  tff(c_184, plain, (![B_55, B_56]: (~v1_xboole_0(B_55) | r1_tarski(B_55, B_56))), inference(resolution, [status(thm)], [c_12, c_174])).
% 3.69/1.63  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.69/1.63  tff(c_199, plain, (![B_58, B_57]: (B_58=B_57 | ~r1_tarski(B_57, B_58) | ~v1_xboole_0(B_58))), inference(resolution, [status(thm)], [c_184, c_8])).
% 3.69/1.63  tff(c_212, plain, (![B_7, B_54]: (B_7=B_54 | ~v1_xboole_0(B_54) | ~v1_xboole_0(B_7))), inference(resolution, [status(thm)], [c_183, c_199])).
% 3.69/1.63  tff(c_345, plain, (![B_79]: (B_79='#skF_3' | ~v1_xboole_0(B_79))), inference(resolution, [status(thm)], [c_337, c_212])).
% 3.69/1.63  tff(c_348, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_341, c_345])).
% 3.69/1.63  tff(c_355, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_348])).
% 3.69/1.63  tff(c_357, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_335])).
% 3.69/1.63  tff(c_100, plain, (![A_36, B_37]: (r2_hidden('#skF_1'(A_36, B_37), A_36) | r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.69/1.63  tff(c_14, plain, (![B_9, A_8]: (m1_subset_1(B_9, A_8) | ~r2_hidden(B_9, A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.69/1.63  tff(c_110, plain, (![A_36, B_37]: (m1_subset_1('#skF_1'(A_36, B_37), A_36) | v1_xboole_0(A_36) | r1_tarski(A_36, B_37))), inference(resolution, [status(thm)], [c_100, c_14])).
% 3.69/1.63  tff(c_150, plain, (![A_45]: (~v1_xboole_0(k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_45, '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_138])).
% 3.69/1.63  tff(c_152, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_150])).
% 3.69/1.63  tff(c_364, plain, (![B_81]: (r2_hidden(B_81, k1_zfmisc_1('#skF_2')) | ~m1_subset_1(B_81, '#skF_4'))), inference(splitRight, [status(thm)], [c_335])).
% 3.69/1.63  tff(c_375, plain, (![B_81]: (m1_subset_1(B_81, k1_zfmisc_1('#skF_2')) | v1_xboole_0(k1_zfmisc_1('#skF_2')) | ~m1_subset_1(B_81, '#skF_4'))), inference(resolution, [status(thm)], [c_364, c_14])).
% 3.69/1.63  tff(c_395, plain, (![B_86]: (m1_subset_1(B_86, k1_zfmisc_1('#skF_2')) | ~m1_subset_1(B_86, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_152, c_375])).
% 3.69/1.63  tff(c_22, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.69/1.63  tff(c_421, plain, (![B_86]: (r1_tarski(B_86, '#skF_2') | ~m1_subset_1(B_86, '#skF_4'))), inference(resolution, [status(thm)], [c_395, c_22])).
% 3.69/1.63  tff(c_124, plain, (![D_40]: (r2_hidden(D_40, '#skF_3') | ~r2_hidden(D_40, '#skF_4') | ~m1_subset_1(D_40, k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.69/1.63  tff(c_133, plain, (![A_10]: (r2_hidden(A_10, '#skF_3') | ~r2_hidden(A_10, '#skF_4') | ~r1_tarski(A_10, '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_124])).
% 3.69/1.63  tff(c_171, plain, (![B_49, A_10]: (~v1_xboole_0(B_49) | ~r1_tarski('#skF_3', B_49) | ~r2_hidden(A_10, '#skF_4') | ~r1_tarski(A_10, '#skF_2'))), inference(resolution, [status(thm)], [c_133, c_164])).
% 3.69/1.63  tff(c_597, plain, (![A_98]: (~r2_hidden(A_98, '#skF_4') | ~r1_tarski(A_98, '#skF_2'))), inference(splitLeft, [status(thm)], [c_171])).
% 3.69/1.63  tff(c_609, plain, (![B_9]: (~r1_tarski(B_9, '#skF_2') | ~m1_subset_1(B_9, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_16, c_597])).
% 3.69/1.63  tff(c_615, plain, (![B_99]: (~r1_tarski(B_99, '#skF_2') | ~m1_subset_1(B_99, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_357, c_609])).
% 3.69/1.63  tff(c_635, plain, (![B_100]: (~m1_subset_1(B_100, '#skF_4'))), inference(resolution, [status(thm)], [c_421, c_615])).
% 3.69/1.63  tff(c_639, plain, (![B_37]: (v1_xboole_0('#skF_4') | r1_tarski('#skF_4', B_37))), inference(resolution, [status(thm)], [c_110, c_635])).
% 3.69/1.63  tff(c_649, plain, (![B_101]: (r1_tarski('#skF_4', B_101))), inference(negUnitSimplification, [status(thm)], [c_357, c_639])).
% 3.69/1.63  tff(c_198, plain, (![B_56, B_55]: (B_56=B_55 | ~r1_tarski(B_56, B_55) | ~v1_xboole_0(B_55))), inference(resolution, [status(thm)], [c_184, c_8])).
% 3.69/1.63  tff(c_672, plain, (![B_102]: (B_102='#skF_4' | ~v1_xboole_0(B_102))), inference(resolution, [status(thm)], [c_649, c_198])).
% 3.69/1.63  tff(c_675, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_337, c_672])).
% 3.69/1.63  tff(c_679, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_675])).
% 3.69/1.63  tff(c_681, plain, (![B_103]: (~v1_xboole_0(B_103) | ~r1_tarski('#skF_3', B_103))), inference(splitRight, [status(thm)], [c_171])).
% 3.69/1.63  tff(c_696, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_12, c_681])).
% 3.69/1.63  tff(c_705, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_337, c_696])).
% 3.69/1.63  tff(c_707, plain, (~v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_334])).
% 3.69/1.63  tff(c_708, plain, (![B_104]: (r2_hidden(B_104, k1_zfmisc_1('#skF_2')) | ~m1_subset_1(B_104, '#skF_3'))), inference(splitRight, [status(thm)], [c_334])).
% 3.69/1.63  tff(c_719, plain, (![B_104]: (m1_subset_1(B_104, k1_zfmisc_1('#skF_2')) | v1_xboole_0(k1_zfmisc_1('#skF_2')) | ~m1_subset_1(B_104, '#skF_3'))), inference(resolution, [status(thm)], [c_708, c_14])).
% 3.69/1.63  tff(c_726, plain, (![B_105]: (m1_subset_1(B_105, k1_zfmisc_1('#skF_2')) | ~m1_subset_1(B_105, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_152, c_719])).
% 3.69/1.63  tff(c_36, plain, (![D_19]: (r2_hidden(D_19, '#skF_4') | ~r2_hidden(D_19, '#skF_3') | ~m1_subset_1(D_19, k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.69/1.63  tff(c_881, plain, (![B_114]: (r2_hidden(B_114, '#skF_4') | ~r2_hidden(B_114, '#skF_3') | ~m1_subset_1(B_114, '#skF_3'))), inference(resolution, [status(thm)], [c_726, c_36])).
% 3.69/1.63  tff(c_899, plain, (![B_9]: (r2_hidden(B_9, '#skF_4') | ~m1_subset_1(B_9, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_16, c_881])).
% 3.69/1.63  tff(c_907, plain, (![B_115]: (r2_hidden(B_115, '#skF_4') | ~m1_subset_1(B_115, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_707, c_899])).
% 3.69/1.63  tff(c_148, plain, (![B_11, A_45, A_10]: (~v1_xboole_0(B_11) | ~r2_hidden(A_45, A_10) | ~r1_tarski(A_10, B_11))), inference(resolution, [status(thm)], [c_24, c_138])).
% 3.69/1.63  tff(c_920, plain, (![B_11, B_115]: (~v1_xboole_0(B_11) | ~r1_tarski('#skF_4', B_11) | ~m1_subset_1(B_115, '#skF_3'))), inference(resolution, [status(thm)], [c_907, c_148])).
% 3.69/1.63  tff(c_941, plain, (![B_120]: (~m1_subset_1(B_120, '#skF_3'))), inference(splitLeft, [status(thm)], [c_920])).
% 3.69/1.63  tff(c_945, plain, (![B_37]: (v1_xboole_0('#skF_3') | r1_tarski('#skF_3', B_37))), inference(resolution, [status(thm)], [c_110, c_941])).
% 3.69/1.63  tff(c_955, plain, (![B_121]: (r1_tarski('#skF_3', B_121))), inference(negUnitSimplification, [status(thm)], [c_707, c_945])).
% 3.69/1.63  tff(c_979, plain, (![B_122]: (B_122='#skF_3' | ~v1_xboole_0(B_122))), inference(resolution, [status(thm)], [c_955, c_198])).
% 3.69/1.63  tff(c_982, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_811, c_979])).
% 3.69/1.63  tff(c_986, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_982])).
% 3.69/1.63  tff(c_988, plain, (![B_123]: (~v1_xboole_0(B_123) | ~r1_tarski('#skF_4', B_123))), inference(splitRight, [status(thm)], [c_920])).
% 3.69/1.63  tff(c_1003, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_12, c_988])).
% 3.69/1.63  tff(c_1012, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_811, c_1003])).
% 3.69/1.63  tff(c_1014, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_335])).
% 3.69/1.63  tff(c_752, plain, (![B_105]: (r1_tarski(B_105, '#skF_2') | ~m1_subset_1(B_105, '#skF_3'))), inference(resolution, [status(thm)], [c_726, c_22])).
% 3.69/1.63  tff(c_59, plain, (![D_27]: (r2_hidden(D_27, '#skF_4') | ~r2_hidden(D_27, '#skF_3') | ~m1_subset_1(D_27, k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.69/1.63  tff(c_228, plain, (![A_64]: (r2_hidden(A_64, '#skF_4') | ~r2_hidden(A_64, '#skF_3') | ~r1_tarski(A_64, '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_59])).
% 3.69/1.63  tff(c_242, plain, (![B_9]: (r2_hidden(B_9, '#skF_4') | ~r1_tarski(B_9, '#skF_2') | ~m1_subset_1(B_9, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_16, c_228])).
% 3.69/1.63  tff(c_1393, plain, (![B_143]: (r2_hidden(B_143, '#skF_4') | ~r1_tarski(B_143, '#skF_2') | ~m1_subset_1(B_143, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_707, c_242])).
% 3.69/1.63  tff(c_1404, plain, (![B_143]: (m1_subset_1(B_143, '#skF_4') | v1_xboole_0('#skF_4') | ~r1_tarski(B_143, '#skF_2') | ~m1_subset_1(B_143, '#skF_3'))), inference(resolution, [status(thm)], [c_1393, c_14])).
% 3.69/1.63  tff(c_1643, plain, (![B_161]: (m1_subset_1(B_161, '#skF_4') | ~r1_tarski(B_161, '#skF_2') | ~m1_subset_1(B_161, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1014, c_1404])).
% 3.69/1.63  tff(c_1686, plain, (![B_166]: (m1_subset_1(B_166, '#skF_4') | ~m1_subset_1(B_166, '#skF_3'))), inference(resolution, [status(thm)], [c_752, c_1643])).
% 3.69/1.63  tff(c_1690, plain, (![B_37]: (m1_subset_1('#skF_1'('#skF_3', B_37), '#skF_4') | v1_xboole_0('#skF_3') | r1_tarski('#skF_3', B_37))), inference(resolution, [status(thm)], [c_110, c_1686])).
% 3.69/1.63  tff(c_1742, plain, (![B_169]: (m1_subset_1('#skF_1'('#skF_3', B_169), '#skF_4') | r1_tarski('#skF_3', B_169))), inference(negUnitSimplification, [status(thm)], [c_707, c_1690])).
% 3.69/1.63  tff(c_90, plain, (![B_34, A_35]: (r2_hidden(B_34, A_35) | ~m1_subset_1(B_34, A_35) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.69/1.63  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.69/1.63  tff(c_98, plain, (![A_1, A_35]: (r1_tarski(A_1, A_35) | ~m1_subset_1('#skF_1'(A_1, A_35), A_35) | v1_xboole_0(A_35))), inference(resolution, [status(thm)], [c_90, c_4])).
% 3.69/1.63  tff(c_1746, plain, (v1_xboole_0('#skF_4') | r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_1742, c_98])).
% 3.69/1.63  tff(c_1752, plain, (r1_tarski('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1014, c_1746])).
% 3.69/1.63  tff(c_1769, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1752, c_8])).
% 3.69/1.63  tff(c_1781, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_28, c_1769])).
% 3.69/1.63  tff(c_1015, plain, (![B_124]: (r2_hidden(B_124, k1_zfmisc_1('#skF_2')) | ~m1_subset_1(B_124, '#skF_4'))), inference(splitRight, [status(thm)], [c_335])).
% 3.69/1.63  tff(c_1026, plain, (![B_124]: (m1_subset_1(B_124, k1_zfmisc_1('#skF_2')) | v1_xboole_0(k1_zfmisc_1('#skF_2')) | ~m1_subset_1(B_124, '#skF_4'))), inference(resolution, [status(thm)], [c_1015, c_14])).
% 3.69/1.63  tff(c_1033, plain, (![B_125]: (m1_subset_1(B_125, k1_zfmisc_1('#skF_2')) | ~m1_subset_1(B_125, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_152, c_1026])).
% 3.69/1.63  tff(c_1059, plain, (![B_125]: (r1_tarski(B_125, '#skF_2') | ~m1_subset_1(B_125, '#skF_4'))), inference(resolution, [status(thm)], [c_1033, c_22])).
% 3.69/1.63  tff(c_153, plain, (![A_46]: (r2_hidden(A_46, '#skF_3') | ~r2_hidden(A_46, '#skF_4') | ~r1_tarski(A_46, '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_124])).
% 3.69/1.63  tff(c_162, plain, (![A_46]: (m1_subset_1(A_46, '#skF_3') | v1_xboole_0('#skF_3') | ~r2_hidden(A_46, '#skF_4') | ~r1_tarski(A_46, '#skF_2'))), inference(resolution, [status(thm)], [c_153, c_14])).
% 3.69/1.63  tff(c_1787, plain, (![A_170]: (m1_subset_1(A_170, '#skF_3') | ~r2_hidden(A_170, '#skF_4') | ~r1_tarski(A_170, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_707, c_162])).
% 3.69/1.63  tff(c_1802, plain, (![B_9]: (m1_subset_1(B_9, '#skF_3') | ~r1_tarski(B_9, '#skF_2') | ~m1_subset_1(B_9, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_16, c_1787])).
% 3.69/1.63  tff(c_2097, plain, (![B_191]: (m1_subset_1(B_191, '#skF_3') | ~r1_tarski(B_191, '#skF_2') | ~m1_subset_1(B_191, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1014, c_1802])).
% 3.69/1.63  tff(c_2122, plain, (![B_192]: (m1_subset_1(B_192, '#skF_3') | ~m1_subset_1(B_192, '#skF_4'))), inference(resolution, [status(thm)], [c_1059, c_2097])).
% 3.69/1.63  tff(c_2135, plain, (![A_1]: (r1_tarski(A_1, '#skF_3') | v1_xboole_0('#skF_3') | ~m1_subset_1('#skF_1'(A_1, '#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_2122, c_98])).
% 3.69/1.63  tff(c_2164, plain, (![A_195]: (r1_tarski(A_195, '#skF_3') | ~m1_subset_1('#skF_1'(A_195, '#skF_3'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_707, c_2135])).
% 3.69/1.63  tff(c_2172, plain, (v1_xboole_0('#skF_4') | r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_110, c_2164])).
% 3.69/1.63  tff(c_2181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1781, c_1014, c_1781, c_2172])).
% 3.69/1.63  tff(c_2185, plain, (![A_196]: (~r2_hidden(A_196, '#skF_4'))), inference(splitRight, [status(thm)], [c_150])).
% 3.69/1.63  tff(c_2194, plain, (![B_2]: (r1_tarski('#skF_4', B_2))), inference(resolution, [status(thm)], [c_6, c_2185])).
% 3.69/1.63  tff(c_2183, plain, (v1_xboole_0(k1_zfmisc_1('#skF_2'))), inference(splitRight, [status(thm)], [c_150])).
% 3.69/1.63  tff(c_151, plain, (![A_45]: (~v1_xboole_0(k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_45, '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_138])).
% 3.69/1.63  tff(c_2201, plain, (![A_197]: (~r2_hidden(A_197, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2183, c_151])).
% 3.69/1.63  tff(c_2218, plain, (![B_199]: (r1_tarski('#skF_3', B_199))), inference(resolution, [status(thm)], [c_6, c_2201])).
% 3.69/1.63  tff(c_2275, plain, (![B_203]: (B_203='#skF_3' | ~r1_tarski(B_203, '#skF_3'))), inference(resolution, [status(thm)], [c_2218, c_8])).
% 3.69/1.63  tff(c_2283, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_2194, c_2275])).
% 3.69/1.63  tff(c_2293, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_2283])).
% 3.69/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.63  
% 3.69/1.63  Inference rules
% 3.69/1.63  ----------------------
% 3.69/1.63  #Ref     : 0
% 3.69/1.63  #Sup     : 450
% 3.69/1.63  #Fact    : 0
% 3.69/1.63  #Define  : 0
% 3.69/1.63  #Split   : 20
% 3.69/1.63  #Chain   : 0
% 3.69/1.63  #Close   : 0
% 3.69/1.63  
% 3.69/1.63  Ordering : KBO
% 3.69/1.63  
% 3.69/1.63  Simplification rules
% 3.69/1.63  ----------------------
% 3.69/1.63  #Subsume      : 269
% 3.69/1.63  #Demod        : 52
% 3.69/1.63  #Tautology    : 84
% 3.69/1.63  #SimpNegUnit  : 98
% 3.69/1.63  #BackRed      : 19
% 3.69/1.63  
% 3.69/1.63  #Partial instantiations: 0
% 3.69/1.63  #Strategies tried      : 1
% 3.69/1.63  
% 3.69/1.63  Timing (in seconds)
% 3.69/1.63  ----------------------
% 3.69/1.63  Preprocessing        : 0.29
% 3.69/1.63  Parsing              : 0.15
% 3.69/1.63  CNF conversion       : 0.02
% 3.69/1.63  Main loop            : 0.56
% 3.69/1.63  Inferencing          : 0.20
% 3.69/1.63  Reduction            : 0.15
% 3.69/1.63  Demodulation         : 0.09
% 3.69/1.63  BG Simplification    : 0.02
% 3.69/1.63  Subsumption          : 0.13
% 3.69/1.63  Abstraction          : 0.02
% 3.69/1.63  MUC search           : 0.00
% 3.69/1.63  Cooper               : 0.00
% 3.69/1.63  Total                : 0.90
% 3.69/1.63  Index Insertion      : 0.00
% 3.69/1.63  Index Deletion       : 0.00
% 3.69/1.63  Index Matching       : 0.00
% 3.69/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
