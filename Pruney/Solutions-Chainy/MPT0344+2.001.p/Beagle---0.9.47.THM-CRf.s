%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:19 EST 2020

% Result     : Theorem 4.53s
% Output     : CNFRefutation 4.53s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 406 expanded)
%              Number of leaves         :   22 ( 136 expanded)
%              Depth                    :   18
%              Number of atoms          :  238 ( 998 expanded)
%              Number of equality atoms :   20 (  71 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ~ ( B != k1_xboole_0
            & ! [C] :
                ( m1_subset_1(C,A)
               => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_46,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_36,plain,(
    ! [B_19,A_18] :
      ( m1_subset_1(B_19,A_18)
      | ~ v1_xboole_0(B_19)
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_61,plain,(
    ! [B_28,A_29] :
      ( m1_subset_1(B_28,A_29)
      | ~ v1_xboole_0(B_28)
      | ~ v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    ! [C_27] :
      ( ~ r2_hidden(C_27,'#skF_6')
      | ~ m1_subset_1(C_27,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_59,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6'),'#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_54])).

tff(c_60,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_59])).

tff(c_65,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_6'))
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_61,c_60])).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_170,plain,(
    ! [B_48,A_49] :
      ( m1_subset_1(B_48,A_49)
      | ~ r2_hidden(B_48,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_197,plain,(
    ! [A_53] :
      ( m1_subset_1('#skF_1'(A_53),A_53)
      | v1_xboole_0(A_53) ) ),
    inference(resolution,[status(thm)],[c_4,c_170])).

tff(c_93,plain,(
    ! [B_38,A_39] :
      ( r2_hidden(B_38,A_39)
      | ~ m1_subset_1(B_38,A_39)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_40,plain,(
    ! [C_21] :
      ( ~ r2_hidden(C_21,'#skF_6')
      | ~ m1_subset_1(C_21,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_106,plain,(
    ! [B_38] :
      ( ~ m1_subset_1(B_38,'#skF_5')
      | ~ m1_subset_1(B_38,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_93,c_40])).

tff(c_108,plain,(
    ! [B_38] :
      ( ~ m1_subset_1(B_38,'#skF_5')
      | ~ m1_subset_1(B_38,'#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_201,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_197,c_108])).

tff(c_207,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_201])).

tff(c_217,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_5'))
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_207])).

tff(c_218,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_186,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_170])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_82,plain,(
    ! [C_36,A_37] :
      ( r1_tarski(C_36,A_37)
      | ~ r2_hidden(C_36,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_247,plain,(
    ! [A_62] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_62)),A_62)
      | v1_xboole_0(k1_zfmisc_1(A_62)) ) ),
    inference(resolution,[status(thm)],[c_4,c_82])).

tff(c_18,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_115,plain,(
    ! [B_41,A_42] :
      ( B_41 = A_42
      | ~ r1_tarski(B_41,A_42)
      | ~ r1_tarski(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_124,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_115])).

tff(c_258,plain,
    ( '#skF_1'(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_247,c_124])).

tff(c_260,plain,(
    v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_258])).

tff(c_67,plain,(
    ! [C_30,A_31] :
      ( r2_hidden(C_30,k1_zfmisc_1(A_31))
      | ~ r1_tarski(C_30,A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_71,plain,(
    ! [A_31,C_30] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_31))
      | ~ r1_tarski(C_30,A_31) ) ),
    inference(resolution,[status(thm)],[c_67,c_2])).

tff(c_302,plain,(
    ! [C_65] : ~ r1_tarski(C_65,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_260,c_71])).

tff(c_322,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_16,c_302])).

tff(c_324,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_258])).

tff(c_149,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_2'(A_46,B_47),A_46)
      | r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_20,plain,(
    ! [C_17,A_13] :
      ( r1_tarski(C_17,A_13)
      | ~ r2_hidden(C_17,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1215,plain,(
    ! [A_132,B_133] :
      ( r1_tarski('#skF_2'(k1_zfmisc_1(A_132),B_133),A_132)
      | r1_tarski(k1_zfmisc_1(A_132),B_133) ) ),
    inference(resolution,[status(thm)],[c_149,c_20])).

tff(c_1243,plain,(
    ! [B_135] :
      ( '#skF_2'(k1_zfmisc_1(k1_xboole_0),B_135) = k1_xboole_0
      | r1_tarski(k1_zfmisc_1(k1_xboole_0),B_135) ) ),
    inference(resolution,[status(thm)],[c_1215,c_124])).

tff(c_234,plain,(
    ! [C_59,B_60,A_61] :
      ( r2_hidden(C_59,B_60)
      | ~ r2_hidden(C_59,A_61)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_407,plain,(
    ! [A_69,B_70] :
      ( r2_hidden('#skF_1'(A_69),B_70)
      | ~ r1_tarski(A_69,B_70)
      | v1_xboole_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_4,c_234])).

tff(c_431,plain,(
    ! [B_70,A_69] :
      ( ~ v1_xboole_0(B_70)
      | ~ r1_tarski(A_69,B_70)
      | v1_xboole_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_407,c_2])).

tff(c_1255,plain,(
    ! [B_135] :
      ( ~ v1_xboole_0(B_135)
      | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
      | '#skF_2'(k1_zfmisc_1(k1_xboole_0),B_135) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1243,c_431])).

tff(c_1347,plain,(
    ! [B_138] :
      ( ~ v1_xboole_0(B_138)
      | '#skF_2'(k1_zfmisc_1(k1_xboole_0),B_138) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_324,c_1255])).

tff(c_22,plain,(
    ! [C_17,A_13] :
      ( r2_hidden(C_17,k1_zfmisc_1(A_13))
      | ~ r1_tarski(C_17,A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_138,plain,(
    ! [A_44,B_45] :
      ( ~ r2_hidden('#skF_2'(A_44,B_45),B_45)
      | r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_148,plain,(
    ! [A_44,A_13] :
      ( r1_tarski(A_44,k1_zfmisc_1(A_13))
      | ~ r1_tarski('#skF_2'(A_44,k1_zfmisc_1(A_13)),A_13) ) ),
    inference(resolution,[status(thm)],[c_22,c_138])).

tff(c_1370,plain,(
    ! [A_13] :
      ( r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(A_13))
      | ~ r1_tarski(k1_xboole_0,A_13)
      | ~ v1_xboole_0(k1_zfmisc_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1347,c_148])).

tff(c_1400,plain,(
    ! [A_139] :
      ( r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(A_139))
      | ~ v1_xboole_0(k1_zfmisc_1(A_139)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1370])).

tff(c_1405,plain,(
    ! [A_139] :
      ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_zfmisc_1(A_139)) ) ),
    inference(resolution,[status(thm)],[c_1400,c_431])).

tff(c_1417,plain,(
    ! [A_139] : ~ v1_xboole_0(k1_zfmisc_1(A_139)) ),
    inference(negUnitSimplification,[status(thm)],[c_324,c_1405])).

tff(c_105,plain,(
    ! [B_38,A_13] :
      ( r1_tarski(B_38,A_13)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_13))
      | v1_xboole_0(k1_zfmisc_1(A_13)) ) ),
    inference(resolution,[status(thm)],[c_93,c_20])).

tff(c_1614,plain,(
    ! [B_152,A_153] :
      ( r1_tarski(B_152,A_153)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(A_153)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1417,c_105])).

tff(c_1649,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_1614])).

tff(c_34,plain,(
    ! [B_19,A_18] :
      ( r2_hidden(B_19,A_18)
      | ~ m1_subset_1(B_19,A_18)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2472,plain,(
    ! [B_187,B_188,A_189] :
      ( r2_hidden(B_187,B_188)
      | ~ r1_tarski(A_189,B_188)
      | ~ m1_subset_1(B_187,A_189)
      | v1_xboole_0(A_189) ) ),
    inference(resolution,[status(thm)],[c_34,c_234])).

tff(c_2478,plain,(
    ! [B_187] :
      ( r2_hidden(B_187,'#skF_5')
      | ~ m1_subset_1(B_187,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1649,c_2472])).

tff(c_2517,plain,(
    ! [B_190] :
      ( r2_hidden(B_190,'#skF_5')
      | ~ m1_subset_1(B_190,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_2478])).

tff(c_32,plain,(
    ! [B_19,A_18] :
      ( m1_subset_1(B_19,A_18)
      | ~ r2_hidden(B_19,A_18)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2529,plain,(
    ! [B_190] :
      ( m1_subset_1(B_190,'#skF_5')
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(B_190,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2517,c_32])).

tff(c_2545,plain,(
    ! [B_191] :
      ( m1_subset_1(B_191,'#skF_5')
      | ~ m1_subset_1(B_191,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2529])).

tff(c_2593,plain,(
    ! [B_192] : ~ m1_subset_1(B_192,'#skF_6') ),
    inference(resolution,[status(thm)],[c_2545,c_108])).

tff(c_2601,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_186,c_2593])).

tff(c_2612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_2601])).

tff(c_2614,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_187,plain,(
    ! [A_50,B_51] :
      ( ~ v1_xboole_0(A_50)
      | r1_tarski(A_50,B_51) ) ),
    inference(resolution,[status(thm)],[c_149,c_2])).

tff(c_194,plain,(
    ! [A_50] :
      ( k1_xboole_0 = A_50
      | ~ v1_xboole_0(A_50) ) ),
    inference(resolution,[status(thm)],[c_187,c_124])).

tff(c_2617,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2614,c_194])).

tff(c_2621,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_2617])).

tff(c_2622,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_2657,plain,(
    ! [A_198,B_199] :
      ( r2_hidden('#skF_2'(A_198,B_199),A_198)
      | r1_tarski(A_198,B_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2695,plain,(
    ! [A_202,B_203] :
      ( ~ v1_xboole_0(A_202)
      | r1_tarski(A_202,B_203) ) ),
    inference(resolution,[status(thm)],[c_2657,c_2])).

tff(c_2623,plain,(
    ! [B_193,A_194] :
      ( B_193 = A_194
      | ~ r1_tarski(B_193,A_194)
      | ~ r1_tarski(A_194,B_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2632,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_2623])).

tff(c_2704,plain,(
    ! [A_204] :
      ( k1_xboole_0 = A_204
      | ~ v1_xboole_0(A_204) ) ),
    inference(resolution,[status(thm)],[c_2695,c_2632])).

tff(c_2707,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2622,c_2704])).

tff(c_2711,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_2707])).

tff(c_2713,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_2739,plain,(
    ! [B_211,A_212] :
      ( r2_hidden(B_211,A_212)
      | ~ m1_subset_1(B_211,A_212)
      | v1_xboole_0(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2752,plain,(
    ! [B_211] :
      ( ~ m1_subset_1(B_211,'#skF_5')
      | ~ m1_subset_1(B_211,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2739,c_40])).

tff(c_2779,plain,(
    ! [B_218] :
      ( ~ m1_subset_1(B_218,'#skF_5')
      | ~ m1_subset_1(B_218,'#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_2752])).

tff(c_2783,plain,(
    ! [B_19] :
      ( ~ m1_subset_1(B_19,'#skF_6')
      | ~ v1_xboole_0(B_19)
      | ~ v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_2779])).

tff(c_2787,plain,(
    ! [B_219] :
      ( ~ m1_subset_1(B_219,'#skF_6')
      | ~ v1_xboole_0(B_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2713,c_2783])).

tff(c_2792,plain,(
    ! [B_19] :
      ( ~ v1_xboole_0(B_19)
      | ~ v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_36,c_2787])).

tff(c_2793,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2792])).

tff(c_2714,plain,(
    ! [B_205,A_206] :
      ( v1_xboole_0(B_205)
      | ~ m1_subset_1(B_205,A_206)
      | ~ v1_xboole_0(A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2722,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_44,c_2714])).

tff(c_2723,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2722])).

tff(c_3471,plain,(
    ! [B_275,A_276] :
      ( r1_tarski(B_275,A_276)
      | ~ m1_subset_1(B_275,k1_zfmisc_1(A_276))
      | v1_xboole_0(k1_zfmisc_1(A_276)) ) ),
    inference(resolution,[status(thm)],[c_2739,c_20])).

tff(c_3491,plain,
    ( r1_tarski('#skF_6','#skF_5')
    | v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_44,c_3471])).

tff(c_3503,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_2723,c_3491])).

tff(c_2899,plain,(
    ! [C_233,B_234,A_235] :
      ( r2_hidden(C_233,B_234)
      | ~ r2_hidden(C_233,A_235)
      | ~ r1_tarski(A_235,B_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3047,plain,(
    ! [A_246,B_247] :
      ( r2_hidden('#skF_1'(A_246),B_247)
      | ~ r1_tarski(A_246,B_247)
      | v1_xboole_0(A_246) ) ),
    inference(resolution,[status(thm)],[c_4,c_2899])).

tff(c_3071,plain,(
    ! [B_247,A_246] :
      ( ~ v1_xboole_0(B_247)
      | ~ r1_tarski(A_246,B_247)
      | v1_xboole_0(A_246) ) ),
    inference(resolution,[status(thm)],[c_3047,c_2])).

tff(c_3506,plain,
    ( ~ v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_3503,c_3071])).

tff(c_3517,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2713,c_3506])).

tff(c_3519,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2793,c_3517])).

tff(c_3520,plain,(
    ! [B_19] : ~ v1_xboole_0(B_19) ),
    inference(splitRight,[status(thm)],[c_2792])).

tff(c_3521,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_2792])).

tff(c_3527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3520,c_3521])).

tff(c_3528,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_2752])).

tff(c_3547,plain,(
    ! [A_280,B_281] :
      ( r2_hidden('#skF_2'(A_280,B_281),A_280)
      | r1_tarski(A_280,B_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3573,plain,(
    ! [A_283,B_284] :
      ( ~ v1_xboole_0(A_283)
      | r1_tarski(A_283,B_284) ) ),
    inference(resolution,[status(thm)],[c_3547,c_2])).

tff(c_2755,plain,(
    ! [B_215,A_216] :
      ( B_215 = A_216
      | ~ r1_tarski(B_215,A_216)
      | ~ r1_tarski(A_216,B_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2764,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_2755])).

tff(c_3582,plain,(
    ! [A_285] :
      ( k1_xboole_0 = A_285
      | ~ v1_xboole_0(A_285) ) ),
    inference(resolution,[status(thm)],[c_3573,c_2764])).

tff(c_3585,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3528,c_3582])).

tff(c_3592,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_3585])).

tff(c_3594,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2722])).

tff(c_3595,plain,(
    ! [C_286,A_287] :
      ( r2_hidden(C_286,k1_zfmisc_1(A_287))
      | ~ r1_tarski(C_286,A_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3610,plain,(
    ! [A_290,C_291] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_290))
      | ~ r1_tarski(C_291,A_290) ) ),
    inference(resolution,[status(thm)],[c_3595,c_2])).

tff(c_3614,plain,(
    ! [C_292] : ~ r1_tarski(C_292,'#skF_5') ),
    inference(resolution,[status(thm)],[c_3594,c_3610])).

tff(c_3622,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_16,c_3614])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:15:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.53/1.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.53/1.86  
% 4.53/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.53/1.86  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 4.53/1.86  
% 4.53/1.86  %Foreground sorts:
% 4.53/1.86  
% 4.53/1.86  
% 4.53/1.86  %Background operators:
% 4.53/1.86  
% 4.53/1.86  
% 4.53/1.86  %Foreground operators:
% 4.53/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.53/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.53/1.86  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.53/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.53/1.86  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.53/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.53/1.86  tff('#skF_5', type, '#skF_5': $i).
% 4.53/1.86  tff('#skF_6', type, '#skF_6': $i).
% 4.53/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.53/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.53/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.53/1.86  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.53/1.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.53/1.86  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.53/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.53/1.86  
% 4.53/1.88  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.53/1.88  tff(f_79, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_subset_1)).
% 4.53/1.88  tff(f_66, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.53/1.88  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.53/1.88  tff(f_53, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.53/1.88  tff(f_46, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.53/1.88  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.53/1.88  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.53/1.88  tff(c_42, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.53/1.88  tff(c_36, plain, (![B_19, A_18]: (m1_subset_1(B_19, A_18) | ~v1_xboole_0(B_19) | ~v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.53/1.88  tff(c_61, plain, (![B_28, A_29]: (m1_subset_1(B_28, A_29) | ~v1_xboole_0(B_28) | ~v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.53/1.88  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.53/1.88  tff(c_54, plain, (![C_27]: (~r2_hidden(C_27, '#skF_6') | ~m1_subset_1(C_27, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.53/1.88  tff(c_59, plain, (~m1_subset_1('#skF_1'('#skF_6'), '#skF_5') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_4, c_54])).
% 4.53/1.88  tff(c_60, plain, (~m1_subset_1('#skF_1'('#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_59])).
% 4.53/1.88  tff(c_65, plain, (~v1_xboole_0('#skF_1'('#skF_6')) | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_61, c_60])).
% 4.53/1.88  tff(c_66, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_65])).
% 4.53/1.88  tff(c_170, plain, (![B_48, A_49]: (m1_subset_1(B_48, A_49) | ~r2_hidden(B_48, A_49) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.53/1.88  tff(c_197, plain, (![A_53]: (m1_subset_1('#skF_1'(A_53), A_53) | v1_xboole_0(A_53))), inference(resolution, [status(thm)], [c_4, c_170])).
% 4.53/1.88  tff(c_93, plain, (![B_38, A_39]: (r2_hidden(B_38, A_39) | ~m1_subset_1(B_38, A_39) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.53/1.88  tff(c_40, plain, (![C_21]: (~r2_hidden(C_21, '#skF_6') | ~m1_subset_1(C_21, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.53/1.88  tff(c_106, plain, (![B_38]: (~m1_subset_1(B_38, '#skF_5') | ~m1_subset_1(B_38, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_93, c_40])).
% 4.53/1.88  tff(c_108, plain, (![B_38]: (~m1_subset_1(B_38, '#skF_5') | ~m1_subset_1(B_38, '#skF_6'))), inference(splitLeft, [status(thm)], [c_106])).
% 4.53/1.88  tff(c_201, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_197, c_108])).
% 4.53/1.88  tff(c_207, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_66, c_201])).
% 4.53/1.88  tff(c_217, plain, (~v1_xboole_0('#skF_1'('#skF_5')) | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_36, c_207])).
% 4.53/1.88  tff(c_218, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_217])).
% 4.53/1.88  tff(c_186, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_170])).
% 4.53/1.88  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.53/1.88  tff(c_82, plain, (![C_36, A_37]: (r1_tarski(C_36, A_37) | ~r2_hidden(C_36, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.53/1.88  tff(c_247, plain, (![A_62]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_62)), A_62) | v1_xboole_0(k1_zfmisc_1(A_62)))), inference(resolution, [status(thm)], [c_4, c_82])).
% 4.53/1.88  tff(c_18, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.53/1.88  tff(c_115, plain, (![B_41, A_42]: (B_41=A_42 | ~r1_tarski(B_41, A_42) | ~r1_tarski(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.53/1.88  tff(c_124, plain, (![A_12]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_115])).
% 4.53/1.88  tff(c_258, plain, ('#skF_1'(k1_zfmisc_1(k1_xboole_0))=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_247, c_124])).
% 4.53/1.88  tff(c_260, plain, (v1_xboole_0(k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_258])).
% 4.53/1.88  tff(c_67, plain, (![C_30, A_31]: (r2_hidden(C_30, k1_zfmisc_1(A_31)) | ~r1_tarski(C_30, A_31))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.53/1.88  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.53/1.88  tff(c_71, plain, (![A_31, C_30]: (~v1_xboole_0(k1_zfmisc_1(A_31)) | ~r1_tarski(C_30, A_31))), inference(resolution, [status(thm)], [c_67, c_2])).
% 4.53/1.88  tff(c_302, plain, (![C_65]: (~r1_tarski(C_65, k1_xboole_0))), inference(resolution, [status(thm)], [c_260, c_71])).
% 4.53/1.88  tff(c_322, plain, $false, inference(resolution, [status(thm)], [c_16, c_302])).
% 4.53/1.88  tff(c_324, plain, (~v1_xboole_0(k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_258])).
% 4.53/1.88  tff(c_149, plain, (![A_46, B_47]: (r2_hidden('#skF_2'(A_46, B_47), A_46) | r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.53/1.88  tff(c_20, plain, (![C_17, A_13]: (r1_tarski(C_17, A_13) | ~r2_hidden(C_17, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.53/1.88  tff(c_1215, plain, (![A_132, B_133]: (r1_tarski('#skF_2'(k1_zfmisc_1(A_132), B_133), A_132) | r1_tarski(k1_zfmisc_1(A_132), B_133))), inference(resolution, [status(thm)], [c_149, c_20])).
% 4.53/1.88  tff(c_1243, plain, (![B_135]: ('#skF_2'(k1_zfmisc_1(k1_xboole_0), B_135)=k1_xboole_0 | r1_tarski(k1_zfmisc_1(k1_xboole_0), B_135))), inference(resolution, [status(thm)], [c_1215, c_124])).
% 4.53/1.88  tff(c_234, plain, (![C_59, B_60, A_61]: (r2_hidden(C_59, B_60) | ~r2_hidden(C_59, A_61) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.53/1.88  tff(c_407, plain, (![A_69, B_70]: (r2_hidden('#skF_1'(A_69), B_70) | ~r1_tarski(A_69, B_70) | v1_xboole_0(A_69))), inference(resolution, [status(thm)], [c_4, c_234])).
% 4.53/1.88  tff(c_431, plain, (![B_70, A_69]: (~v1_xboole_0(B_70) | ~r1_tarski(A_69, B_70) | v1_xboole_0(A_69))), inference(resolution, [status(thm)], [c_407, c_2])).
% 4.53/1.88  tff(c_1255, plain, (![B_135]: (~v1_xboole_0(B_135) | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) | '#skF_2'(k1_zfmisc_1(k1_xboole_0), B_135)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1243, c_431])).
% 4.53/1.88  tff(c_1347, plain, (![B_138]: (~v1_xboole_0(B_138) | '#skF_2'(k1_zfmisc_1(k1_xboole_0), B_138)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_324, c_1255])).
% 4.53/1.88  tff(c_22, plain, (![C_17, A_13]: (r2_hidden(C_17, k1_zfmisc_1(A_13)) | ~r1_tarski(C_17, A_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.53/1.88  tff(c_138, plain, (![A_44, B_45]: (~r2_hidden('#skF_2'(A_44, B_45), B_45) | r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.53/1.88  tff(c_148, plain, (![A_44, A_13]: (r1_tarski(A_44, k1_zfmisc_1(A_13)) | ~r1_tarski('#skF_2'(A_44, k1_zfmisc_1(A_13)), A_13))), inference(resolution, [status(thm)], [c_22, c_138])).
% 4.53/1.88  tff(c_1370, plain, (![A_13]: (r1_tarski(k1_zfmisc_1(k1_xboole_0), k1_zfmisc_1(A_13)) | ~r1_tarski(k1_xboole_0, A_13) | ~v1_xboole_0(k1_zfmisc_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_1347, c_148])).
% 4.53/1.88  tff(c_1400, plain, (![A_139]: (r1_tarski(k1_zfmisc_1(k1_xboole_0), k1_zfmisc_1(A_139)) | ~v1_xboole_0(k1_zfmisc_1(A_139)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1370])).
% 4.53/1.88  tff(c_1405, plain, (![A_139]: (v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_zfmisc_1(A_139)))), inference(resolution, [status(thm)], [c_1400, c_431])).
% 4.53/1.88  tff(c_1417, plain, (![A_139]: (~v1_xboole_0(k1_zfmisc_1(A_139)))), inference(negUnitSimplification, [status(thm)], [c_324, c_1405])).
% 4.53/1.88  tff(c_105, plain, (![B_38, A_13]: (r1_tarski(B_38, A_13) | ~m1_subset_1(B_38, k1_zfmisc_1(A_13)) | v1_xboole_0(k1_zfmisc_1(A_13)))), inference(resolution, [status(thm)], [c_93, c_20])).
% 4.53/1.88  tff(c_1614, plain, (![B_152, A_153]: (r1_tarski(B_152, A_153) | ~m1_subset_1(B_152, k1_zfmisc_1(A_153)))), inference(negUnitSimplification, [status(thm)], [c_1417, c_105])).
% 4.53/1.88  tff(c_1649, plain, (r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_1614])).
% 4.53/1.88  tff(c_34, plain, (![B_19, A_18]: (r2_hidden(B_19, A_18) | ~m1_subset_1(B_19, A_18) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.53/1.88  tff(c_2472, plain, (![B_187, B_188, A_189]: (r2_hidden(B_187, B_188) | ~r1_tarski(A_189, B_188) | ~m1_subset_1(B_187, A_189) | v1_xboole_0(A_189))), inference(resolution, [status(thm)], [c_34, c_234])).
% 4.53/1.88  tff(c_2478, plain, (![B_187]: (r2_hidden(B_187, '#skF_5') | ~m1_subset_1(B_187, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_1649, c_2472])).
% 4.53/1.88  tff(c_2517, plain, (![B_190]: (r2_hidden(B_190, '#skF_5') | ~m1_subset_1(B_190, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_218, c_2478])).
% 4.53/1.88  tff(c_32, plain, (![B_19, A_18]: (m1_subset_1(B_19, A_18) | ~r2_hidden(B_19, A_18) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.53/1.88  tff(c_2529, plain, (![B_190]: (m1_subset_1(B_190, '#skF_5') | v1_xboole_0('#skF_5') | ~m1_subset_1(B_190, '#skF_6'))), inference(resolution, [status(thm)], [c_2517, c_32])).
% 4.53/1.88  tff(c_2545, plain, (![B_191]: (m1_subset_1(B_191, '#skF_5') | ~m1_subset_1(B_191, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_66, c_2529])).
% 4.53/1.88  tff(c_2593, plain, (![B_192]: (~m1_subset_1(B_192, '#skF_6'))), inference(resolution, [status(thm)], [c_2545, c_108])).
% 4.53/1.88  tff(c_2601, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_186, c_2593])).
% 4.53/1.88  tff(c_2612, plain, $false, inference(negUnitSimplification, [status(thm)], [c_218, c_2601])).
% 4.53/1.88  tff(c_2614, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_217])).
% 4.53/1.88  tff(c_187, plain, (![A_50, B_51]: (~v1_xboole_0(A_50) | r1_tarski(A_50, B_51))), inference(resolution, [status(thm)], [c_149, c_2])).
% 4.53/1.88  tff(c_194, plain, (![A_50]: (k1_xboole_0=A_50 | ~v1_xboole_0(A_50))), inference(resolution, [status(thm)], [c_187, c_124])).
% 4.53/1.88  tff(c_2617, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_2614, c_194])).
% 4.53/1.88  tff(c_2621, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_2617])).
% 4.53/1.88  tff(c_2622, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_106])).
% 4.53/1.88  tff(c_2657, plain, (![A_198, B_199]: (r2_hidden('#skF_2'(A_198, B_199), A_198) | r1_tarski(A_198, B_199))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.53/1.88  tff(c_2695, plain, (![A_202, B_203]: (~v1_xboole_0(A_202) | r1_tarski(A_202, B_203))), inference(resolution, [status(thm)], [c_2657, c_2])).
% 4.53/1.88  tff(c_2623, plain, (![B_193, A_194]: (B_193=A_194 | ~r1_tarski(B_193, A_194) | ~r1_tarski(A_194, B_193))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.53/1.88  tff(c_2632, plain, (![A_12]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_2623])).
% 4.53/1.88  tff(c_2704, plain, (![A_204]: (k1_xboole_0=A_204 | ~v1_xboole_0(A_204))), inference(resolution, [status(thm)], [c_2695, c_2632])).
% 4.53/1.88  tff(c_2707, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_2622, c_2704])).
% 4.53/1.88  tff(c_2711, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_2707])).
% 4.53/1.88  tff(c_2713, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_65])).
% 4.53/1.88  tff(c_2739, plain, (![B_211, A_212]: (r2_hidden(B_211, A_212) | ~m1_subset_1(B_211, A_212) | v1_xboole_0(A_212))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.53/1.88  tff(c_2752, plain, (![B_211]: (~m1_subset_1(B_211, '#skF_5') | ~m1_subset_1(B_211, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_2739, c_40])).
% 4.53/1.88  tff(c_2779, plain, (![B_218]: (~m1_subset_1(B_218, '#skF_5') | ~m1_subset_1(B_218, '#skF_6'))), inference(splitLeft, [status(thm)], [c_2752])).
% 4.53/1.88  tff(c_2783, plain, (![B_19]: (~m1_subset_1(B_19, '#skF_6') | ~v1_xboole_0(B_19) | ~v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_2779])).
% 4.53/1.88  tff(c_2787, plain, (![B_219]: (~m1_subset_1(B_219, '#skF_6') | ~v1_xboole_0(B_219))), inference(demodulation, [status(thm), theory('equality')], [c_2713, c_2783])).
% 4.53/1.88  tff(c_2792, plain, (![B_19]: (~v1_xboole_0(B_19) | ~v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_36, c_2787])).
% 4.53/1.88  tff(c_2793, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_2792])).
% 4.53/1.88  tff(c_2714, plain, (![B_205, A_206]: (v1_xboole_0(B_205) | ~m1_subset_1(B_205, A_206) | ~v1_xboole_0(A_206))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.53/1.88  tff(c_2722, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_44, c_2714])).
% 4.53/1.88  tff(c_2723, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_2722])).
% 4.53/1.88  tff(c_3471, plain, (![B_275, A_276]: (r1_tarski(B_275, A_276) | ~m1_subset_1(B_275, k1_zfmisc_1(A_276)) | v1_xboole_0(k1_zfmisc_1(A_276)))), inference(resolution, [status(thm)], [c_2739, c_20])).
% 4.53/1.88  tff(c_3491, plain, (r1_tarski('#skF_6', '#skF_5') | v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_44, c_3471])).
% 4.53/1.88  tff(c_3503, plain, (r1_tarski('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_2723, c_3491])).
% 4.53/1.88  tff(c_2899, plain, (![C_233, B_234, A_235]: (r2_hidden(C_233, B_234) | ~r2_hidden(C_233, A_235) | ~r1_tarski(A_235, B_234))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.53/1.89  tff(c_3047, plain, (![A_246, B_247]: (r2_hidden('#skF_1'(A_246), B_247) | ~r1_tarski(A_246, B_247) | v1_xboole_0(A_246))), inference(resolution, [status(thm)], [c_4, c_2899])).
% 4.53/1.89  tff(c_3071, plain, (![B_247, A_246]: (~v1_xboole_0(B_247) | ~r1_tarski(A_246, B_247) | v1_xboole_0(A_246))), inference(resolution, [status(thm)], [c_3047, c_2])).
% 4.53/1.89  tff(c_3506, plain, (~v1_xboole_0('#skF_5') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_3503, c_3071])).
% 4.53/1.89  tff(c_3517, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2713, c_3506])).
% 4.53/1.89  tff(c_3519, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2793, c_3517])).
% 4.53/1.89  tff(c_3520, plain, (![B_19]: (~v1_xboole_0(B_19))), inference(splitRight, [status(thm)], [c_2792])).
% 4.53/1.89  tff(c_3521, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_2792])).
% 4.53/1.89  tff(c_3527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3520, c_3521])).
% 4.53/1.89  tff(c_3528, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_2752])).
% 4.53/1.89  tff(c_3547, plain, (![A_280, B_281]: (r2_hidden('#skF_2'(A_280, B_281), A_280) | r1_tarski(A_280, B_281))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.53/1.89  tff(c_3573, plain, (![A_283, B_284]: (~v1_xboole_0(A_283) | r1_tarski(A_283, B_284))), inference(resolution, [status(thm)], [c_3547, c_2])).
% 4.53/1.89  tff(c_2755, plain, (![B_215, A_216]: (B_215=A_216 | ~r1_tarski(B_215, A_216) | ~r1_tarski(A_216, B_215))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.53/1.89  tff(c_2764, plain, (![A_12]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_2755])).
% 4.53/1.89  tff(c_3582, plain, (![A_285]: (k1_xboole_0=A_285 | ~v1_xboole_0(A_285))), inference(resolution, [status(thm)], [c_3573, c_2764])).
% 4.53/1.89  tff(c_3585, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_3528, c_3582])).
% 4.53/1.89  tff(c_3592, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_3585])).
% 4.53/1.89  tff(c_3594, plain, (v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(splitRight, [status(thm)], [c_2722])).
% 4.53/1.89  tff(c_3595, plain, (![C_286, A_287]: (r2_hidden(C_286, k1_zfmisc_1(A_287)) | ~r1_tarski(C_286, A_287))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.53/1.89  tff(c_3610, plain, (![A_290, C_291]: (~v1_xboole_0(k1_zfmisc_1(A_290)) | ~r1_tarski(C_291, A_290))), inference(resolution, [status(thm)], [c_3595, c_2])).
% 4.53/1.89  tff(c_3614, plain, (![C_292]: (~r1_tarski(C_292, '#skF_5'))), inference(resolution, [status(thm)], [c_3594, c_3610])).
% 4.53/1.89  tff(c_3622, plain, $false, inference(resolution, [status(thm)], [c_16, c_3614])).
% 4.53/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.53/1.89  
% 4.53/1.89  Inference rules
% 4.53/1.89  ----------------------
% 4.53/1.89  #Ref     : 0
% 4.53/1.89  #Sup     : 800
% 4.53/1.89  #Fact    : 0
% 4.53/1.89  #Define  : 0
% 4.53/1.89  #Split   : 18
% 4.53/1.89  #Chain   : 0
% 4.53/1.89  #Close   : 0
% 4.53/1.89  
% 4.53/1.89  Ordering : KBO
% 4.53/1.89  
% 4.53/1.89  Simplification rules
% 4.53/1.89  ----------------------
% 4.53/1.89  #Subsume      : 259
% 4.53/1.89  #Demod        : 201
% 4.53/1.89  #Tautology    : 217
% 4.53/1.89  #SimpNegUnit  : 115
% 4.53/1.89  #BackRed      : 30
% 4.53/1.89  
% 4.53/1.89  #Partial instantiations: 0
% 4.53/1.89  #Strategies tried      : 1
% 4.53/1.89  
% 4.53/1.89  Timing (in seconds)
% 4.53/1.89  ----------------------
% 4.53/1.89  Preprocessing        : 0.29
% 4.53/1.89  Parsing              : 0.15
% 4.53/1.89  CNF conversion       : 0.02
% 4.53/1.89  Main loop            : 0.81
% 4.53/1.89  Inferencing          : 0.30
% 4.53/1.89  Reduction            : 0.22
% 4.53/1.89  Demodulation         : 0.14
% 4.53/1.89  BG Simplification    : 0.03
% 4.53/1.89  Subsumption          : 0.19
% 4.53/1.89  Abstraction          : 0.04
% 4.53/1.89  MUC search           : 0.00
% 4.53/1.89  Cooper               : 0.00
% 4.53/1.89  Total                : 1.14
% 4.53/1.89  Index Insertion      : 0.00
% 4.53/1.89  Index Deletion       : 0.00
% 4.53/1.89  Index Matching       : 0.00
% 4.53/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
