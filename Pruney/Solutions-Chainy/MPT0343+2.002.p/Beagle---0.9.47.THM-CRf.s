%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:17 EST 2020

% Result     : Theorem 7.50s
% Output     : CNFRefutation 7.75s
% Verified   : 
% Statistics : Number of formulae       :  234 (1274 expanded)
%              Number of leaves         :   21 ( 398 expanded)
%              Depth                    :   19
%              Number of atoms          :  444 (3456 expanded)
%              Number of equality atoms :   23 ( 199 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ! [D] :
                  ( m1_subset_1(D,A)
                 => ( r2_hidden(D,B)
                  <=> r2_hidden(D,C) ) )
             => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_38,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_34,plain,(
    ! [B_18,A_17] :
      ( m1_subset_1(B_18,A_17)
      | ~ v1_xboole_0(B_18)
      | ~ v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_71,plain,(
    ! [D_32] :
      ( r2_hidden(D_32,'#skF_7')
      | ~ r2_hidden(D_32,'#skF_6')
      | ~ m1_subset_1(D_32,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [D_32] :
      ( ~ v1_xboole_0('#skF_7')
      | ~ r2_hidden(D_32,'#skF_6')
      | ~ m1_subset_1(D_32,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_71,c_2])).

tff(c_217,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_130,plain,(
    ! [D_46] :
      ( r2_hidden(D_46,'#skF_6')
      | ~ r2_hidden(D_46,'#skF_7')
      | ~ m1_subset_1(D_46,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_144,plain,
    ( r2_hidden('#skF_1'('#skF_7'),'#skF_6')
    | ~ m1_subset_1('#skF_1'('#skF_7'),'#skF_5')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_4,c_130])).

tff(c_226,plain,
    ( r2_hidden('#skF_1'('#skF_7'),'#skF_6')
    | ~ m1_subset_1('#skF_1'('#skF_7'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_144])).

tff(c_227,plain,(
    ~ m1_subset_1('#skF_1'('#skF_7'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_226])).

tff(c_98,plain,(
    ! [B_41,A_42] :
      ( m1_subset_1(B_41,A_42)
      | ~ r2_hidden(B_41,A_42)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_110,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_98])).

tff(c_231,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_7'))
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_227])).

tff(c_232,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_231])).

tff(c_40,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_61,plain,(
    ! [B_30,A_31] :
      ( v1_xboole_0(B_30)
      | ~ m1_subset_1(B_30,A_31)
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_68,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_40,c_61])).

tff(c_70,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_116,plain,(
    ! [B_44,A_45] :
      ( r2_hidden(B_44,A_45)
      | ~ m1_subset_1(B_44,A_45)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18,plain,(
    ! [C_16,A_12] :
      ( r1_tarski(C_16,A_12)
      | ~ r2_hidden(C_16,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_403,plain,(
    ! [B_82,A_83] :
      ( r1_tarski(B_82,A_83)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_83))
      | v1_xboole_0(k1_zfmisc_1(A_83)) ) ),
    inference(resolution,[status(thm)],[c_116,c_18])).

tff(c_421,plain,
    ( r1_tarski('#skF_7','#skF_5')
    | v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_40,c_403])).

tff(c_432,plain,(
    r1_tarski('#skF_7','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_421])).

tff(c_32,plain,(
    ! [B_18,A_17] :
      ( r2_hidden(B_18,A_17)
      | ~ m1_subset_1(B_18,A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_201,plain,(
    ! [C_57,B_58,A_59] :
      ( r2_hidden(C_57,B_58)
      | ~ r2_hidden(C_57,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_984,plain,(
    ! [B_124,B_125,A_126] :
      ( r2_hidden(B_124,B_125)
      | ~ r1_tarski(A_126,B_125)
      | ~ m1_subset_1(B_124,A_126)
      | v1_xboole_0(A_126) ) ),
    inference(resolution,[status(thm)],[c_32,c_201])).

tff(c_998,plain,(
    ! [B_124] :
      ( r2_hidden(B_124,'#skF_5')
      | ~ m1_subset_1(B_124,'#skF_7')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_432,c_984])).

tff(c_1047,plain,(
    ! [B_128] :
      ( r2_hidden(B_128,'#skF_5')
      | ~ m1_subset_1(B_128,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_998])).

tff(c_30,plain,(
    ! [B_18,A_17] :
      ( m1_subset_1(B_18,A_17)
      | ~ r2_hidden(B_18,A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1063,plain,(
    ! [B_128] :
      ( m1_subset_1(B_128,'#skF_5')
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(B_128,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1047,c_30])).

tff(c_1121,plain,(
    ! [B_131] :
      ( m1_subset_1(B_131,'#skF_5')
      | ~ m1_subset_1(B_131,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_232,c_1063])).

tff(c_1132,plain,
    ( m1_subset_1('#skF_1'('#skF_7'),'#skF_5')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_110,c_1121])).

tff(c_1145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_227,c_1132])).

tff(c_1147,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_231])).

tff(c_1717,plain,(
    ! [B_176,A_177] :
      ( r1_tarski(B_176,A_177)
      | ~ m1_subset_1(B_176,k1_zfmisc_1(A_177))
      | v1_xboole_0(k1_zfmisc_1(A_177)) ) ),
    inference(resolution,[status(thm)],[c_116,c_18])).

tff(c_1737,plain,
    ( r1_tarski('#skF_7','#skF_5')
    | v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_40,c_1717])).

tff(c_1751,plain,(
    r1_tarski('#skF_7','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1737])).

tff(c_1173,plain,(
    ! [A_135,B_136] :
      ( r2_hidden('#skF_1'(A_135),B_136)
      | ~ r1_tarski(A_135,B_136)
      | v1_xboole_0(A_135) ) ),
    inference(resolution,[status(thm)],[c_4,c_201])).

tff(c_1194,plain,(
    ! [B_136,A_135] :
      ( ~ v1_xboole_0(B_136)
      | ~ r1_tarski(A_135,B_136)
      | v1_xboole_0(A_135) ) ),
    inference(resolution,[status(thm)],[c_1173,c_2])).

tff(c_1789,plain,
    ( ~ v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_1751,c_1194])).

tff(c_1797,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1147,c_1789])).

tff(c_1799,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_1797])).

tff(c_1800,plain,(
    r2_hidden('#skF_1'('#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_226])).

tff(c_1812,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1800,c_2])).

tff(c_161,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_2'(A_49,B_50),A_49)
      | r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_183,plain,(
    ! [A_49,B_50] :
      ( m1_subset_1('#skF_2'(A_49,B_50),A_49)
      | v1_xboole_0(A_49)
      | r1_tarski(A_49,B_50) ) ),
    inference(resolution,[status(thm)],[c_161,c_30])).

tff(c_1801,plain,(
    m1_subset_1('#skF_1'('#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_226])).

tff(c_36,plain,(
    ! [B_18,A_17] :
      ( v1_xboole_0(B_18)
      | ~ m1_subset_1(B_18,A_17)
      | ~ v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1816,plain,
    ( v1_xboole_0('#skF_1'('#skF_7'))
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1801,c_36])).

tff(c_1817,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1816])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3587,plain,(
    ! [B_301,A_302] :
      ( r1_tarski(B_301,A_302)
      | ~ m1_subset_1(B_301,k1_zfmisc_1(A_302))
      | v1_xboole_0(k1_zfmisc_1(A_302)) ) ),
    inference(resolution,[status(thm)],[c_116,c_18])).

tff(c_3627,plain,
    ( r1_tarski('#skF_6','#skF_5')
    | v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_42,c_3587])).

tff(c_3643,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_3627])).

tff(c_4205,plain,(
    ! [B_337,B_338,A_339] :
      ( r2_hidden(B_337,B_338)
      | ~ r1_tarski(A_339,B_338)
      | ~ m1_subset_1(B_337,A_339)
      | v1_xboole_0(A_339) ) ),
    inference(resolution,[status(thm)],[c_32,c_201])).

tff(c_4215,plain,(
    ! [B_337] :
      ( r2_hidden(B_337,'#skF_5')
      | ~ m1_subset_1(B_337,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_3643,c_4205])).

tff(c_4261,plain,(
    ! [B_340] :
      ( r2_hidden(B_340,'#skF_5')
      | ~ m1_subset_1(B_340,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1812,c_4215])).

tff(c_4277,plain,(
    ! [B_340] :
      ( m1_subset_1(B_340,'#skF_5')
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(B_340,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_4261,c_30])).

tff(c_4317,plain,(
    ! [B_342] :
      ( m1_subset_1(B_342,'#skF_5')
      | ~ m1_subset_1(B_342,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1817,c_4277])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_46,plain,(
    ! [D_23] :
      ( r2_hidden(D_23,'#skF_7')
      | ~ r2_hidden(D_23,'#skF_6')
      | ~ m1_subset_1(D_23,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_145,plain,(
    ! [A_47,B_48] :
      ( ~ r2_hidden('#skF_2'(A_47,B_48),B_48)
      | r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3376,plain,(
    ! [A_281] :
      ( r1_tarski(A_281,'#skF_7')
      | ~ r2_hidden('#skF_2'(A_281,'#skF_7'),'#skF_6')
      | ~ m1_subset_1('#skF_2'(A_281,'#skF_7'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_145])).

tff(c_3388,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_6','#skF_7'),'#skF_5')
    | r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_10,c_3376])).

tff(c_3392,plain,(
    ~ m1_subset_1('#skF_2'('#skF_6','#skF_7'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3388])).

tff(c_4335,plain,(
    ~ m1_subset_1('#skF_2'('#skF_6','#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_4317,c_3392])).

tff(c_4354,plain,
    ( v1_xboole_0('#skF_6')
    | r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_183,c_4335])).

tff(c_4360,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_1812,c_4354])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4382,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_4360,c_12])).

tff(c_4399,plain,(
    ~ r1_tarski('#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_4382])).

tff(c_3624,plain,
    ( r1_tarski('#skF_7','#skF_5')
    | v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_40,c_3587])).

tff(c_3640,plain,(
    r1_tarski('#skF_7','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_3624])).

tff(c_4217,plain,(
    ! [B_337] :
      ( r2_hidden(B_337,'#skF_5')
      | ~ m1_subset_1(B_337,'#skF_7')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_3640,c_4205])).

tff(c_4289,plain,(
    ! [B_341] :
      ( r2_hidden(B_341,'#skF_5')
      | ~ m1_subset_1(B_341,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_4217])).

tff(c_4305,plain,(
    ! [B_341] :
      ( m1_subset_1(B_341,'#skF_5')
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(B_341,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4289,c_30])).

tff(c_4428,plain,(
    ! [B_346] :
      ( m1_subset_1(B_346,'#skF_5')
      | ~ m1_subset_1(B_346,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1817,c_4305])).

tff(c_4440,plain,(
    ! [B_50] :
      ( m1_subset_1('#skF_2'('#skF_7',B_50),'#skF_5')
      | v1_xboole_0('#skF_7')
      | r1_tarski('#skF_7',B_50) ) ),
    inference(resolution,[status(thm)],[c_183,c_4428])).

tff(c_4700,plain,(
    ! [B_355] :
      ( m1_subset_1('#skF_2'('#skF_7',B_355),'#skF_5')
      | r1_tarski('#skF_7',B_355) ) ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_4440])).

tff(c_44,plain,(
    ! [D_23] :
      ( r2_hidden(D_23,'#skF_6')
      | ~ r2_hidden(D_23,'#skF_7')
      | ~ m1_subset_1(D_23,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3458,plain,(
    ! [B_289] :
      ( r2_hidden('#skF_2'('#skF_7',B_289),'#skF_6')
      | ~ m1_subset_1('#skF_2'('#skF_7',B_289),'#skF_5')
      | r1_tarski('#skF_7',B_289) ) ),
    inference(resolution,[status(thm)],[c_161,c_44])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3485,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_7','#skF_6'),'#skF_5')
    | r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_3458,c_8])).

tff(c_3490,plain,(
    ~ m1_subset_1('#skF_2'('#skF_7','#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3485])).

tff(c_4707,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_4700,c_3490])).

tff(c_4717,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4399,c_4707])).

tff(c_4718,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_3485])).

tff(c_4730,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_4718,c_12])).

tff(c_4738,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_4730])).

tff(c_4747,plain,(
    ! [B_356,A_357] :
      ( r1_tarski(B_356,A_357)
      | ~ m1_subset_1(B_356,k1_zfmisc_1(A_357))
      | v1_xboole_0(k1_zfmisc_1(A_357)) ) ),
    inference(resolution,[status(thm)],[c_116,c_18])).

tff(c_4776,plain,
    ( r1_tarski('#skF_6','#skF_5')
    | v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_42,c_4747])).

tff(c_4788,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_4776])).

tff(c_4992,plain,(
    ! [B_378,B_379,A_380] :
      ( r2_hidden(B_378,B_379)
      | ~ r1_tarski(A_380,B_379)
      | ~ m1_subset_1(B_378,A_380)
      | v1_xboole_0(A_380) ) ),
    inference(resolution,[status(thm)],[c_32,c_201])).

tff(c_4998,plain,(
    ! [B_378] :
      ( r2_hidden(B_378,'#skF_5')
      | ~ m1_subset_1(B_378,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_4788,c_4992])).

tff(c_5041,plain,(
    ! [B_381] :
      ( r2_hidden(B_381,'#skF_5')
      | ~ m1_subset_1(B_381,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1812,c_4998])).

tff(c_5057,plain,(
    ! [B_381] :
      ( m1_subset_1(B_381,'#skF_5')
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(B_381,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_5041,c_30])).

tff(c_5211,plain,(
    ! [B_386] :
      ( m1_subset_1(B_386,'#skF_5')
      | ~ m1_subset_1(B_386,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1817,c_5057])).

tff(c_5225,plain,(
    ~ m1_subset_1('#skF_2'('#skF_6','#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_5211,c_3392])).

tff(c_5229,plain,
    ( v1_xboole_0('#skF_6')
    | r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_183,c_5225])).

tff(c_5236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4738,c_1812,c_5229])).

tff(c_5237,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_3388])).

tff(c_5249,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_5237,c_12])).

tff(c_5257,plain,(
    ~ r1_tarski('#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_5249])).

tff(c_5436,plain,(
    ! [B_401,A_402] :
      ( r1_tarski(B_401,A_402)
      | ~ m1_subset_1(B_401,k1_zfmisc_1(A_402))
      | v1_xboole_0(k1_zfmisc_1(A_402)) ) ),
    inference(resolution,[status(thm)],[c_116,c_18])).

tff(c_5473,plain,
    ( r1_tarski('#skF_7','#skF_5')
    | v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_40,c_5436])).

tff(c_5489,plain,(
    r1_tarski('#skF_7','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_5473])).

tff(c_5775,plain,(
    ! [B_424,B_425,A_426] :
      ( r2_hidden(B_424,B_425)
      | ~ r1_tarski(A_426,B_425)
      | ~ m1_subset_1(B_424,A_426)
      | v1_xboole_0(A_426) ) ),
    inference(resolution,[status(thm)],[c_32,c_201])).

tff(c_5787,plain,(
    ! [B_424] :
      ( r2_hidden(B_424,'#skF_5')
      | ~ m1_subset_1(B_424,'#skF_7')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_5489,c_5775])).

tff(c_5858,plain,(
    ! [B_428] :
      ( r2_hidden(B_428,'#skF_5')
      | ~ m1_subset_1(B_428,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_5787])).

tff(c_5874,plain,(
    ! [B_428] :
      ( m1_subset_1(B_428,'#skF_5')
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(B_428,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_5858,c_30])).

tff(c_5977,plain,(
    ! [B_432] :
      ( m1_subset_1(B_432,'#skF_5')
      | ~ m1_subset_1(B_432,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1817,c_5874])).

tff(c_5988,plain,(
    ! [B_50] :
      ( m1_subset_1('#skF_2'('#skF_7',B_50),'#skF_5')
      | v1_xboole_0('#skF_7')
      | r1_tarski('#skF_7',B_50) ) ),
    inference(resolution,[status(thm)],[c_183,c_5977])).

tff(c_6224,plain,(
    ! [B_445] :
      ( m1_subset_1('#skF_2'('#skF_7',B_445),'#skF_5')
      | r1_tarski('#skF_7',B_445) ) ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_5988])).

tff(c_5295,plain,(
    ! [B_391] :
      ( r2_hidden('#skF_2'('#skF_7',B_391),'#skF_6')
      | ~ m1_subset_1('#skF_2'('#skF_7',B_391),'#skF_5')
      | r1_tarski('#skF_7',B_391) ) ),
    inference(resolution,[status(thm)],[c_161,c_44])).

tff(c_5310,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_7','#skF_6'),'#skF_5')
    | r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_5295,c_8])).

tff(c_5324,plain,(
    ~ m1_subset_1('#skF_2'('#skF_7','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_5257,c_5257,c_5310])).

tff(c_6231,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_6224,c_5324])).

tff(c_6241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5257,c_6231])).

tff(c_6243,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1816])).

tff(c_55,plain,(
    ! [C_28,A_29] :
      ( r1_tarski(C_28,A_29)
      | ~ r2_hidden(C_28,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_60,plain,(
    ! [A_29] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_29)),A_29)
      | v1_xboole_0(k1_zfmisc_1(A_29)) ) ),
    inference(resolution,[status(thm)],[c_4,c_55])).

tff(c_6619,plain,(
    ! [A_465,B_466] :
      ( r2_hidden('#skF_1'(A_465),B_466)
      | ~ r1_tarski(A_465,B_466)
      | v1_xboole_0(A_465) ) ),
    inference(resolution,[status(thm)],[c_4,c_201])).

tff(c_6654,plain,(
    ! [B_467,A_468] :
      ( ~ v1_xboole_0(B_467)
      | ~ r1_tarski(A_468,B_467)
      | v1_xboole_0(A_468) ) ),
    inference(resolution,[status(thm)],[c_6619,c_2])).

tff(c_6712,plain,(
    ! [A_473] :
      ( ~ v1_xboole_0(A_473)
      | v1_xboole_0('#skF_1'(k1_zfmisc_1(A_473)))
      | v1_xboole_0(k1_zfmisc_1(A_473)) ) ),
    inference(resolution,[status(thm)],[c_60,c_6654])).

tff(c_185,plain,(
    ! [A_49,B_50] :
      ( ~ v1_xboole_0(A_49)
      | r1_tarski(A_49,B_50) ) ),
    inference(resolution,[status(thm)],[c_161,c_2])).

tff(c_186,plain,(
    ! [A_51,B_52] :
      ( ~ v1_xboole_0(A_51)
      | r1_tarski(A_51,B_52) ) ),
    inference(resolution,[status(thm)],[c_161,c_2])).

tff(c_190,plain,(
    ! [B_53,A_54] :
      ( B_53 = A_54
      | ~ r1_tarski(B_53,A_54)
      | ~ v1_xboole_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_186,c_12])).

tff(c_197,plain,(
    ! [B_50,A_49] :
      ( B_50 = A_49
      | ~ v1_xboole_0(B_50)
      | ~ v1_xboole_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_185,c_190])).

tff(c_6246,plain,(
    ! [A_49] :
      ( A_49 = '#skF_5'
      | ~ v1_xboole_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_6243,c_197])).

tff(c_6939,plain,(
    ! [A_485] :
      ( '#skF_1'(k1_zfmisc_1(A_485)) = '#skF_5'
      | ~ v1_xboole_0(A_485)
      | v1_xboole_0(k1_zfmisc_1(A_485)) ) ),
    inference(resolution,[status(thm)],[c_6712,c_6246])).

tff(c_81,plain,(
    ! [C_35,A_36] :
      ( r2_hidden(C_35,k1_zfmisc_1(A_36))
      | ~ r1_tarski(C_35,A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_89,plain,(
    ! [A_36,C_35] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_36))
      | ~ r1_tarski(C_35,A_36) ) ),
    inference(resolution,[status(thm)],[c_81,c_2])).

tff(c_7061,plain,(
    ! [C_490,A_491] :
      ( ~ r1_tarski(C_490,A_491)
      | '#skF_1'(k1_zfmisc_1(A_491)) = '#skF_5'
      | ~ v1_xboole_0(A_491) ) ),
    inference(resolution,[status(thm)],[c_6939,c_89])).

tff(c_7083,plain,(
    ! [B_492] :
      ( '#skF_1'(k1_zfmisc_1(B_492)) = '#skF_5'
      | ~ v1_xboole_0(B_492) ) ),
    inference(resolution,[status(thm)],[c_16,c_7061])).

tff(c_7142,plain,(
    ! [B_495] :
      ( r1_tarski('#skF_5',B_495)
      | v1_xboole_0(k1_zfmisc_1(B_495))
      | ~ v1_xboole_0(B_495) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7083,c_60])).

tff(c_7204,plain,(
    ! [C_498,B_499] :
      ( ~ r1_tarski(C_498,B_499)
      | r1_tarski('#skF_5',B_499)
      | ~ v1_xboole_0(B_499) ) ),
    inference(resolution,[status(thm)],[c_7142,c_89])).

tff(c_7231,plain,(
    ! [B_11] :
      ( r1_tarski('#skF_5',B_11)
      | ~ v1_xboole_0(B_11) ) ),
    inference(resolution,[status(thm)],[c_16,c_7204])).

tff(c_6242,plain,(
    v1_xboole_0('#skF_1'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1816])).

tff(c_6250,plain,(
    ! [A_446] :
      ( A_446 = '#skF_5'
      | ~ v1_xboole_0(A_446) ) ),
    inference(resolution,[status(thm)],[c_6243,c_197])).

tff(c_6257,plain,(
    '#skF_1'('#skF_7') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_6242,c_6250])).

tff(c_6286,plain,
    ( v1_xboole_0('#skF_7')
    | r2_hidden('#skF_5','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_6257,c_4])).

tff(c_6290,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_6286])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6476,plain,(
    ! [B_455] :
      ( r2_hidden('#skF_5',B_455)
      | ~ r1_tarski('#skF_7',B_455) ) ),
    inference(resolution,[status(thm)],[c_6290,c_6])).

tff(c_7293,plain,(
    ! [B_509,B_510] :
      ( r2_hidden('#skF_5',B_509)
      | ~ r1_tarski(B_510,B_509)
      | ~ r1_tarski('#skF_7',B_510) ) ),
    inference(resolution,[status(thm)],[c_6476,c_6])).

tff(c_7312,plain,(
    ! [B_11] :
      ( r2_hidden('#skF_5',B_11)
      | ~ r1_tarski('#skF_7','#skF_5')
      | ~ v1_xboole_0(B_11) ) ),
    inference(resolution,[status(thm)],[c_7231,c_7293])).

tff(c_7321,plain,(
    ~ r1_tarski('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_7312])).

tff(c_7390,plain,(
    ! [B_518,A_519] :
      ( r1_tarski(B_518,A_519)
      | ~ m1_subset_1(B_518,k1_zfmisc_1(A_519))
      | v1_xboole_0(k1_zfmisc_1(A_519)) ) ),
    inference(resolution,[status(thm)],[c_116,c_18])).

tff(c_7414,plain,
    ( r1_tarski('#skF_7','#skF_5')
    | v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_40,c_7390])).

tff(c_7430,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_7321,c_7414])).

tff(c_7432,plain,(
    r1_tarski('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_7312])).

tff(c_6652,plain,(
    ! [B_466,A_465] :
      ( ~ v1_xboole_0(B_466)
      | ~ r1_tarski(A_465,B_466)
      | v1_xboole_0(A_465) ) ),
    inference(resolution,[status(thm)],[c_6619,c_2])).

tff(c_7439,plain,
    ( ~ v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_7432,c_6652])).

tff(c_7457,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6243,c_7439])).

tff(c_7459,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_7457])).

tff(c_7471,plain,(
    ! [D_521] :
      ( ~ r2_hidden(D_521,'#skF_6')
      | ~ m1_subset_1(D_521,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_7486,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6'),'#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_7471])).

tff(c_7521,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_7486])).

tff(c_7525,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_6'))
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_7521])).

tff(c_7526,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_7525])).

tff(c_7485,plain,(
    ! [B_18] :
      ( ~ m1_subset_1(B_18,'#skF_5')
      | ~ m1_subset_1(B_18,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_32,c_7471])).

tff(c_7537,plain,(
    ! [B_525] :
      ( ~ m1_subset_1(B_525,'#skF_5')
      | ~ m1_subset_1(B_525,'#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_7485])).

tff(c_7541,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_110,c_7537])).

tff(c_7548,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_7526,c_7541])).

tff(c_7553,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_5'))
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_7548])).

tff(c_7565,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_7553])).

tff(c_8014,plain,(
    ! [B_574,A_575] :
      ( r1_tarski(B_574,A_575)
      | ~ m1_subset_1(B_574,k1_zfmisc_1(A_575))
      | v1_xboole_0(k1_zfmisc_1(A_575)) ) ),
    inference(resolution,[status(thm)],[c_116,c_18])).

tff(c_8037,plain,
    ( r1_tarski('#skF_6','#skF_5')
    | v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_42,c_8014])).

tff(c_8049,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_8037])).

tff(c_8166,plain,(
    ! [B_583,B_584,A_585] :
      ( r2_hidden(B_583,B_584)
      | ~ r1_tarski(A_585,B_584)
      | ~ m1_subset_1(B_583,A_585)
      | v1_xboole_0(A_585) ) ),
    inference(resolution,[status(thm)],[c_32,c_201])).

tff(c_8170,plain,(
    ! [B_583] :
      ( r2_hidden(B_583,'#skF_5')
      | ~ m1_subset_1(B_583,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_8049,c_8166])).

tff(c_8204,plain,(
    ! [B_586] :
      ( r2_hidden(B_586,'#skF_5')
      | ~ m1_subset_1(B_586,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_7565,c_8170])).

tff(c_8220,plain,(
    ! [B_586] :
      ( m1_subset_1(B_586,'#skF_5')
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(B_586,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_8204,c_30])).

tff(c_8232,plain,(
    ! [B_587] :
      ( m1_subset_1(B_587,'#skF_5')
      | ~ m1_subset_1(B_587,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_7526,c_8220])).

tff(c_7536,plain,(
    ! [B_18] :
      ( ~ m1_subset_1(B_18,'#skF_5')
      | ~ m1_subset_1(B_18,'#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_7485])).

tff(c_8304,plain,(
    ! [B_591] : ~ m1_subset_1(B_591,'#skF_6') ),
    inference(resolution,[status(thm)],[c_8232,c_7536])).

tff(c_8312,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_110,c_8304])).

tff(c_8323,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7565,c_8312])).

tff(c_8325,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_7553])).

tff(c_7461,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_7464,plain,(
    ! [A_49] :
      ( A_49 = '#skF_7'
      | ~ v1_xboole_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_7461,c_197])).

tff(c_8328,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_8325,c_7464])).

tff(c_8334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_8328])).

tff(c_8335,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_7485])).

tff(c_8338,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_8335,c_7464])).

tff(c_8344,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_8338])).

tff(c_8346,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_7525])).

tff(c_8353,plain,(
    '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_8346,c_7464])).

tff(c_8359,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8353,c_38])).

tff(c_8419,plain,(
    ! [B_597] :
      ( ~ m1_subset_1(B_597,'#skF_5')
      | ~ m1_subset_1(B_597,'#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_7485])).

tff(c_8427,plain,(
    ! [B_18] :
      ( ~ m1_subset_1(B_18,'#skF_6')
      | ~ v1_xboole_0(B_18)
      | ~ v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_8419])).

tff(c_8433,plain,(
    ! [B_598] :
      ( ~ m1_subset_1(B_598,'#skF_6')
      | ~ v1_xboole_0(B_598) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8346,c_8427])).

tff(c_8443,plain,(
    ! [B_18] :
      ( ~ v1_xboole_0(B_18)
      | ~ v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_8433])).

tff(c_8444,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_8443])).

tff(c_8975,plain,(
    ! [B_643,A_644] :
      ( r1_tarski(B_643,A_644)
      | ~ m1_subset_1(B_643,k1_zfmisc_1(A_644))
      | v1_xboole_0(k1_zfmisc_1(A_644)) ) ),
    inference(resolution,[status(thm)],[c_116,c_18])).

tff(c_9002,plain,
    ( r1_tarski('#skF_6','#skF_5')
    | v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_42,c_8975])).

tff(c_9015,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_9002])).

tff(c_8462,plain,(
    ! [A_603,B_604] :
      ( r2_hidden('#skF_1'(A_603),B_604)
      | ~ r1_tarski(A_603,B_604)
      | v1_xboole_0(A_603) ) ),
    inference(resolution,[status(thm)],[c_4,c_201])).

tff(c_8488,plain,(
    ! [B_604,A_603] :
      ( ~ v1_xboole_0(B_604)
      | ~ r1_tarski(A_603,B_604)
      | v1_xboole_0(A_603) ) ),
    inference(resolution,[status(thm)],[c_8462,c_2])).

tff(c_9018,plain,
    ( ~ v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_9015,c_8488])).

tff(c_9026,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8346,c_9018])).

tff(c_9028,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8444,c_9026])).

tff(c_9030,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_8443])).

tff(c_8354,plain,(
    ! [A_49] :
      ( A_49 = '#skF_5'
      | ~ v1_xboole_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_8346,c_197])).

tff(c_9042,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_9030,c_8354])).

tff(c_9048,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8359,c_9042])).

tff(c_9050,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_9072,plain,(
    ! [C_651,A_652] :
      ( r2_hidden(C_651,k1_zfmisc_1(A_652))
      | ~ r1_tarski(C_651,A_652) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_9081,plain,(
    ! [A_653,C_654] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_653))
      | ~ r1_tarski(C_654,A_653) ) ),
    inference(resolution,[status(thm)],[c_9072,c_2])).

tff(c_9094,plain,(
    ! [C_657] : ~ r1_tarski(C_657,'#skF_5') ),
    inference(resolution,[status(thm)],[c_9050,c_9081])).

tff(c_9099,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_16,c_9094])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:45:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.50/2.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.50/2.59  
% 7.50/2.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.50/2.59  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 7.50/2.59  
% 7.50/2.59  %Foreground sorts:
% 7.50/2.59  
% 7.50/2.59  
% 7.50/2.59  %Background operators:
% 7.50/2.59  
% 7.50/2.59  
% 7.50/2.59  %Foreground operators:
% 7.50/2.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.50/2.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.50/2.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.50/2.59  tff('#skF_7', type, '#skF_7': $i).
% 7.50/2.59  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.50/2.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.50/2.59  tff('#skF_5', type, '#skF_5': $i).
% 7.50/2.59  tff('#skF_6', type, '#skF_6': $i).
% 7.50/2.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.50/2.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.50/2.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.50/2.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.50/2.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.50/2.59  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.50/2.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.50/2.59  
% 7.75/2.65  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.75/2.65  tff(f_79, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_subset_1)).
% 7.75/2.65  tff(f_64, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 7.75/2.65  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.75/2.65  tff(f_51, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 7.75/2.65  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.75/2.65  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.75/2.65  tff(c_38, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.75/2.65  tff(c_34, plain, (![B_18, A_17]: (m1_subset_1(B_18, A_17) | ~v1_xboole_0(B_18) | ~v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.75/2.65  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.75/2.65  tff(c_71, plain, (![D_32]: (r2_hidden(D_32, '#skF_7') | ~r2_hidden(D_32, '#skF_6') | ~m1_subset_1(D_32, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.75/2.65  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.75/2.65  tff(c_75, plain, (![D_32]: (~v1_xboole_0('#skF_7') | ~r2_hidden(D_32, '#skF_6') | ~m1_subset_1(D_32, '#skF_5'))), inference(resolution, [status(thm)], [c_71, c_2])).
% 7.75/2.65  tff(c_217, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_75])).
% 7.75/2.65  tff(c_130, plain, (![D_46]: (r2_hidden(D_46, '#skF_6') | ~r2_hidden(D_46, '#skF_7') | ~m1_subset_1(D_46, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.75/2.65  tff(c_144, plain, (r2_hidden('#skF_1'('#skF_7'), '#skF_6') | ~m1_subset_1('#skF_1'('#skF_7'), '#skF_5') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_4, c_130])).
% 7.75/2.65  tff(c_226, plain, (r2_hidden('#skF_1'('#skF_7'), '#skF_6') | ~m1_subset_1('#skF_1'('#skF_7'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_217, c_144])).
% 7.75/2.65  tff(c_227, plain, (~m1_subset_1('#skF_1'('#skF_7'), '#skF_5')), inference(splitLeft, [status(thm)], [c_226])).
% 7.75/2.65  tff(c_98, plain, (![B_41, A_42]: (m1_subset_1(B_41, A_42) | ~r2_hidden(B_41, A_42) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.75/2.65  tff(c_110, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_98])).
% 7.75/2.65  tff(c_231, plain, (~v1_xboole_0('#skF_1'('#skF_7')) | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_34, c_227])).
% 7.75/2.65  tff(c_232, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_231])).
% 7.75/2.65  tff(c_40, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.75/2.65  tff(c_61, plain, (![B_30, A_31]: (v1_xboole_0(B_30) | ~m1_subset_1(B_30, A_31) | ~v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.75/2.65  tff(c_68, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_61])).
% 7.75/2.65  tff(c_70, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_68])).
% 7.75/2.65  tff(c_116, plain, (![B_44, A_45]: (r2_hidden(B_44, A_45) | ~m1_subset_1(B_44, A_45) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.75/2.65  tff(c_18, plain, (![C_16, A_12]: (r1_tarski(C_16, A_12) | ~r2_hidden(C_16, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.75/2.65  tff(c_403, plain, (![B_82, A_83]: (r1_tarski(B_82, A_83) | ~m1_subset_1(B_82, k1_zfmisc_1(A_83)) | v1_xboole_0(k1_zfmisc_1(A_83)))), inference(resolution, [status(thm)], [c_116, c_18])).
% 7.75/2.65  tff(c_421, plain, (r1_tarski('#skF_7', '#skF_5') | v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_403])).
% 7.75/2.65  tff(c_432, plain, (r1_tarski('#skF_7', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_421])).
% 7.75/2.65  tff(c_32, plain, (![B_18, A_17]: (r2_hidden(B_18, A_17) | ~m1_subset_1(B_18, A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.75/2.65  tff(c_201, plain, (![C_57, B_58, A_59]: (r2_hidden(C_57, B_58) | ~r2_hidden(C_57, A_59) | ~r1_tarski(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.75/2.65  tff(c_984, plain, (![B_124, B_125, A_126]: (r2_hidden(B_124, B_125) | ~r1_tarski(A_126, B_125) | ~m1_subset_1(B_124, A_126) | v1_xboole_0(A_126))), inference(resolution, [status(thm)], [c_32, c_201])).
% 7.75/2.65  tff(c_998, plain, (![B_124]: (r2_hidden(B_124, '#skF_5') | ~m1_subset_1(B_124, '#skF_7') | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_432, c_984])).
% 7.75/2.65  tff(c_1047, plain, (![B_128]: (r2_hidden(B_128, '#skF_5') | ~m1_subset_1(B_128, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_217, c_998])).
% 7.75/2.65  tff(c_30, plain, (![B_18, A_17]: (m1_subset_1(B_18, A_17) | ~r2_hidden(B_18, A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.75/2.65  tff(c_1063, plain, (![B_128]: (m1_subset_1(B_128, '#skF_5') | v1_xboole_0('#skF_5') | ~m1_subset_1(B_128, '#skF_7'))), inference(resolution, [status(thm)], [c_1047, c_30])).
% 7.75/2.65  tff(c_1121, plain, (![B_131]: (m1_subset_1(B_131, '#skF_5') | ~m1_subset_1(B_131, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_232, c_1063])).
% 7.75/2.65  tff(c_1132, plain, (m1_subset_1('#skF_1'('#skF_7'), '#skF_5') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_110, c_1121])).
% 7.75/2.65  tff(c_1145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_217, c_227, c_1132])).
% 7.75/2.65  tff(c_1147, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_231])).
% 7.75/2.65  tff(c_1717, plain, (![B_176, A_177]: (r1_tarski(B_176, A_177) | ~m1_subset_1(B_176, k1_zfmisc_1(A_177)) | v1_xboole_0(k1_zfmisc_1(A_177)))), inference(resolution, [status(thm)], [c_116, c_18])).
% 7.75/2.65  tff(c_1737, plain, (r1_tarski('#skF_7', '#skF_5') | v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_1717])).
% 7.75/2.65  tff(c_1751, plain, (r1_tarski('#skF_7', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_1737])).
% 7.75/2.65  tff(c_1173, plain, (![A_135, B_136]: (r2_hidden('#skF_1'(A_135), B_136) | ~r1_tarski(A_135, B_136) | v1_xboole_0(A_135))), inference(resolution, [status(thm)], [c_4, c_201])).
% 7.75/2.65  tff(c_1194, plain, (![B_136, A_135]: (~v1_xboole_0(B_136) | ~r1_tarski(A_135, B_136) | v1_xboole_0(A_135))), inference(resolution, [status(thm)], [c_1173, c_2])).
% 7.75/2.65  tff(c_1789, plain, (~v1_xboole_0('#skF_5') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_1751, c_1194])).
% 7.75/2.65  tff(c_1797, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1147, c_1789])).
% 7.75/2.65  tff(c_1799, plain, $false, inference(negUnitSimplification, [status(thm)], [c_217, c_1797])).
% 7.75/2.65  tff(c_1800, plain, (r2_hidden('#skF_1'('#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_226])).
% 7.75/2.65  tff(c_1812, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_1800, c_2])).
% 7.75/2.65  tff(c_161, plain, (![A_49, B_50]: (r2_hidden('#skF_2'(A_49, B_50), A_49) | r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.75/2.65  tff(c_183, plain, (![A_49, B_50]: (m1_subset_1('#skF_2'(A_49, B_50), A_49) | v1_xboole_0(A_49) | r1_tarski(A_49, B_50))), inference(resolution, [status(thm)], [c_161, c_30])).
% 7.75/2.65  tff(c_1801, plain, (m1_subset_1('#skF_1'('#skF_7'), '#skF_5')), inference(splitRight, [status(thm)], [c_226])).
% 7.75/2.65  tff(c_36, plain, (![B_18, A_17]: (v1_xboole_0(B_18) | ~m1_subset_1(B_18, A_17) | ~v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.75/2.65  tff(c_1816, plain, (v1_xboole_0('#skF_1'('#skF_7')) | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_1801, c_36])).
% 7.75/2.65  tff(c_1817, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_1816])).
% 7.75/2.65  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.75/2.65  tff(c_3587, plain, (![B_301, A_302]: (r1_tarski(B_301, A_302) | ~m1_subset_1(B_301, k1_zfmisc_1(A_302)) | v1_xboole_0(k1_zfmisc_1(A_302)))), inference(resolution, [status(thm)], [c_116, c_18])).
% 7.75/2.65  tff(c_3627, plain, (r1_tarski('#skF_6', '#skF_5') | v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_3587])).
% 7.75/2.65  tff(c_3643, plain, (r1_tarski('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_3627])).
% 7.75/2.65  tff(c_4205, plain, (![B_337, B_338, A_339]: (r2_hidden(B_337, B_338) | ~r1_tarski(A_339, B_338) | ~m1_subset_1(B_337, A_339) | v1_xboole_0(A_339))), inference(resolution, [status(thm)], [c_32, c_201])).
% 7.75/2.65  tff(c_4215, plain, (![B_337]: (r2_hidden(B_337, '#skF_5') | ~m1_subset_1(B_337, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_3643, c_4205])).
% 7.75/2.65  tff(c_4261, plain, (![B_340]: (r2_hidden(B_340, '#skF_5') | ~m1_subset_1(B_340, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_1812, c_4215])).
% 7.75/2.65  tff(c_4277, plain, (![B_340]: (m1_subset_1(B_340, '#skF_5') | v1_xboole_0('#skF_5') | ~m1_subset_1(B_340, '#skF_6'))), inference(resolution, [status(thm)], [c_4261, c_30])).
% 7.75/2.65  tff(c_4317, plain, (![B_342]: (m1_subset_1(B_342, '#skF_5') | ~m1_subset_1(B_342, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_1817, c_4277])).
% 7.75/2.65  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.75/2.65  tff(c_46, plain, (![D_23]: (r2_hidden(D_23, '#skF_7') | ~r2_hidden(D_23, '#skF_6') | ~m1_subset_1(D_23, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.75/2.65  tff(c_145, plain, (![A_47, B_48]: (~r2_hidden('#skF_2'(A_47, B_48), B_48) | r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.75/2.65  tff(c_3376, plain, (![A_281]: (r1_tarski(A_281, '#skF_7') | ~r2_hidden('#skF_2'(A_281, '#skF_7'), '#skF_6') | ~m1_subset_1('#skF_2'(A_281, '#skF_7'), '#skF_5'))), inference(resolution, [status(thm)], [c_46, c_145])).
% 7.75/2.65  tff(c_3388, plain, (~m1_subset_1('#skF_2'('#skF_6', '#skF_7'), '#skF_5') | r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_10, c_3376])).
% 7.75/2.65  tff(c_3392, plain, (~m1_subset_1('#skF_2'('#skF_6', '#skF_7'), '#skF_5')), inference(splitLeft, [status(thm)], [c_3388])).
% 7.75/2.65  tff(c_4335, plain, (~m1_subset_1('#skF_2'('#skF_6', '#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_4317, c_3392])).
% 7.75/2.65  tff(c_4354, plain, (v1_xboole_0('#skF_6') | r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_183, c_4335])).
% 7.75/2.65  tff(c_4360, plain, (r1_tarski('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_1812, c_4354])).
% 7.75/2.65  tff(c_12, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.75/2.65  tff(c_4382, plain, ('#skF_7'='#skF_6' | ~r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_4360, c_12])).
% 7.75/2.65  tff(c_4399, plain, (~r1_tarski('#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_38, c_4382])).
% 7.75/2.65  tff(c_3624, plain, (r1_tarski('#skF_7', '#skF_5') | v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_3587])).
% 7.75/2.65  tff(c_3640, plain, (r1_tarski('#skF_7', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_3624])).
% 7.75/2.65  tff(c_4217, plain, (![B_337]: (r2_hidden(B_337, '#skF_5') | ~m1_subset_1(B_337, '#skF_7') | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_3640, c_4205])).
% 7.75/2.65  tff(c_4289, plain, (![B_341]: (r2_hidden(B_341, '#skF_5') | ~m1_subset_1(B_341, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_217, c_4217])).
% 7.75/2.65  tff(c_4305, plain, (![B_341]: (m1_subset_1(B_341, '#skF_5') | v1_xboole_0('#skF_5') | ~m1_subset_1(B_341, '#skF_7'))), inference(resolution, [status(thm)], [c_4289, c_30])).
% 7.75/2.65  tff(c_4428, plain, (![B_346]: (m1_subset_1(B_346, '#skF_5') | ~m1_subset_1(B_346, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_1817, c_4305])).
% 7.75/2.65  tff(c_4440, plain, (![B_50]: (m1_subset_1('#skF_2'('#skF_7', B_50), '#skF_5') | v1_xboole_0('#skF_7') | r1_tarski('#skF_7', B_50))), inference(resolution, [status(thm)], [c_183, c_4428])).
% 7.75/2.65  tff(c_4700, plain, (![B_355]: (m1_subset_1('#skF_2'('#skF_7', B_355), '#skF_5') | r1_tarski('#skF_7', B_355))), inference(negUnitSimplification, [status(thm)], [c_217, c_4440])).
% 7.75/2.65  tff(c_44, plain, (![D_23]: (r2_hidden(D_23, '#skF_6') | ~r2_hidden(D_23, '#skF_7') | ~m1_subset_1(D_23, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.75/2.65  tff(c_3458, plain, (![B_289]: (r2_hidden('#skF_2'('#skF_7', B_289), '#skF_6') | ~m1_subset_1('#skF_2'('#skF_7', B_289), '#skF_5') | r1_tarski('#skF_7', B_289))), inference(resolution, [status(thm)], [c_161, c_44])).
% 7.75/2.65  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.75/2.65  tff(c_3485, plain, (~m1_subset_1('#skF_2'('#skF_7', '#skF_6'), '#skF_5') | r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_3458, c_8])).
% 7.75/2.65  tff(c_3490, plain, (~m1_subset_1('#skF_2'('#skF_7', '#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_3485])).
% 7.75/2.65  tff(c_4707, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_4700, c_3490])).
% 7.75/2.65  tff(c_4717, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4399, c_4707])).
% 7.75/2.65  tff(c_4718, plain, (r1_tarski('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_3485])).
% 7.75/2.65  tff(c_4730, plain, ('#skF_7'='#skF_6' | ~r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_4718, c_12])).
% 7.75/2.65  tff(c_4738, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_38, c_4730])).
% 7.75/2.65  tff(c_4747, plain, (![B_356, A_357]: (r1_tarski(B_356, A_357) | ~m1_subset_1(B_356, k1_zfmisc_1(A_357)) | v1_xboole_0(k1_zfmisc_1(A_357)))), inference(resolution, [status(thm)], [c_116, c_18])).
% 7.75/2.65  tff(c_4776, plain, (r1_tarski('#skF_6', '#skF_5') | v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_4747])).
% 7.75/2.65  tff(c_4788, plain, (r1_tarski('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_4776])).
% 7.75/2.65  tff(c_4992, plain, (![B_378, B_379, A_380]: (r2_hidden(B_378, B_379) | ~r1_tarski(A_380, B_379) | ~m1_subset_1(B_378, A_380) | v1_xboole_0(A_380))), inference(resolution, [status(thm)], [c_32, c_201])).
% 7.75/2.65  tff(c_4998, plain, (![B_378]: (r2_hidden(B_378, '#skF_5') | ~m1_subset_1(B_378, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_4788, c_4992])).
% 7.75/2.65  tff(c_5041, plain, (![B_381]: (r2_hidden(B_381, '#skF_5') | ~m1_subset_1(B_381, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_1812, c_4998])).
% 7.75/2.65  tff(c_5057, plain, (![B_381]: (m1_subset_1(B_381, '#skF_5') | v1_xboole_0('#skF_5') | ~m1_subset_1(B_381, '#skF_6'))), inference(resolution, [status(thm)], [c_5041, c_30])).
% 7.75/2.65  tff(c_5211, plain, (![B_386]: (m1_subset_1(B_386, '#skF_5') | ~m1_subset_1(B_386, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_1817, c_5057])).
% 7.75/2.65  tff(c_5225, plain, (~m1_subset_1('#skF_2'('#skF_6', '#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_5211, c_3392])).
% 7.75/2.65  tff(c_5229, plain, (v1_xboole_0('#skF_6') | r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_183, c_5225])).
% 7.75/2.65  tff(c_5236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4738, c_1812, c_5229])).
% 7.75/2.65  tff(c_5237, plain, (r1_tarski('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_3388])).
% 7.75/2.65  tff(c_5249, plain, ('#skF_7'='#skF_6' | ~r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_5237, c_12])).
% 7.75/2.65  tff(c_5257, plain, (~r1_tarski('#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_38, c_5249])).
% 7.75/2.65  tff(c_5436, plain, (![B_401, A_402]: (r1_tarski(B_401, A_402) | ~m1_subset_1(B_401, k1_zfmisc_1(A_402)) | v1_xboole_0(k1_zfmisc_1(A_402)))), inference(resolution, [status(thm)], [c_116, c_18])).
% 7.75/2.65  tff(c_5473, plain, (r1_tarski('#skF_7', '#skF_5') | v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_5436])).
% 7.75/2.65  tff(c_5489, plain, (r1_tarski('#skF_7', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_5473])).
% 7.75/2.65  tff(c_5775, plain, (![B_424, B_425, A_426]: (r2_hidden(B_424, B_425) | ~r1_tarski(A_426, B_425) | ~m1_subset_1(B_424, A_426) | v1_xboole_0(A_426))), inference(resolution, [status(thm)], [c_32, c_201])).
% 7.75/2.65  tff(c_5787, plain, (![B_424]: (r2_hidden(B_424, '#skF_5') | ~m1_subset_1(B_424, '#skF_7') | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_5489, c_5775])).
% 7.75/2.65  tff(c_5858, plain, (![B_428]: (r2_hidden(B_428, '#skF_5') | ~m1_subset_1(B_428, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_217, c_5787])).
% 7.75/2.65  tff(c_5874, plain, (![B_428]: (m1_subset_1(B_428, '#skF_5') | v1_xboole_0('#skF_5') | ~m1_subset_1(B_428, '#skF_7'))), inference(resolution, [status(thm)], [c_5858, c_30])).
% 7.75/2.65  tff(c_5977, plain, (![B_432]: (m1_subset_1(B_432, '#skF_5') | ~m1_subset_1(B_432, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_1817, c_5874])).
% 7.75/2.65  tff(c_5988, plain, (![B_50]: (m1_subset_1('#skF_2'('#skF_7', B_50), '#skF_5') | v1_xboole_0('#skF_7') | r1_tarski('#skF_7', B_50))), inference(resolution, [status(thm)], [c_183, c_5977])).
% 7.75/2.65  tff(c_6224, plain, (![B_445]: (m1_subset_1('#skF_2'('#skF_7', B_445), '#skF_5') | r1_tarski('#skF_7', B_445))), inference(negUnitSimplification, [status(thm)], [c_217, c_5988])).
% 7.75/2.65  tff(c_5295, plain, (![B_391]: (r2_hidden('#skF_2'('#skF_7', B_391), '#skF_6') | ~m1_subset_1('#skF_2'('#skF_7', B_391), '#skF_5') | r1_tarski('#skF_7', B_391))), inference(resolution, [status(thm)], [c_161, c_44])).
% 7.75/2.65  tff(c_5310, plain, (~m1_subset_1('#skF_2'('#skF_7', '#skF_6'), '#skF_5') | r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_5295, c_8])).
% 7.75/2.65  tff(c_5324, plain, (~m1_subset_1('#skF_2'('#skF_7', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_5257, c_5257, c_5310])).
% 7.75/2.65  tff(c_6231, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_6224, c_5324])).
% 7.75/2.65  tff(c_6241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5257, c_6231])).
% 7.75/2.65  tff(c_6243, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_1816])).
% 7.75/2.65  tff(c_55, plain, (![C_28, A_29]: (r1_tarski(C_28, A_29) | ~r2_hidden(C_28, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.75/2.65  tff(c_60, plain, (![A_29]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_29)), A_29) | v1_xboole_0(k1_zfmisc_1(A_29)))), inference(resolution, [status(thm)], [c_4, c_55])).
% 7.75/2.65  tff(c_6619, plain, (![A_465, B_466]: (r2_hidden('#skF_1'(A_465), B_466) | ~r1_tarski(A_465, B_466) | v1_xboole_0(A_465))), inference(resolution, [status(thm)], [c_4, c_201])).
% 7.75/2.65  tff(c_6654, plain, (![B_467, A_468]: (~v1_xboole_0(B_467) | ~r1_tarski(A_468, B_467) | v1_xboole_0(A_468))), inference(resolution, [status(thm)], [c_6619, c_2])).
% 7.75/2.65  tff(c_6712, plain, (![A_473]: (~v1_xboole_0(A_473) | v1_xboole_0('#skF_1'(k1_zfmisc_1(A_473))) | v1_xboole_0(k1_zfmisc_1(A_473)))), inference(resolution, [status(thm)], [c_60, c_6654])).
% 7.75/2.65  tff(c_185, plain, (![A_49, B_50]: (~v1_xboole_0(A_49) | r1_tarski(A_49, B_50))), inference(resolution, [status(thm)], [c_161, c_2])).
% 7.75/2.65  tff(c_186, plain, (![A_51, B_52]: (~v1_xboole_0(A_51) | r1_tarski(A_51, B_52))), inference(resolution, [status(thm)], [c_161, c_2])).
% 7.75/2.65  tff(c_190, plain, (![B_53, A_54]: (B_53=A_54 | ~r1_tarski(B_53, A_54) | ~v1_xboole_0(A_54))), inference(resolution, [status(thm)], [c_186, c_12])).
% 7.75/2.65  tff(c_197, plain, (![B_50, A_49]: (B_50=A_49 | ~v1_xboole_0(B_50) | ~v1_xboole_0(A_49))), inference(resolution, [status(thm)], [c_185, c_190])).
% 7.75/2.65  tff(c_6246, plain, (![A_49]: (A_49='#skF_5' | ~v1_xboole_0(A_49))), inference(resolution, [status(thm)], [c_6243, c_197])).
% 7.75/2.65  tff(c_6939, plain, (![A_485]: ('#skF_1'(k1_zfmisc_1(A_485))='#skF_5' | ~v1_xboole_0(A_485) | v1_xboole_0(k1_zfmisc_1(A_485)))), inference(resolution, [status(thm)], [c_6712, c_6246])).
% 7.75/2.65  tff(c_81, plain, (![C_35, A_36]: (r2_hidden(C_35, k1_zfmisc_1(A_36)) | ~r1_tarski(C_35, A_36))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.75/2.65  tff(c_89, plain, (![A_36, C_35]: (~v1_xboole_0(k1_zfmisc_1(A_36)) | ~r1_tarski(C_35, A_36))), inference(resolution, [status(thm)], [c_81, c_2])).
% 7.75/2.65  tff(c_7061, plain, (![C_490, A_491]: (~r1_tarski(C_490, A_491) | '#skF_1'(k1_zfmisc_1(A_491))='#skF_5' | ~v1_xboole_0(A_491))), inference(resolution, [status(thm)], [c_6939, c_89])).
% 7.75/2.65  tff(c_7083, plain, (![B_492]: ('#skF_1'(k1_zfmisc_1(B_492))='#skF_5' | ~v1_xboole_0(B_492))), inference(resolution, [status(thm)], [c_16, c_7061])).
% 7.75/2.65  tff(c_7142, plain, (![B_495]: (r1_tarski('#skF_5', B_495) | v1_xboole_0(k1_zfmisc_1(B_495)) | ~v1_xboole_0(B_495))), inference(superposition, [status(thm), theory('equality')], [c_7083, c_60])).
% 7.75/2.65  tff(c_7204, plain, (![C_498, B_499]: (~r1_tarski(C_498, B_499) | r1_tarski('#skF_5', B_499) | ~v1_xboole_0(B_499))), inference(resolution, [status(thm)], [c_7142, c_89])).
% 7.75/2.65  tff(c_7231, plain, (![B_11]: (r1_tarski('#skF_5', B_11) | ~v1_xboole_0(B_11))), inference(resolution, [status(thm)], [c_16, c_7204])).
% 7.75/2.65  tff(c_6242, plain, (v1_xboole_0('#skF_1'('#skF_7'))), inference(splitRight, [status(thm)], [c_1816])).
% 7.75/2.65  tff(c_6250, plain, (![A_446]: (A_446='#skF_5' | ~v1_xboole_0(A_446))), inference(resolution, [status(thm)], [c_6243, c_197])).
% 7.75/2.65  tff(c_6257, plain, ('#skF_1'('#skF_7')='#skF_5'), inference(resolution, [status(thm)], [c_6242, c_6250])).
% 7.75/2.65  tff(c_6286, plain, (v1_xboole_0('#skF_7') | r2_hidden('#skF_5', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_6257, c_4])).
% 7.75/2.65  tff(c_6290, plain, (r2_hidden('#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_217, c_6286])).
% 7.75/2.65  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.75/2.65  tff(c_6476, plain, (![B_455]: (r2_hidden('#skF_5', B_455) | ~r1_tarski('#skF_7', B_455))), inference(resolution, [status(thm)], [c_6290, c_6])).
% 7.75/2.65  tff(c_7293, plain, (![B_509, B_510]: (r2_hidden('#skF_5', B_509) | ~r1_tarski(B_510, B_509) | ~r1_tarski('#skF_7', B_510))), inference(resolution, [status(thm)], [c_6476, c_6])).
% 7.75/2.65  tff(c_7312, plain, (![B_11]: (r2_hidden('#skF_5', B_11) | ~r1_tarski('#skF_7', '#skF_5') | ~v1_xboole_0(B_11))), inference(resolution, [status(thm)], [c_7231, c_7293])).
% 7.75/2.65  tff(c_7321, plain, (~r1_tarski('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_7312])).
% 7.75/2.65  tff(c_7390, plain, (![B_518, A_519]: (r1_tarski(B_518, A_519) | ~m1_subset_1(B_518, k1_zfmisc_1(A_519)) | v1_xboole_0(k1_zfmisc_1(A_519)))), inference(resolution, [status(thm)], [c_116, c_18])).
% 7.75/2.65  tff(c_7414, plain, (r1_tarski('#skF_7', '#skF_5') | v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_7390])).
% 7.75/2.65  tff(c_7430, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_7321, c_7414])).
% 7.75/2.65  tff(c_7432, plain, (r1_tarski('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_7312])).
% 7.75/2.65  tff(c_6652, plain, (![B_466, A_465]: (~v1_xboole_0(B_466) | ~r1_tarski(A_465, B_466) | v1_xboole_0(A_465))), inference(resolution, [status(thm)], [c_6619, c_2])).
% 7.75/2.65  tff(c_7439, plain, (~v1_xboole_0('#skF_5') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_7432, c_6652])).
% 7.75/2.65  tff(c_7457, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6243, c_7439])).
% 7.75/2.65  tff(c_7459, plain, $false, inference(negUnitSimplification, [status(thm)], [c_217, c_7457])).
% 7.75/2.65  tff(c_7471, plain, (![D_521]: (~r2_hidden(D_521, '#skF_6') | ~m1_subset_1(D_521, '#skF_5'))), inference(splitRight, [status(thm)], [c_75])).
% 7.75/2.65  tff(c_7486, plain, (~m1_subset_1('#skF_1'('#skF_6'), '#skF_5') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_4, c_7471])).
% 7.75/2.65  tff(c_7521, plain, (~m1_subset_1('#skF_1'('#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_7486])).
% 7.75/2.65  tff(c_7525, plain, (~v1_xboole_0('#skF_1'('#skF_6')) | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_34, c_7521])).
% 7.75/2.65  tff(c_7526, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_7525])).
% 7.75/2.65  tff(c_7485, plain, (![B_18]: (~m1_subset_1(B_18, '#skF_5') | ~m1_subset_1(B_18, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_32, c_7471])).
% 7.75/2.65  tff(c_7537, plain, (![B_525]: (~m1_subset_1(B_525, '#skF_5') | ~m1_subset_1(B_525, '#skF_6'))), inference(splitLeft, [status(thm)], [c_7485])).
% 7.75/2.65  tff(c_7541, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_110, c_7537])).
% 7.75/2.65  tff(c_7548, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_7526, c_7541])).
% 7.75/2.65  tff(c_7553, plain, (~v1_xboole_0('#skF_1'('#skF_5')) | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_34, c_7548])).
% 7.75/2.65  tff(c_7565, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_7553])).
% 7.75/2.65  tff(c_8014, plain, (![B_574, A_575]: (r1_tarski(B_574, A_575) | ~m1_subset_1(B_574, k1_zfmisc_1(A_575)) | v1_xboole_0(k1_zfmisc_1(A_575)))), inference(resolution, [status(thm)], [c_116, c_18])).
% 7.75/2.65  tff(c_8037, plain, (r1_tarski('#skF_6', '#skF_5') | v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_8014])).
% 7.75/2.65  tff(c_8049, plain, (r1_tarski('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_8037])).
% 7.75/2.65  tff(c_8166, plain, (![B_583, B_584, A_585]: (r2_hidden(B_583, B_584) | ~r1_tarski(A_585, B_584) | ~m1_subset_1(B_583, A_585) | v1_xboole_0(A_585))), inference(resolution, [status(thm)], [c_32, c_201])).
% 7.75/2.65  tff(c_8170, plain, (![B_583]: (r2_hidden(B_583, '#skF_5') | ~m1_subset_1(B_583, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_8049, c_8166])).
% 7.75/2.65  tff(c_8204, plain, (![B_586]: (r2_hidden(B_586, '#skF_5') | ~m1_subset_1(B_586, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_7565, c_8170])).
% 7.75/2.65  tff(c_8220, plain, (![B_586]: (m1_subset_1(B_586, '#skF_5') | v1_xboole_0('#skF_5') | ~m1_subset_1(B_586, '#skF_6'))), inference(resolution, [status(thm)], [c_8204, c_30])).
% 7.75/2.65  tff(c_8232, plain, (![B_587]: (m1_subset_1(B_587, '#skF_5') | ~m1_subset_1(B_587, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_7526, c_8220])).
% 7.75/2.65  tff(c_7536, plain, (![B_18]: (~m1_subset_1(B_18, '#skF_5') | ~m1_subset_1(B_18, '#skF_6'))), inference(splitLeft, [status(thm)], [c_7485])).
% 7.75/2.65  tff(c_8304, plain, (![B_591]: (~m1_subset_1(B_591, '#skF_6'))), inference(resolution, [status(thm)], [c_8232, c_7536])).
% 7.75/2.65  tff(c_8312, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_110, c_8304])).
% 7.75/2.65  tff(c_8323, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7565, c_8312])).
% 7.75/2.65  tff(c_8325, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_7553])).
% 7.75/2.65  tff(c_7461, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_75])).
% 7.75/2.65  tff(c_7464, plain, (![A_49]: (A_49='#skF_7' | ~v1_xboole_0(A_49))), inference(resolution, [status(thm)], [c_7461, c_197])).
% 7.75/2.65  tff(c_8328, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_8325, c_7464])).
% 7.75/2.65  tff(c_8334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_8328])).
% 7.75/2.65  tff(c_8335, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_7485])).
% 7.75/2.65  tff(c_8338, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_8335, c_7464])).
% 7.75/2.65  tff(c_8344, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_8338])).
% 7.75/2.65  tff(c_8346, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_7525])).
% 7.75/2.65  tff(c_8353, plain, ('#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_8346, c_7464])).
% 7.75/2.65  tff(c_8359, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_8353, c_38])).
% 7.75/2.65  tff(c_8419, plain, (![B_597]: (~m1_subset_1(B_597, '#skF_5') | ~m1_subset_1(B_597, '#skF_6'))), inference(splitLeft, [status(thm)], [c_7485])).
% 7.75/2.65  tff(c_8427, plain, (![B_18]: (~m1_subset_1(B_18, '#skF_6') | ~v1_xboole_0(B_18) | ~v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_34, c_8419])).
% 7.75/2.65  tff(c_8433, plain, (![B_598]: (~m1_subset_1(B_598, '#skF_6') | ~v1_xboole_0(B_598))), inference(demodulation, [status(thm), theory('equality')], [c_8346, c_8427])).
% 7.75/2.65  tff(c_8443, plain, (![B_18]: (~v1_xboole_0(B_18) | ~v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_34, c_8433])).
% 7.75/2.65  tff(c_8444, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_8443])).
% 7.75/2.65  tff(c_8975, plain, (![B_643, A_644]: (r1_tarski(B_643, A_644) | ~m1_subset_1(B_643, k1_zfmisc_1(A_644)) | v1_xboole_0(k1_zfmisc_1(A_644)))), inference(resolution, [status(thm)], [c_116, c_18])).
% 7.75/2.65  tff(c_9002, plain, (r1_tarski('#skF_6', '#skF_5') | v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_8975])).
% 7.75/2.65  tff(c_9015, plain, (r1_tarski('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_9002])).
% 7.75/2.65  tff(c_8462, plain, (![A_603, B_604]: (r2_hidden('#skF_1'(A_603), B_604) | ~r1_tarski(A_603, B_604) | v1_xboole_0(A_603))), inference(resolution, [status(thm)], [c_4, c_201])).
% 7.75/2.65  tff(c_8488, plain, (![B_604, A_603]: (~v1_xboole_0(B_604) | ~r1_tarski(A_603, B_604) | v1_xboole_0(A_603))), inference(resolution, [status(thm)], [c_8462, c_2])).
% 7.75/2.65  tff(c_9018, plain, (~v1_xboole_0('#skF_5') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_9015, c_8488])).
% 7.75/2.65  tff(c_9026, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8346, c_9018])).
% 7.75/2.65  tff(c_9028, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8444, c_9026])).
% 7.75/2.65  tff(c_9030, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_8443])).
% 7.75/2.65  tff(c_8354, plain, (![A_49]: (A_49='#skF_5' | ~v1_xboole_0(A_49))), inference(resolution, [status(thm)], [c_8346, c_197])).
% 7.75/2.65  tff(c_9042, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_9030, c_8354])).
% 7.75/2.65  tff(c_9048, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8359, c_9042])).
% 7.75/2.65  tff(c_9050, plain, (v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(splitRight, [status(thm)], [c_68])).
% 7.75/2.65  tff(c_9072, plain, (![C_651, A_652]: (r2_hidden(C_651, k1_zfmisc_1(A_652)) | ~r1_tarski(C_651, A_652))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.75/2.65  tff(c_9081, plain, (![A_653, C_654]: (~v1_xboole_0(k1_zfmisc_1(A_653)) | ~r1_tarski(C_654, A_653))), inference(resolution, [status(thm)], [c_9072, c_2])).
% 7.75/2.65  tff(c_9094, plain, (![C_657]: (~r1_tarski(C_657, '#skF_5'))), inference(resolution, [status(thm)], [c_9050, c_9081])).
% 7.75/2.65  tff(c_9099, plain, $false, inference(resolution, [status(thm)], [c_16, c_9094])).
% 7.75/2.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.75/2.65  
% 7.75/2.65  Inference rules
% 7.75/2.65  ----------------------
% 7.75/2.65  #Ref     : 0
% 7.75/2.65  #Sup     : 2023
% 7.75/2.65  #Fact    : 0
% 7.75/2.65  #Define  : 0
% 7.75/2.65  #Split   : 44
% 7.75/2.65  #Chain   : 0
% 7.75/2.65  #Close   : 0
% 7.75/2.65  
% 7.75/2.65  Ordering : KBO
% 7.75/2.65  
% 7.75/2.65  Simplification rules
% 7.75/2.65  ----------------------
% 7.75/2.65  #Subsume      : 601
% 7.75/2.65  #Demod        : 377
% 7.75/2.65  #Tautology    : 324
% 7.75/2.65  #SimpNegUnit  : 253
% 7.75/2.65  #BackRed      : 8
% 7.75/2.65  
% 7.75/2.65  #Partial instantiations: 0
% 7.75/2.65  #Strategies tried      : 1
% 7.75/2.65  
% 7.75/2.65  Timing (in seconds)
% 7.75/2.65  ----------------------
% 7.75/2.65  Preprocessing        : 0.30
% 7.75/2.66  Parsing              : 0.15
% 7.75/2.66  CNF conversion       : 0.02
% 7.75/2.66  Main loop            : 1.50
% 7.75/2.66  Inferencing          : 0.54
% 7.75/2.66  Reduction            : 0.39
% 7.75/2.66  Demodulation         : 0.23
% 7.75/2.66  BG Simplification    : 0.05
% 7.75/2.66  Subsumption          : 0.39
% 7.75/2.66  Abstraction          : 0.06
% 7.75/2.66  MUC search           : 0.00
% 7.75/2.66  Cooper               : 0.00
% 7.75/2.66  Total                : 1.91
% 7.75/2.66  Index Insertion      : 0.00
% 7.75/2.66  Index Deletion       : 0.00
% 7.75/2.66  Index Matching       : 0.00
% 7.75/2.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
