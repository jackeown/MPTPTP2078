%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:44 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 418 expanded)
%              Number of leaves         :   33 ( 163 expanded)
%              Depth                    :   11
%              Number of atoms          :  170 (1137 expanded)
%              Number of equality atoms :  125 ( 915 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_120,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & ~ ! [D] :
                ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
               => ( D != k5_mcart_1(A,B,C,D)
                  & D != k6_mcart_1(A,B,C,D)
                  & D != k7_mcart_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C,D] : k3_zfmisc_1(k1_tarski(A),k2_tarski(B,C),k1_tarski(D)) = k2_tarski(k3_mcart_1(A,B,D),k3_mcart_1(A,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_mcart_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_tarski(A,k3_zfmisc_1(A,B,C))
          & ~ r1_tarski(A,k3_zfmisc_1(B,C,A))
          & ~ r1_tarski(A,k3_zfmisc_1(C,A,B)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_mcart_1)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(k1_tarski(B_7),k1_tarski(B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_894,plain,(
    ! [A_174,B_175,C_176,D_177] :
      ( k7_mcart_1(A_174,B_175,C_176,D_177) = k2_mcart_1(D_177)
      | ~ m1_subset_1(D_177,k3_zfmisc_1(A_174,B_175,C_176))
      | k1_xboole_0 = C_176
      | k1_xboole_0 = B_175
      | k1_xboole_0 = A_174 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_903,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_mcart_1('#skF_4')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_38,c_894])).

tff(c_906,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_mcart_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_903])).

tff(c_152,plain,(
    ! [A_54,B_55,C_56,D_57] :
      ( k7_mcart_1(A_54,B_55,C_56,D_57) = k2_mcart_1(D_57)
      | ~ m1_subset_1(D_57,k3_zfmisc_1(A_54,B_55,C_56))
      | k1_xboole_0 = C_56
      | k1_xboole_0 = B_55
      | k1_xboole_0 = A_54 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_158,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_mcart_1('#skF_4')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_38,c_152])).

tff(c_161,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_mcart_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_158])).

tff(c_36,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_4'
    | k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_4'
    | k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_72,plain,(
    k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_273,plain,(
    ! [A_94,B_95,C_96,D_97] :
      ( k3_mcart_1(k5_mcart_1(A_94,B_95,C_96,D_97),k6_mcart_1(A_94,B_95,C_96,D_97),k7_mcart_1(A_94,B_95,C_96,D_97)) = D_97
      | ~ m1_subset_1(D_97,k3_zfmisc_1(A_94,B_95,C_96))
      | k1_xboole_0 = C_96
      | k1_xboole_0 = B_95
      | k1_xboole_0 = A_94 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_321,plain,
    ( k3_mcart_1('#skF_4',k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | ~ m1_subset_1('#skF_4',k3_zfmisc_1('#skF_1','#skF_2','#skF_3'))
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_273])).

tff(c_329,plain,
    ( k3_mcart_1('#skF_4',k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_mcart_1('#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_161,c_321])).

tff(c_330,plain,(
    k3_mcart_1('#skF_4',k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_mcart_1('#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_329])).

tff(c_6,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_106,plain,(
    ! [A_50,B_51,C_52,D_53] : k3_zfmisc_1(k1_tarski(A_50),k2_tarski(B_51,C_52),k1_tarski(D_53)) = k2_tarski(k3_mcart_1(A_50,B_51,D_53),k3_mcart_1(A_50,C_52,D_53)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_144,plain,(
    ! [A_50,B_51,D_53] : k3_zfmisc_1(k1_tarski(A_50),k2_tarski(B_51,B_51),k1_tarski(D_53)) = k1_tarski(k3_mcart_1(A_50,B_51,D_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_106])).

tff(c_166,plain,(
    ! [A_58,B_59,D_60] : k3_zfmisc_1(k1_tarski(A_58),k1_tarski(B_59),k1_tarski(D_60)) = k1_tarski(k3_mcart_1(A_58,B_59,D_60)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_144])).

tff(c_28,plain,(
    ! [A_19,B_20,C_21] :
      ( ~ r1_tarski(A_19,k3_zfmisc_1(A_19,B_20,C_21))
      | k1_xboole_0 = A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_175,plain,(
    ! [A_58,B_59,D_60] :
      ( ~ r1_tarski(k1_tarski(A_58),k1_tarski(k3_mcart_1(A_58,B_59,D_60)))
      | k1_tarski(A_58) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_28])).

tff(c_358,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_175])).

tff(c_362,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_358])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( r2_hidden(B_5,A_4)
      | k3_xboole_0(A_4,k1_tarski(B_5)) != k1_tarski(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_409,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_4',A_4)
      | k3_xboole_0(A_4,k1_xboole_0) != k1_tarski('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_8])).

tff(c_439,plain,(
    ! [A_4] : r2_hidden('#skF_4',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_2,c_409])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( ~ r2_hidden(B_9,A_8)
      | k4_xboole_0(A_8,k1_tarski(B_9)) != A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_412,plain,(
    ! [A_8] :
      ( ~ r2_hidden('#skF_4',A_8)
      | k4_xboole_0(A_8,k1_xboole_0) != A_8 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_16])).

tff(c_441,plain,(
    ! [A_8] : ~ r2_hidden('#skF_4',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_412])).

tff(c_449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_441])).

tff(c_450,plain,
    ( k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_4'
    | k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_480,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_450])).

tff(c_653,plain,(
    ! [A_160,B_161,C_162,D_163] :
      ( k3_mcart_1(k5_mcart_1(A_160,B_161,C_162,D_163),k6_mcart_1(A_160,B_161,C_162,D_163),k7_mcart_1(A_160,B_161,C_162,D_163)) = D_163
      | ~ m1_subset_1(D_163,k3_zfmisc_1(A_160,B_161,C_162))
      | k1_xboole_0 = C_162
      | k1_xboole_0 = B_161
      | k1_xboole_0 = A_160 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_698,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k3_zfmisc_1('#skF_1','#skF_2','#skF_3'))
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_653])).

tff(c_703,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4') = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_698])).

tff(c_704,plain,(
    k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_703])).

tff(c_486,plain,(
    ! [A_116,B_117,C_118,D_119] : k3_zfmisc_1(k1_tarski(A_116),k2_tarski(B_117,C_118),k1_tarski(D_119)) = k2_tarski(k3_mcart_1(A_116,B_117,D_119),k3_mcart_1(A_116,C_118,D_119)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_508,plain,(
    ! [A_116,C_118,D_119] : k3_zfmisc_1(k1_tarski(A_116),k2_tarski(C_118,C_118),k1_tarski(D_119)) = k1_tarski(k3_mcart_1(A_116,C_118,D_119)) ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_6])).

tff(c_532,plain,(
    ! [A_120,C_121,D_122] : k3_zfmisc_1(k1_tarski(A_120),k1_tarski(C_121),k1_tarski(D_122)) = k1_tarski(k3_mcart_1(A_120,C_121,D_122)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_508])).

tff(c_26,plain,(
    ! [A_19,B_20,C_21] :
      ( ~ r1_tarski(A_19,k3_zfmisc_1(B_20,C_21,A_19))
      | k1_xboole_0 = A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_538,plain,(
    ! [D_122,A_120,C_121] :
      ( ~ r1_tarski(k1_tarski(D_122),k1_tarski(k3_mcart_1(A_120,C_121,D_122)))
      | k1_tarski(D_122) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_532,c_26])).

tff(c_732,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_704,c_538])).

tff(c_736,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_732])).

tff(c_780,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_4',A_4)
      | k3_xboole_0(A_4,k1_xboole_0) != k1_tarski('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_736,c_8])).

tff(c_812,plain,(
    ! [A_4] : r2_hidden('#skF_4',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_736,c_2,c_780])).

tff(c_786,plain,(
    ! [A_8] :
      ( ~ r2_hidden('#skF_4',A_8)
      | k4_xboole_0(A_8,k1_xboole_0) != A_8 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_736,c_16])).

tff(c_815,plain,(
    ! [A_8] : ~ r2_hidden('#skF_4',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_786])).

tff(c_822,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_812,c_815])).

tff(c_823,plain,(
    k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_450])).

tff(c_998,plain,(
    ! [A_211,B_212,C_213,D_214] :
      ( k3_mcart_1(k5_mcart_1(A_211,B_212,C_213,D_214),k6_mcart_1(A_211,B_212,C_213,D_214),k7_mcart_1(A_211,B_212,C_213,D_214)) = D_214
      | ~ m1_subset_1(D_214,k3_zfmisc_1(A_211,B_212,C_213))
      | k1_xboole_0 = C_213
      | k1_xboole_0 = B_212
      | k1_xboole_0 = A_211 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1046,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4',k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | ~ m1_subset_1('#skF_4',k3_zfmisc_1('#skF_1','#skF_2','#skF_3'))
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_823,c_998])).

tff(c_1054,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4',k2_mcart_1('#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_906,c_1046])).

tff(c_1055,plain,(
    k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4',k2_mcart_1('#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_1054])).

tff(c_830,plain,(
    ! [A_167,B_168,C_169,D_170] : k3_zfmisc_1(k1_tarski(A_167),k2_tarski(B_168,C_169),k1_tarski(D_170)) = k2_tarski(k3_mcart_1(A_167,B_168,D_170),k3_mcart_1(A_167,C_169,D_170)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_852,plain,(
    ! [A_167,C_169,D_170] : k3_zfmisc_1(k1_tarski(A_167),k2_tarski(C_169,C_169),k1_tarski(D_170)) = k1_tarski(k3_mcart_1(A_167,C_169,D_170)) ),
    inference(superposition,[status(thm),theory(equality)],[c_830,c_6])).

tff(c_876,plain,(
    ! [A_171,C_172,D_173] : k3_zfmisc_1(k1_tarski(A_171),k1_tarski(C_172),k1_tarski(D_173)) = k1_tarski(k3_mcart_1(A_171,C_172,D_173)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_852])).

tff(c_24,plain,(
    ! [A_19,C_21,B_20] :
      ( ~ r1_tarski(A_19,k3_zfmisc_1(C_21,A_19,B_20))
      | k1_xboole_0 = A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_888,plain,(
    ! [C_172,A_171,D_173] :
      ( ~ r1_tarski(k1_tarski(C_172),k1_tarski(k3_mcart_1(A_171,C_172,D_173)))
      | k1_tarski(C_172) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_876,c_24])).

tff(c_1080,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1055,c_888])).

tff(c_1093,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1080])).

tff(c_1137,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_4',A_4)
      | k3_xboole_0(A_4,k1_xboole_0) != k1_tarski('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1093,c_8])).

tff(c_1169,plain,(
    ! [A_4] : r2_hidden('#skF_4',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1093,c_2,c_1137])).

tff(c_1143,plain,(
    ! [A_8] :
      ( ~ r2_hidden('#skF_4',A_8)
      | k4_xboole_0(A_8,k1_xboole_0) != A_8 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1093,c_16])).

tff(c_1172,plain,(
    ! [A_8] : ~ r2_hidden('#skF_4',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1143])).

tff(c_1180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1169,c_1172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:41:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.21/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.50  
% 3.21/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.50  %$ r2_hidden > r1_tarski > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.21/1.50  
% 3.21/1.50  %Foreground sorts:
% 3.21/1.50  
% 3.21/1.50  
% 3.21/1.50  %Background operators:
% 3.21/1.50  
% 3.21/1.50  
% 3.21/1.50  %Foreground operators:
% 3.21/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.21/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.21/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.21/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.21/1.50  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.21/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.21/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.21/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.21/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.21/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.21/1.50  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 3.21/1.50  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.21/1.50  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 3.21/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.50  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.21/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.21/1.50  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 3.21/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.50  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.21/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.21/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.21/1.50  
% 3.35/1.52  tff(f_41, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.35/1.52  tff(f_120, negated_conjecture, ~(![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ((~(D = k5_mcart_1(A, B, C, D)) & ~(D = k6_mcart_1(A, B, C, D))) & ~(D = k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_mcart_1)).
% 3.35/1.52  tff(f_96, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 3.35/1.52  tff(f_64, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 3.35/1.52  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.35/1.52  tff(f_48, axiom, (![A, B, C, D]: (k3_zfmisc_1(k1_tarski(A), k2_tarski(B, C), k1_tarski(D)) = k2_tarski(k3_mcart_1(A, B, D), k3_mcart_1(A, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_mcart_1)).
% 3.35/1.52  tff(f_76, axiom, (![A, B, C]: (~((~r1_tarski(A, k3_zfmisc_1(A, B, C)) & ~r1_tarski(A, k3_zfmisc_1(B, C, A))) & ~r1_tarski(A, k3_zfmisc_1(C, A, B))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_mcart_1)).
% 3.35/1.52  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.35/1.52  tff(f_35, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 3.35/1.52  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.35/1.52  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.35/1.52  tff(c_12, plain, (![B_7]: (r1_tarski(k1_tarski(B_7), k1_tarski(B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.35/1.52  tff(c_44, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.35/1.52  tff(c_42, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.35/1.52  tff(c_40, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.35/1.52  tff(c_38, plain, (m1_subset_1('#skF_4', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.35/1.52  tff(c_894, plain, (![A_174, B_175, C_176, D_177]: (k7_mcart_1(A_174, B_175, C_176, D_177)=k2_mcart_1(D_177) | ~m1_subset_1(D_177, k3_zfmisc_1(A_174, B_175, C_176)) | k1_xboole_0=C_176 | k1_xboole_0=B_175 | k1_xboole_0=A_174)), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.35/1.52  tff(c_903, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_mcart_1('#skF_4') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_38, c_894])).
% 3.35/1.52  tff(c_906, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_mcart_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_903])).
% 3.35/1.52  tff(c_152, plain, (![A_54, B_55, C_56, D_57]: (k7_mcart_1(A_54, B_55, C_56, D_57)=k2_mcart_1(D_57) | ~m1_subset_1(D_57, k3_zfmisc_1(A_54, B_55, C_56)) | k1_xboole_0=C_56 | k1_xboole_0=B_55 | k1_xboole_0=A_54)), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.35/1.52  tff(c_158, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_mcart_1('#skF_4') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_38, c_152])).
% 3.35/1.52  tff(c_161, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_mcart_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_158])).
% 3.35/1.52  tff(c_36, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_4' | k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_4' | k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.35/1.52  tff(c_72, plain, (k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(splitLeft, [status(thm)], [c_36])).
% 3.35/1.52  tff(c_273, plain, (![A_94, B_95, C_96, D_97]: (k3_mcart_1(k5_mcart_1(A_94, B_95, C_96, D_97), k6_mcart_1(A_94, B_95, C_96, D_97), k7_mcart_1(A_94, B_95, C_96, D_97))=D_97 | ~m1_subset_1(D_97, k3_zfmisc_1(A_94, B_95, C_96)) | k1_xboole_0=C_96 | k1_xboole_0=B_95 | k1_xboole_0=A_94)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.35/1.52  tff(c_321, plain, (k3_mcart_1('#skF_4', k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_4' | ~m1_subset_1('#skF_4', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')) | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_72, c_273])).
% 3.35/1.52  tff(c_329, plain, (k3_mcart_1('#skF_4', k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_mcart_1('#skF_4'))='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_161, c_321])).
% 3.35/1.52  tff(c_330, plain, (k3_mcart_1('#skF_4', k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_mcart_1('#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_329])).
% 3.35/1.52  tff(c_6, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.35/1.52  tff(c_106, plain, (![A_50, B_51, C_52, D_53]: (k3_zfmisc_1(k1_tarski(A_50), k2_tarski(B_51, C_52), k1_tarski(D_53))=k2_tarski(k3_mcart_1(A_50, B_51, D_53), k3_mcart_1(A_50, C_52, D_53)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.35/1.52  tff(c_144, plain, (![A_50, B_51, D_53]: (k3_zfmisc_1(k1_tarski(A_50), k2_tarski(B_51, B_51), k1_tarski(D_53))=k1_tarski(k3_mcart_1(A_50, B_51, D_53)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_106])).
% 3.35/1.52  tff(c_166, plain, (![A_58, B_59, D_60]: (k3_zfmisc_1(k1_tarski(A_58), k1_tarski(B_59), k1_tarski(D_60))=k1_tarski(k3_mcart_1(A_58, B_59, D_60)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_144])).
% 3.35/1.52  tff(c_28, plain, (![A_19, B_20, C_21]: (~r1_tarski(A_19, k3_zfmisc_1(A_19, B_20, C_21)) | k1_xboole_0=A_19)), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.35/1.52  tff(c_175, plain, (![A_58, B_59, D_60]: (~r1_tarski(k1_tarski(A_58), k1_tarski(k3_mcart_1(A_58, B_59, D_60))) | k1_tarski(A_58)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_166, c_28])).
% 3.35/1.52  tff(c_358, plain, (~r1_tarski(k1_tarski('#skF_4'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_330, c_175])).
% 3.35/1.52  tff(c_362, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_358])).
% 3.35/1.52  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.35/1.52  tff(c_8, plain, (![B_5, A_4]: (r2_hidden(B_5, A_4) | k3_xboole_0(A_4, k1_tarski(B_5))!=k1_tarski(B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.35/1.52  tff(c_409, plain, (![A_4]: (r2_hidden('#skF_4', A_4) | k3_xboole_0(A_4, k1_xboole_0)!=k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_362, c_8])).
% 3.35/1.52  tff(c_439, plain, (![A_4]: (r2_hidden('#skF_4', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_362, c_2, c_409])).
% 3.35/1.52  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.35/1.52  tff(c_16, plain, (![B_9, A_8]: (~r2_hidden(B_9, A_8) | k4_xboole_0(A_8, k1_tarski(B_9))!=A_8)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.35/1.52  tff(c_412, plain, (![A_8]: (~r2_hidden('#skF_4', A_8) | k4_xboole_0(A_8, k1_xboole_0)!=A_8)), inference(superposition, [status(thm), theory('equality')], [c_362, c_16])).
% 3.35/1.52  tff(c_441, plain, (![A_8]: (~r2_hidden('#skF_4', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_412])).
% 3.35/1.52  tff(c_449, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_439, c_441])).
% 3.35/1.52  tff(c_450, plain, (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_4' | k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_36])).
% 3.35/1.52  tff(c_480, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(splitLeft, [status(thm)], [c_450])).
% 3.35/1.52  tff(c_653, plain, (![A_160, B_161, C_162, D_163]: (k3_mcart_1(k5_mcart_1(A_160, B_161, C_162, D_163), k6_mcart_1(A_160, B_161, C_162, D_163), k7_mcart_1(A_160, B_161, C_162, D_163))=D_163 | ~m1_subset_1(D_163, k3_zfmisc_1(A_160, B_161, C_162)) | k1_xboole_0=C_162 | k1_xboole_0=B_161 | k1_xboole_0=A_160)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.35/1.52  tff(c_698, plain, (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4')='#skF_4' | ~m1_subset_1('#skF_4', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')) | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_480, c_653])).
% 3.35/1.52  tff(c_703, plain, (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4')='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_698])).
% 3.35/1.52  tff(c_704, plain, (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_703])).
% 3.35/1.52  tff(c_486, plain, (![A_116, B_117, C_118, D_119]: (k3_zfmisc_1(k1_tarski(A_116), k2_tarski(B_117, C_118), k1_tarski(D_119))=k2_tarski(k3_mcart_1(A_116, B_117, D_119), k3_mcart_1(A_116, C_118, D_119)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.35/1.52  tff(c_508, plain, (![A_116, C_118, D_119]: (k3_zfmisc_1(k1_tarski(A_116), k2_tarski(C_118, C_118), k1_tarski(D_119))=k1_tarski(k3_mcart_1(A_116, C_118, D_119)))), inference(superposition, [status(thm), theory('equality')], [c_486, c_6])).
% 3.35/1.52  tff(c_532, plain, (![A_120, C_121, D_122]: (k3_zfmisc_1(k1_tarski(A_120), k1_tarski(C_121), k1_tarski(D_122))=k1_tarski(k3_mcart_1(A_120, C_121, D_122)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_508])).
% 3.35/1.52  tff(c_26, plain, (![A_19, B_20, C_21]: (~r1_tarski(A_19, k3_zfmisc_1(B_20, C_21, A_19)) | k1_xboole_0=A_19)), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.35/1.52  tff(c_538, plain, (![D_122, A_120, C_121]: (~r1_tarski(k1_tarski(D_122), k1_tarski(k3_mcart_1(A_120, C_121, D_122))) | k1_tarski(D_122)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_532, c_26])).
% 3.35/1.52  tff(c_732, plain, (~r1_tarski(k1_tarski('#skF_4'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_704, c_538])).
% 3.35/1.52  tff(c_736, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_732])).
% 3.35/1.52  tff(c_780, plain, (![A_4]: (r2_hidden('#skF_4', A_4) | k3_xboole_0(A_4, k1_xboole_0)!=k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_736, c_8])).
% 3.35/1.52  tff(c_812, plain, (![A_4]: (r2_hidden('#skF_4', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_736, c_2, c_780])).
% 3.35/1.52  tff(c_786, plain, (![A_8]: (~r2_hidden('#skF_4', A_8) | k4_xboole_0(A_8, k1_xboole_0)!=A_8)), inference(superposition, [status(thm), theory('equality')], [c_736, c_16])).
% 3.35/1.52  tff(c_815, plain, (![A_8]: (~r2_hidden('#skF_4', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_786])).
% 3.35/1.52  tff(c_822, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_812, c_815])).
% 3.35/1.52  tff(c_823, plain, (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_450])).
% 3.35/1.52  tff(c_998, plain, (![A_211, B_212, C_213, D_214]: (k3_mcart_1(k5_mcart_1(A_211, B_212, C_213, D_214), k6_mcart_1(A_211, B_212, C_213, D_214), k7_mcart_1(A_211, B_212, C_213, D_214))=D_214 | ~m1_subset_1(D_214, k3_zfmisc_1(A_211, B_212, C_213)) | k1_xboole_0=C_213 | k1_xboole_0=B_212 | k1_xboole_0=A_211)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.35/1.52  tff(c_1046, plain, (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_4' | ~m1_subset_1('#skF_4', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')) | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_823, c_998])).
% 3.35/1.52  tff(c_1054, plain, (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', k2_mcart_1('#skF_4'))='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_906, c_1046])).
% 3.35/1.52  tff(c_1055, plain, (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', k2_mcart_1('#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_1054])).
% 3.35/1.52  tff(c_830, plain, (![A_167, B_168, C_169, D_170]: (k3_zfmisc_1(k1_tarski(A_167), k2_tarski(B_168, C_169), k1_tarski(D_170))=k2_tarski(k3_mcart_1(A_167, B_168, D_170), k3_mcart_1(A_167, C_169, D_170)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.35/1.52  tff(c_852, plain, (![A_167, C_169, D_170]: (k3_zfmisc_1(k1_tarski(A_167), k2_tarski(C_169, C_169), k1_tarski(D_170))=k1_tarski(k3_mcart_1(A_167, C_169, D_170)))), inference(superposition, [status(thm), theory('equality')], [c_830, c_6])).
% 3.35/1.52  tff(c_876, plain, (![A_171, C_172, D_173]: (k3_zfmisc_1(k1_tarski(A_171), k1_tarski(C_172), k1_tarski(D_173))=k1_tarski(k3_mcart_1(A_171, C_172, D_173)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_852])).
% 3.35/1.52  tff(c_24, plain, (![A_19, C_21, B_20]: (~r1_tarski(A_19, k3_zfmisc_1(C_21, A_19, B_20)) | k1_xboole_0=A_19)), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.35/1.52  tff(c_888, plain, (![C_172, A_171, D_173]: (~r1_tarski(k1_tarski(C_172), k1_tarski(k3_mcart_1(A_171, C_172, D_173))) | k1_tarski(C_172)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_876, c_24])).
% 3.35/1.52  tff(c_1080, plain, (~r1_tarski(k1_tarski('#skF_4'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1055, c_888])).
% 3.35/1.52  tff(c_1093, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1080])).
% 3.35/1.52  tff(c_1137, plain, (![A_4]: (r2_hidden('#skF_4', A_4) | k3_xboole_0(A_4, k1_xboole_0)!=k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1093, c_8])).
% 3.35/1.52  tff(c_1169, plain, (![A_4]: (r2_hidden('#skF_4', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_1093, c_2, c_1137])).
% 3.35/1.52  tff(c_1143, plain, (![A_8]: (~r2_hidden('#skF_4', A_8) | k4_xboole_0(A_8, k1_xboole_0)!=A_8)), inference(superposition, [status(thm), theory('equality')], [c_1093, c_16])).
% 3.35/1.52  tff(c_1172, plain, (![A_8]: (~r2_hidden('#skF_4', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1143])).
% 3.35/1.52  tff(c_1180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1169, c_1172])).
% 3.35/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.52  
% 3.35/1.52  Inference rules
% 3.35/1.52  ----------------------
% 3.35/1.52  #Ref     : 0
% 3.35/1.52  #Sup     : 296
% 3.35/1.52  #Fact    : 0
% 3.35/1.52  #Define  : 0
% 3.35/1.52  #Split   : 2
% 3.35/1.52  #Chain   : 0
% 3.35/1.52  #Close   : 0
% 3.35/1.52  
% 3.35/1.52  Ordering : KBO
% 3.35/1.52  
% 3.35/1.52  Simplification rules
% 3.35/1.52  ----------------------
% 3.35/1.52  #Subsume      : 21
% 3.35/1.52  #Demod        : 105
% 3.35/1.52  #Tautology    : 120
% 3.35/1.52  #SimpNegUnit  : 14
% 3.35/1.52  #BackRed      : 1
% 3.35/1.52  
% 3.35/1.52  #Partial instantiations: 0
% 3.35/1.52  #Strategies tried      : 1
% 3.35/1.52  
% 3.35/1.52  Timing (in seconds)
% 3.35/1.52  ----------------------
% 3.35/1.52  Preprocessing        : 0.32
% 3.35/1.52  Parsing              : 0.17
% 3.35/1.52  CNF conversion       : 0.02
% 3.35/1.52  Main loop            : 0.44
% 3.35/1.52  Inferencing          : 0.18
% 3.35/1.52  Reduction            : 0.14
% 3.35/1.52  Demodulation         : 0.10
% 3.35/1.52  BG Simplification    : 0.03
% 3.35/1.52  Subsumption          : 0.07
% 3.35/1.52  Abstraction          : 0.03
% 3.35/1.52  MUC search           : 0.00
% 3.35/1.52  Cooper               : 0.00
% 3.35/1.52  Total                : 0.80
% 3.35/1.52  Index Insertion      : 0.00
% 3.35/1.52  Index Deletion       : 0.00
% 3.35/1.52  Index Matching       : 0.00
% 3.35/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
