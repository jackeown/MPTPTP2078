%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:44 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 139 expanded)
%              Number of leaves         :   28 (  63 expanded)
%              Depth                    :    8
%              Number of atoms          :  134 ( 357 expanded)
%              Number of equality atoms :  102 ( 286 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_118,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & ~ ! [D] :
                ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
               => ( D != k5_mcart_1(A,B,C,D)
                  & D != k6_mcart_1(A,B,C,D)
                  & D != k7_mcart_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_mcart_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_42,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B,C] : k3_zfmisc_1(k1_tarski(A),k1_tarski(B),k1_tarski(C)) = k1_tarski(k3_mcart_1(A,B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_mcart_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_tarski(A,k3_zfmisc_1(A,B,C))
          & ~ r1_tarski(A,k3_zfmisc_1(B,C,A))
          & ~ r1_tarski(A,k3_zfmisc_1(C,A,B)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_mcart_1)).

tff(c_10,plain,(
    ! [B_5] : r1_tarski(k1_tarski(B_5),k1_tarski(B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_637,plain,(
    ! [A_203,B_204,C_205,D_206] :
      ( k7_mcart_1(A_203,B_204,C_205,D_206) = k2_mcart_1(D_206)
      | ~ m1_subset_1(D_206,k3_zfmisc_1(A_203,B_204,C_205))
      | k1_xboole_0 = C_205
      | k1_xboole_0 = B_204
      | k1_xboole_0 = A_203 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_643,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_mcart_1('#skF_4')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_36,c_637])).

tff(c_647,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_mcart_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_643])).

tff(c_127,plain,(
    ! [A_55,B_56,C_57,D_58] :
      ( k7_mcart_1(A_55,B_56,C_57,D_58) = k2_mcart_1(D_58)
      | ~ m1_subset_1(D_58,k3_zfmisc_1(A_55,B_56,C_57))
      | k1_xboole_0 = C_57
      | k1_xboole_0 = B_56
      | k1_xboole_0 = A_55 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_133,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_mcart_1('#skF_4')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_36,c_127])).

tff(c_137,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_mcart_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_133])).

tff(c_34,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_4'
    | k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_4'
    | k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_60,plain,(
    k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_256,plain,(
    ! [A_99,B_100,C_101,D_102] :
      ( k3_mcart_1(k5_mcart_1(A_99,B_100,C_101,D_102),k6_mcart_1(A_99,B_100,C_101,D_102),k7_mcart_1(A_99,B_100,C_101,D_102)) = D_102
      | ~ m1_subset_1(D_102,k3_zfmisc_1(A_99,B_100,C_101))
      | k1_xboole_0 = C_101
      | k1_xboole_0 = B_100
      | k1_xboole_0 = A_99 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_283,plain,
    ( k3_mcart_1('#skF_4',k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | ~ m1_subset_1('#skF_4',k3_zfmisc_1('#skF_1','#skF_2','#skF_3'))
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_256])).

tff(c_292,plain,
    ( k3_mcart_1('#skF_4',k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_mcart_1('#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_137,c_283])).

tff(c_293,plain,(
    k3_mcart_1('#skF_4',k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_mcart_1('#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_292])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_54,plain,(
    ! [A_31,B_32] : k2_xboole_0(k1_tarski(A_31),B_32) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_58,plain,(
    ! [A_31] : k1_tarski(A_31) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_54])).

tff(c_106,plain,(
    ! [A_52,B_53,C_54] : k3_zfmisc_1(k1_tarski(A_52),k1_tarski(B_53),k1_tarski(C_54)) = k1_tarski(k3_mcart_1(A_52,B_53,C_54)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26,plain,(
    ! [A_19,B_20,C_21] :
      ( ~ r1_tarski(A_19,k3_zfmisc_1(A_19,B_20,C_21))
      | k1_xboole_0 = A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_118,plain,(
    ! [A_52,B_53,C_54] :
      ( ~ r1_tarski(k1_tarski(A_52),k1_tarski(k3_mcart_1(A_52,B_53,C_54)))
      | k1_tarski(A_52) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_26])).

tff(c_125,plain,(
    ! [A_52,B_53,C_54] : ~ r1_tarski(k1_tarski(A_52),k1_tarski(k3_mcart_1(A_52,B_53,C_54))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_118])).

tff(c_300,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_125])).

tff(c_311,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_300])).

tff(c_312,plain,
    ( k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_4'
    | k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_315,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_312])).

tff(c_511,plain,(
    ! [A_171,B_172,C_173,D_174] :
      ( k3_mcart_1(k5_mcart_1(A_171,B_172,C_173,D_174),k6_mcart_1(A_171,B_172,C_173,D_174),k7_mcart_1(A_171,B_172,C_173,D_174)) = D_174
      | ~ m1_subset_1(D_174,k3_zfmisc_1(A_171,B_172,C_173))
      | k1_xboole_0 = C_173
      | k1_xboole_0 = B_172
      | k1_xboole_0 = A_171 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_538,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k3_zfmisc_1('#skF_1','#skF_2','#skF_3'))
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_511])).

tff(c_544,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4') = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_538])).

tff(c_545,plain,(
    k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_544])).

tff(c_360,plain,(
    ! [A_121,B_122,C_123] : k3_zfmisc_1(k1_tarski(A_121),k1_tarski(B_122),k1_tarski(C_123)) = k1_tarski(k3_mcart_1(A_121,B_122,C_123)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    ! [A_19,B_20,C_21] :
      ( ~ r1_tarski(A_19,k3_zfmisc_1(B_20,C_21,A_19))
      | k1_xboole_0 = A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_366,plain,(
    ! [C_123,A_121,B_122] :
      ( ~ r1_tarski(k1_tarski(C_123),k1_tarski(k3_mcart_1(A_121,B_122,C_123)))
      | k1_tarski(C_123) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_24])).

tff(c_377,plain,(
    ! [C_123,A_121,B_122] : ~ r1_tarski(k1_tarski(C_123),k1_tarski(k3_mcart_1(A_121,B_122,C_123))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_366])).

tff(c_561,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_545,c_377])).

tff(c_566,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_561])).

tff(c_567,plain,(
    k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_312])).

tff(c_774,plain,(
    ! [A_245,B_246,C_247,D_248] :
      ( k3_mcart_1(k5_mcart_1(A_245,B_246,C_247,D_248),k6_mcart_1(A_245,B_246,C_247,D_248),k7_mcart_1(A_245,B_246,C_247,D_248)) = D_248
      | ~ m1_subset_1(D_248,k3_zfmisc_1(A_245,B_246,C_247))
      | k1_xboole_0 = C_247
      | k1_xboole_0 = B_246
      | k1_xboole_0 = A_245 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_807,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4',k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | ~ m1_subset_1('#skF_4',k3_zfmisc_1('#skF_1','#skF_2','#skF_3'))
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_567,c_774])).

tff(c_818,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4',k2_mcart_1('#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_647,c_807])).

tff(c_819,plain,(
    k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4',k2_mcart_1('#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_818])).

tff(c_613,plain,(
    ! [A_191,B_192,C_193] : k3_zfmisc_1(k1_tarski(A_191),k1_tarski(B_192),k1_tarski(C_193)) = k1_tarski(k3_mcart_1(A_191,B_192,C_193)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_22,plain,(
    ! [A_19,C_21,B_20] :
      ( ~ r1_tarski(A_19,k3_zfmisc_1(C_21,A_19,B_20))
      | k1_xboole_0 = A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_619,plain,(
    ! [B_192,A_191,C_193] :
      ( ~ r1_tarski(k1_tarski(B_192),k1_tarski(k3_mcart_1(A_191,B_192,C_193)))
      | k1_tarski(B_192) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_613,c_22])).

tff(c_630,plain,(
    ! [B_192,A_191,C_193] : ~ r1_tarski(k1_tarski(B_192),k1_tarski(k3_mcart_1(A_191,B_192,C_193))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_619])).

tff(c_835,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_819,c_630])).

tff(c_840,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_835])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:30:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.35/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.65  
% 3.35/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.65  %$ r1_tarski > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.35/1.65  
% 3.35/1.65  %Foreground sorts:
% 3.35/1.65  
% 3.35/1.65  
% 3.35/1.65  %Background operators:
% 3.35/1.65  
% 3.35/1.65  
% 3.35/1.65  %Foreground operators:
% 3.35/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.35/1.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.35/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.35/1.65  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.35/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.35/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.35/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.35/1.65  tff('#skF_1', type, '#skF_1': $i).
% 3.35/1.65  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 3.35/1.65  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.35/1.65  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 3.35/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.35/1.65  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.35/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.35/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.35/1.65  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 3.35/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.35/1.65  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.35/1.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.35/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.35/1.65  
% 3.35/1.67  tff(f_39, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 3.35/1.67  tff(f_118, negated_conjecture, ~(![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ((~(D = k5_mcart_1(A, B, C, D)) & ~(D = k6_mcart_1(A, B, C, D))) & ~(D = k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_mcart_1)).
% 3.35/1.67  tff(f_94, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 3.35/1.67  tff(f_62, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 3.35/1.67  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.35/1.67  tff(f_42, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.35/1.67  tff(f_46, axiom, (![A, B, C]: (k3_zfmisc_1(k1_tarski(A), k1_tarski(B), k1_tarski(C)) = k1_tarski(k3_mcart_1(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_mcart_1)).
% 3.35/1.67  tff(f_74, axiom, (![A, B, C]: (~((~r1_tarski(A, k3_zfmisc_1(A, B, C)) & ~r1_tarski(A, k3_zfmisc_1(B, C, A))) & ~r1_tarski(A, k3_zfmisc_1(C, A, B))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_mcart_1)).
% 3.35/1.67  tff(c_10, plain, (![B_5]: (r1_tarski(k1_tarski(B_5), k1_tarski(B_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.35/1.67  tff(c_42, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.35/1.67  tff(c_40, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.35/1.67  tff(c_38, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.35/1.67  tff(c_36, plain, (m1_subset_1('#skF_4', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.35/1.67  tff(c_637, plain, (![A_203, B_204, C_205, D_206]: (k7_mcart_1(A_203, B_204, C_205, D_206)=k2_mcart_1(D_206) | ~m1_subset_1(D_206, k3_zfmisc_1(A_203, B_204, C_205)) | k1_xboole_0=C_205 | k1_xboole_0=B_204 | k1_xboole_0=A_203)), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.35/1.67  tff(c_643, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_mcart_1('#skF_4') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_36, c_637])).
% 3.35/1.67  tff(c_647, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_mcart_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_643])).
% 3.35/1.67  tff(c_127, plain, (![A_55, B_56, C_57, D_58]: (k7_mcart_1(A_55, B_56, C_57, D_58)=k2_mcart_1(D_58) | ~m1_subset_1(D_58, k3_zfmisc_1(A_55, B_56, C_57)) | k1_xboole_0=C_57 | k1_xboole_0=B_56 | k1_xboole_0=A_55)), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.35/1.67  tff(c_133, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_mcart_1('#skF_4') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_36, c_127])).
% 3.35/1.67  tff(c_137, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_mcart_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_133])).
% 3.35/1.67  tff(c_34, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_4' | k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_4' | k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.35/1.67  tff(c_60, plain, (k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(splitLeft, [status(thm)], [c_34])).
% 3.35/1.67  tff(c_256, plain, (![A_99, B_100, C_101, D_102]: (k3_mcart_1(k5_mcart_1(A_99, B_100, C_101, D_102), k6_mcart_1(A_99, B_100, C_101, D_102), k7_mcart_1(A_99, B_100, C_101, D_102))=D_102 | ~m1_subset_1(D_102, k3_zfmisc_1(A_99, B_100, C_101)) | k1_xboole_0=C_101 | k1_xboole_0=B_100 | k1_xboole_0=A_99)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.35/1.67  tff(c_283, plain, (k3_mcart_1('#skF_4', k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_4' | ~m1_subset_1('#skF_4', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')) | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_60, c_256])).
% 3.35/1.67  tff(c_292, plain, (k3_mcart_1('#skF_4', k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_mcart_1('#skF_4'))='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_137, c_283])).
% 3.35/1.67  tff(c_293, plain, (k3_mcart_1('#skF_4', k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_mcart_1('#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_292])).
% 3.35/1.67  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.35/1.67  tff(c_54, plain, (![A_31, B_32]: (k2_xboole_0(k1_tarski(A_31), B_32)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.35/1.67  tff(c_58, plain, (![A_31]: (k1_tarski(A_31)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_54])).
% 3.35/1.67  tff(c_106, plain, (![A_52, B_53, C_54]: (k3_zfmisc_1(k1_tarski(A_52), k1_tarski(B_53), k1_tarski(C_54))=k1_tarski(k3_mcart_1(A_52, B_53, C_54)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.35/1.67  tff(c_26, plain, (![A_19, B_20, C_21]: (~r1_tarski(A_19, k3_zfmisc_1(A_19, B_20, C_21)) | k1_xboole_0=A_19)), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.35/1.67  tff(c_118, plain, (![A_52, B_53, C_54]: (~r1_tarski(k1_tarski(A_52), k1_tarski(k3_mcart_1(A_52, B_53, C_54))) | k1_tarski(A_52)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_106, c_26])).
% 3.35/1.67  tff(c_125, plain, (![A_52, B_53, C_54]: (~r1_tarski(k1_tarski(A_52), k1_tarski(k3_mcart_1(A_52, B_53, C_54))))), inference(negUnitSimplification, [status(thm)], [c_58, c_118])).
% 3.35/1.67  tff(c_300, plain, (~r1_tarski(k1_tarski('#skF_4'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_293, c_125])).
% 3.35/1.67  tff(c_311, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_300])).
% 3.35/1.67  tff(c_312, plain, (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_4' | k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_34])).
% 3.35/1.67  tff(c_315, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(splitLeft, [status(thm)], [c_312])).
% 3.35/1.67  tff(c_511, plain, (![A_171, B_172, C_173, D_174]: (k3_mcart_1(k5_mcart_1(A_171, B_172, C_173, D_174), k6_mcart_1(A_171, B_172, C_173, D_174), k7_mcart_1(A_171, B_172, C_173, D_174))=D_174 | ~m1_subset_1(D_174, k3_zfmisc_1(A_171, B_172, C_173)) | k1_xboole_0=C_173 | k1_xboole_0=B_172 | k1_xboole_0=A_171)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.35/1.67  tff(c_538, plain, (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4')='#skF_4' | ~m1_subset_1('#skF_4', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')) | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_315, c_511])).
% 3.35/1.67  tff(c_544, plain, (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4')='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_538])).
% 3.35/1.67  tff(c_545, plain, (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_544])).
% 3.35/1.67  tff(c_360, plain, (![A_121, B_122, C_123]: (k3_zfmisc_1(k1_tarski(A_121), k1_tarski(B_122), k1_tarski(C_123))=k1_tarski(k3_mcart_1(A_121, B_122, C_123)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.35/1.67  tff(c_24, plain, (![A_19, B_20, C_21]: (~r1_tarski(A_19, k3_zfmisc_1(B_20, C_21, A_19)) | k1_xboole_0=A_19)), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.35/1.67  tff(c_366, plain, (![C_123, A_121, B_122]: (~r1_tarski(k1_tarski(C_123), k1_tarski(k3_mcart_1(A_121, B_122, C_123))) | k1_tarski(C_123)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_360, c_24])).
% 3.35/1.67  tff(c_377, plain, (![C_123, A_121, B_122]: (~r1_tarski(k1_tarski(C_123), k1_tarski(k3_mcart_1(A_121, B_122, C_123))))), inference(negUnitSimplification, [status(thm)], [c_58, c_366])).
% 3.35/1.67  tff(c_561, plain, (~r1_tarski(k1_tarski('#skF_4'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_545, c_377])).
% 3.35/1.67  tff(c_566, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_561])).
% 3.35/1.67  tff(c_567, plain, (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_312])).
% 3.35/1.67  tff(c_774, plain, (![A_245, B_246, C_247, D_248]: (k3_mcart_1(k5_mcart_1(A_245, B_246, C_247, D_248), k6_mcart_1(A_245, B_246, C_247, D_248), k7_mcart_1(A_245, B_246, C_247, D_248))=D_248 | ~m1_subset_1(D_248, k3_zfmisc_1(A_245, B_246, C_247)) | k1_xboole_0=C_247 | k1_xboole_0=B_246 | k1_xboole_0=A_245)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.35/1.67  tff(c_807, plain, (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_4' | ~m1_subset_1('#skF_4', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')) | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_567, c_774])).
% 3.35/1.67  tff(c_818, plain, (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', k2_mcart_1('#skF_4'))='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_647, c_807])).
% 3.35/1.67  tff(c_819, plain, (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', k2_mcart_1('#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_818])).
% 3.35/1.67  tff(c_613, plain, (![A_191, B_192, C_193]: (k3_zfmisc_1(k1_tarski(A_191), k1_tarski(B_192), k1_tarski(C_193))=k1_tarski(k3_mcart_1(A_191, B_192, C_193)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.35/1.67  tff(c_22, plain, (![A_19, C_21, B_20]: (~r1_tarski(A_19, k3_zfmisc_1(C_21, A_19, B_20)) | k1_xboole_0=A_19)), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.35/1.67  tff(c_619, plain, (![B_192, A_191, C_193]: (~r1_tarski(k1_tarski(B_192), k1_tarski(k3_mcart_1(A_191, B_192, C_193))) | k1_tarski(B_192)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_613, c_22])).
% 3.35/1.67  tff(c_630, plain, (![B_192, A_191, C_193]: (~r1_tarski(k1_tarski(B_192), k1_tarski(k3_mcart_1(A_191, B_192, C_193))))), inference(negUnitSimplification, [status(thm)], [c_58, c_619])).
% 3.35/1.67  tff(c_835, plain, (~r1_tarski(k1_tarski('#skF_4'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_819, c_630])).
% 3.35/1.67  tff(c_840, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_835])).
% 3.35/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.67  
% 3.35/1.67  Inference rules
% 3.35/1.67  ----------------------
% 3.35/1.67  #Ref     : 0
% 3.35/1.67  #Sup     : 192
% 3.35/1.67  #Fact    : 0
% 3.35/1.67  #Define  : 0
% 3.35/1.67  #Split   : 2
% 3.35/1.67  #Chain   : 0
% 3.35/1.67  #Close   : 0
% 3.35/1.67  
% 3.35/1.67  Ordering : KBO
% 3.35/1.67  
% 3.35/1.67  Simplification rules
% 3.35/1.67  ----------------------
% 3.35/1.67  #Subsume      : 21
% 3.35/1.67  #Demod        : 62
% 3.35/1.67  #Tautology    : 73
% 3.35/1.67  #SimpNegUnit  : 45
% 3.35/1.67  #BackRed      : 1
% 3.35/1.67  
% 3.35/1.67  #Partial instantiations: 0
% 3.35/1.67  #Strategies tried      : 1
% 3.35/1.67  
% 3.35/1.67  Timing (in seconds)
% 3.35/1.67  ----------------------
% 3.35/1.68  Preprocessing        : 0.39
% 3.35/1.68  Parsing              : 0.21
% 3.35/1.68  CNF conversion       : 0.02
% 3.35/1.68  Main loop            : 0.44
% 3.35/1.68  Inferencing          : 0.18
% 3.35/1.68  Reduction            : 0.13
% 3.35/1.68  Demodulation         : 0.08
% 3.35/1.68  BG Simplification    : 0.03
% 3.35/1.68  Subsumption          : 0.07
% 3.35/1.68  Abstraction          : 0.03
% 3.35/1.68  MUC search           : 0.00
% 3.35/1.68  Cooper               : 0.00
% 3.35/1.68  Total                : 0.87
% 3.35/1.68  Index Insertion      : 0.00
% 3.35/1.68  Index Deletion       : 0.00
% 3.35/1.68  Index Matching       : 0.00
% 3.35/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
