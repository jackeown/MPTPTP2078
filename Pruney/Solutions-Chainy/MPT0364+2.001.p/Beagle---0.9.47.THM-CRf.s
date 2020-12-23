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
% DateTime   : Thu Dec  3 09:56:39 EST 2020

% Result     : Theorem 15.08s
% Output     : CNFRefutation 15.08s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 507 expanded)
%              Number of leaves         :   40 ( 185 expanded)
%              Depth                    :   19
%              Number of atoms          :  220 ( 702 expanded)
%              Number of equality atoms :  110 ( 341 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_108,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,k3_subset_1(A,C))
            <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_63,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_98,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(c_341,plain,(
    ! [A_71,B_72] :
      ( r1_xboole_0(A_71,B_72)
      | k3_xboole_0(A_71,B_72) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_74,plain,
    ( r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5'))
    | r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_135,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_68,plain,
    ( ~ r1_tarski('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_269,plain,(
    ~ r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_68])).

tff(c_348,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_341,c_269])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2243,plain,(
    ! [A_147,B_148] :
      ( k4_xboole_0(A_147,B_148) = k3_subset_1(A_147,B_148)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(A_147)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2259,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_2243])).

tff(c_34,plain,(
    ! [A_27] : r1_xboole_0(A_27,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_170,plain,(
    ! [A_57,B_58] :
      ( k3_xboole_0(A_57,B_58) = k1_xboole_0
      | ~ r1_xboole_0(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_178,plain,(
    ! [A_27] : k3_xboole_0(A_27,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_170])).

tff(c_38,plain,(
    ! [A_31,B_32] : r1_xboole_0(k4_xboole_0(A_31,B_32),B_32) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_272,plain,(
    ! [A_63,B_64] : k3_xboole_0(k4_xboole_0(A_63,B_64),B_64) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_170])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_280,plain,(
    ! [B_64,A_63] : k3_xboole_0(B_64,k4_xboole_0(A_63,B_64)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_4])).

tff(c_210,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(A_60,B_61) = A_60
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_217,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_135,c_210])).

tff(c_1204,plain,(
    ! [A_115,B_116,C_117] : k3_xboole_0(k3_xboole_0(A_115,B_116),C_117) = k3_xboole_0(A_115,k3_xboole_0(B_116,C_117)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1922,plain,(
    ! [C_140] : k3_xboole_0('#skF_4',k3_xboole_0('#skF_5',C_140)) = k3_xboole_0('#skF_4',C_140) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_1204])).

tff(c_1956,plain,(
    ! [A_63] : k3_xboole_0('#skF_4',k4_xboole_0(A_63,'#skF_5')) = k3_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_1922])).

tff(c_1980,plain,(
    ! [A_63] : k3_xboole_0('#skF_4',k4_xboole_0(A_63,'#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_1956])).

tff(c_2297,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2259,c_1980])).

tff(c_2334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_348,c_2297])).

tff(c_2336,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_28,plain,(
    ! [A_21] : k4_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2371,plain,(
    ! [A_157,B_158] :
      ( k3_xboole_0(A_157,B_158) = k1_xboole_0
      | ~ r1_xboole_0(A_157,B_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2383,plain,(
    ! [A_27] : k3_xboole_0(A_27,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_2371])).

tff(c_2778,plain,(
    ! [A_201,B_202] : k5_xboole_0(A_201,k3_xboole_0(A_201,B_202)) = k4_xboole_0(A_201,B_202) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2808,plain,(
    ! [A_27] : k5_xboole_0(A_27,k1_xboole_0) = k4_xboole_0(A_27,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2383,c_2778])).

tff(c_2820,plain,(
    ! [A_27] : k5_xboole_0(A_27,k1_xboole_0) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2808])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_xboole_0(A_5,B_6)
      | k3_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2578,plain,(
    ! [A_179,B_180,C_181] :
      ( r1_tarski(A_179,B_180)
      | ~ r1_tarski(A_179,k4_xboole_0(B_180,C_181)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2586,plain,(
    ! [B_180,C_181] : r1_tarski(k4_xboole_0(B_180,C_181),B_180) ),
    inference(resolution,[status(thm)],[c_16,c_2578])).

tff(c_2727,plain,(
    ! [A_199,B_200] : k4_xboole_0(A_199,k4_xboole_0(A_199,B_200)) = k3_xboole_0(A_199,B_200) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2774,plain,(
    ! [A_21] : k4_xboole_0(A_21,A_21) = k3_xboole_0(A_21,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2727])).

tff(c_2821,plain,(
    ! [A_203] : k4_xboole_0(A_203,A_203) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2383,c_2774])).

tff(c_2874,plain,(
    ! [A_204] : r1_tarski(k1_xboole_0,A_204) ),
    inference(superposition,[status(thm),theory(equality)],[c_2821,c_2586])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( B_10 = A_9
      | ~ r1_tarski(B_10,A_9)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3138,plain,(
    ! [A_216] :
      ( k1_xboole_0 = A_216
      | ~ r1_tarski(A_216,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2874,c_12])).

tff(c_3165,plain,(
    ! [C_181] : k4_xboole_0(k1_xboole_0,C_181) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2586,c_3138])).

tff(c_2480,plain,(
    ! [A_163,B_164] : k3_xboole_0(k4_xboole_0(A_163,B_164),B_164) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_2371])).

tff(c_2488,plain,(
    ! [B_164,A_163] : k3_xboole_0(B_164,k4_xboole_0(A_163,B_164)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2480,c_4])).

tff(c_2382,plain,(
    ! [A_31,B_32] : k3_xboole_0(k4_xboole_0(A_31,B_32),B_32) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_2371])).

tff(c_4978,plain,(
    ! [A_267,B_268] : k5_xboole_0(A_267,k3_xboole_0(B_268,A_267)) = k4_xboole_0(A_267,B_268) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2778])).

tff(c_5034,plain,(
    ! [B_32,A_31] : k4_xboole_0(B_32,k4_xboole_0(A_31,B_32)) = k5_xboole_0(B_32,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2382,c_4978])).

tff(c_5065,plain,(
    ! [B_32,A_31] : k4_xboole_0(B_32,k4_xboole_0(A_31,B_32)) = B_32 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2820,c_5034])).

tff(c_32,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2979,plain,(
    ! [A_209,B_210,C_211] : k4_xboole_0(k4_xboole_0(A_209,B_210),C_211) = k4_xboole_0(A_209,k2_xboole_0(B_210,C_211)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_15187,plain,(
    ! [A_424,B_425,C_426] : k4_xboole_0(A_424,k2_xboole_0(k4_xboole_0(A_424,B_425),C_426)) = k4_xboole_0(k3_xboole_0(A_424,B_425),C_426) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2979])).

tff(c_15394,plain,(
    ! [B_32,A_31,C_426] : k4_xboole_0(k3_xboole_0(B_32,k4_xboole_0(A_31,B_32)),C_426) = k4_xboole_0(B_32,k2_xboole_0(B_32,C_426)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5065,c_15187])).

tff(c_15532,plain,(
    ! [B_427,C_428] : k4_xboole_0(B_427,k2_xboole_0(B_427,C_428)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3165,c_2488,c_15394])).

tff(c_15671,plain,(
    ! [B_427,C_428] : k3_xboole_0(B_427,k2_xboole_0(B_427,C_428)) = k4_xboole_0(B_427,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_15532,c_32])).

tff(c_15783,plain,(
    ! [B_429,C_430] : k3_xboole_0(B_429,k2_xboole_0(B_429,C_430)) = B_429 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_15671])).

tff(c_2916,plain,(
    ! [A_207,B_208] : r1_tarski(k3_xboole_0(A_207,B_208),A_207) ),
    inference(superposition,[status(thm),theory(equality)],[c_2727,c_2586])).

tff(c_2959,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2916])).

tff(c_16013,plain,(
    ! [B_431,C_432] : r1_tarski(B_431,k2_xboole_0(B_431,C_432)) ),
    inference(superposition,[status(thm),theory(equality)],[c_15783,c_2959])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_3699,plain,(
    ! [A_228,B_229,C_230] :
      ( r1_tarski(A_228,B_229)
      | ~ r1_xboole_0(A_228,C_230)
      | ~ r1_tarski(A_228,k2_xboole_0(B_229,C_230)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3718,plain,(
    ! [A_228,A_1,B_2] :
      ( r1_tarski(A_228,A_1)
      | ~ r1_xboole_0(A_228,B_2)
      | ~ r1_tarski(A_228,k2_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3699])).

tff(c_17338,plain,(
    ! [B_446,C_447] :
      ( r1_tarski(B_446,C_447)
      | ~ r1_xboole_0(B_446,B_446) ) ),
    inference(resolution,[status(thm)],[c_16013,c_3718])).

tff(c_17350,plain,(
    ! [B_6,C_447] :
      ( r1_tarski(B_6,C_447)
      | k3_xboole_0(B_6,B_6) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_17338])).

tff(c_17364,plain,(
    ! [B_448,C_449] :
      ( r1_tarski(B_448,C_449)
      | k1_xboole_0 != B_448 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_17350])).

tff(c_20,plain,(
    ! [A_13,C_15,B_14] :
      ( r1_xboole_0(A_13,C_15)
      | ~ r1_tarski(A_13,k4_xboole_0(B_14,C_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3422,plain,(
    ! [A_221,A_222] :
      ( r1_xboole_0(A_221,A_222)
      | ~ r1_tarski(A_221,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2821,c_20])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3426,plain,(
    ! [A_221,A_222] :
      ( k3_xboole_0(A_221,A_222) = k1_xboole_0
      | ~ r1_tarski(A_221,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_3422,c_6])).

tff(c_19728,plain,(
    ! [B_466,A_467] :
      ( k3_xboole_0(B_466,A_467) = k1_xboole_0
      | k1_xboole_0 != B_466 ) ),
    inference(resolution,[status(thm)],[c_17364,c_3426])).

tff(c_2811,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(B_4,A_3)) = k4_xboole_0(A_3,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2778])).

tff(c_19981,plain,(
    ! [A_467,B_466] :
      ( k5_xboole_0(A_467,k1_xboole_0) = k4_xboole_0(A_467,B_466)
      | k1_xboole_0 != B_466 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19728,c_2811])).

tff(c_23819,plain,(
    ! [A_467] : k4_xboole_0(A_467,k1_xboole_0) = A_467 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2820,c_19981])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_62,plain,(
    ! [A_42] : ~ v1_xboole_0(k1_zfmisc_1(A_42)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2552,plain,(
    ! [B_175,A_176] :
      ( r2_hidden(B_175,A_176)
      | ~ m1_subset_1(B_175,A_176)
      | v1_xboole_0(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_40,plain,(
    ! [C_37,A_33] :
      ( r1_tarski(C_37,A_33)
      | ~ r2_hidden(C_37,k1_zfmisc_1(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2556,plain,(
    ! [B_175,A_33] :
      ( r1_tarski(B_175,A_33)
      | ~ m1_subset_1(B_175,k1_zfmisc_1(A_33))
      | v1_xboole_0(k1_zfmisc_1(A_33)) ) ),
    inference(resolution,[status(thm)],[c_2552,c_40])).

tff(c_2560,plain,(
    ! [B_177,A_178] :
      ( r1_tarski(B_177,A_178)
      | ~ m1_subset_1(B_177,k1_zfmisc_1(A_178)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2556])).

tff(c_2573,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_2560])).

tff(c_26,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(A_19,B_20) = A_19
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2590,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2573,c_26])).

tff(c_3290,plain,(
    ! [A_219,B_220] :
      ( k4_xboole_0(A_219,B_220) = k3_subset_1(A_219,B_220)
      | ~ m1_subset_1(B_220,k1_zfmisc_1(A_219)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_3307,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_3290])).

tff(c_3384,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3307,c_32])).

tff(c_3405,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2590,c_4,c_3384])).

tff(c_30,plain,(
    ! [A_22,B_23,C_24] : k4_xboole_0(k4_xboole_0(A_22,B_23),C_24) = k4_xboole_0(A_22,k2_xboole_0(B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4900,plain,(
    ! [C_266] : k4_xboole_0(k3_subset_1('#skF_3','#skF_4'),C_266) = k4_xboole_0('#skF_3',k2_xboole_0('#skF_4',C_266)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3307,c_30])).

tff(c_4946,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_4',k1_xboole_0)) = k3_subset_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4900,c_28])).

tff(c_26871,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_3',k2_xboole_0('#skF_4',k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4946,c_32])).

tff(c_26928,plain,(
    k3_xboole_0('#skF_3',k2_xboole_0('#skF_4',k1_xboole_0)) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3405,c_26871])).

tff(c_7301,plain,(
    ! [A_314,C_315] : k4_xboole_0(A_314,k2_xboole_0(k1_xboole_0,C_315)) = k4_xboole_0(A_314,C_315) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2979])).

tff(c_2777,plain,(
    ! [A_21] : k4_xboole_0(A_21,A_21) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2383,c_2774])).

tff(c_7484,plain,(
    ! [C_316] : k4_xboole_0(k2_xboole_0(k1_xboole_0,C_316),C_316) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7301,c_2777])).

tff(c_7558,plain,(
    ! [B_2] : k4_xboole_0(k2_xboole_0(B_2,k1_xboole_0),B_2) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_7484])).

tff(c_3453,plain,(
    ! [A_225,B_226,C_227] : k3_xboole_0(k3_xboole_0(A_225,B_226),C_227) = k3_xboole_0(A_225,k3_xboole_0(B_226,C_227)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8633,plain,(
    ! [C_333,A_334,B_335] : k3_xboole_0(C_333,k3_xboole_0(A_334,B_335)) = k3_xboole_0(A_334,k3_xboole_0(B_335,C_333)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3453,c_4])).

tff(c_37243,plain,(
    ! [A_643,C_644] : k3_xboole_0(A_643,k3_xboole_0(A_643,C_644)) = k3_xboole_0(C_644,A_643) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_8633])).

tff(c_37553,plain,(
    k3_xboole_0(k2_xboole_0('#skF_4',k1_xboole_0),'#skF_3') = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_26928,c_37243])).

tff(c_37773,plain,(
    k3_xboole_0(k2_xboole_0('#skF_4',k1_xboole_0),'#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2590,c_4,c_37553])).

tff(c_18,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5535,plain,(
    ! [A_278,C_279] : k3_xboole_0(A_278,k3_xboole_0(A_278,C_279)) = k3_xboole_0(A_278,C_279) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_3453])).

tff(c_5570,plain,(
    ! [A_278,C_279] : k5_xboole_0(A_278,k3_xboole_0(A_278,C_279)) = k4_xboole_0(A_278,k3_xboole_0(A_278,C_279)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5535,c_18])).

tff(c_39422,plain,(
    ! [A_648,C_649] : k4_xboole_0(A_648,k3_xboole_0(A_648,C_649)) = k4_xboole_0(A_648,C_649) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_5570])).

tff(c_39629,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4',k1_xboole_0),'#skF_3') = k4_xboole_0(k2_xboole_0('#skF_4',k1_xboole_0),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_37773,c_39422])).

tff(c_39830,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4',k1_xboole_0),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7558,c_39629])).

tff(c_39994,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4',k1_xboole_0),k1_xboole_0) = k3_xboole_0(k2_xboole_0('#skF_4',k1_xboole_0),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_39830,c_32])).

tff(c_40068,plain,(
    k2_xboole_0('#skF_4',k1_xboole_0) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23819,c_26928,c_4,c_39994])).

tff(c_37681,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k3_xboole_0('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2590,c_37243])).

tff(c_37805,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_37681])).

tff(c_3034,plain,(
    ! [A_25,B_26,C_211] : k4_xboole_0(A_25,k2_xboole_0(k4_xboole_0(A_25,B_26),C_211)) = k4_xboole_0(k3_xboole_0(A_25,B_26),C_211) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2979])).

tff(c_3306,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_3290])).

tff(c_3345,plain,(
    ! [C_24] : k4_xboole_0(k3_subset_1('#skF_3','#skF_5'),C_24) = k4_xboole_0('#skF_3',k2_xboole_0('#skF_5',C_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3306,c_30])).

tff(c_2768,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k3_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,k4_xboole_0(A_25,B_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2727])).

tff(c_20746,plain,(
    ! [A_470,B_471,C_472] : k5_xboole_0(k3_xboole_0(A_470,B_471),k3_xboole_0(A_470,k3_xboole_0(B_471,C_472))) = k4_xboole_0(k3_xboole_0(A_470,B_471),C_472) ),
    inference(superposition,[status(thm),theory(equality)],[c_3453,c_18])).

tff(c_21001,plain,(
    ! [A_7,C_472] : k5_xboole_0(A_7,k3_xboole_0(A_7,k3_xboole_0(A_7,C_472))) = k4_xboole_0(k3_xboole_0(A_7,A_7),C_472) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_20746])).

tff(c_44453,plain,(
    ! [A_689,C_690] : k3_xboole_0(A_689,k4_xboole_0(A_689,C_690)) = k4_xboole_0(A_689,C_690) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2768,c_18,c_10,c_21001])).

tff(c_2335,plain,(
    r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_2381,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2335,c_2371])).

tff(c_2802,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) = k5_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2381,c_2778])).

tff(c_16760,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2820,c_2802])).

tff(c_2672,plain,(
    ! [A_189,C_190,B_191] :
      ( r1_xboole_0(A_189,C_190)
      | ~ r1_tarski(A_189,k4_xboole_0(B_191,C_190)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2689,plain,(
    ! [B_191,C_190,C_181] : r1_xboole_0(k4_xboole_0(k4_xboole_0(B_191,C_190),C_181),C_190) ),
    inference(resolution,[status(thm)],[c_2586,c_2672])).

tff(c_6237,plain,(
    ! [B_289,C_290,B_291] : r1_xboole_0(k3_xboole_0(k4_xboole_0(B_289,C_290),B_291),C_290) ),
    inference(superposition,[status(thm),theory(equality)],[c_2727,c_2689])).

tff(c_6253,plain,(
    ! [B_32,B_291,A_31] : r1_xboole_0(k3_xboole_0(B_32,B_291),k4_xboole_0(A_31,B_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5065,c_6237])).

tff(c_16788,plain,(
    ! [B_291] : r1_xboole_0(k3_xboole_0(k3_subset_1('#skF_3','#skF_5'),B_291),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_16760,c_6253])).

tff(c_44554,plain,(
    ! [C_690] : r1_xboole_0(k4_xboole_0(k3_subset_1('#skF_3','#skF_5'),C_690),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_44453,c_16788])).

tff(c_47236,plain,(
    ! [C_702] : r1_xboole_0(k4_xboole_0('#skF_3',k2_xboole_0('#skF_5',C_702)),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3345,c_44554])).

tff(c_47739,plain,(
    ! [A_704] : r1_xboole_0(k4_xboole_0('#skF_3',k2_xboole_0(A_704,'#skF_5')),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_47236])).

tff(c_48637,plain,(
    ! [B_711] : r1_xboole_0(k4_xboole_0(k3_xboole_0('#skF_3',B_711),'#skF_5'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3034,c_47739])).

tff(c_48649,plain,(
    r1_xboole_0(k4_xboole_0('#skF_4','#skF_5'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_37805,c_48637])).

tff(c_48767,plain,(
    k3_xboole_0(k4_xboole_0('#skF_4','#skF_5'),'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48649,c_6])).

tff(c_49279,plain,(
    k4_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_5')) = k5_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_48767,c_2811])).

tff(c_49372,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2820,c_32,c_49279])).

tff(c_10375,plain,(
    ! [B_354,C_355] :
      ( r1_tarski(k2_xboole_0(B_354,C_355),B_354)
      | ~ r1_xboole_0(k2_xboole_0(B_354,C_355),C_355) ) ),
    inference(resolution,[status(thm)],[c_16,c_3699])).

tff(c_10397,plain,(
    ! [B_356] : r1_tarski(k2_xboole_0(B_356,k1_xboole_0),B_356) ),
    inference(resolution,[status(thm)],[c_34,c_10375])).

tff(c_22,plain,(
    ! [A_13,B_14,C_15] :
      ( r1_tarski(A_13,B_14)
      | ~ r1_tarski(A_13,k4_xboole_0(B_14,C_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2756,plain,(
    ! [A_13,A_199,B_200] :
      ( r1_tarski(A_13,A_199)
      | ~ r1_tarski(A_13,k3_xboole_0(A_199,B_200)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2727,c_22])).

tff(c_10404,plain,(
    ! [A_199,B_200] : r1_tarski(k2_xboole_0(k3_xboole_0(A_199,B_200),k1_xboole_0),A_199) ),
    inference(resolution,[status(thm)],[c_10397,c_2756])).

tff(c_10900,plain,(
    ! [A_360,B_361] : r1_tarski(k2_xboole_0(k1_xboole_0,k3_xboole_0(A_360,B_361)),A_360) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10404])).

tff(c_11026,plain,(
    ! [A_3,B_4] : r1_tarski(k2_xboole_0(k1_xboole_0,k3_xboole_0(A_3,B_4)),B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_10900])).

tff(c_49706,plain,(
    r1_tarski(k2_xboole_0(k1_xboole_0,'#skF_4'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_49372,c_11026])).

tff(c_49809,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40068,c_2,c_49706])).

tff(c_49811,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2336,c_49809])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:11:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.08/7.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.08/7.80  
% 15.08/7.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.08/7.80  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 15.08/7.80  
% 15.08/7.80  %Foreground sorts:
% 15.08/7.80  
% 15.08/7.80  
% 15.08/7.80  %Background operators:
% 15.08/7.80  
% 15.08/7.80  
% 15.08/7.80  %Foreground operators:
% 15.08/7.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.08/7.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.08/7.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.08/7.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.08/7.80  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 15.08/7.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.08/7.80  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 15.08/7.80  tff('#skF_5', type, '#skF_5': $i).
% 15.08/7.80  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 15.08/7.80  tff('#skF_3', type, '#skF_3': $i).
% 15.08/7.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.08/7.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.08/7.80  tff('#skF_4', type, '#skF_4': $i).
% 15.08/7.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.08/7.80  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 15.08/7.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.08/7.80  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 15.08/7.80  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 15.08/7.80  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 15.08/7.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.08/7.80  
% 15.08/7.83  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 15.08/7.83  tff(f_108, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_subset_1)).
% 15.08/7.83  tff(f_95, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 15.08/7.83  tff(f_63, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 15.08/7.83  tff(f_71, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 15.08/7.83  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 15.08/7.83  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 15.08/7.83  tff(f_51, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 15.08/7.83  tff(f_57, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 15.08/7.83  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 15.08/7.83  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 15.08/7.83  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.08/7.83  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 15.08/7.83  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 15.08/7.83  tff(f_59, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 15.08/7.83  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 15.08/7.83  tff(f_69, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 15.08/7.83  tff(f_98, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 15.08/7.83  tff(f_91, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 15.08/7.83  tff(f_78, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 15.08/7.83  tff(c_341, plain, (![A_71, B_72]: (r1_xboole_0(A_71, B_72) | k3_xboole_0(A_71, B_72)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 15.08/7.83  tff(c_74, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5')) | r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 15.08/7.83  tff(c_135, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_74])).
% 15.08/7.83  tff(c_68, plain, (~r1_tarski('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 15.08/7.83  tff(c_269, plain, (~r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_68])).
% 15.08/7.83  tff(c_348, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_341, c_269])).
% 15.08/7.83  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 15.08/7.83  tff(c_2243, plain, (![A_147, B_148]: (k4_xboole_0(A_147, B_148)=k3_subset_1(A_147, B_148) | ~m1_subset_1(B_148, k1_zfmisc_1(A_147)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 15.08/7.83  tff(c_2259, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_64, c_2243])).
% 15.08/7.83  tff(c_34, plain, (![A_27]: (r1_xboole_0(A_27, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_63])).
% 15.08/7.83  tff(c_170, plain, (![A_57, B_58]: (k3_xboole_0(A_57, B_58)=k1_xboole_0 | ~r1_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_33])).
% 15.08/7.83  tff(c_178, plain, (![A_27]: (k3_xboole_0(A_27, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_170])).
% 15.08/7.83  tff(c_38, plain, (![A_31, B_32]: (r1_xboole_0(k4_xboole_0(A_31, B_32), B_32))), inference(cnfTransformation, [status(thm)], [f_71])).
% 15.08/7.83  tff(c_272, plain, (![A_63, B_64]: (k3_xboole_0(k4_xboole_0(A_63, B_64), B_64)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_170])).
% 15.08/7.83  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 15.08/7.83  tff(c_280, plain, (![B_64, A_63]: (k3_xboole_0(B_64, k4_xboole_0(A_63, B_64))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_272, c_4])).
% 15.08/7.83  tff(c_210, plain, (![A_60, B_61]: (k3_xboole_0(A_60, B_61)=A_60 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_55])).
% 15.08/7.83  tff(c_217, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_135, c_210])).
% 15.08/7.83  tff(c_1204, plain, (![A_115, B_116, C_117]: (k3_xboole_0(k3_xboole_0(A_115, B_116), C_117)=k3_xboole_0(A_115, k3_xboole_0(B_116, C_117)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.08/7.83  tff(c_1922, plain, (![C_140]: (k3_xboole_0('#skF_4', k3_xboole_0('#skF_5', C_140))=k3_xboole_0('#skF_4', C_140))), inference(superposition, [status(thm), theory('equality')], [c_217, c_1204])).
% 15.08/7.83  tff(c_1956, plain, (![A_63]: (k3_xboole_0('#skF_4', k4_xboole_0(A_63, '#skF_5'))=k3_xboole_0('#skF_4', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_280, c_1922])).
% 15.08/7.83  tff(c_1980, plain, (![A_63]: (k3_xboole_0('#skF_4', k4_xboole_0(A_63, '#skF_5'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_178, c_1956])).
% 15.08/7.83  tff(c_2297, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2259, c_1980])).
% 15.08/7.83  tff(c_2334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_348, c_2297])).
% 15.08/7.83  tff(c_2336, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_74])).
% 15.08/7.83  tff(c_28, plain, (![A_21]: (k4_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_57])).
% 15.08/7.83  tff(c_2371, plain, (![A_157, B_158]: (k3_xboole_0(A_157, B_158)=k1_xboole_0 | ~r1_xboole_0(A_157, B_158))), inference(cnfTransformation, [status(thm)], [f_33])).
% 15.08/7.83  tff(c_2383, plain, (![A_27]: (k3_xboole_0(A_27, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_2371])).
% 15.08/7.83  tff(c_2778, plain, (![A_201, B_202]: (k5_xboole_0(A_201, k3_xboole_0(A_201, B_202))=k4_xboole_0(A_201, B_202))), inference(cnfTransformation, [status(thm)], [f_43])).
% 15.08/7.83  tff(c_2808, plain, (![A_27]: (k5_xboole_0(A_27, k1_xboole_0)=k4_xboole_0(A_27, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2383, c_2778])).
% 15.08/7.83  tff(c_2820, plain, (![A_27]: (k5_xboole_0(A_27, k1_xboole_0)=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2808])).
% 15.08/7.83  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.08/7.83  tff(c_8, plain, (![A_5, B_6]: (r1_xboole_0(A_5, B_6) | k3_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 15.08/7.83  tff(c_16, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.08/7.83  tff(c_2578, plain, (![A_179, B_180, C_181]: (r1_tarski(A_179, B_180) | ~r1_tarski(A_179, k4_xboole_0(B_180, C_181)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 15.08/7.83  tff(c_2586, plain, (![B_180, C_181]: (r1_tarski(k4_xboole_0(B_180, C_181), B_180))), inference(resolution, [status(thm)], [c_16, c_2578])).
% 15.08/7.83  tff(c_2727, plain, (![A_199, B_200]: (k4_xboole_0(A_199, k4_xboole_0(A_199, B_200))=k3_xboole_0(A_199, B_200))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.08/7.83  tff(c_2774, plain, (![A_21]: (k4_xboole_0(A_21, A_21)=k3_xboole_0(A_21, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2727])).
% 15.08/7.83  tff(c_2821, plain, (![A_203]: (k4_xboole_0(A_203, A_203)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2383, c_2774])).
% 15.08/7.83  tff(c_2874, plain, (![A_204]: (r1_tarski(k1_xboole_0, A_204))), inference(superposition, [status(thm), theory('equality')], [c_2821, c_2586])).
% 15.08/7.83  tff(c_12, plain, (![B_10, A_9]: (B_10=A_9 | ~r1_tarski(B_10, A_9) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.08/7.83  tff(c_3138, plain, (![A_216]: (k1_xboole_0=A_216 | ~r1_tarski(A_216, k1_xboole_0))), inference(resolution, [status(thm)], [c_2874, c_12])).
% 15.08/7.83  tff(c_3165, plain, (![C_181]: (k4_xboole_0(k1_xboole_0, C_181)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2586, c_3138])).
% 15.08/7.83  tff(c_2480, plain, (![A_163, B_164]: (k3_xboole_0(k4_xboole_0(A_163, B_164), B_164)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_2371])).
% 15.08/7.83  tff(c_2488, plain, (![B_164, A_163]: (k3_xboole_0(B_164, k4_xboole_0(A_163, B_164))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2480, c_4])).
% 15.08/7.83  tff(c_2382, plain, (![A_31, B_32]: (k3_xboole_0(k4_xboole_0(A_31, B_32), B_32)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_2371])).
% 15.08/7.83  tff(c_4978, plain, (![A_267, B_268]: (k5_xboole_0(A_267, k3_xboole_0(B_268, A_267))=k4_xboole_0(A_267, B_268))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2778])).
% 15.08/7.83  tff(c_5034, plain, (![B_32, A_31]: (k4_xboole_0(B_32, k4_xboole_0(A_31, B_32))=k5_xboole_0(B_32, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2382, c_4978])).
% 15.08/7.83  tff(c_5065, plain, (![B_32, A_31]: (k4_xboole_0(B_32, k4_xboole_0(A_31, B_32))=B_32)), inference(demodulation, [status(thm), theory('equality')], [c_2820, c_5034])).
% 15.08/7.83  tff(c_32, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.08/7.83  tff(c_2979, plain, (![A_209, B_210, C_211]: (k4_xboole_0(k4_xboole_0(A_209, B_210), C_211)=k4_xboole_0(A_209, k2_xboole_0(B_210, C_211)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 15.08/7.83  tff(c_15187, plain, (![A_424, B_425, C_426]: (k4_xboole_0(A_424, k2_xboole_0(k4_xboole_0(A_424, B_425), C_426))=k4_xboole_0(k3_xboole_0(A_424, B_425), C_426))), inference(superposition, [status(thm), theory('equality')], [c_32, c_2979])).
% 15.08/7.83  tff(c_15394, plain, (![B_32, A_31, C_426]: (k4_xboole_0(k3_xboole_0(B_32, k4_xboole_0(A_31, B_32)), C_426)=k4_xboole_0(B_32, k2_xboole_0(B_32, C_426)))), inference(superposition, [status(thm), theory('equality')], [c_5065, c_15187])).
% 15.08/7.83  tff(c_15532, plain, (![B_427, C_428]: (k4_xboole_0(B_427, k2_xboole_0(B_427, C_428))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3165, c_2488, c_15394])).
% 15.08/7.83  tff(c_15671, plain, (![B_427, C_428]: (k3_xboole_0(B_427, k2_xboole_0(B_427, C_428))=k4_xboole_0(B_427, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_15532, c_32])).
% 15.08/7.83  tff(c_15783, plain, (![B_429, C_430]: (k3_xboole_0(B_429, k2_xboole_0(B_429, C_430))=B_429)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_15671])).
% 15.08/7.83  tff(c_2916, plain, (![A_207, B_208]: (r1_tarski(k3_xboole_0(A_207, B_208), A_207))), inference(superposition, [status(thm), theory('equality')], [c_2727, c_2586])).
% 15.08/7.83  tff(c_2959, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2916])).
% 15.08/7.83  tff(c_16013, plain, (![B_431, C_432]: (r1_tarski(B_431, k2_xboole_0(B_431, C_432)))), inference(superposition, [status(thm), theory('equality')], [c_15783, c_2959])).
% 15.08/7.83  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 15.08/7.83  tff(c_3699, plain, (![A_228, B_229, C_230]: (r1_tarski(A_228, B_229) | ~r1_xboole_0(A_228, C_230) | ~r1_tarski(A_228, k2_xboole_0(B_229, C_230)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 15.08/7.83  tff(c_3718, plain, (![A_228, A_1, B_2]: (r1_tarski(A_228, A_1) | ~r1_xboole_0(A_228, B_2) | ~r1_tarski(A_228, k2_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3699])).
% 15.08/7.83  tff(c_17338, plain, (![B_446, C_447]: (r1_tarski(B_446, C_447) | ~r1_xboole_0(B_446, B_446))), inference(resolution, [status(thm)], [c_16013, c_3718])).
% 15.08/7.83  tff(c_17350, plain, (![B_6, C_447]: (r1_tarski(B_6, C_447) | k3_xboole_0(B_6, B_6)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_17338])).
% 15.08/7.83  tff(c_17364, plain, (![B_448, C_449]: (r1_tarski(B_448, C_449) | k1_xboole_0!=B_448)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_17350])).
% 15.08/7.83  tff(c_20, plain, (![A_13, C_15, B_14]: (r1_xboole_0(A_13, C_15) | ~r1_tarski(A_13, k4_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 15.08/7.83  tff(c_3422, plain, (![A_221, A_222]: (r1_xboole_0(A_221, A_222) | ~r1_tarski(A_221, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2821, c_20])).
% 15.08/7.83  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 15.08/7.83  tff(c_3426, plain, (![A_221, A_222]: (k3_xboole_0(A_221, A_222)=k1_xboole_0 | ~r1_tarski(A_221, k1_xboole_0))), inference(resolution, [status(thm)], [c_3422, c_6])).
% 15.08/7.83  tff(c_19728, plain, (![B_466, A_467]: (k3_xboole_0(B_466, A_467)=k1_xboole_0 | k1_xboole_0!=B_466)), inference(resolution, [status(thm)], [c_17364, c_3426])).
% 15.08/7.83  tff(c_2811, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(B_4, A_3))=k4_xboole_0(A_3, B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2778])).
% 15.08/7.83  tff(c_19981, plain, (![A_467, B_466]: (k5_xboole_0(A_467, k1_xboole_0)=k4_xboole_0(A_467, B_466) | k1_xboole_0!=B_466)), inference(superposition, [status(thm), theory('equality')], [c_19728, c_2811])).
% 15.08/7.83  tff(c_23819, plain, (![A_467]: (k4_xboole_0(A_467, k1_xboole_0)=A_467)), inference(demodulation, [status(thm), theory('equality')], [c_2820, c_19981])).
% 15.08/7.83  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 15.08/7.83  tff(c_62, plain, (![A_42]: (~v1_xboole_0(k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 15.08/7.83  tff(c_2552, plain, (![B_175, A_176]: (r2_hidden(B_175, A_176) | ~m1_subset_1(B_175, A_176) | v1_xboole_0(A_176))), inference(cnfTransformation, [status(thm)], [f_91])).
% 15.08/7.83  tff(c_40, plain, (![C_37, A_33]: (r1_tarski(C_37, A_33) | ~r2_hidden(C_37, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 15.08/7.83  tff(c_2556, plain, (![B_175, A_33]: (r1_tarski(B_175, A_33) | ~m1_subset_1(B_175, k1_zfmisc_1(A_33)) | v1_xboole_0(k1_zfmisc_1(A_33)))), inference(resolution, [status(thm)], [c_2552, c_40])).
% 15.08/7.83  tff(c_2560, plain, (![B_177, A_178]: (r1_tarski(B_177, A_178) | ~m1_subset_1(B_177, k1_zfmisc_1(A_178)))), inference(negUnitSimplification, [status(thm)], [c_62, c_2556])).
% 15.08/7.83  tff(c_2573, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_2560])).
% 15.08/7.83  tff(c_26, plain, (![A_19, B_20]: (k3_xboole_0(A_19, B_20)=A_19 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_55])).
% 15.08/7.83  tff(c_2590, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_2573, c_26])).
% 15.08/7.83  tff(c_3290, plain, (![A_219, B_220]: (k4_xboole_0(A_219, B_220)=k3_subset_1(A_219, B_220) | ~m1_subset_1(B_220, k1_zfmisc_1(A_219)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 15.08/7.83  tff(c_3307, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_66, c_3290])).
% 15.08/7.83  tff(c_3384, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3307, c_32])).
% 15.08/7.83  tff(c_3405, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2590, c_4, c_3384])).
% 15.08/7.83  tff(c_30, plain, (![A_22, B_23, C_24]: (k4_xboole_0(k4_xboole_0(A_22, B_23), C_24)=k4_xboole_0(A_22, k2_xboole_0(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 15.08/7.83  tff(c_4900, plain, (![C_266]: (k4_xboole_0(k3_subset_1('#skF_3', '#skF_4'), C_266)=k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', C_266)))), inference(superposition, [status(thm), theory('equality')], [c_3307, c_30])).
% 15.08/7.83  tff(c_4946, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', k1_xboole_0))=k3_subset_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4900, c_28])).
% 15.08/7.83  tff(c_26871, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4946, c_32])).
% 15.08/7.83  tff(c_26928, plain, (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', k1_xboole_0))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3405, c_26871])).
% 15.08/7.83  tff(c_7301, plain, (![A_314, C_315]: (k4_xboole_0(A_314, k2_xboole_0(k1_xboole_0, C_315))=k4_xboole_0(A_314, C_315))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2979])).
% 15.08/7.83  tff(c_2777, plain, (![A_21]: (k4_xboole_0(A_21, A_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2383, c_2774])).
% 15.08/7.83  tff(c_7484, plain, (![C_316]: (k4_xboole_0(k2_xboole_0(k1_xboole_0, C_316), C_316)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7301, c_2777])).
% 15.08/7.83  tff(c_7558, plain, (![B_2]: (k4_xboole_0(k2_xboole_0(B_2, k1_xboole_0), B_2)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_7484])).
% 15.08/7.83  tff(c_3453, plain, (![A_225, B_226, C_227]: (k3_xboole_0(k3_xboole_0(A_225, B_226), C_227)=k3_xboole_0(A_225, k3_xboole_0(B_226, C_227)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.08/7.83  tff(c_8633, plain, (![C_333, A_334, B_335]: (k3_xboole_0(C_333, k3_xboole_0(A_334, B_335))=k3_xboole_0(A_334, k3_xboole_0(B_335, C_333)))), inference(superposition, [status(thm), theory('equality')], [c_3453, c_4])).
% 15.08/7.83  tff(c_37243, plain, (![A_643, C_644]: (k3_xboole_0(A_643, k3_xboole_0(A_643, C_644))=k3_xboole_0(C_644, A_643))), inference(superposition, [status(thm), theory('equality')], [c_10, c_8633])).
% 15.08/7.83  tff(c_37553, plain, (k3_xboole_0(k2_xboole_0('#skF_4', k1_xboole_0), '#skF_3')=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_26928, c_37243])).
% 15.08/7.83  tff(c_37773, plain, (k3_xboole_0(k2_xboole_0('#skF_4', k1_xboole_0), '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2590, c_4, c_37553])).
% 15.08/7.83  tff(c_18, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 15.08/7.83  tff(c_5535, plain, (![A_278, C_279]: (k3_xboole_0(A_278, k3_xboole_0(A_278, C_279))=k3_xboole_0(A_278, C_279))), inference(superposition, [status(thm), theory('equality')], [c_10, c_3453])).
% 15.08/7.83  tff(c_5570, plain, (![A_278, C_279]: (k5_xboole_0(A_278, k3_xboole_0(A_278, C_279))=k4_xboole_0(A_278, k3_xboole_0(A_278, C_279)))), inference(superposition, [status(thm), theory('equality')], [c_5535, c_18])).
% 15.08/7.83  tff(c_39422, plain, (![A_648, C_649]: (k4_xboole_0(A_648, k3_xboole_0(A_648, C_649))=k4_xboole_0(A_648, C_649))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_5570])).
% 15.08/7.83  tff(c_39629, plain, (k4_xboole_0(k2_xboole_0('#skF_4', k1_xboole_0), '#skF_3')=k4_xboole_0(k2_xboole_0('#skF_4', k1_xboole_0), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_37773, c_39422])).
% 15.08/7.83  tff(c_39830, plain, (k4_xboole_0(k2_xboole_0('#skF_4', k1_xboole_0), '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7558, c_39629])).
% 15.08/7.83  tff(c_39994, plain, (k4_xboole_0(k2_xboole_0('#skF_4', k1_xboole_0), k1_xboole_0)=k3_xboole_0(k2_xboole_0('#skF_4', k1_xboole_0), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_39830, c_32])).
% 15.08/7.83  tff(c_40068, plain, (k2_xboole_0('#skF_4', k1_xboole_0)='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_23819, c_26928, c_4, c_39994])).
% 15.08/7.83  tff(c_37681, plain, (k3_xboole_0('#skF_3', '#skF_4')=k3_xboole_0('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2590, c_37243])).
% 15.08/7.83  tff(c_37805, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_37681])).
% 15.08/7.83  tff(c_3034, plain, (![A_25, B_26, C_211]: (k4_xboole_0(A_25, k2_xboole_0(k4_xboole_0(A_25, B_26), C_211))=k4_xboole_0(k3_xboole_0(A_25, B_26), C_211))), inference(superposition, [status(thm), theory('equality')], [c_32, c_2979])).
% 15.08/7.83  tff(c_3306, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_64, c_3290])).
% 15.08/7.83  tff(c_3345, plain, (![C_24]: (k4_xboole_0(k3_subset_1('#skF_3', '#skF_5'), C_24)=k4_xboole_0('#skF_3', k2_xboole_0('#skF_5', C_24)))), inference(superposition, [status(thm), theory('equality')], [c_3306, c_30])).
% 15.08/7.83  tff(c_2768, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k3_xboole_0(A_25, B_26))=k3_xboole_0(A_25, k4_xboole_0(A_25, B_26)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_2727])).
% 15.08/7.83  tff(c_20746, plain, (![A_470, B_471, C_472]: (k5_xboole_0(k3_xboole_0(A_470, B_471), k3_xboole_0(A_470, k3_xboole_0(B_471, C_472)))=k4_xboole_0(k3_xboole_0(A_470, B_471), C_472))), inference(superposition, [status(thm), theory('equality')], [c_3453, c_18])).
% 15.08/7.83  tff(c_21001, plain, (![A_7, C_472]: (k5_xboole_0(A_7, k3_xboole_0(A_7, k3_xboole_0(A_7, C_472)))=k4_xboole_0(k3_xboole_0(A_7, A_7), C_472))), inference(superposition, [status(thm), theory('equality')], [c_10, c_20746])).
% 15.08/7.83  tff(c_44453, plain, (![A_689, C_690]: (k3_xboole_0(A_689, k4_xboole_0(A_689, C_690))=k4_xboole_0(A_689, C_690))), inference(demodulation, [status(thm), theory('equality')], [c_2768, c_18, c_10, c_21001])).
% 15.08/7.83  tff(c_2335, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_74])).
% 15.08/7.83  tff(c_2381, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_2335, c_2371])).
% 15.08/7.83  tff(c_2802, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))=k5_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2381, c_2778])).
% 15.08/7.83  tff(c_16760, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2820, c_2802])).
% 15.08/7.83  tff(c_2672, plain, (![A_189, C_190, B_191]: (r1_xboole_0(A_189, C_190) | ~r1_tarski(A_189, k4_xboole_0(B_191, C_190)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 15.08/7.83  tff(c_2689, plain, (![B_191, C_190, C_181]: (r1_xboole_0(k4_xboole_0(k4_xboole_0(B_191, C_190), C_181), C_190))), inference(resolution, [status(thm)], [c_2586, c_2672])).
% 15.08/7.83  tff(c_6237, plain, (![B_289, C_290, B_291]: (r1_xboole_0(k3_xboole_0(k4_xboole_0(B_289, C_290), B_291), C_290))), inference(superposition, [status(thm), theory('equality')], [c_2727, c_2689])).
% 15.08/7.83  tff(c_6253, plain, (![B_32, B_291, A_31]: (r1_xboole_0(k3_xboole_0(B_32, B_291), k4_xboole_0(A_31, B_32)))), inference(superposition, [status(thm), theory('equality')], [c_5065, c_6237])).
% 15.08/7.83  tff(c_16788, plain, (![B_291]: (r1_xboole_0(k3_xboole_0(k3_subset_1('#skF_3', '#skF_5'), B_291), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_16760, c_6253])).
% 15.08/7.83  tff(c_44554, plain, (![C_690]: (r1_xboole_0(k4_xboole_0(k3_subset_1('#skF_3', '#skF_5'), C_690), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_44453, c_16788])).
% 15.08/7.83  tff(c_47236, plain, (![C_702]: (r1_xboole_0(k4_xboole_0('#skF_3', k2_xboole_0('#skF_5', C_702)), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3345, c_44554])).
% 15.08/7.83  tff(c_47739, plain, (![A_704]: (r1_xboole_0(k4_xboole_0('#skF_3', k2_xboole_0(A_704, '#skF_5')), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_47236])).
% 15.08/7.83  tff(c_48637, plain, (![B_711]: (r1_xboole_0(k4_xboole_0(k3_xboole_0('#skF_3', B_711), '#skF_5'), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3034, c_47739])).
% 15.08/7.83  tff(c_48649, plain, (r1_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_37805, c_48637])).
% 15.08/7.83  tff(c_48767, plain, (k3_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_48649, c_6])).
% 15.08/7.83  tff(c_49279, plain, (k4_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_5'))=k5_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_48767, c_2811])).
% 15.08/7.83  tff(c_49372, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2820, c_32, c_49279])).
% 15.08/7.83  tff(c_10375, plain, (![B_354, C_355]: (r1_tarski(k2_xboole_0(B_354, C_355), B_354) | ~r1_xboole_0(k2_xboole_0(B_354, C_355), C_355))), inference(resolution, [status(thm)], [c_16, c_3699])).
% 15.08/7.83  tff(c_10397, plain, (![B_356]: (r1_tarski(k2_xboole_0(B_356, k1_xboole_0), B_356))), inference(resolution, [status(thm)], [c_34, c_10375])).
% 15.08/7.83  tff(c_22, plain, (![A_13, B_14, C_15]: (r1_tarski(A_13, B_14) | ~r1_tarski(A_13, k4_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 15.08/7.83  tff(c_2756, plain, (![A_13, A_199, B_200]: (r1_tarski(A_13, A_199) | ~r1_tarski(A_13, k3_xboole_0(A_199, B_200)))), inference(superposition, [status(thm), theory('equality')], [c_2727, c_22])).
% 15.08/7.83  tff(c_10404, plain, (![A_199, B_200]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_199, B_200), k1_xboole_0), A_199))), inference(resolution, [status(thm)], [c_10397, c_2756])).
% 15.08/7.83  tff(c_10900, plain, (![A_360, B_361]: (r1_tarski(k2_xboole_0(k1_xboole_0, k3_xboole_0(A_360, B_361)), A_360))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10404])).
% 15.08/7.83  tff(c_11026, plain, (![A_3, B_4]: (r1_tarski(k2_xboole_0(k1_xboole_0, k3_xboole_0(A_3, B_4)), B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_10900])).
% 15.08/7.83  tff(c_49706, plain, (r1_tarski(k2_xboole_0(k1_xboole_0, '#skF_4'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_49372, c_11026])).
% 15.08/7.83  tff(c_49809, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40068, c_2, c_49706])).
% 15.08/7.83  tff(c_49811, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2336, c_49809])).
% 15.08/7.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.08/7.83  
% 15.08/7.83  Inference rules
% 15.08/7.83  ----------------------
% 15.08/7.83  #Ref     : 1
% 15.08/7.83  #Sup     : 12457
% 15.08/7.83  #Fact    : 0
% 15.08/7.83  #Define  : 0
% 15.08/7.83  #Split   : 10
% 15.08/7.83  #Chain   : 0
% 15.08/7.83  #Close   : 0
% 15.08/7.83  
% 15.08/7.83  Ordering : KBO
% 15.08/7.83  
% 15.08/7.83  Simplification rules
% 15.08/7.83  ----------------------
% 15.08/7.83  #Subsume      : 1316
% 15.08/7.83  #Demod        : 11075
% 15.08/7.83  #Tautology    : 7510
% 15.08/7.83  #SimpNegUnit  : 243
% 15.08/7.83  #BackRed      : 44
% 15.08/7.83  
% 15.08/7.83  #Partial instantiations: 0
% 15.08/7.83  #Strategies tried      : 1
% 15.08/7.83  
% 15.08/7.83  Timing (in seconds)
% 15.08/7.83  ----------------------
% 15.08/7.83  Preprocessing        : 0.35
% 15.08/7.83  Parsing              : 0.18
% 15.08/7.83  CNF conversion       : 0.03
% 15.08/7.83  Main loop            : 6.64
% 15.08/7.83  Inferencing          : 0.97
% 15.08/7.83  Reduction            : 4.05
% 15.08/7.83  Demodulation         : 3.55
% 15.08/7.83  BG Simplification    : 0.12
% 15.08/7.83  Subsumption          : 1.19
% 15.08/7.83  Abstraction          : 0.14
% 15.08/7.83  MUC search           : 0.00
% 15.08/7.83  Cooper               : 0.00
% 15.08/7.83  Total                : 7.05
% 15.08/7.83  Index Insertion      : 0.00
% 15.08/7.83  Index Deletion       : 0.00
% 15.08/7.83  Index Matching       : 0.00
% 15.08/7.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
