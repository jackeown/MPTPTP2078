%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:48 EST 2020

% Result     : Theorem 9.65s
% Output     : CNFRefutation 9.65s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 144 expanded)
%              Number of leaves         :   31 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :  115 ( 227 expanded)
%              Number of equality atoms :   40 (  65 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_74,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_54,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_134,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_48,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_225,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_48])).

tff(c_229,plain,(
    k4_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_225])).

tff(c_12,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_42,plain,(
    ! [A_27] : ~ v1_xboole_0(k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_234,plain,(
    ! [B_52,A_53] :
      ( r2_hidden(B_52,A_53)
      | ~ m1_subset_1(B_52,A_53)
      | v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_20,plain,(
    ! [C_22,A_18] :
      ( r1_tarski(C_22,A_18)
      | ~ r2_hidden(C_22,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_238,plain,(
    ! [B_52,A_18] :
      ( r1_tarski(B_52,A_18)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_18))
      | v1_xboole_0(k1_zfmisc_1(A_18)) ) ),
    inference(resolution,[status(thm)],[c_234,c_20])).

tff(c_242,plain,(
    ! [B_54,A_55] :
      ( r1_tarski(B_54,A_55)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_55)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_238])).

tff(c_255,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_242])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_274,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_255,c_8])).

tff(c_18,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_286,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_18])).

tff(c_289,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_286])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_477,plain,(
    ! [A_71,B_72] :
      ( k4_xboole_0(A_71,B_72) = k3_subset_1(A_71,B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_494,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_477])).

tff(c_514,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_18])).

tff(c_517,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_4,c_514])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_493,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_477])).

tff(c_602,plain,(
    ! [A_75,B_76,C_77] :
      ( r1_tarski(A_75,k2_xboole_0(B_76,C_77))
      | ~ r1_tarski(k4_xboole_0(A_75,B_76),C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_879,plain,(
    ! [C_90] :
      ( r1_tarski('#skF_3',k2_xboole_0('#skF_5',C_90))
      | ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),C_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_602])).

tff(c_901,plain,(
    r1_tarski('#skF_3',k2_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_134,c_879])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_331,plain,(
    ! [A_60,B_61,C_62] :
      ( r1_tarski(k4_xboole_0(A_60,B_61),C_62)
      | ~ r1_tarski(A_60,k2_xboole_0(B_61,C_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2134,plain,(
    ! [A_136,B_137,C_138] :
      ( k4_xboole_0(k4_xboole_0(A_136,B_137),C_138) = k1_xboole_0
      | ~ r1_tarski(A_136,k2_xboole_0(B_137,C_138)) ) ),
    inference(resolution,[status(thm)],[c_331,c_8])).

tff(c_5649,plain,(
    ! [A_216,B_217,A_218] :
      ( k4_xboole_0(k4_xboole_0(A_216,B_217),A_218) = k1_xboole_0
      | ~ r1_tarski(A_216,k2_xboole_0(A_218,B_217)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2134])).

tff(c_5734,plain,(
    k4_xboole_0(k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')),'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_901,c_5649])).

tff(c_5799,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_5734])).

tff(c_5801,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_229,c_5799])).

tff(c_5802,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_5804,plain,(
    ! [A_219,B_220] :
      ( k4_xboole_0(A_219,B_220) = k1_xboole_0
      | ~ r1_tarski(A_219,B_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_5811,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5802,c_5804])).

tff(c_5841,plain,(
    ! [B_225,A_226] :
      ( r2_hidden(B_225,A_226)
      | ~ m1_subset_1(B_225,A_226)
      | v1_xboole_0(A_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_5845,plain,(
    ! [B_225,A_18] :
      ( r1_tarski(B_225,A_18)
      | ~ m1_subset_1(B_225,k1_zfmisc_1(A_18))
      | v1_xboole_0(k1_zfmisc_1(A_18)) ) ),
    inference(resolution,[status(thm)],[c_5841,c_20])).

tff(c_5849,plain,(
    ! [B_227,A_228] :
      ( r1_tarski(B_227,A_228)
      | ~ m1_subset_1(B_227,k1_zfmisc_1(A_228)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_5845])).

tff(c_5862,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_5849])).

tff(c_5885,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5862,c_8])).

tff(c_5914,plain,(
    ! [A_235,B_236] : k4_xboole_0(A_235,k4_xboole_0(A_235,B_236)) = k3_xboole_0(A_235,B_236) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_5929,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5885,c_5914])).

tff(c_5941,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_5929])).

tff(c_5956,plain,(
    ! [A_237,B_238] :
      ( k4_xboole_0(A_237,B_238) = k3_subset_1(A_237,B_238)
      | ~ m1_subset_1(B_238,k1_zfmisc_1(A_237)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_5973,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_5956])).

tff(c_6000,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5973,c_18])).

tff(c_6003,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5941,c_4,c_6000])).

tff(c_6046,plain,(
    ! [A_240,B_241,C_242] :
      ( r1_tarski(A_240,k2_xboole_0(B_241,C_242))
      | ~ r1_tarski(k4_xboole_0(A_240,B_241),C_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_13145,plain,(
    ! [A_449,B_450,B_451] :
      ( r1_tarski(A_449,k2_xboole_0(B_450,B_451))
      | k4_xboole_0(k4_xboole_0(A_449,B_450),B_451) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_6046])).

tff(c_18082,plain,(
    ! [A_559,A_560,B_561] :
      ( r1_tarski(A_559,k2_xboole_0(A_560,B_561))
      | k4_xboole_0(k4_xboole_0(A_559,B_561),A_560) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_13145])).

tff(c_5972,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_5956])).

tff(c_6178,plain,(
    ! [A_248,B_249,C_250] :
      ( r1_tarski(k4_xboole_0(A_248,B_249),C_250)
      | ~ r1_tarski(A_248,k2_xboole_0(B_249,C_250)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6269,plain,(
    ! [C_255] :
      ( r1_tarski(k3_subset_1('#skF_3','#skF_5'),C_255)
      | ~ r1_tarski('#skF_3',k2_xboole_0('#skF_5',C_255)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5972,c_6178])).

tff(c_5818,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5802,c_48])).

tff(c_6281,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_6269,c_5818])).

tff(c_18237,plain,(
    k4_xboole_0(k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')),'#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18082,c_6281])).

tff(c_18315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5811,c_6003,c_18237])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:09:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.65/3.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.65/3.72  
% 9.65/3.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.65/3.72  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 9.65/3.72  
% 9.65/3.72  %Foreground sorts:
% 9.65/3.72  
% 9.65/3.72  
% 9.65/3.72  %Background operators:
% 9.65/3.72  
% 9.65/3.72  
% 9.65/3.72  %Foreground operators:
% 9.65/3.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.65/3.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.65/3.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.65/3.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.65/3.72  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.65/3.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.65/3.72  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 9.65/3.72  tff('#skF_5', type, '#skF_5': $i).
% 9.65/3.72  tff('#skF_3', type, '#skF_3': $i).
% 9.65/3.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.65/3.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.65/3.72  tff('#skF_4', type, '#skF_4': $i).
% 9.65/3.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.65/3.72  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.65/3.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.65/3.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.65/3.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.65/3.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.65/3.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.65/3.72  
% 9.65/3.74  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 9.65/3.74  tff(f_84, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 9.65/3.74  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 9.65/3.74  tff(f_74, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 9.65/3.74  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 9.65/3.74  tff(f_54, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 9.65/3.74  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.65/3.74  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.65/3.74  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 9.65/3.74  tff(f_45, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 9.65/3.74  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 9.65/3.74  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 9.65/3.74  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.65/3.74  tff(c_54, plain, (r1_tarski('#skF_4', '#skF_5') | r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.65/3.74  tff(c_134, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_54])).
% 9.65/3.74  tff(c_48, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.65/3.74  tff(c_225, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_48])).
% 9.65/3.74  tff(c_229, plain, (k4_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_225])).
% 9.65/3.74  tff(c_12, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.65/3.74  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.65/3.74  tff(c_42, plain, (![A_27]: (~v1_xboole_0(k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.65/3.74  tff(c_234, plain, (![B_52, A_53]: (r2_hidden(B_52, A_53) | ~m1_subset_1(B_52, A_53) | v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.65/3.74  tff(c_20, plain, (![C_22, A_18]: (r1_tarski(C_22, A_18) | ~r2_hidden(C_22, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.65/3.74  tff(c_238, plain, (![B_52, A_18]: (r1_tarski(B_52, A_18) | ~m1_subset_1(B_52, k1_zfmisc_1(A_18)) | v1_xboole_0(k1_zfmisc_1(A_18)))), inference(resolution, [status(thm)], [c_234, c_20])).
% 9.65/3.74  tff(c_242, plain, (![B_54, A_55]: (r1_tarski(B_54, A_55) | ~m1_subset_1(B_54, k1_zfmisc_1(A_55)))), inference(negUnitSimplification, [status(thm)], [c_42, c_238])).
% 9.65/3.74  tff(c_255, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_242])).
% 9.65/3.74  tff(c_8, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.65/3.74  tff(c_274, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_255, c_8])).
% 9.65/3.74  tff(c_18, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.65/3.74  tff(c_286, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_274, c_18])).
% 9.65/3.74  tff(c_289, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_286])).
% 9.65/3.74  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.65/3.74  tff(c_477, plain, (![A_71, B_72]: (k4_xboole_0(A_71, B_72)=k3_subset_1(A_71, B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.65/3.74  tff(c_494, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_477])).
% 9.65/3.74  tff(c_514, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_494, c_18])).
% 9.65/3.74  tff(c_517, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_289, c_4, c_514])).
% 9.65/3.74  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.65/3.74  tff(c_493, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_477])).
% 9.65/3.74  tff(c_602, plain, (![A_75, B_76, C_77]: (r1_tarski(A_75, k2_xboole_0(B_76, C_77)) | ~r1_tarski(k4_xboole_0(A_75, B_76), C_77))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.65/3.74  tff(c_879, plain, (![C_90]: (r1_tarski('#skF_3', k2_xboole_0('#skF_5', C_90)) | ~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), C_90))), inference(superposition, [status(thm), theory('equality')], [c_493, c_602])).
% 9.65/3.74  tff(c_901, plain, (r1_tarski('#skF_3', k2_xboole_0('#skF_5', k3_subset_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_134, c_879])).
% 9.65/3.74  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.65/3.74  tff(c_331, plain, (![A_60, B_61, C_62]: (r1_tarski(k4_xboole_0(A_60, B_61), C_62) | ~r1_tarski(A_60, k2_xboole_0(B_61, C_62)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.65/3.74  tff(c_2134, plain, (![A_136, B_137, C_138]: (k4_xboole_0(k4_xboole_0(A_136, B_137), C_138)=k1_xboole_0 | ~r1_tarski(A_136, k2_xboole_0(B_137, C_138)))), inference(resolution, [status(thm)], [c_331, c_8])).
% 9.65/3.74  tff(c_5649, plain, (![A_216, B_217, A_218]: (k4_xboole_0(k4_xboole_0(A_216, B_217), A_218)=k1_xboole_0 | ~r1_tarski(A_216, k2_xboole_0(A_218, B_217)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2134])).
% 9.65/3.74  tff(c_5734, plain, (k4_xboole_0(k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4')), '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_901, c_5649])).
% 9.65/3.74  tff(c_5799, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_517, c_5734])).
% 9.65/3.74  tff(c_5801, plain, $false, inference(negUnitSimplification, [status(thm)], [c_229, c_5799])).
% 9.65/3.74  tff(c_5802, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_54])).
% 9.65/3.74  tff(c_5804, plain, (![A_219, B_220]: (k4_xboole_0(A_219, B_220)=k1_xboole_0 | ~r1_tarski(A_219, B_220))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.65/3.74  tff(c_5811, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_5802, c_5804])).
% 9.65/3.74  tff(c_5841, plain, (![B_225, A_226]: (r2_hidden(B_225, A_226) | ~m1_subset_1(B_225, A_226) | v1_xboole_0(A_226))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.65/3.74  tff(c_5845, plain, (![B_225, A_18]: (r1_tarski(B_225, A_18) | ~m1_subset_1(B_225, k1_zfmisc_1(A_18)) | v1_xboole_0(k1_zfmisc_1(A_18)))), inference(resolution, [status(thm)], [c_5841, c_20])).
% 9.65/3.74  tff(c_5849, plain, (![B_227, A_228]: (r1_tarski(B_227, A_228) | ~m1_subset_1(B_227, k1_zfmisc_1(A_228)))), inference(negUnitSimplification, [status(thm)], [c_42, c_5845])).
% 9.65/3.74  tff(c_5862, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_5849])).
% 9.65/3.74  tff(c_5885, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_5862, c_8])).
% 9.65/3.74  tff(c_5914, plain, (![A_235, B_236]: (k4_xboole_0(A_235, k4_xboole_0(A_235, B_236))=k3_xboole_0(A_235, B_236))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.65/3.74  tff(c_5929, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5885, c_5914])).
% 9.65/3.74  tff(c_5941, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_5929])).
% 9.65/3.74  tff(c_5956, plain, (![A_237, B_238]: (k4_xboole_0(A_237, B_238)=k3_subset_1(A_237, B_238) | ~m1_subset_1(B_238, k1_zfmisc_1(A_237)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.65/3.74  tff(c_5973, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_5956])).
% 9.65/3.74  tff(c_6000, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5973, c_18])).
% 9.65/3.74  tff(c_6003, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5941, c_4, c_6000])).
% 9.65/3.74  tff(c_6046, plain, (![A_240, B_241, C_242]: (r1_tarski(A_240, k2_xboole_0(B_241, C_242)) | ~r1_tarski(k4_xboole_0(A_240, B_241), C_242))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.65/3.74  tff(c_13145, plain, (![A_449, B_450, B_451]: (r1_tarski(A_449, k2_xboole_0(B_450, B_451)) | k4_xboole_0(k4_xboole_0(A_449, B_450), B_451)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_6046])).
% 9.65/3.74  tff(c_18082, plain, (![A_559, A_560, B_561]: (r1_tarski(A_559, k2_xboole_0(A_560, B_561)) | k4_xboole_0(k4_xboole_0(A_559, B_561), A_560)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_13145])).
% 9.65/3.74  tff(c_5972, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_5956])).
% 9.65/3.74  tff(c_6178, plain, (![A_248, B_249, C_250]: (r1_tarski(k4_xboole_0(A_248, B_249), C_250) | ~r1_tarski(A_248, k2_xboole_0(B_249, C_250)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.65/3.74  tff(c_6269, plain, (![C_255]: (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), C_255) | ~r1_tarski('#skF_3', k2_xboole_0('#skF_5', C_255)))), inference(superposition, [status(thm), theory('equality')], [c_5972, c_6178])).
% 9.65/3.74  tff(c_5818, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5802, c_48])).
% 9.65/3.74  tff(c_6281, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_5', k3_subset_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_6269, c_5818])).
% 9.65/3.74  tff(c_18237, plain, (k4_xboole_0(k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4')), '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_18082, c_6281])).
% 9.65/3.74  tff(c_18315, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5811, c_6003, c_18237])).
% 9.65/3.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.65/3.74  
% 9.65/3.74  Inference rules
% 9.65/3.74  ----------------------
% 9.65/3.74  #Ref     : 0
% 9.65/3.74  #Sup     : 4195
% 9.65/3.74  #Fact    : 0
% 9.65/3.74  #Define  : 0
% 9.65/3.74  #Split   : 20
% 9.65/3.74  #Chain   : 0
% 9.65/3.74  #Close   : 0
% 9.65/3.74  
% 9.65/3.74  Ordering : KBO
% 9.65/3.74  
% 9.65/3.74  Simplification rules
% 9.65/3.74  ----------------------
% 9.65/3.74  #Subsume      : 921
% 9.65/3.74  #Demod        : 2008
% 9.65/3.74  #Tautology    : 1155
% 9.65/3.74  #SimpNegUnit  : 113
% 9.65/3.74  #BackRed      : 6
% 9.65/3.74  
% 9.65/3.74  #Partial instantiations: 0
% 9.65/3.74  #Strategies tried      : 1
% 9.65/3.74  
% 9.65/3.74  Timing (in seconds)
% 9.65/3.74  ----------------------
% 9.65/3.74  Preprocessing        : 0.31
% 9.65/3.74  Parsing              : 0.16
% 9.65/3.74  CNF conversion       : 0.02
% 9.65/3.74  Main loop            : 2.66
% 9.65/3.74  Inferencing          : 0.76
% 9.65/3.74  Reduction            : 0.97
% 9.65/3.74  Demodulation         : 0.71
% 9.65/3.74  BG Simplification    : 0.08
% 9.65/3.74  Subsumption          : 0.67
% 9.65/3.74  Abstraction          : 0.09
% 9.65/3.74  MUC search           : 0.00
% 9.65/3.74  Cooper               : 0.00
% 9.65/3.74  Total                : 3.01
% 9.65/3.74  Index Insertion      : 0.00
% 9.65/3.74  Index Deletion       : 0.00
% 9.65/3.74  Index Matching       : 0.00
% 9.65/3.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
