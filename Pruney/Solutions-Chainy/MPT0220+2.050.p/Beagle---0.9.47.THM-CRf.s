%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:10 EST 2020

% Result     : Theorem 8.93s
% Output     : CNFRefutation 9.00s
% Verified   : 
% Statistics : Number of formulae       :   61 (  78 expanded)
%              Number of leaves         :   32 (  41 expanded)
%              Depth                    :    6
%              Number of atoms          :   46 (  67 expanded)
%              Number of equality atoms :   38 (  53 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_28,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k4_xboole_0(B_20,A_19)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_435,plain,(
    ! [A_85,B_86,C_87] : k5_xboole_0(k5_xboole_0(A_85,B_86),C_87) = k5_xboole_0(A_85,k5_xboole_0(B_86,C_87)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1944,plain,(
    ! [A_151,B_152,C_153] : k5_xboole_0(k5_xboole_0(A_151,B_152),C_153) = k5_xboole_0(B_152,k5_xboole_0(A_151,C_153)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_435])).

tff(c_26,plain,(
    ! [A_17,B_18] : k5_xboole_0(k5_xboole_0(A_17,B_18),k3_xboole_0(A_17,B_18)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1993,plain,(
    ! [B_152,A_151] : k5_xboole_0(B_152,k5_xboole_0(A_151,k3_xboole_0(A_151,B_152))) = k2_xboole_0(A_151,B_152) ),
    inference(superposition,[status(thm),theory(equality)],[c_1944,c_26])).

tff(c_2145,plain,(
    ! [B_152,A_151] : k2_xboole_0(B_152,A_151) = k2_xboole_0(A_151,B_152) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_14,c_1993])).

tff(c_16,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [A_13] : k4_xboole_0(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_264,plain,(
    ! [A_76,B_77] : k5_xboole_0(A_76,k4_xboole_0(B_77,A_76)) = k2_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_285,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = k2_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_264])).

tff(c_309,plain,(
    ! [A_79] : k5_xboole_0(A_79,k1_xboole_0) = A_79 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_285])).

tff(c_329,plain,(
    ! [B_2] : k5_xboole_0(k1_xboole_0,B_2) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_309])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_132,plain,(
    ! [A_62,B_63] :
      ( k4_xboole_0(A_62,B_63) = k1_xboole_0
      | ~ r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_144,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_132])).

tff(c_18,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_203,plain,(
    ! [A_71,B_72] : k4_xboole_0(A_71,k4_xboole_0(A_71,B_72)) = k3_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_228,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k3_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_203])).

tff(c_240,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_228])).

tff(c_44,plain,(
    ! [A_49,B_50] : r1_tarski(k1_tarski(A_49),k2_tarski(A_49,B_50)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_143,plain,(
    ! [A_49,B_50] : k4_xboole_0(k1_tarski(A_49),k2_tarski(A_49,B_50)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_132])).

tff(c_573,plain,(
    ! [A_90,B_91] : k5_xboole_0(k5_xboole_0(A_90,B_91),k3_xboole_0(A_90,B_91)) = k2_xboole_0(A_90,B_91) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_13138,plain,(
    ! [A_266,B_267] : k5_xboole_0(k2_xboole_0(A_266,B_267),k3_xboole_0(A_266,k4_xboole_0(B_267,A_266))) = k2_xboole_0(A_266,k4_xboole_0(B_267,A_266)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_573])).

tff(c_13272,plain,(
    ! [A_49,B_50] : k5_xboole_0(k2_xboole_0(k2_tarski(A_49,B_50),k1_tarski(A_49)),k3_xboole_0(k2_tarski(A_49,B_50),k1_xboole_0)) = k2_xboole_0(k2_tarski(A_49,B_50),k4_xboole_0(k1_tarski(A_49),k2_tarski(A_49,B_50))) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_13138])).

tff(c_13310,plain,(
    ! [A_49,B_50] : k2_xboole_0(k1_tarski(A_49),k2_tarski(A_49,B_50)) = k2_tarski(A_49,B_50) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2145,c_329,c_2,c_240,c_16,c_143,c_13272])).

tff(c_46,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_15276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13310,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:50:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.93/3.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.95/3.60  
% 8.95/3.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.95/3.60  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 8.95/3.60  
% 8.95/3.60  %Foreground sorts:
% 8.95/3.60  
% 8.95/3.60  
% 8.95/3.60  %Background operators:
% 8.95/3.60  
% 8.95/3.60  
% 8.95/3.60  %Foreground operators:
% 8.95/3.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.95/3.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.95/3.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.95/3.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.95/3.60  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.95/3.60  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.95/3.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.95/3.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.95/3.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.95/3.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.95/3.60  tff('#skF_2', type, '#skF_2': $i).
% 8.95/3.60  tff('#skF_1', type, '#skF_1': $i).
% 8.95/3.60  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.95/3.60  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.95/3.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.95/3.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.95/3.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.95/3.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.95/3.60  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.95/3.60  
% 9.00/3.62  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 9.00/3.62  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.00/3.62  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 9.00/3.62  tff(f_49, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 9.00/3.62  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 9.00/3.62  tff(f_41, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 9.00/3.62  tff(f_47, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 9.00/3.62  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.00/3.62  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 9.00/3.62  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 9.00/3.62  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.00/3.62  tff(f_69, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 9.00/3.62  tff(f_72, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 9.00/3.62  tff(c_28, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k4_xboole_0(B_20, A_19))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.00/3.62  tff(c_14, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.00/3.62  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.00/3.62  tff(c_435, plain, (![A_85, B_86, C_87]: (k5_xboole_0(k5_xboole_0(A_85, B_86), C_87)=k5_xboole_0(A_85, k5_xboole_0(B_86, C_87)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.00/3.62  tff(c_1944, plain, (![A_151, B_152, C_153]: (k5_xboole_0(k5_xboole_0(A_151, B_152), C_153)=k5_xboole_0(B_152, k5_xboole_0(A_151, C_153)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_435])).
% 9.00/3.62  tff(c_26, plain, (![A_17, B_18]: (k5_xboole_0(k5_xboole_0(A_17, B_18), k3_xboole_0(A_17, B_18))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.00/3.62  tff(c_1993, plain, (![B_152, A_151]: (k5_xboole_0(B_152, k5_xboole_0(A_151, k3_xboole_0(A_151, B_152)))=k2_xboole_0(A_151, B_152))), inference(superposition, [status(thm), theory('equality')], [c_1944, c_26])).
% 9.00/3.62  tff(c_2145, plain, (![B_152, A_151]: (k2_xboole_0(B_152, A_151)=k2_xboole_0(A_151, B_152))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_14, c_1993])).
% 9.00/3.62  tff(c_16, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.00/3.62  tff(c_22, plain, (![A_13]: (k4_xboole_0(k1_xboole_0, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.00/3.62  tff(c_264, plain, (![A_76, B_77]: (k5_xboole_0(A_76, k4_xboole_0(B_77, A_76))=k2_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.00/3.62  tff(c_285, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=k2_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_264])).
% 9.00/3.62  tff(c_309, plain, (![A_79]: (k5_xboole_0(A_79, k1_xboole_0)=A_79)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_285])).
% 9.00/3.62  tff(c_329, plain, (![B_2]: (k5_xboole_0(k1_xboole_0, B_2)=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_309])).
% 9.00/3.62  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.00/3.62  tff(c_132, plain, (![A_62, B_63]: (k4_xboole_0(A_62, B_63)=k1_xboole_0 | ~r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.00/3.62  tff(c_144, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_132])).
% 9.00/3.62  tff(c_18, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.00/3.62  tff(c_203, plain, (![A_71, B_72]: (k4_xboole_0(A_71, k4_xboole_0(A_71, B_72))=k3_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.00/3.62  tff(c_228, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k3_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_203])).
% 9.00/3.62  tff(c_240, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_144, c_228])).
% 9.00/3.62  tff(c_44, plain, (![A_49, B_50]: (r1_tarski(k1_tarski(A_49), k2_tarski(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.00/3.62  tff(c_143, plain, (![A_49, B_50]: (k4_xboole_0(k1_tarski(A_49), k2_tarski(A_49, B_50))=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_132])).
% 9.00/3.62  tff(c_573, plain, (![A_90, B_91]: (k5_xboole_0(k5_xboole_0(A_90, B_91), k3_xboole_0(A_90, B_91))=k2_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.00/3.62  tff(c_13138, plain, (![A_266, B_267]: (k5_xboole_0(k2_xboole_0(A_266, B_267), k3_xboole_0(A_266, k4_xboole_0(B_267, A_266)))=k2_xboole_0(A_266, k4_xboole_0(B_267, A_266)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_573])).
% 9.00/3.62  tff(c_13272, plain, (![A_49, B_50]: (k5_xboole_0(k2_xboole_0(k2_tarski(A_49, B_50), k1_tarski(A_49)), k3_xboole_0(k2_tarski(A_49, B_50), k1_xboole_0))=k2_xboole_0(k2_tarski(A_49, B_50), k4_xboole_0(k1_tarski(A_49), k2_tarski(A_49, B_50))))), inference(superposition, [status(thm), theory('equality')], [c_143, c_13138])).
% 9.00/3.62  tff(c_13310, plain, (![A_49, B_50]: (k2_xboole_0(k1_tarski(A_49), k2_tarski(A_49, B_50))=k2_tarski(A_49, B_50))), inference(demodulation, [status(thm), theory('equality')], [c_2145, c_329, c_2, c_240, c_16, c_143, c_13272])).
% 9.00/3.62  tff(c_46, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.00/3.62  tff(c_15276, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13310, c_46])).
% 9.00/3.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.00/3.62  
% 9.00/3.62  Inference rules
% 9.00/3.62  ----------------------
% 9.00/3.62  #Ref     : 0
% 9.00/3.62  #Sup     : 3844
% 9.00/3.62  #Fact    : 0
% 9.00/3.62  #Define  : 0
% 9.00/3.62  #Split   : 0
% 9.00/3.62  #Chain   : 0
% 9.00/3.62  #Close   : 0
% 9.00/3.62  
% 9.00/3.62  Ordering : KBO
% 9.00/3.62  
% 9.00/3.62  Simplification rules
% 9.00/3.62  ----------------------
% 9.00/3.62  #Subsume      : 226
% 9.00/3.62  #Demod        : 4870
% 9.00/3.62  #Tautology    : 2024
% 9.00/3.62  #SimpNegUnit  : 0
% 9.00/3.62  #BackRed      : 2
% 9.00/3.62  
% 9.00/3.62  #Partial instantiations: 0
% 9.00/3.62  #Strategies tried      : 1
% 9.00/3.62  
% 9.00/3.62  Timing (in seconds)
% 9.00/3.62  ----------------------
% 9.00/3.62  Preprocessing        : 0.32
% 9.00/3.62  Parsing              : 0.17
% 9.00/3.62  CNF conversion       : 0.02
% 9.00/3.62  Main loop            : 2.55
% 9.00/3.62  Inferencing          : 0.51
% 9.00/3.62  Reduction            : 1.58
% 9.00/3.62  Demodulation         : 1.45
% 9.00/3.62  BG Simplification    : 0.08
% 9.00/3.62  Subsumption          : 0.29
% 9.00/3.62  Abstraction          : 0.12
% 9.00/3.62  MUC search           : 0.00
% 9.00/3.62  Cooper               : 0.00
% 9.00/3.62  Total                : 2.90
% 9.00/3.62  Index Insertion      : 0.00
% 9.00/3.62  Index Deletion       : 0.00
% 9.00/3.62  Index Matching       : 0.00
% 9.00/3.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
