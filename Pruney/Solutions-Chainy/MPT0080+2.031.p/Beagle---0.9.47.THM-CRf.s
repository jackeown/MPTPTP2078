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
% DateTime   : Thu Dec  3 09:43:53 EST 2020

% Result     : Theorem 7.51s
% Output     : CNFRefutation 7.51s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 150 expanded)
%              Number of leaves         :   20 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :   67 ( 186 expanded)
%              Number of equality atoms :   49 ( 120 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_74,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | k4_xboole_0(A_24,B_25) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_78,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_74,c_20])).

tff(c_22,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_61,plain,(
    ! [A_22,B_23] :
      ( k3_xboole_0(A_22,B_23) = k1_xboole_0
      | ~ r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_69,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_61])).

tff(c_14,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_79,plain,(
    ! [A_26,B_27] :
      ( k2_xboole_0(A_26,B_27) = B_27
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_92,plain,(
    ! [A_28,B_29] : k2_xboole_0(k4_xboole_0(A_28,B_29),A_28) = A_28 ),
    inference(resolution,[status(thm)],[c_14,c_79])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_98,plain,(
    ! [A_28,B_29] : k2_xboole_0(A_28,k4_xboole_0(A_28,B_29)) = A_28 ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_2])).

tff(c_18,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_560,plain,(
    ! [A_52,B_53] :
      ( k2_xboole_0(A_52,B_53) = B_53
      | k4_xboole_0(A_52,B_53) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_79])).

tff(c_581,plain,(
    ! [A_14,B_15] :
      ( k2_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15)
      | k3_xboole_0(A_14,B_15) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_560])).

tff(c_4788,plain,(
    ! [A_137,B_138] :
      ( k4_xboole_0(A_137,B_138) = A_137
      | k3_xboole_0(A_137,B_138) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_581])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] : k4_xboole_0(k4_xboole_0(A_11,B_12),C_13) = k4_xboole_0(A_11,k2_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_126,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_346,plain,(
    ! [A_41,B_42] : k4_xboole_0(k4_xboole_0(A_41,B_42),A_41) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_126])).

tff(c_595,plain,(
    ! [C_54,B_55] : k4_xboole_0(C_54,k2_xboole_0(B_55,C_54)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_346])).

tff(c_625,plain,(
    ! [C_54] : k2_xboole_0(C_54,k1_xboole_0) = C_54 ),
    inference(superposition,[status(thm),theory(equality)],[c_595,c_98])).

tff(c_24,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_25,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_24])).

tff(c_137,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_25,c_126])).

tff(c_274,plain,(
    ! [A_36,B_37,C_38] : k4_xboole_0(k4_xboole_0(A_36,B_37),C_38) = k4_xboole_0(A_36,k2_xboole_0(B_37,C_38)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_287,plain,(
    ! [A_36,B_37,B_15] : k4_xboole_0(A_36,k2_xboole_0(B_37,k4_xboole_0(k4_xboole_0(A_36,B_37),B_15))) = k3_xboole_0(k4_xboole_0(A_36,B_37),B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_18])).

tff(c_1672,plain,(
    ! [A_79,B_80,B_81] : k4_xboole_0(A_79,k2_xboole_0(B_80,k4_xboole_0(A_79,k2_xboole_0(B_80,B_81)))) = k3_xboole_0(k4_xboole_0(A_79,B_80),B_81) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_287])).

tff(c_1804,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3',k1_xboole_0)) = k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_1672])).

tff(c_1843,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = k4_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_1804])).

tff(c_4865,plain,
    ( k4_xboole_0('#skF_1','#skF_3') = k3_xboole_0('#skF_1','#skF_2')
    | k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4788,c_1843])).

tff(c_5078,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_4865])).

tff(c_592,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = A_14
      | k3_xboole_0(A_14,B_15) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_581])).

tff(c_5112,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5078,c_592])).

tff(c_5175,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_5112])).

tff(c_1411,plain,(
    ! [A_74,B_75,C_76] : k4_xboole_0(A_74,k2_xboole_0(k4_xboole_0(A_74,B_75),C_76)) = k4_xboole_0(k3_xboole_0(A_74,B_75),C_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_274])).

tff(c_13415,plain,(
    ! [A_213,A_214,B_215] : k4_xboole_0(A_213,k2_xboole_0(A_214,k4_xboole_0(A_213,B_215))) = k4_xboole_0(k3_xboole_0(A_213,B_215),A_214) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1411])).

tff(c_10129,plain,(
    ! [A_191,B_192] : k4_xboole_0(k4_xboole_0(A_191,B_192),k1_xboole_0) = k3_xboole_0(k4_xboole_0(A_191,B_192),A_191) ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_18])).

tff(c_390,plain,(
    ! [A_14,B_15] : k4_xboole_0(k3_xboole_0(A_14,B_15),A_14) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_346])).

tff(c_10281,plain,(
    ! [A_191,B_192] : k4_xboole_0(k4_xboole_0(k4_xboole_0(A_191,B_192),k1_xboole_0),k4_xboole_0(A_191,B_192)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10129,c_390])).

tff(c_10516,plain,(
    ! [A_191,B_192] : k4_xboole_0(A_191,k2_xboole_0(B_192,k4_xboole_0(A_191,B_192))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_16,c_16,c_10281])).

tff(c_13835,plain,(
    ! [A_216,B_217] : k4_xboole_0(k3_xboole_0(A_216,B_217),B_217) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_13415,c_10516])).

tff(c_14053,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5175,c_13835])).

tff(c_14135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_14053])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:37:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.51/2.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.51/2.82  
% 7.51/2.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.51/2.82  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.51/2.82  
% 7.51/2.82  %Foreground sorts:
% 7.51/2.82  
% 7.51/2.82  
% 7.51/2.82  %Background operators:
% 7.51/2.82  
% 7.51/2.82  
% 7.51/2.82  %Foreground operators:
% 7.51/2.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.51/2.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.51/2.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.51/2.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.51/2.82  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.51/2.82  tff('#skF_2', type, '#skF_2': $i).
% 7.51/2.82  tff('#skF_3', type, '#skF_3': $i).
% 7.51/2.82  tff('#skF_1', type, '#skF_1': $i).
% 7.51/2.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.51/2.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.51/2.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.51/2.82  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.51/2.82  
% 7.51/2.84  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.51/2.84  tff(f_52, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 7.51/2.84  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.51/2.84  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.51/2.84  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.51/2.84  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 7.51/2.84  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.51/2.84  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 7.51/2.84  tff(c_74, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | k4_xboole_0(A_24, B_25)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.51/2.84  tff(c_20, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.51/2.84  tff(c_78, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_74, c_20])).
% 7.51/2.84  tff(c_22, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.51/2.84  tff(c_61, plain, (![A_22, B_23]: (k3_xboole_0(A_22, B_23)=k1_xboole_0 | ~r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.51/2.84  tff(c_69, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_61])).
% 7.51/2.84  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.51/2.84  tff(c_79, plain, (![A_26, B_27]: (k2_xboole_0(A_26, B_27)=B_27 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.51/2.84  tff(c_92, plain, (![A_28, B_29]: (k2_xboole_0(k4_xboole_0(A_28, B_29), A_28)=A_28)), inference(resolution, [status(thm)], [c_14, c_79])).
% 7.51/2.84  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.51/2.84  tff(c_98, plain, (![A_28, B_29]: (k2_xboole_0(A_28, k4_xboole_0(A_28, B_29))=A_28)), inference(superposition, [status(thm), theory('equality')], [c_92, c_2])).
% 7.51/2.84  tff(c_18, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.51/2.84  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.51/2.84  tff(c_560, plain, (![A_52, B_53]: (k2_xboole_0(A_52, B_53)=B_53 | k4_xboole_0(A_52, B_53)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_79])).
% 7.51/2.84  tff(c_581, plain, (![A_14, B_15]: (k2_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15) | k3_xboole_0(A_14, B_15)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_560])).
% 7.51/2.84  tff(c_4788, plain, (![A_137, B_138]: (k4_xboole_0(A_137, B_138)=A_137 | k3_xboole_0(A_137, B_138)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_98, c_581])).
% 7.51/2.84  tff(c_16, plain, (![A_11, B_12, C_13]: (k4_xboole_0(k4_xboole_0(A_11, B_12), C_13)=k4_xboole_0(A_11, k2_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.51/2.84  tff(c_126, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=k1_xboole_0 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.51/2.84  tff(c_346, plain, (![A_41, B_42]: (k4_xboole_0(k4_xboole_0(A_41, B_42), A_41)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_126])).
% 7.51/2.84  tff(c_595, plain, (![C_54, B_55]: (k4_xboole_0(C_54, k2_xboole_0(B_55, C_54))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_346])).
% 7.51/2.84  tff(c_625, plain, (![C_54]: (k2_xboole_0(C_54, k1_xboole_0)=C_54)), inference(superposition, [status(thm), theory('equality')], [c_595, c_98])).
% 7.51/2.84  tff(c_24, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.51/2.84  tff(c_25, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_24])).
% 7.51/2.84  tff(c_137, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_25, c_126])).
% 7.51/2.84  tff(c_274, plain, (![A_36, B_37, C_38]: (k4_xboole_0(k4_xboole_0(A_36, B_37), C_38)=k4_xboole_0(A_36, k2_xboole_0(B_37, C_38)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.51/2.84  tff(c_287, plain, (![A_36, B_37, B_15]: (k4_xboole_0(A_36, k2_xboole_0(B_37, k4_xboole_0(k4_xboole_0(A_36, B_37), B_15)))=k3_xboole_0(k4_xboole_0(A_36, B_37), B_15))), inference(superposition, [status(thm), theory('equality')], [c_274, c_18])).
% 7.51/2.84  tff(c_1672, plain, (![A_79, B_80, B_81]: (k4_xboole_0(A_79, k2_xboole_0(B_80, k4_xboole_0(A_79, k2_xboole_0(B_80, B_81))))=k3_xboole_0(k4_xboole_0(A_79, B_80), B_81))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_287])).
% 7.51/2.84  tff(c_1804, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', k1_xboole_0))=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_137, c_1672])).
% 7.51/2.84  tff(c_1843, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k4_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_625, c_1804])).
% 7.51/2.84  tff(c_4865, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_xboole_0('#skF_1', '#skF_2') | k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4788, c_1843])).
% 7.51/2.84  tff(c_5078, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_4865])).
% 7.51/2.84  tff(c_592, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=A_14 | k3_xboole_0(A_14, B_15)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_98, c_581])).
% 7.51/2.84  tff(c_5112, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5078, c_592])).
% 7.51/2.84  tff(c_5175, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_69, c_5112])).
% 7.51/2.84  tff(c_1411, plain, (![A_74, B_75, C_76]: (k4_xboole_0(A_74, k2_xboole_0(k4_xboole_0(A_74, B_75), C_76))=k4_xboole_0(k3_xboole_0(A_74, B_75), C_76))), inference(superposition, [status(thm), theory('equality')], [c_18, c_274])).
% 7.51/2.84  tff(c_13415, plain, (![A_213, A_214, B_215]: (k4_xboole_0(A_213, k2_xboole_0(A_214, k4_xboole_0(A_213, B_215)))=k4_xboole_0(k3_xboole_0(A_213, B_215), A_214))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1411])).
% 7.51/2.84  tff(c_10129, plain, (![A_191, B_192]: (k4_xboole_0(k4_xboole_0(A_191, B_192), k1_xboole_0)=k3_xboole_0(k4_xboole_0(A_191, B_192), A_191))), inference(superposition, [status(thm), theory('equality')], [c_346, c_18])).
% 7.51/2.84  tff(c_390, plain, (![A_14, B_15]: (k4_xboole_0(k3_xboole_0(A_14, B_15), A_14)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_346])).
% 7.51/2.84  tff(c_10281, plain, (![A_191, B_192]: (k4_xboole_0(k4_xboole_0(k4_xboole_0(A_191, B_192), k1_xboole_0), k4_xboole_0(A_191, B_192))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10129, c_390])).
% 7.51/2.84  tff(c_10516, plain, (![A_191, B_192]: (k4_xboole_0(A_191, k2_xboole_0(B_192, k4_xboole_0(A_191, B_192)))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_625, c_16, c_16, c_10281])).
% 7.51/2.84  tff(c_13835, plain, (![A_216, B_217]: (k4_xboole_0(k3_xboole_0(A_216, B_217), B_217)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13415, c_10516])).
% 7.51/2.84  tff(c_14053, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5175, c_13835])).
% 7.51/2.84  tff(c_14135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_14053])).
% 7.51/2.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.51/2.84  
% 7.51/2.84  Inference rules
% 7.51/2.84  ----------------------
% 7.51/2.84  #Ref     : 0
% 7.51/2.84  #Sup     : 3522
% 7.51/2.84  #Fact    : 0
% 7.51/2.84  #Define  : 0
% 7.51/2.84  #Split   : 3
% 7.51/2.84  #Chain   : 0
% 7.51/2.84  #Close   : 0
% 7.51/2.84  
% 7.51/2.84  Ordering : KBO
% 7.51/2.84  
% 7.51/2.84  Simplification rules
% 7.51/2.84  ----------------------
% 7.51/2.84  #Subsume      : 40
% 7.51/2.84  #Demod        : 3962
% 7.51/2.84  #Tautology    : 2448
% 7.51/2.84  #SimpNegUnit  : 11
% 7.51/2.84  #BackRed      : 27
% 7.51/2.84  
% 7.51/2.84  #Partial instantiations: 0
% 7.51/2.84  #Strategies tried      : 1
% 7.51/2.84  
% 7.51/2.84  Timing (in seconds)
% 7.51/2.84  ----------------------
% 7.51/2.84  Preprocessing        : 0.28
% 7.51/2.84  Parsing              : 0.16
% 7.51/2.84  CNF conversion       : 0.02
% 7.51/2.84  Main loop            : 1.77
% 7.51/2.84  Inferencing          : 0.44
% 7.51/2.84  Reduction            : 0.92
% 7.51/2.84  Demodulation         : 0.78
% 7.51/2.84  BG Simplification    : 0.05
% 7.51/2.84  Subsumption          : 0.25
% 7.51/2.84  Abstraction          : 0.08
% 7.51/2.84  MUC search           : 0.00
% 7.51/2.84  Cooper               : 0.00
% 7.51/2.84  Total                : 2.08
% 7.51/2.84  Index Insertion      : 0.00
% 7.51/2.84  Index Deletion       : 0.00
% 7.51/2.84  Index Matching       : 0.00
% 7.51/2.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
