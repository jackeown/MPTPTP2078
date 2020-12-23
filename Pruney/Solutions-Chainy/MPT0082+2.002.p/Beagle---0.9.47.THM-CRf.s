%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:59 EST 2020

% Result     : Theorem 4.30s
% Output     : CNFRefutation 4.34s
% Verified   : 
% Statistics : Number of formulae       :   43 (  69 expanded)
%              Number of leaves         :   19 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :   39 (  67 expanded)
%              Number of equality atoms :   26 (  51 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k3_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_xboole_1)).

tff(c_242,plain,(
    ! [A_50,B_51] :
      ( r1_xboole_0(A_50,B_51)
      | k3_xboole_0(A_50,B_51) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_279,plain,(
    ! [B_55,A_56] :
      ( r1_xboole_0(B_55,A_56)
      | k3_xboole_0(A_56,B_55) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_242,c_8])).

tff(c_38,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_295,plain,(
    k3_xboole_0('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_279,c_38])).

tff(c_12,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_296,plain,(
    ! [A_57,B_58] : k4_xboole_0(A_57,k4_xboole_0(A_57,B_58)) = k3_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_311,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_296])).

tff(c_314,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_311])).

tff(c_10,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_877,plain,(
    ! [A_107,B_108,C_109] : k2_xboole_0(k4_xboole_0(A_107,B_108),k4_xboole_0(A_107,C_109)) = k4_xboole_0(A_107,k3_xboole_0(B_108,C_109)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_923,plain,(
    ! [A_9,B_108] : k4_xboole_0(A_9,k3_xboole_0(B_108,A_9)) = k2_xboole_0(k4_xboole_0(A_9,B_108),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_877])).

tff(c_945,plain,(
    ! [A_9,B_108] : k4_xboole_0(A_9,k3_xboole_0(B_108,A_9)) = k4_xboole_0(A_9,B_108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_923])).

tff(c_36,plain,(
    r1_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_178,plain,(
    ! [A_45,B_46] :
      ( k3_xboole_0(A_45,B_46) = k1_xboole_0
      | ~ r1_xboole_0(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_189,plain,(
    k3_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_178])).

tff(c_2968,plain,(
    ! [A_195,B_196] : k4_xboole_0(A_195,k3_xboole_0(B_196,A_195)) = k4_xboole_0(A_195,B_196) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_923])).

tff(c_3052,plain,(
    k4_xboole_0('#skF_2',k3_xboole_0('#skF_1','#skF_2')) = k4_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_2968])).

tff(c_3073,plain,(
    k4_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_945,c_14,c_3052])).

tff(c_16,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3107,plain,(
    k4_xboole_0('#skF_2','#skF_2') = k3_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3073,c_16])).

tff(c_3115,plain,(
    k3_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_3107])).

tff(c_3117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_295,c_3115])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.30/1.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.30/1.83  
% 4.30/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.30/1.83  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 4.30/1.83  
% 4.30/1.83  %Foreground sorts:
% 4.30/1.83  
% 4.30/1.83  
% 4.30/1.83  %Background operators:
% 4.30/1.83  
% 4.30/1.83  
% 4.30/1.83  %Foreground operators:
% 4.30/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.30/1.83  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.30/1.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.30/1.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.30/1.83  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.30/1.83  tff('#skF_2', type, '#skF_2': $i).
% 4.30/1.83  tff('#skF_1', type, '#skF_1': $i).
% 4.30/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.30/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.30/1.83  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.30/1.83  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.30/1.83  
% 4.34/1.84  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.34/1.84  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.34/1.84  tff(f_92, negated_conjecture, ~(![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 4.34/1.84  tff(f_39, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.34/1.84  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.34/1.84  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.34/1.84  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.34/1.84  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(A, k3_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_xboole_1)).
% 4.34/1.84  tff(c_242, plain, (![A_50, B_51]: (r1_xboole_0(A_50, B_51) | k3_xboole_0(A_50, B_51)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.34/1.84  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.34/1.84  tff(c_279, plain, (![B_55, A_56]: (r1_xboole_0(B_55, A_56) | k3_xboole_0(A_56, B_55)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_242, c_8])).
% 4.34/1.84  tff(c_38, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.34/1.84  tff(c_295, plain, (k3_xboole_0('#skF_2', '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_279, c_38])).
% 4.34/1.84  tff(c_12, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.34/1.84  tff(c_14, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.34/1.84  tff(c_296, plain, (![A_57, B_58]: (k4_xboole_0(A_57, k4_xboole_0(A_57, B_58))=k3_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.34/1.84  tff(c_311, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_296])).
% 4.34/1.84  tff(c_314, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_311])).
% 4.34/1.84  tff(c_10, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.34/1.84  tff(c_877, plain, (![A_107, B_108, C_109]: (k2_xboole_0(k4_xboole_0(A_107, B_108), k4_xboole_0(A_107, C_109))=k4_xboole_0(A_107, k3_xboole_0(B_108, C_109)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.34/1.84  tff(c_923, plain, (![A_9, B_108]: (k4_xboole_0(A_9, k3_xboole_0(B_108, A_9))=k2_xboole_0(k4_xboole_0(A_9, B_108), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_314, c_877])).
% 4.34/1.84  tff(c_945, plain, (![A_9, B_108]: (k4_xboole_0(A_9, k3_xboole_0(B_108, A_9))=k4_xboole_0(A_9, B_108))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_923])).
% 4.34/1.84  tff(c_36, plain, (r1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.34/1.84  tff(c_178, plain, (![A_45, B_46]: (k3_xboole_0(A_45, B_46)=k1_xboole_0 | ~r1_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.34/1.84  tff(c_189, plain, (k3_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_178])).
% 4.34/1.84  tff(c_2968, plain, (![A_195, B_196]: (k4_xboole_0(A_195, k3_xboole_0(B_196, A_195))=k4_xboole_0(A_195, B_196))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_923])).
% 4.34/1.84  tff(c_3052, plain, (k4_xboole_0('#skF_2', k3_xboole_0('#skF_1', '#skF_2'))=k4_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_189, c_2968])).
% 4.34/1.84  tff(c_3073, plain, (k4_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_945, c_14, c_3052])).
% 4.34/1.84  tff(c_16, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.34/1.84  tff(c_3107, plain, (k4_xboole_0('#skF_2', '#skF_2')=k3_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3073, c_16])).
% 4.34/1.84  tff(c_3115, plain, (k3_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_314, c_3107])).
% 4.34/1.84  tff(c_3117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_295, c_3115])).
% 4.34/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.34/1.84  
% 4.34/1.84  Inference rules
% 4.34/1.84  ----------------------
% 4.34/1.84  #Ref     : 0
% 4.34/1.84  #Sup     : 781
% 4.34/1.84  #Fact    : 0
% 4.34/1.84  #Define  : 0
% 4.34/1.84  #Split   : 0
% 4.34/1.84  #Chain   : 0
% 4.34/1.84  #Close   : 0
% 4.34/1.84  
% 4.34/1.84  Ordering : KBO
% 4.34/1.84  
% 4.34/1.84  Simplification rules
% 4.34/1.84  ----------------------
% 4.34/1.84  #Subsume      : 206
% 4.34/1.84  #Demod        : 381
% 4.34/1.84  #Tautology    : 345
% 4.34/1.84  #SimpNegUnit  : 5
% 4.34/1.84  #BackRed      : 0
% 4.34/1.84  
% 4.34/1.84  #Partial instantiations: 0
% 4.34/1.84  #Strategies tried      : 1
% 4.34/1.84  
% 4.34/1.84  Timing (in seconds)
% 4.34/1.84  ----------------------
% 4.34/1.84  Preprocessing        : 0.34
% 4.34/1.84  Parsing              : 0.18
% 4.34/1.84  CNF conversion       : 0.02
% 4.34/1.84  Main loop            : 0.65
% 4.34/1.84  Inferencing          : 0.22
% 4.34/1.84  Reduction            : 0.24
% 4.34/1.84  Demodulation         : 0.18
% 4.34/1.84  BG Simplification    : 0.03
% 4.34/1.84  Subsumption          : 0.13
% 4.34/1.84  Abstraction          : 0.03
% 4.34/1.84  MUC search           : 0.00
% 4.34/1.84  Cooper               : 0.00
% 4.34/1.84  Total                : 1.02
% 4.34/1.84  Index Insertion      : 0.00
% 4.34/1.84  Index Deletion       : 0.00
% 4.34/1.84  Index Matching       : 0.00
% 4.34/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
