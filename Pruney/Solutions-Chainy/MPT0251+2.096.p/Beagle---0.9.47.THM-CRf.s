%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:59 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :   47 (  49 expanded)
%              Number of leaves         :   28 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   35 (  38 expanded)
%              Number of equality atoms :   22 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(c_38,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_107,plain,(
    ! [B_51,A_52] : k5_xboole_0(B_51,A_52) = k5_xboole_0(A_52,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_123,plain,(
    ! [A_52] : k5_xboole_0(k1_xboole_0,A_52) = A_52 ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_8])).

tff(c_12,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_473,plain,(
    ! [A_76,B_77,C_78] : k5_xboole_0(k5_xboole_0(A_76,B_77),C_78) = k5_xboole_0(A_76,k5_xboole_0(B_77,C_78)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_554,plain,(
    ! [A_11,C_78] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_78)) = k5_xboole_0(k1_xboole_0,C_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_473])).

tff(c_574,plain,(
    ! [A_11,C_78] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_78)) = C_78 ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_554])).

tff(c_32,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(k1_tarski(A_42),B_43)
      | ~ r2_hidden(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_239,plain,(
    ! [A_61,B_62] :
      ( k3_xboole_0(A_61,B_62) = A_61
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_243,plain,(
    ! [A_42,B_43] :
      ( k3_xboole_0(k1_tarski(A_42),B_43) = k1_tarski(A_42)
      | ~ r2_hidden(A_42,B_43) ) ),
    inference(resolution,[status(thm)],[c_32,c_239])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_285,plain,(
    ! [A_70,B_71] : k5_xboole_0(k5_xboole_0(A_70,B_71),k3_xboole_0(A_70,B_71)) = k2_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1658,plain,(
    ! [A_120,B_121] : k5_xboole_0(k3_xboole_0(A_120,B_121),k5_xboole_0(A_120,B_121)) = k2_xboole_0(A_120,B_121) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_285])).

tff(c_1745,plain,(
    ! [A_42,B_43] :
      ( k5_xboole_0(k1_tarski(A_42),k5_xboole_0(k1_tarski(A_42),B_43)) = k2_xboole_0(k1_tarski(A_42),B_43)
      | ~ r2_hidden(A_42,B_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_1658])).

tff(c_1779,plain,(
    ! [A_122,B_123] :
      ( k2_xboole_0(k1_tarski(A_122),B_123) = B_123
      | ~ r2_hidden(A_122,B_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_574,c_1745])).

tff(c_36,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1813,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1779,c_36])).

tff(c_1834,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1813])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:00:08 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.38/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.51  
% 3.38/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.51  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.38/1.51  
% 3.38/1.51  %Foreground sorts:
% 3.38/1.51  
% 3.38/1.51  
% 3.38/1.51  %Background operators:
% 3.38/1.51  
% 3.38/1.51  
% 3.38/1.51  %Foreground operators:
% 3.38/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.38/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.38/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.38/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.38/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.38/1.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.38/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.38/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.38/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.38/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.38/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.38/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.38/1.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.38/1.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.38/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.38/1.51  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.38/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.38/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.38/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.38/1.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.38/1.51  
% 3.38/1.52  tff(f_66, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.38/1.52  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.38/1.52  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.38/1.52  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.38/1.52  tff(f_37, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.38/1.52  tff(f_59, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.38/1.52  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.38/1.52  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 3.38/1.52  tff(c_38, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.38/1.52  tff(c_107, plain, (![B_51, A_52]: (k5_xboole_0(B_51, A_52)=k5_xboole_0(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.38/1.52  tff(c_8, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.38/1.52  tff(c_123, plain, (![A_52]: (k5_xboole_0(k1_xboole_0, A_52)=A_52)), inference(superposition, [status(thm), theory('equality')], [c_107, c_8])).
% 3.38/1.52  tff(c_12, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.38/1.52  tff(c_473, plain, (![A_76, B_77, C_78]: (k5_xboole_0(k5_xboole_0(A_76, B_77), C_78)=k5_xboole_0(A_76, k5_xboole_0(B_77, C_78)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.38/1.52  tff(c_554, plain, (![A_11, C_78]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_78))=k5_xboole_0(k1_xboole_0, C_78))), inference(superposition, [status(thm), theory('equality')], [c_12, c_473])).
% 3.38/1.52  tff(c_574, plain, (![A_11, C_78]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_78))=C_78)), inference(demodulation, [status(thm), theory('equality')], [c_123, c_554])).
% 3.38/1.52  tff(c_32, plain, (![A_42, B_43]: (r1_tarski(k1_tarski(A_42), B_43) | ~r2_hidden(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.38/1.52  tff(c_239, plain, (![A_61, B_62]: (k3_xboole_0(A_61, B_62)=A_61 | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.38/1.52  tff(c_243, plain, (![A_42, B_43]: (k3_xboole_0(k1_tarski(A_42), B_43)=k1_tarski(A_42) | ~r2_hidden(A_42, B_43))), inference(resolution, [status(thm)], [c_32, c_239])).
% 3.38/1.52  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.38/1.52  tff(c_285, plain, (![A_70, B_71]: (k5_xboole_0(k5_xboole_0(A_70, B_71), k3_xboole_0(A_70, B_71))=k2_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.38/1.52  tff(c_1658, plain, (![A_120, B_121]: (k5_xboole_0(k3_xboole_0(A_120, B_121), k5_xboole_0(A_120, B_121))=k2_xboole_0(A_120, B_121))), inference(superposition, [status(thm), theory('equality')], [c_4, c_285])).
% 3.38/1.52  tff(c_1745, plain, (![A_42, B_43]: (k5_xboole_0(k1_tarski(A_42), k5_xboole_0(k1_tarski(A_42), B_43))=k2_xboole_0(k1_tarski(A_42), B_43) | ~r2_hidden(A_42, B_43))), inference(superposition, [status(thm), theory('equality')], [c_243, c_1658])).
% 3.38/1.52  tff(c_1779, plain, (![A_122, B_123]: (k2_xboole_0(k1_tarski(A_122), B_123)=B_123 | ~r2_hidden(A_122, B_123))), inference(demodulation, [status(thm), theory('equality')], [c_574, c_1745])).
% 3.38/1.52  tff(c_36, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.38/1.52  tff(c_1813, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1779, c_36])).
% 3.38/1.52  tff(c_1834, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_1813])).
% 3.38/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.52  
% 3.38/1.52  Inference rules
% 3.38/1.52  ----------------------
% 3.38/1.52  #Ref     : 0
% 3.38/1.52  #Sup     : 448
% 3.38/1.52  #Fact    : 0
% 3.38/1.52  #Define  : 0
% 3.38/1.52  #Split   : 0
% 3.38/1.52  #Chain   : 0
% 3.38/1.52  #Close   : 0
% 3.38/1.52  
% 3.38/1.52  Ordering : KBO
% 3.38/1.52  
% 3.38/1.52  Simplification rules
% 3.38/1.52  ----------------------
% 3.38/1.52  #Subsume      : 15
% 3.38/1.52  #Demod        : 194
% 3.38/1.52  #Tautology    : 237
% 3.38/1.52  #SimpNegUnit  : 0
% 3.38/1.52  #BackRed      : 1
% 3.38/1.52  
% 3.38/1.52  #Partial instantiations: 0
% 3.38/1.52  #Strategies tried      : 1
% 3.38/1.52  
% 3.38/1.52  Timing (in seconds)
% 3.38/1.52  ----------------------
% 3.51/1.53  Preprocessing        : 0.32
% 3.51/1.53  Parsing              : 0.18
% 3.51/1.53  CNF conversion       : 0.02
% 3.51/1.53  Main loop            : 0.46
% 3.51/1.53  Inferencing          : 0.15
% 3.51/1.53  Reduction            : 0.19
% 3.51/1.53  Demodulation         : 0.16
% 3.51/1.53  BG Simplification    : 0.02
% 3.51/1.53  Subsumption          : 0.07
% 3.51/1.53  Abstraction          : 0.03
% 3.51/1.53  MUC search           : 0.00
% 3.51/1.53  Cooper               : 0.00
% 3.51/1.53  Total                : 0.80
% 3.51/1.53  Index Insertion      : 0.00
% 3.51/1.53  Index Deletion       : 0.00
% 3.51/1.53  Index Matching       : 0.00
% 3.51/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
