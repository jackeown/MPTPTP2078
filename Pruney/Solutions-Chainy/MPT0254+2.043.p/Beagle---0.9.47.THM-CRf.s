%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:25 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   44 (  70 expanded)
%              Number of leaves         :   25 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   36 (  70 expanded)
%              Number of equality atoms :   23 (  57 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_61,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_63,plain,(
    ! [B_30,A_31] : k2_xboole_0(B_30,A_31) = k2_xboole_0(A_31,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_78,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_38])).

tff(c_152,plain,(
    ! [A_35,B_36] :
      ( k1_xboole_0 = A_35
      | k2_xboole_0(A_35,B_36) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_168,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_152])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_115,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k2_xboole_0(A_32,B_33)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_134,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_115])).

tff(c_179,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_134])).

tff(c_493,plain,(
    ! [A_65,B_66] :
      ( r1_xboole_0(A_65,B_66)
      | k4_xboole_0(A_65,B_66) != A_65 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_169,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_152])).

tff(c_188,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_169])).

tff(c_20,plain,(
    ! [C_18] : r2_hidden(C_18,k1_tarski(C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_195,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_20])).

tff(c_476,plain,(
    ! [A_62,B_63] :
      ( ~ r2_hidden(A_62,B_63)
      | ~ r1_xboole_0(k1_tarski(A_62),B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_481,plain,(
    ! [B_64] :
      ( ~ r2_hidden('#skF_3',B_64)
      | ~ r1_xboole_0('#skF_4',B_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_476])).

tff(c_489,plain,(
    ~ r1_xboole_0('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_195,c_481])).

tff(c_496,plain,(
    k4_xboole_0('#skF_4','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_493,c_489])).

tff(c_507,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_496])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:44:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.35  
% 2.21/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.36  %$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.21/1.36  
% 2.21/1.36  %Foreground sorts:
% 2.21/1.36  
% 2.21/1.36  
% 2.21/1.36  %Background operators:
% 2.21/1.36  
% 2.21/1.36  
% 2.21/1.36  %Foreground operators:
% 2.21/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.21/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.21/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.21/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.21/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.21/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.21/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.21/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.21/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.21/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.21/1.36  
% 2.39/1.37  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.39/1.37  tff(f_67, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.39/1.37  tff(f_37, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_xboole_1)).
% 2.39/1.37  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.39/1.37  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.39/1.37  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.39/1.37  tff(f_52, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.39/1.37  tff(f_61, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.39/1.37  tff(c_63, plain, (![B_30, A_31]: (k2_xboole_0(B_30, A_31)=k2_xboole_0(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.39/1.37  tff(c_38, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.39/1.37  tff(c_78, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_63, c_38])).
% 2.39/1.37  tff(c_152, plain, (![A_35, B_36]: (k1_xboole_0=A_35 | k2_xboole_0(A_35, B_36)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.39/1.37  tff(c_168, plain, (k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_78, c_152])).
% 2.39/1.37  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.39/1.37  tff(c_115, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k2_xboole_0(A_32, B_33))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.39/1.37  tff(c_134, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_115])).
% 2.39/1.37  tff(c_179, plain, (![A_3]: (k4_xboole_0(A_3, A_3)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_134])).
% 2.39/1.37  tff(c_493, plain, (![A_65, B_66]: (r1_xboole_0(A_65, B_66) | k4_xboole_0(A_65, B_66)!=A_65)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.39/1.37  tff(c_169, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_38, c_152])).
% 2.39/1.37  tff(c_188, plain, (k1_tarski('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_168, c_169])).
% 2.39/1.37  tff(c_20, plain, (![C_18]: (r2_hidden(C_18, k1_tarski(C_18)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.39/1.37  tff(c_195, plain, (r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_188, c_20])).
% 2.39/1.37  tff(c_476, plain, (![A_62, B_63]: (~r2_hidden(A_62, B_63) | ~r1_xboole_0(k1_tarski(A_62), B_63))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.39/1.37  tff(c_481, plain, (![B_64]: (~r2_hidden('#skF_3', B_64) | ~r1_xboole_0('#skF_4', B_64))), inference(superposition, [status(thm), theory('equality')], [c_188, c_476])).
% 2.39/1.37  tff(c_489, plain, (~r1_xboole_0('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_195, c_481])).
% 2.39/1.37  tff(c_496, plain, (k4_xboole_0('#skF_4', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_493, c_489])).
% 2.39/1.37  tff(c_507, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_179, c_496])).
% 2.39/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.37  
% 2.39/1.37  Inference rules
% 2.39/1.37  ----------------------
% 2.39/1.37  #Ref     : 0
% 2.39/1.37  #Sup     : 119
% 2.39/1.37  #Fact    : 0
% 2.39/1.37  #Define  : 0
% 2.39/1.37  #Split   : 0
% 2.39/1.37  #Chain   : 0
% 2.39/1.37  #Close   : 0
% 2.39/1.37  
% 2.39/1.37  Ordering : KBO
% 2.39/1.37  
% 2.39/1.37  Simplification rules
% 2.39/1.37  ----------------------
% 2.39/1.37  #Subsume      : 6
% 2.39/1.37  #Demod        : 48
% 2.39/1.37  #Tautology    : 97
% 2.39/1.37  #SimpNegUnit  : 0
% 2.39/1.37  #BackRed      : 8
% 2.39/1.37  
% 2.39/1.37  #Partial instantiations: 0
% 2.39/1.37  #Strategies tried      : 1
% 2.39/1.37  
% 2.39/1.37  Timing (in seconds)
% 2.39/1.37  ----------------------
% 2.39/1.37  Preprocessing        : 0.33
% 2.39/1.37  Parsing              : 0.17
% 2.39/1.37  CNF conversion       : 0.02
% 2.39/1.37  Main loop            : 0.22
% 2.39/1.37  Inferencing          : 0.08
% 2.39/1.37  Reduction            : 0.08
% 2.39/1.37  Demodulation         : 0.06
% 2.39/1.37  BG Simplification    : 0.01
% 2.39/1.37  Subsumption          : 0.04
% 2.39/1.37  Abstraction          : 0.01
% 2.39/1.37  MUC search           : 0.00
% 2.39/1.37  Cooper               : 0.00
% 2.39/1.37  Total                : 0.58
% 2.39/1.37  Index Insertion      : 0.00
% 2.39/1.37  Index Deletion       : 0.00
% 2.39/1.37  Index Matching       : 0.00
% 2.39/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
