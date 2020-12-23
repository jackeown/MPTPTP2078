%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:43 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 101 expanded)
%              Number of leaves         :   26 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   37 ( 102 expanded)
%              Number of equality atoms :   17 (  56 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_46,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_34,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_18,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_163,plain,(
    ! [A_46,B_47] :
      ( k2_xboole_0(A_46,B_47) = B_47
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_205,plain,(
    ! [A_49] : k2_xboole_0(k1_xboole_0,A_49) = A_49 ),
    inference(resolution,[status(thm)],[c_18,c_163])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_218,plain,(
    ! [A_49] : k2_xboole_0(A_49,k1_xboole_0) = A_49 ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_2])).

tff(c_46,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_70,plain,(
    ! [B_39,A_40] : k2_xboole_0(B_39,A_40) = k2_xboole_0(A_40,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_121,plain,(
    ! [A_41,B_42] : r1_tarski(A_41,k2_xboole_0(B_42,A_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_20])).

tff(c_130,plain,(
    r1_tarski('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_121])).

tff(c_182,plain,(
    k2_xboole_0('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_130,c_163])).

tff(c_313,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_182])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_321,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_8])).

tff(c_319,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_46])).

tff(c_314,plain,(
    ! [A_49] : k2_xboole_0(A_49,'#skF_6') = A_49 ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_218])).

tff(c_451,plain,(
    k2_tarski('#skF_4','#skF_5') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_314])).

tff(c_51,plain,(
    ! [D_31,B_32] : r2_hidden(D_31,k2_tarski(D_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_55,plain,(
    ! [D_31,B_32] : ~ v1_xboole_0(k2_tarski(D_31,B_32)) ),
    inference(resolution,[status(thm)],[c_51,c_4])).

tff(c_485,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_451,c_55])).

tff(c_496,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_485])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:31:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.24  
% 2.10/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.24  %$ r2_hidden > r1_tarski > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.10/1.24  
% 2.10/1.24  %Foreground sorts:
% 2.10/1.24  
% 2.10/1.24  
% 2.10/1.24  %Background operators:
% 2.10/1.24  
% 2.10/1.24  
% 2.10/1.24  %Foreground operators:
% 2.10/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.10/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.10/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.10/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.10/1.24  tff('#skF_5', type, '#skF_5': $i).
% 2.10/1.24  tff('#skF_6', type, '#skF_6': $i).
% 2.10/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.10/1.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.10/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.10/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.24  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.10/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.10/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.10/1.24  
% 2.10/1.25  tff(f_46, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.10/1.25  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.10/1.25  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.10/1.25  tff(f_67, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.10/1.25  tff(f_48, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.10/1.25  tff(f_34, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.10/1.25  tff(f_57, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.10/1.25  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.10/1.25  tff(c_18, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.10/1.25  tff(c_163, plain, (![A_46, B_47]: (k2_xboole_0(A_46, B_47)=B_47 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.10/1.25  tff(c_205, plain, (![A_49]: (k2_xboole_0(k1_xboole_0, A_49)=A_49)), inference(resolution, [status(thm)], [c_18, c_163])).
% 2.10/1.25  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.10/1.25  tff(c_218, plain, (![A_49]: (k2_xboole_0(A_49, k1_xboole_0)=A_49)), inference(superposition, [status(thm), theory('equality')], [c_205, c_2])).
% 2.10/1.25  tff(c_46, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.10/1.25  tff(c_70, plain, (![B_39, A_40]: (k2_xboole_0(B_39, A_40)=k2_xboole_0(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.10/1.25  tff(c_20, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.10/1.25  tff(c_121, plain, (![A_41, B_42]: (r1_tarski(A_41, k2_xboole_0(B_42, A_41)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_20])).
% 2.10/1.25  tff(c_130, plain, (r1_tarski('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_46, c_121])).
% 2.10/1.25  tff(c_182, plain, (k2_xboole_0('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_130, c_163])).
% 2.10/1.25  tff(c_313, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_218, c_182])).
% 2.10/1.25  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.10/1.25  tff(c_321, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_313, c_8])).
% 2.10/1.25  tff(c_319, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_313, c_46])).
% 2.10/1.25  tff(c_314, plain, (![A_49]: (k2_xboole_0(A_49, '#skF_6')=A_49)), inference(demodulation, [status(thm), theory('equality')], [c_313, c_218])).
% 2.10/1.25  tff(c_451, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_319, c_314])).
% 2.10/1.25  tff(c_51, plain, (![D_31, B_32]: (r2_hidden(D_31, k2_tarski(D_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.10/1.25  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.10/1.25  tff(c_55, plain, (![D_31, B_32]: (~v1_xboole_0(k2_tarski(D_31, B_32)))), inference(resolution, [status(thm)], [c_51, c_4])).
% 2.10/1.25  tff(c_485, plain, (~v1_xboole_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_451, c_55])).
% 2.10/1.25  tff(c_496, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_321, c_485])).
% 2.10/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.25  
% 2.10/1.25  Inference rules
% 2.10/1.25  ----------------------
% 2.10/1.25  #Ref     : 0
% 2.10/1.25  #Sup     : 108
% 2.10/1.25  #Fact    : 0
% 2.10/1.25  #Define  : 0
% 2.10/1.25  #Split   : 0
% 2.10/1.25  #Chain   : 0
% 2.10/1.25  #Close   : 0
% 2.10/1.25  
% 2.10/1.25  Ordering : KBO
% 2.10/1.25  
% 2.10/1.25  Simplification rules
% 2.10/1.25  ----------------------
% 2.10/1.25  #Subsume      : 1
% 2.10/1.25  #Demod        : 50
% 2.10/1.25  #Tautology    : 83
% 2.10/1.25  #SimpNegUnit  : 0
% 2.10/1.25  #BackRed      : 9
% 2.10/1.25  
% 2.10/1.25  #Partial instantiations: 0
% 2.10/1.25  #Strategies tried      : 1
% 2.10/1.25  
% 2.10/1.25  Timing (in seconds)
% 2.10/1.25  ----------------------
% 2.10/1.25  Preprocessing        : 0.30
% 2.10/1.25  Parsing              : 0.16
% 2.10/1.25  CNF conversion       : 0.02
% 2.10/1.25  Main loop            : 0.20
% 2.10/1.25  Inferencing          : 0.07
% 2.10/1.25  Reduction            : 0.08
% 2.10/1.25  Demodulation         : 0.06
% 2.10/1.25  BG Simplification    : 0.01
% 2.10/1.25  Subsumption          : 0.03
% 2.10/1.26  Abstraction          : 0.01
% 2.10/1.26  MUC search           : 0.00
% 2.10/1.26  Cooper               : 0.00
% 2.10/1.26  Total                : 0.52
% 2.10/1.26  Index Insertion      : 0.00
% 2.10/1.26  Index Deletion       : 0.00
% 2.10/1.26  Index Matching       : 0.00
% 2.10/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
