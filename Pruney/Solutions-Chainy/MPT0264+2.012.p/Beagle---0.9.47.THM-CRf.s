%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:22 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   43 (  48 expanded)
%              Number of leaves         :   26 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   47 (  61 expanded)
%              Number of equality atoms :   17 (  27 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_6 > #skF_7 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k3_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
          & r2_hidden(B,C)
          & A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_46,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_72,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_84,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_86,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_62,plain,(
    ! [D_26,A_21] : r2_hidden(D_26,k2_tarski(A_21,D_26)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_88,plain,(
    k3_xboole_0(k2_tarski('#skF_7','#skF_8'),'#skF_9') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_34,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_297,plain,(
    ! [A_73,C_74,B_75] :
      ( r2_hidden(A_73,C_74)
      | ~ r2_hidden(A_73,B_75)
      | r2_hidden(A_73,k5_xboole_0(B_75,C_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_470,plain,(
    ! [A_108,A_109,B_110] :
      ( r2_hidden(A_108,k3_xboole_0(A_109,B_110))
      | ~ r2_hidden(A_108,A_109)
      | r2_hidden(A_108,k4_xboole_0(A_109,B_110)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_297])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_488,plain,(
    ! [A_111,B_112,A_113] :
      ( ~ r2_hidden(A_111,B_112)
      | r2_hidden(A_111,k3_xboole_0(A_113,B_112))
      | ~ r2_hidden(A_111,A_113) ) ),
    inference(resolution,[status(thm)],[c_470,c_6])).

tff(c_540,plain,(
    ! [A_117] :
      ( ~ r2_hidden(A_117,'#skF_9')
      | r2_hidden(A_117,k1_tarski('#skF_7'))
      | ~ r2_hidden(A_117,k2_tarski('#skF_7','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_488])).

tff(c_547,plain,
    ( ~ r2_hidden('#skF_8','#skF_9')
    | r2_hidden('#skF_8',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_62,c_540])).

tff(c_555,plain,(
    r2_hidden('#skF_8',k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_547])).

tff(c_78,plain,(
    ! [A_27] : k2_tarski(A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_259,plain,(
    ! [D_65,B_66,A_67] :
      ( D_65 = B_66
      | D_65 = A_67
      | ~ r2_hidden(D_65,k2_tarski(A_67,B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_268,plain,(
    ! [D_65,A_27] :
      ( D_65 = A_27
      | D_65 = A_27
      | ~ r2_hidden(D_65,k1_tarski(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_259])).

tff(c_567,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_555,c_268])).

tff(c_577,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_84,c_567])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:37:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.37  
% 2.74/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.37  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_6 > #skF_7 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 2.74/1.37  
% 2.74/1.37  %Foreground sorts:
% 2.74/1.37  
% 2.74/1.37  
% 2.74/1.37  %Background operators:
% 2.74/1.37  
% 2.74/1.37  
% 2.74/1.37  %Foreground operators:
% 2.74/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.74/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.74/1.37  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.74/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.74/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.74/1.37  tff('#skF_7', type, '#skF_7': $i).
% 2.74/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.74/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.74/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.74/1.37  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.74/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.74/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.74/1.37  tff('#skF_9', type, '#skF_9': $i).
% 2.74/1.37  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.74/1.37  tff('#skF_8', type, '#skF_8': $i).
% 2.74/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.74/1.37  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.74/1.37  
% 2.74/1.38  tff(f_85, negated_conjecture, ~(![A, B, C]: ~(((k3_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) & r2_hidden(B, C)) & ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_zfmisc_1)).
% 2.74/1.38  tff(f_70, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.74/1.38  tff(f_46, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.74/1.38  tff(f_44, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.74/1.38  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.74/1.38  tff(f_72, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.74/1.38  tff(c_84, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.74/1.38  tff(c_86, plain, (r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.74/1.38  tff(c_62, plain, (![D_26, A_21]: (r2_hidden(D_26, k2_tarski(A_21, D_26)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.74/1.38  tff(c_88, plain, (k3_xboole_0(k2_tarski('#skF_7', '#skF_8'), '#skF_9')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.74/1.38  tff(c_34, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.74/1.38  tff(c_297, plain, (![A_73, C_74, B_75]: (r2_hidden(A_73, C_74) | ~r2_hidden(A_73, B_75) | r2_hidden(A_73, k5_xboole_0(B_75, C_74)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.74/1.38  tff(c_470, plain, (![A_108, A_109, B_110]: (r2_hidden(A_108, k3_xboole_0(A_109, B_110)) | ~r2_hidden(A_108, A_109) | r2_hidden(A_108, k4_xboole_0(A_109, B_110)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_297])).
% 2.74/1.38  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.74/1.38  tff(c_488, plain, (![A_111, B_112, A_113]: (~r2_hidden(A_111, B_112) | r2_hidden(A_111, k3_xboole_0(A_113, B_112)) | ~r2_hidden(A_111, A_113))), inference(resolution, [status(thm)], [c_470, c_6])).
% 2.74/1.38  tff(c_540, plain, (![A_117]: (~r2_hidden(A_117, '#skF_9') | r2_hidden(A_117, k1_tarski('#skF_7')) | ~r2_hidden(A_117, k2_tarski('#skF_7', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_88, c_488])).
% 2.74/1.38  tff(c_547, plain, (~r2_hidden('#skF_8', '#skF_9') | r2_hidden('#skF_8', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_62, c_540])).
% 2.74/1.38  tff(c_555, plain, (r2_hidden('#skF_8', k1_tarski('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_547])).
% 2.74/1.38  tff(c_78, plain, (![A_27]: (k2_tarski(A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.74/1.38  tff(c_259, plain, (![D_65, B_66, A_67]: (D_65=B_66 | D_65=A_67 | ~r2_hidden(D_65, k2_tarski(A_67, B_66)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.74/1.38  tff(c_268, plain, (![D_65, A_27]: (D_65=A_27 | D_65=A_27 | ~r2_hidden(D_65, k1_tarski(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_78, c_259])).
% 2.74/1.38  tff(c_567, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_555, c_268])).
% 2.74/1.38  tff(c_577, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_84, c_567])).
% 2.74/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.38  
% 2.74/1.38  Inference rules
% 2.74/1.38  ----------------------
% 2.74/1.38  #Ref     : 0
% 2.74/1.38  #Sup     : 119
% 2.74/1.38  #Fact    : 0
% 2.74/1.38  #Define  : 0
% 2.74/1.38  #Split   : 0
% 2.74/1.38  #Chain   : 0
% 2.74/1.38  #Close   : 0
% 2.74/1.38  
% 2.74/1.38  Ordering : KBO
% 2.74/1.38  
% 2.74/1.38  Simplification rules
% 2.74/1.38  ----------------------
% 2.74/1.38  #Subsume      : 18
% 2.74/1.38  #Demod        : 16
% 2.74/1.38  #Tautology    : 65
% 2.74/1.38  #SimpNegUnit  : 3
% 2.74/1.38  #BackRed      : 0
% 2.74/1.38  
% 2.74/1.38  #Partial instantiations: 0
% 2.74/1.38  #Strategies tried      : 1
% 2.74/1.38  
% 2.74/1.38  Timing (in seconds)
% 2.74/1.38  ----------------------
% 2.74/1.39  Preprocessing        : 0.33
% 2.74/1.39  Parsing              : 0.16
% 2.74/1.39  CNF conversion       : 0.03
% 2.74/1.39  Main loop            : 0.30
% 2.74/1.39  Inferencing          : 0.10
% 2.74/1.39  Reduction            : 0.10
% 2.74/1.39  Demodulation         : 0.08
% 2.74/1.39  BG Simplification    : 0.02
% 2.74/1.39  Subsumption          : 0.06
% 2.74/1.39  Abstraction          : 0.02
% 2.74/1.39  MUC search           : 0.00
% 2.74/1.39  Cooper               : 0.00
% 2.74/1.39  Total                : 0.66
% 2.74/1.39  Index Insertion      : 0.00
% 2.74/1.39  Index Deletion       : 0.00
% 2.74/1.39  Index Matching       : 0.00
% 2.74/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
