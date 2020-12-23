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
% DateTime   : Thu Dec  3 09:54:46 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   36 (  39 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   39 (  49 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C)
          & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,B)
        & ~ r2_hidden(C,B)
        & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_28,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_180,plain,(
    ! [A_62,C_63,B_64] :
      ( r1_xboole_0(k2_tarski(A_62,C_63),B_64)
      | r2_hidden(C_63,B_64)
      | r2_hidden(A_62,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_143,plain,(
    ! [A_50,B_51] :
      ( r2_hidden('#skF_1'(A_50,B_51),k3_xboole_0(A_50,B_51))
      | r1_xboole_0(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_77,plain,(
    ! [A_37,B_38,C_39] :
      ( ~ r1_xboole_0(A_37,B_38)
      | ~ r2_hidden(C_39,k3_xboole_0(A_37,B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_83,plain,(
    ! [B_2,A_1,C_39] :
      ( ~ r1_xboole_0(B_2,A_1)
      | ~ r2_hidden(C_39,k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_77])).

tff(c_156,plain,(
    ! [B_51,A_50] :
      ( ~ r1_xboole_0(B_51,A_50)
      | r1_xboole_0(A_50,B_51) ) ),
    inference(resolution,[status(thm)],[c_143,c_83])).

tff(c_203,plain,(
    ! [B_67,A_68,C_69] :
      ( r1_xboole_0(B_67,k2_tarski(A_68,C_69))
      | r2_hidden(C_69,B_67)
      | r2_hidden(A_68,B_67) ) ),
    inference(resolution,[status(thm)],[c_180,c_156])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = A_10
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_211,plain,(
    ! [B_70,A_71,C_72] :
      ( k4_xboole_0(B_70,k2_tarski(A_71,C_72)) = B_70
      | r2_hidden(C_72,B_70)
      | r2_hidden(A_71,B_70) ) ),
    inference(resolution,[status(thm)],[c_203,c_10])).

tff(c_24,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_2','#skF_3')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_219,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | r2_hidden('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_24])).

tff(c_228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_26,c_219])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:44:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.41  
% 1.97/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.41  %$ r2_hidden > r1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.97/1.41  
% 1.97/1.41  %Foreground sorts:
% 1.97/1.41  
% 1.97/1.41  
% 1.97/1.41  %Background operators:
% 1.97/1.41  
% 1.97/1.41  
% 1.97/1.41  %Foreground operators:
% 1.97/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.97/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.97/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.97/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.97/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.97/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.97/1.41  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.41  tff('#skF_3', type, '#skF_3': $i).
% 1.97/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.97/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.41  tff('#skF_4', type, '#skF_4': $i).
% 1.97/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.97/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.97/1.41  
% 1.97/1.42  tff(f_76, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 1.97/1.42  tff(f_65, axiom, (![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 1.97/1.42  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.97/1.42  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.97/1.42  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.97/1.42  tff(c_28, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.97/1.42  tff(c_26, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.97/1.42  tff(c_180, plain, (![A_62, C_63, B_64]: (r1_xboole_0(k2_tarski(A_62, C_63), B_64) | r2_hidden(C_63, B_64) | r2_hidden(A_62, B_64))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.97/1.42  tff(c_143, plain, (![A_50, B_51]: (r2_hidden('#skF_1'(A_50, B_51), k3_xboole_0(A_50, B_51)) | r1_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.97/1.42  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.97/1.42  tff(c_77, plain, (![A_37, B_38, C_39]: (~r1_xboole_0(A_37, B_38) | ~r2_hidden(C_39, k3_xboole_0(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.97/1.42  tff(c_83, plain, (![B_2, A_1, C_39]: (~r1_xboole_0(B_2, A_1) | ~r2_hidden(C_39, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_77])).
% 1.97/1.42  tff(c_156, plain, (![B_51, A_50]: (~r1_xboole_0(B_51, A_50) | r1_xboole_0(A_50, B_51))), inference(resolution, [status(thm)], [c_143, c_83])).
% 1.97/1.42  tff(c_203, plain, (![B_67, A_68, C_69]: (r1_xboole_0(B_67, k2_tarski(A_68, C_69)) | r2_hidden(C_69, B_67) | r2_hidden(A_68, B_67))), inference(resolution, [status(thm)], [c_180, c_156])).
% 1.97/1.42  tff(c_10, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=A_10 | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.97/1.42  tff(c_211, plain, (![B_70, A_71, C_72]: (k4_xboole_0(B_70, k2_tarski(A_71, C_72))=B_70 | r2_hidden(C_72, B_70) | r2_hidden(A_71, B_70))), inference(resolution, [status(thm)], [c_203, c_10])).
% 1.97/1.42  tff(c_24, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_2', '#skF_3'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.97/1.42  tff(c_219, plain, (r2_hidden('#skF_3', '#skF_4') | r2_hidden('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_211, c_24])).
% 1.97/1.42  tff(c_228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_26, c_219])).
% 1.97/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.42  
% 1.97/1.42  Inference rules
% 1.97/1.42  ----------------------
% 1.97/1.42  #Ref     : 0
% 1.97/1.42  #Sup     : 48
% 1.97/1.42  #Fact    : 0
% 1.97/1.42  #Define  : 0
% 1.97/1.42  #Split   : 0
% 1.97/1.42  #Chain   : 0
% 1.97/1.42  #Close   : 0
% 1.97/1.42  
% 1.97/1.42  Ordering : KBO
% 1.97/1.42  
% 1.97/1.42  Simplification rules
% 1.97/1.42  ----------------------
% 1.97/1.42  #Subsume      : 9
% 1.97/1.42  #Demod        : 3
% 1.97/1.42  #Tautology    : 27
% 1.97/1.42  #SimpNegUnit  : 1
% 1.97/1.42  #BackRed      : 0
% 1.97/1.42  
% 1.97/1.42  #Partial instantiations: 0
% 1.97/1.42  #Strategies tried      : 1
% 1.97/1.42  
% 1.97/1.42  Timing (in seconds)
% 1.97/1.42  ----------------------
% 1.97/1.42  Preprocessing        : 0.36
% 1.97/1.43  Parsing              : 0.20
% 1.97/1.43  CNF conversion       : 0.02
% 1.97/1.43  Main loop            : 0.15
% 1.97/1.43  Inferencing          : 0.06
% 1.97/1.43  Reduction            : 0.05
% 1.97/1.43  Demodulation         : 0.03
% 1.97/1.43  BG Simplification    : 0.01
% 1.97/1.43  Subsumption          : 0.02
% 1.97/1.43  Abstraction          : 0.01
% 1.97/1.43  MUC search           : 0.00
% 1.97/1.43  Cooper               : 0.00
% 1.97/1.43  Total                : 0.53
% 1.97/1.43  Index Insertion      : 0.00
% 1.97/1.43  Index Deletion       : 0.00
% 1.97/1.43  Index Matching       : 0.00
% 1.97/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
