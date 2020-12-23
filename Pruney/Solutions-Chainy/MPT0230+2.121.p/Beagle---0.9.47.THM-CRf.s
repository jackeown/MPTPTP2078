%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:11 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   35 (  40 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   34 (  49 expanded)
%              Number of equality atoms :   24 (  35 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_50,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_40,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_38,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_102,plain,(
    ! [A_45,B_46,C_47] : k2_xboole_0(k1_tarski(A_45),k2_tarski(B_46,C_47)) = k1_enumset1(A_45,B_46,C_47) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_42,plain,(
    r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_77,plain,(
    ! [A_37,B_38] :
      ( k2_xboole_0(A_37,B_38) = B_38
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_81,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) = k2_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_77])).

tff(c_108,plain,(
    k1_enumset1('#skF_3','#skF_4','#skF_5') = k2_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_81])).

tff(c_10,plain,(
    ! [E_9,B_4,C_5] : r2_hidden(E_9,k1_enumset1(E_9,B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_126,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_10])).

tff(c_32,plain,(
    ! [A_14,B_15] : k1_enumset1(A_14,A_14,B_15) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_238,plain,(
    ! [E_56,C_57,B_58,A_59] :
      ( E_56 = C_57
      | E_56 = B_58
      | E_56 = A_59
      | ~ r2_hidden(E_56,k1_enumset1(A_59,B_58,C_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_315,plain,(
    ! [E_67,B_68,A_69] :
      ( E_67 = B_68
      | E_67 = A_69
      | E_67 = A_69
      | ~ r2_hidden(E_67,k2_tarski(A_69,B_68)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_238])).

tff(c_318,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_126,c_315])).

tff(c_331,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_40,c_38,c_318])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:24:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.25  
% 2.08/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.26  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.08/1.26  
% 2.08/1.26  %Foreground sorts:
% 2.08/1.26  
% 2.08/1.26  
% 2.08/1.26  %Background operators:
% 2.08/1.26  
% 2.08/1.26  
% 2.08/1.26  %Foreground operators:
% 2.08/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.08/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.08/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.08/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.08/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.08/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.08/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.08/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.08/1.26  
% 2.08/1.26  tff(f_64, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.08/1.26  tff(f_46, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 2.08/1.26  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.08/1.26  tff(f_44, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.08/1.26  tff(f_50, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.08/1.26  tff(c_40, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.08/1.26  tff(c_38, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.08/1.26  tff(c_102, plain, (![A_45, B_46, C_47]: (k2_xboole_0(k1_tarski(A_45), k2_tarski(B_46, C_47))=k1_enumset1(A_45, B_46, C_47))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.08/1.26  tff(c_42, plain, (r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.08/1.26  tff(c_77, plain, (![A_37, B_38]: (k2_xboole_0(A_37, B_38)=B_38 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.08/1.26  tff(c_81, plain, (k2_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k2_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_77])).
% 2.08/1.26  tff(c_108, plain, (k1_enumset1('#skF_3', '#skF_4', '#skF_5')=k2_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_102, c_81])).
% 2.08/1.26  tff(c_10, plain, (![E_9, B_4, C_5]: (r2_hidden(E_9, k1_enumset1(E_9, B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.08/1.26  tff(c_126, plain, (r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_108, c_10])).
% 2.08/1.26  tff(c_32, plain, (![A_14, B_15]: (k1_enumset1(A_14, A_14, B_15)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.08/1.26  tff(c_238, plain, (![E_56, C_57, B_58, A_59]: (E_56=C_57 | E_56=B_58 | E_56=A_59 | ~r2_hidden(E_56, k1_enumset1(A_59, B_58, C_57)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.08/1.26  tff(c_315, plain, (![E_67, B_68, A_69]: (E_67=B_68 | E_67=A_69 | E_67=A_69 | ~r2_hidden(E_67, k2_tarski(A_69, B_68)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_238])).
% 2.08/1.26  tff(c_318, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_126, c_315])).
% 2.08/1.26  tff(c_331, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_40, c_38, c_318])).
% 2.08/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.26  
% 2.08/1.26  Inference rules
% 2.08/1.26  ----------------------
% 2.08/1.26  #Ref     : 0
% 2.08/1.26  #Sup     : 67
% 2.08/1.26  #Fact    : 0
% 2.08/1.26  #Define  : 0
% 2.08/1.26  #Split   : 0
% 2.08/1.26  #Chain   : 0
% 2.08/1.26  #Close   : 0
% 2.08/1.26  
% 2.08/1.26  Ordering : KBO
% 2.08/1.26  
% 2.08/1.26  Simplification rules
% 2.08/1.26  ----------------------
% 2.08/1.27  #Subsume      : 0
% 2.08/1.27  #Demod        : 21
% 2.08/1.27  #Tautology    : 48
% 2.08/1.27  #SimpNegUnit  : 4
% 2.08/1.27  #BackRed      : 0
% 2.08/1.27  
% 2.08/1.27  #Partial instantiations: 0
% 2.08/1.27  #Strategies tried      : 1
% 2.08/1.27  
% 2.08/1.27  Timing (in seconds)
% 2.08/1.27  ----------------------
% 2.08/1.27  Preprocessing        : 0.30
% 2.08/1.27  Parsing              : 0.15
% 2.08/1.27  CNF conversion       : 0.02
% 2.08/1.27  Main loop            : 0.19
% 2.08/1.27  Inferencing          : 0.07
% 2.08/1.27  Reduction            : 0.06
% 2.08/1.27  Demodulation         : 0.05
% 2.08/1.27  BG Simplification    : 0.01
% 2.08/1.27  Subsumption          : 0.03
% 2.08/1.27  Abstraction          : 0.01
% 2.08/1.27  MUC search           : 0.00
% 2.08/1.27  Cooper               : 0.00
% 2.08/1.27  Total                : 0.52
% 2.08/1.27  Index Insertion      : 0.00
% 2.08/1.27  Index Deletion       : 0.00
% 2.08/1.27  Index Matching       : 0.00
% 2.08/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
