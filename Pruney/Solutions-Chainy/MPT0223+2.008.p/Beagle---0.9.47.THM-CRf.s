%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:17 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   41 (  48 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  54 expanded)
%              Number of equality atoms :   32 (  45 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_52,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_50,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_42,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_44,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_99,plain,(
    ! [B_40,A_41] : k3_xboole_0(B_40,A_41) = k3_xboole_0(A_41,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_114,plain,(
    ! [A_41,B_40] : k2_xboole_0(A_41,k3_xboole_0(B_40,A_41)) = A_41 ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_6])).

tff(c_168,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_114])).

tff(c_32,plain,(
    ! [A_14,B_15] : k2_xboole_0(k1_tarski(A_14),k1_tarski(B_15)) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_267,plain,(
    k2_tarski('#skF_4','#skF_3') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_32])).

tff(c_188,plain,(
    ! [A_44,B_45] : k1_enumset1(A_44,A_44,B_45) = k2_tarski(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10,plain,(
    ! [E_13,A_7,B_8] : r2_hidden(E_13,k1_enumset1(A_7,B_8,E_13)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_194,plain,(
    ! [B_45,A_44] : r2_hidden(B_45,k2_tarski(A_44,B_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_10])).

tff(c_280,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_194])).

tff(c_34,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_36,plain,(
    ! [A_17,B_18] : k1_enumset1(A_17,A_17,B_18) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_431,plain,(
    ! [E_64,C_65,B_66,A_67] :
      ( E_64 = C_65
      | E_64 = B_66
      | E_64 = A_67
      | ~ r2_hidden(E_64,k1_enumset1(A_67,B_66,C_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_450,plain,(
    ! [E_68,B_69,A_70] :
      ( E_68 = B_69
      | E_68 = A_70
      | E_68 = A_70
      | ~ r2_hidden(E_68,k2_tarski(A_70,B_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_431])).

tff(c_492,plain,(
    ! [E_72,A_73] :
      ( E_72 = A_73
      | E_72 = A_73
      | E_72 = A_73
      | ~ r2_hidden(E_72,k1_tarski(A_73)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_450])).

tff(c_495,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_280,c_492])).

tff(c_502,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_42,c_42,c_495])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:31:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.29  
% 2.12/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.30  %$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.12/1.30  
% 2.12/1.30  %Foreground sorts:
% 2.12/1.30  
% 2.12/1.30  
% 2.12/1.30  %Background operators:
% 2.12/1.30  
% 2.12/1.30  
% 2.12/1.30  %Foreground operators:
% 2.12/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.12/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.12/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.12/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.12/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.12/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.12/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.12/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.12/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.12/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.12/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.12/1.30  
% 2.12/1.30  tff(f_61, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 2.12/1.30  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.12/1.30  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.12/1.30  tff(f_48, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.12/1.30  tff(f_52, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.12/1.30  tff(f_46, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.12/1.30  tff(f_50, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.12/1.30  tff(c_42, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.12/1.30  tff(c_44, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.12/1.30  tff(c_99, plain, (![B_40, A_41]: (k3_xboole_0(B_40, A_41)=k3_xboole_0(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.12/1.30  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k3_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.12/1.30  tff(c_114, plain, (![A_41, B_40]: (k2_xboole_0(A_41, k3_xboole_0(B_40, A_41))=A_41)), inference(superposition, [status(thm), theory('equality')], [c_99, c_6])).
% 2.12/1.30  tff(c_168, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_44, c_114])).
% 2.12/1.30  tff(c_32, plain, (![A_14, B_15]: (k2_xboole_0(k1_tarski(A_14), k1_tarski(B_15))=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.12/1.30  tff(c_267, plain, (k2_tarski('#skF_4', '#skF_3')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_168, c_32])).
% 2.12/1.30  tff(c_188, plain, (![A_44, B_45]: (k1_enumset1(A_44, A_44, B_45)=k2_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.12/1.30  tff(c_10, plain, (![E_13, A_7, B_8]: (r2_hidden(E_13, k1_enumset1(A_7, B_8, E_13)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.12/1.30  tff(c_194, plain, (![B_45, A_44]: (r2_hidden(B_45, k2_tarski(A_44, B_45)))), inference(superposition, [status(thm), theory('equality')], [c_188, c_10])).
% 2.12/1.30  tff(c_280, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_267, c_194])).
% 2.12/1.30  tff(c_34, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.12/1.30  tff(c_36, plain, (![A_17, B_18]: (k1_enumset1(A_17, A_17, B_18)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.12/1.30  tff(c_431, plain, (![E_64, C_65, B_66, A_67]: (E_64=C_65 | E_64=B_66 | E_64=A_67 | ~r2_hidden(E_64, k1_enumset1(A_67, B_66, C_65)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.12/1.30  tff(c_450, plain, (![E_68, B_69, A_70]: (E_68=B_69 | E_68=A_70 | E_68=A_70 | ~r2_hidden(E_68, k2_tarski(A_70, B_69)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_431])).
% 2.12/1.30  tff(c_492, plain, (![E_72, A_73]: (E_72=A_73 | E_72=A_73 | E_72=A_73 | ~r2_hidden(E_72, k1_tarski(A_73)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_450])).
% 2.12/1.30  tff(c_495, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_280, c_492])).
% 2.12/1.30  tff(c_502, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_42, c_42, c_495])).
% 2.12/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.30  
% 2.12/1.30  Inference rules
% 2.12/1.30  ----------------------
% 2.12/1.30  #Ref     : 0
% 2.12/1.30  #Sup     : 116
% 2.12/1.30  #Fact    : 0
% 2.12/1.30  #Define  : 0
% 2.12/1.30  #Split   : 0
% 2.12/1.30  #Chain   : 0
% 2.12/1.30  #Close   : 0
% 2.12/1.30  
% 2.12/1.30  Ordering : KBO
% 2.12/1.30  
% 2.12/1.30  Simplification rules
% 2.12/1.30  ----------------------
% 2.12/1.30  #Subsume      : 1
% 2.12/1.30  #Demod        : 34
% 2.12/1.30  #Tautology    : 95
% 2.12/1.30  #SimpNegUnit  : 3
% 2.12/1.30  #BackRed      : 0
% 2.12/1.30  
% 2.12/1.30  #Partial instantiations: 0
% 2.12/1.30  #Strategies tried      : 1
% 2.12/1.30  
% 2.12/1.30  Timing (in seconds)
% 2.12/1.30  ----------------------
% 2.12/1.31  Preprocessing        : 0.31
% 2.12/1.31  Parsing              : 0.17
% 2.12/1.31  CNF conversion       : 0.02
% 2.12/1.31  Main loop            : 0.23
% 2.12/1.31  Inferencing          : 0.08
% 2.12/1.31  Reduction            : 0.08
% 2.12/1.31  Demodulation         : 0.06
% 2.12/1.31  BG Simplification    : 0.01
% 2.12/1.31  Subsumption          : 0.04
% 2.12/1.31  Abstraction          : 0.01
% 2.12/1.31  MUC search           : 0.00
% 2.12/1.31  Cooper               : 0.00
% 2.12/1.31  Total                : 0.56
% 2.12/1.31  Index Insertion      : 0.00
% 2.12/1.31  Index Deletion       : 0.00
% 2.12/1.31  Index Matching       : 0.00
% 2.12/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
