%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:36 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   37 (  44 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   39 (  53 expanded)
%              Number of equality atoms :   27 (  37 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_36,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_89,plain,(
    ! [A_37,B_38] : k2_xboole_0(k1_tarski(A_37),k1_tarski(B_38)) = k2_tarski(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_38,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_51,plain,(
    ! [A_28,B_29] :
      ( k2_xboole_0(A_28,B_29) = B_29
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_55,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_51])).

tff(c_95,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_55])).

tff(c_56,plain,(
    ! [A_30,B_31] : k1_enumset1(A_30,A_30,B_31) = k2_tarski(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    ! [E_9,B_4,C_5] : r2_hidden(E_9,k1_enumset1(E_9,B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_62,plain,(
    ! [A_30,B_31] : r2_hidden(A_30,k2_tarski(A_30,B_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_10])).

tff(c_110,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_62])).

tff(c_30,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_32,plain,(
    ! [A_13,B_14] : k1_enumset1(A_13,A_13,B_14) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_125,plain,(
    ! [E_42,C_43,B_44,A_45] :
      ( E_42 = C_43
      | E_42 = B_44
      | E_42 = A_45
      | ~ r2_hidden(E_42,k1_enumset1(A_45,B_44,C_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_145,plain,(
    ! [E_50,B_51,A_52] :
      ( E_50 = B_51
      | E_50 = A_52
      | E_50 = A_52
      | ~ r2_hidden(E_50,k2_tarski(A_52,B_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_125])).

tff(c_162,plain,(
    ! [E_53,A_54] :
      ( E_53 = A_54
      | E_53 = A_54
      | E_53 = A_54
      | ~ r2_hidden(E_53,k1_tarski(A_54)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_145])).

tff(c_165,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_110,c_162])).

tff(c_172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_36,c_36,c_165])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:32:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.26  
% 1.92/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.26  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.92/1.26  
% 1.92/1.26  %Foreground sorts:
% 1.92/1.26  
% 1.92/1.26  
% 1.92/1.26  %Background operators:
% 1.92/1.26  
% 1.92/1.26  
% 1.92/1.26  %Foreground operators:
% 1.92/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.92/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.92/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.92/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.92/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 1.92/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.92/1.26  tff('#skF_3', type, '#skF_3': $i).
% 1.92/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.26  tff('#skF_4', type, '#skF_4': $i).
% 1.92/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.92/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.01/1.26  
% 2.01/1.27  tff(f_57, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.01/1.27  tff(f_46, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.01/1.27  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.01/1.27  tff(f_50, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.01/1.27  tff(f_44, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.01/1.27  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.01/1.27  tff(c_36, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.01/1.27  tff(c_89, plain, (![A_37, B_38]: (k2_xboole_0(k1_tarski(A_37), k1_tarski(B_38))=k2_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.01/1.27  tff(c_38, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.01/1.27  tff(c_51, plain, (![A_28, B_29]: (k2_xboole_0(A_28, B_29)=B_29 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.01/1.27  tff(c_55, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_38, c_51])).
% 2.01/1.27  tff(c_95, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_89, c_55])).
% 2.01/1.27  tff(c_56, plain, (![A_30, B_31]: (k1_enumset1(A_30, A_30, B_31)=k2_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.01/1.27  tff(c_10, plain, (![E_9, B_4, C_5]: (r2_hidden(E_9, k1_enumset1(E_9, B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.01/1.27  tff(c_62, plain, (![A_30, B_31]: (r2_hidden(A_30, k2_tarski(A_30, B_31)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_10])).
% 2.01/1.27  tff(c_110, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_95, c_62])).
% 2.01/1.27  tff(c_30, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.01/1.27  tff(c_32, plain, (![A_13, B_14]: (k1_enumset1(A_13, A_13, B_14)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.01/1.27  tff(c_125, plain, (![E_42, C_43, B_44, A_45]: (E_42=C_43 | E_42=B_44 | E_42=A_45 | ~r2_hidden(E_42, k1_enumset1(A_45, B_44, C_43)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.01/1.27  tff(c_145, plain, (![E_50, B_51, A_52]: (E_50=B_51 | E_50=A_52 | E_50=A_52 | ~r2_hidden(E_50, k2_tarski(A_52, B_51)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_125])).
% 2.01/1.27  tff(c_162, plain, (![E_53, A_54]: (E_53=A_54 | E_53=A_54 | E_53=A_54 | ~r2_hidden(E_53, k1_tarski(A_54)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_145])).
% 2.01/1.27  tff(c_165, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_110, c_162])).
% 2.01/1.27  tff(c_172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_36, c_36, c_165])).
% 2.01/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.27  
% 2.01/1.27  Inference rules
% 2.01/1.27  ----------------------
% 2.01/1.27  #Ref     : 0
% 2.01/1.27  #Sup     : 32
% 2.01/1.27  #Fact    : 0
% 2.01/1.27  #Define  : 0
% 2.01/1.27  #Split   : 0
% 2.01/1.27  #Chain   : 0
% 2.01/1.27  #Close   : 0
% 2.01/1.27  
% 2.01/1.27  Ordering : KBO
% 2.01/1.27  
% 2.01/1.27  Simplification rules
% 2.01/1.27  ----------------------
% 2.01/1.27  #Subsume      : 0
% 2.01/1.27  #Demod        : 4
% 2.01/1.27  #Tautology    : 21
% 2.01/1.27  #SimpNegUnit  : 1
% 2.01/1.27  #BackRed      : 0
% 2.01/1.27  
% 2.01/1.27  #Partial instantiations: 0
% 2.01/1.27  #Strategies tried      : 1
% 2.01/1.27  
% 2.01/1.27  Timing (in seconds)
% 2.01/1.27  ----------------------
% 2.01/1.27  Preprocessing        : 0.31
% 2.01/1.27  Parsing              : 0.16
% 2.01/1.27  CNF conversion       : 0.02
% 2.01/1.27  Main loop            : 0.13
% 2.01/1.27  Inferencing          : 0.04
% 2.01/1.27  Reduction            : 0.04
% 2.01/1.27  Demodulation         : 0.03
% 2.01/1.27  BG Simplification    : 0.01
% 2.01/1.27  Subsumption          : 0.02
% 2.01/1.27  Abstraction          : 0.01
% 2.01/1.27  MUC search           : 0.00
% 2.01/1.27  Cooper               : 0.00
% 2.01/1.27  Total                : 0.46
% 2.01/1.27  Index Insertion      : 0.00
% 2.01/1.27  Index Deletion       : 0.00
% 2.01/1.27  Index Matching       : 0.00
% 2.01/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
