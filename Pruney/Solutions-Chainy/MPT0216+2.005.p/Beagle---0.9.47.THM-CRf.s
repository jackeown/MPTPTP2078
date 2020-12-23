%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:44 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   39 (  55 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  75 expanded)
%              Number of equality atoms :   25 (  58 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k1_tarski(A) = k2_tarski(B,C)
       => B = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_40,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_42,plain,(
    k2_tarski('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_59,plain,(
    ! [A_46,B_47] : k1_enumset1(A_46,A_46,B_47) = k2_tarski(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [E_7,B_2,C_3] : r2_hidden(E_7,k1_enumset1(E_7,B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_85,plain,(
    ! [A_51,B_52] : r2_hidden(A_51,k2_tarski(A_51,B_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_8])).

tff(c_91,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_85])).

tff(c_26,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_28,plain,(
    ! [A_9,B_10] : k1_enumset1(A_9,A_9,B_10) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_112,plain,(
    ! [E_60,C_61,B_62,A_63] :
      ( E_60 = C_61
      | E_60 = B_62
      | E_60 = A_63
      | ~ r2_hidden(E_60,k1_enumset1(A_63,B_62,C_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_131,plain,(
    ! [E_64,B_65,A_66] :
      ( E_64 = B_65
      | E_64 = A_66
      | E_64 = A_66
      | ~ r2_hidden(E_64,k2_tarski(A_66,B_65)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_112])).

tff(c_148,plain,(
    ! [E_67,A_68] :
      ( E_67 = A_68
      | E_67 = A_68
      | E_67 = A_68
      | ~ r2_hidden(E_67,k1_tarski(A_68)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_131])).

tff(c_158,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_91,c_148])).

tff(c_4,plain,(
    ! [E_7,A_1,B_2] : r2_hidden(E_7,k1_enumset1(A_1,B_2,E_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_77,plain,(
    ! [B_48,A_49] : r2_hidden(B_48,k2_tarski(A_49,B_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_4])).

tff(c_83,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_77])).

tff(c_159,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_83,c_148])).

tff(c_184,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_159])).

tff(c_185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_184])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:36:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.20  
% 1.95/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.20  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.95/1.20  
% 1.95/1.20  %Foreground sorts:
% 1.95/1.20  
% 1.95/1.20  
% 1.95/1.20  %Background operators:
% 1.95/1.20  
% 1.95/1.20  
% 1.95/1.20  %Foreground operators:
% 1.95/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.95/1.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.95/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.95/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.20  tff('#skF_5', type, '#skF_5': $i).
% 1.95/1.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 1.95/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.95/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.20  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.95/1.20  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.95/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.95/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.20  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.95/1.20  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 1.95/1.20  
% 1.95/1.21  tff(f_59, negated_conjecture, ~(![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (B = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_zfmisc_1)).
% 1.95/1.21  tff(f_44, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.95/1.21  tff(f_40, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 1.95/1.21  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.95/1.21  tff(c_40, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.95/1.21  tff(c_42, plain, (k2_tarski('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.95/1.21  tff(c_59, plain, (![A_46, B_47]: (k1_enumset1(A_46, A_46, B_47)=k2_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.95/1.21  tff(c_8, plain, (![E_7, B_2, C_3]: (r2_hidden(E_7, k1_enumset1(E_7, B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.95/1.21  tff(c_85, plain, (![A_51, B_52]: (r2_hidden(A_51, k2_tarski(A_51, B_52)))), inference(superposition, [status(thm), theory('equality')], [c_59, c_8])).
% 1.95/1.21  tff(c_91, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_85])).
% 1.95/1.21  tff(c_26, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.95/1.21  tff(c_28, plain, (![A_9, B_10]: (k1_enumset1(A_9, A_9, B_10)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.95/1.21  tff(c_112, plain, (![E_60, C_61, B_62, A_63]: (E_60=C_61 | E_60=B_62 | E_60=A_63 | ~r2_hidden(E_60, k1_enumset1(A_63, B_62, C_61)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.95/1.21  tff(c_131, plain, (![E_64, B_65, A_66]: (E_64=B_65 | E_64=A_66 | E_64=A_66 | ~r2_hidden(E_64, k2_tarski(A_66, B_65)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_112])).
% 1.95/1.21  tff(c_148, plain, (![E_67, A_68]: (E_67=A_68 | E_67=A_68 | E_67=A_68 | ~r2_hidden(E_67, k1_tarski(A_68)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_131])).
% 1.95/1.21  tff(c_158, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_91, c_148])).
% 1.95/1.21  tff(c_4, plain, (![E_7, A_1, B_2]: (r2_hidden(E_7, k1_enumset1(A_1, B_2, E_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.95/1.21  tff(c_77, plain, (![B_48, A_49]: (r2_hidden(B_48, k2_tarski(A_49, B_48)))), inference(superposition, [status(thm), theory('equality')], [c_59, c_4])).
% 1.95/1.21  tff(c_83, plain, (r2_hidden('#skF_5', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_77])).
% 1.95/1.21  tff(c_159, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_83, c_148])).
% 1.95/1.21  tff(c_184, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_158, c_159])).
% 1.95/1.21  tff(c_185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_184])).
% 1.95/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.21  
% 1.95/1.21  Inference rules
% 1.95/1.21  ----------------------
% 1.95/1.21  #Ref     : 0
% 1.95/1.21  #Sup     : 35
% 1.95/1.21  #Fact    : 0
% 1.95/1.21  #Define  : 0
% 1.95/1.21  #Split   : 0
% 1.95/1.21  #Chain   : 0
% 1.95/1.21  #Close   : 0
% 1.95/1.21  
% 1.95/1.21  Ordering : KBO
% 1.95/1.21  
% 1.95/1.21  Simplification rules
% 1.95/1.21  ----------------------
% 1.95/1.21  #Subsume      : 0
% 1.95/1.21  #Demod        : 8
% 1.95/1.21  #Tautology    : 24
% 1.95/1.21  #SimpNegUnit  : 1
% 1.95/1.21  #BackRed      : 3
% 1.95/1.21  
% 1.95/1.21  #Partial instantiations: 0
% 1.95/1.21  #Strategies tried      : 1
% 1.95/1.21  
% 1.95/1.21  Timing (in seconds)
% 1.95/1.21  ----------------------
% 2.05/1.21  Preprocessing        : 0.31
% 2.05/1.21  Parsing              : 0.16
% 2.05/1.21  CNF conversion       : 0.02
% 2.05/1.21  Main loop            : 0.14
% 2.05/1.21  Inferencing          : 0.05
% 2.05/1.21  Reduction            : 0.05
% 2.05/1.21  Demodulation         : 0.04
% 2.05/1.21  BG Simplification    : 0.02
% 2.05/1.21  Subsumption          : 0.03
% 2.05/1.21  Abstraction          : 0.01
% 2.05/1.21  MUC search           : 0.00
% 2.05/1.21  Cooper               : 0.00
% 2.05/1.21  Total                : 0.48
% 2.05/1.21  Index Insertion      : 0.00
% 2.05/1.21  Index Deletion       : 0.00
% 2.05/1.21  Index Matching       : 0.00
% 2.05/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
