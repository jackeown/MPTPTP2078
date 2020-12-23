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
% DateTime   : Thu Dec  3 09:48:02 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   38 (  48 expanded)
%              Number of leaves         :   21 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  51 expanded)
%              Number of equality atoms :   28 (  44 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_enumset1 > k3_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_55,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_50,axiom,(
    ! [A] : k3_enumset1(A,A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C] : k4_enumset1(A,A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(c_36,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_34,plain,(
    ! [A_24] : k3_enumset1(A_24,A_24,A_24,A_24,A_24) = k1_tarski(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_151,plain,(
    ! [E_55,A_56,D_57,F_58,B_54,C_59] : k2_xboole_0(k3_enumset1(A_56,B_54,C_59,D_57,E_55),k1_tarski(F_58)) = k4_enumset1(A_56,B_54,C_59,D_57,E_55,F_58) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_175,plain,(
    ! [A_66,F_67] : k4_enumset1(A_66,A_66,A_66,A_66,A_66,F_67) = k2_xboole_0(k1_tarski(A_66),k1_tarski(F_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_151])).

tff(c_32,plain,(
    ! [A_21,B_22,C_23] : k4_enumset1(A_21,A_21,A_21,A_21,B_22,C_23) = k1_enumset1(A_21,B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_212,plain,(
    ! [A_68,F_69] : k2_xboole_0(k1_tarski(A_68),k1_tarski(F_69)) = k1_enumset1(A_68,A_68,F_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_32])).

tff(c_38,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_231,plain,(
    k1_enumset1('#skF_3','#skF_3','#skF_4') = k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_38])).

tff(c_6,plain,(
    ! [E_9,A_3,B_4] : r2_hidden(E_9,k1_enumset1(A_3,B_4,E_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_271,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_6])).

tff(c_95,plain,(
    ! [A_46,C_48,E_45,D_47,B_44] : k4_enumset1(A_46,A_46,B_44,C_48,D_47,E_45) = k3_enumset1(A_46,B_44,C_48,D_47,E_45) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_111,plain,(
    ! [C_49,D_50,E_51] : k3_enumset1(C_49,C_49,C_49,D_50,E_51) = k1_enumset1(C_49,D_50,E_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_32])).

tff(c_127,plain,(
    ! [E_52] : k1_enumset1(E_52,E_52,E_52) = k1_tarski(E_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_34])).

tff(c_4,plain,(
    ! [E_9,C_5,B_4,A_3] :
      ( E_9 = C_5
      | E_9 = B_4
      | E_9 = A_3
      | ~ r2_hidden(E_9,k1_enumset1(A_3,B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_133,plain,(
    ! [E_9,E_52] :
      ( E_9 = E_52
      | E_9 = E_52
      | E_9 = E_52
      | ~ r2_hidden(E_9,k1_tarski(E_52)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_4])).

tff(c_282,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_271,c_133])).

tff(c_286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_36,c_36,c_282])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.26  
% 2.11/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.26  %$ r2_hidden > k4_enumset1 > k3_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.11/1.26  
% 2.11/1.26  %Foreground sorts:
% 2.11/1.26  
% 2.11/1.26  
% 2.11/1.26  %Background operators:
% 2.11/1.26  
% 2.11/1.26  
% 2.11/1.26  %Foreground operators:
% 2.11/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.11/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.11/1.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.11/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.11/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.11/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.26  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.11/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.11/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.11/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.11/1.26  
% 2.11/1.27  tff(f_55, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 2.11/1.27  tff(f_50, axiom, (![A]: (k3_enumset1(A, A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_enumset1)).
% 2.11/1.27  tff(f_44, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 2.11/1.27  tff(f_48, axiom, (![A, B, C]: (k4_enumset1(A, A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_enumset1)).
% 2.11/1.27  tff(f_42, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.11/1.27  tff(f_46, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.11/1.27  tff(c_36, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.11/1.27  tff(c_34, plain, (![A_24]: (k3_enumset1(A_24, A_24, A_24, A_24, A_24)=k1_tarski(A_24))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.11/1.27  tff(c_151, plain, (![E_55, A_56, D_57, F_58, B_54, C_59]: (k2_xboole_0(k3_enumset1(A_56, B_54, C_59, D_57, E_55), k1_tarski(F_58))=k4_enumset1(A_56, B_54, C_59, D_57, E_55, F_58))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.11/1.27  tff(c_175, plain, (![A_66, F_67]: (k4_enumset1(A_66, A_66, A_66, A_66, A_66, F_67)=k2_xboole_0(k1_tarski(A_66), k1_tarski(F_67)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_151])).
% 2.11/1.27  tff(c_32, plain, (![A_21, B_22, C_23]: (k4_enumset1(A_21, A_21, A_21, A_21, B_22, C_23)=k1_enumset1(A_21, B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.11/1.27  tff(c_212, plain, (![A_68, F_69]: (k2_xboole_0(k1_tarski(A_68), k1_tarski(F_69))=k1_enumset1(A_68, A_68, F_69))), inference(superposition, [status(thm), theory('equality')], [c_175, c_32])).
% 2.11/1.27  tff(c_38, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.11/1.27  tff(c_231, plain, (k1_enumset1('#skF_3', '#skF_3', '#skF_4')=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_212, c_38])).
% 2.11/1.27  tff(c_6, plain, (![E_9, A_3, B_4]: (r2_hidden(E_9, k1_enumset1(A_3, B_4, E_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.11/1.27  tff(c_271, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_231, c_6])).
% 2.11/1.27  tff(c_95, plain, (![A_46, C_48, E_45, D_47, B_44]: (k4_enumset1(A_46, A_46, B_44, C_48, D_47, E_45)=k3_enumset1(A_46, B_44, C_48, D_47, E_45))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.11/1.27  tff(c_111, plain, (![C_49, D_50, E_51]: (k3_enumset1(C_49, C_49, C_49, D_50, E_51)=k1_enumset1(C_49, D_50, E_51))), inference(superposition, [status(thm), theory('equality')], [c_95, c_32])).
% 2.11/1.27  tff(c_127, plain, (![E_52]: (k1_enumset1(E_52, E_52, E_52)=k1_tarski(E_52))), inference(superposition, [status(thm), theory('equality')], [c_111, c_34])).
% 2.11/1.27  tff(c_4, plain, (![E_9, C_5, B_4, A_3]: (E_9=C_5 | E_9=B_4 | E_9=A_3 | ~r2_hidden(E_9, k1_enumset1(A_3, B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.11/1.27  tff(c_133, plain, (![E_9, E_52]: (E_9=E_52 | E_9=E_52 | E_9=E_52 | ~r2_hidden(E_9, k1_tarski(E_52)))), inference(superposition, [status(thm), theory('equality')], [c_127, c_4])).
% 2.11/1.27  tff(c_282, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_271, c_133])).
% 2.11/1.27  tff(c_286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_36, c_36, c_282])).
% 2.11/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.27  
% 2.11/1.27  Inference rules
% 2.11/1.27  ----------------------
% 2.11/1.27  #Ref     : 0
% 2.11/1.27  #Sup     : 63
% 2.11/1.27  #Fact    : 0
% 2.11/1.27  #Define  : 0
% 2.11/1.27  #Split   : 0
% 2.11/1.27  #Chain   : 0
% 2.11/1.27  #Close   : 0
% 2.11/1.27  
% 2.11/1.27  Ordering : KBO
% 2.11/1.27  
% 2.11/1.27  Simplification rules
% 2.11/1.27  ----------------------
% 2.11/1.27  #Subsume      : 0
% 2.11/1.27  #Demod        : 12
% 2.11/1.27  #Tautology    : 38
% 2.11/1.27  #SimpNegUnit  : 1
% 2.11/1.27  #BackRed      : 0
% 2.11/1.27  
% 2.11/1.27  #Partial instantiations: 0
% 2.11/1.27  #Strategies tried      : 1
% 2.11/1.27  
% 2.11/1.27  Timing (in seconds)
% 2.11/1.27  ----------------------
% 2.11/1.28  Preprocessing        : 0.32
% 2.11/1.28  Parsing              : 0.16
% 2.11/1.28  CNF conversion       : 0.02
% 2.11/1.28  Main loop            : 0.19
% 2.11/1.28  Inferencing          : 0.07
% 2.11/1.28  Reduction            : 0.06
% 2.11/1.28  Demodulation         : 0.05
% 2.11/1.28  BG Simplification    : 0.02
% 2.11/1.28  Subsumption          : 0.03
% 2.11/1.28  Abstraction          : 0.01
% 2.11/1.28  MUC search           : 0.00
% 2.11/1.28  Cooper               : 0.00
% 2.11/1.28  Total                : 0.53
% 2.11/1.28  Index Insertion      : 0.00
% 2.11/1.28  Index Deletion       : 0.00
% 2.11/1.28  Index Matching       : 0.00
% 2.11/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
