%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:42 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   40 (  47 expanded)
%              Number of leaves         :   24 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   44 (  54 expanded)
%              Number of equality atoms :   32 (  42 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( A != B
       => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_50,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_30,plain,(
    ! [A_12,B_13] : k2_xboole_0(k1_tarski(A_12),k1_tarski(B_13)) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_32,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_44,plain,(
    ! [B_25,C_26] :
      ( k4_xboole_0(k2_tarski(B_25,B_25),C_26) = k1_tarski(B_25)
      | r2_hidden(B_25,C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_129,plain,(
    ! [B_53,C_54] :
      ( k4_xboole_0(k1_tarski(B_53),C_54) = k1_tarski(B_53)
      | r2_hidden(B_53,C_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_44])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_178,plain,(
    ! [C_68,B_69] :
      ( k5_xboole_0(C_68,k1_tarski(B_69)) = k2_xboole_0(C_68,k1_tarski(B_69))
      | r2_hidden(B_69,C_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_4])).

tff(c_48,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k2_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_184,plain,
    ( k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k2_tarski('#skF_3','#skF_4')
    | r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_48])).

tff(c_190,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_184])).

tff(c_34,plain,(
    ! [A_15,B_16] : k1_enumset1(A_15,A_15,B_16) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_159,plain,(
    ! [E_64,C_65,B_66,A_67] :
      ( E_64 = C_65
      | E_64 = B_66
      | E_64 = A_67
      | ~ r2_hidden(E_64,k1_enumset1(A_67,B_66,C_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_192,plain,(
    ! [E_70,B_71,A_72] :
      ( E_70 = B_71
      | E_70 = A_72
      | E_70 = A_72
      | ~ r2_hidden(E_70,k2_tarski(A_72,B_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_159])).

tff(c_206,plain,(
    ! [E_73,A_74] :
      ( E_73 = A_74
      | E_73 = A_74
      | E_73 = A_74
      | ~ r2_hidden(E_73,k1_tarski(A_74)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_192])).

tff(c_209,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_190,c_206])).

tff(c_216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_50,c_50,c_209])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:25:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.35  
% 2.11/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.36  %$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.11/1.36  
% 2.11/1.36  %Foreground sorts:
% 2.11/1.36  
% 2.11/1.36  
% 2.11/1.36  %Background operators:
% 2.11/1.36  
% 2.11/1.36  
% 2.11/1.36  %Foreground operators:
% 2.11/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.11/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.11/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.11/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.11/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.11/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.11/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.11/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.11/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.11/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.11/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.11/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.11/1.36  
% 2.11/1.37  tff(f_69, negated_conjecture, ~(![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 2.11/1.37  tff(f_46, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.11/1.37  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.11/1.37  tff(f_63, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 2.11/1.37  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.11/1.37  tff(f_50, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.11/1.37  tff(f_44, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.11/1.37  tff(c_50, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.11/1.37  tff(c_30, plain, (![A_12, B_13]: (k2_xboole_0(k1_tarski(A_12), k1_tarski(B_13))=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.11/1.37  tff(c_32, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.11/1.37  tff(c_44, plain, (![B_25, C_26]: (k4_xboole_0(k2_tarski(B_25, B_25), C_26)=k1_tarski(B_25) | r2_hidden(B_25, C_26))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.11/1.37  tff(c_129, plain, (![B_53, C_54]: (k4_xboole_0(k1_tarski(B_53), C_54)=k1_tarski(B_53) | r2_hidden(B_53, C_54))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_44])).
% 2.11/1.37  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.11/1.37  tff(c_178, plain, (![C_68, B_69]: (k5_xboole_0(C_68, k1_tarski(B_69))=k2_xboole_0(C_68, k1_tarski(B_69)) | r2_hidden(B_69, C_68))), inference(superposition, [status(thm), theory('equality')], [c_129, c_4])).
% 2.11/1.37  tff(c_48, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k2_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.11/1.37  tff(c_184, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k2_tarski('#skF_3', '#skF_4') | r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_178, c_48])).
% 2.11/1.37  tff(c_190, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_184])).
% 2.11/1.37  tff(c_34, plain, (![A_15, B_16]: (k1_enumset1(A_15, A_15, B_16)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.11/1.37  tff(c_159, plain, (![E_64, C_65, B_66, A_67]: (E_64=C_65 | E_64=B_66 | E_64=A_67 | ~r2_hidden(E_64, k1_enumset1(A_67, B_66, C_65)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.11/1.37  tff(c_192, plain, (![E_70, B_71, A_72]: (E_70=B_71 | E_70=A_72 | E_70=A_72 | ~r2_hidden(E_70, k2_tarski(A_72, B_71)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_159])).
% 2.11/1.37  tff(c_206, plain, (![E_73, A_74]: (E_73=A_74 | E_73=A_74 | E_73=A_74 | ~r2_hidden(E_73, k1_tarski(A_74)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_192])).
% 2.11/1.37  tff(c_209, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_190, c_206])).
% 2.11/1.37  tff(c_216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_50, c_50, c_209])).
% 2.11/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.37  
% 2.11/1.37  Inference rules
% 2.11/1.37  ----------------------
% 2.11/1.37  #Ref     : 0
% 2.11/1.37  #Sup     : 36
% 2.11/1.37  #Fact    : 0
% 2.11/1.37  #Define  : 0
% 2.11/1.37  #Split   : 0
% 2.11/1.37  #Chain   : 0
% 2.11/1.37  #Close   : 0
% 2.11/1.37  
% 2.11/1.37  Ordering : KBO
% 2.11/1.37  
% 2.11/1.37  Simplification rules
% 2.11/1.37  ----------------------
% 2.11/1.37  #Subsume      : 0
% 2.11/1.37  #Demod        : 4
% 2.11/1.37  #Tautology    : 26
% 2.11/1.37  #SimpNegUnit  : 1
% 2.11/1.37  #BackRed      : 0
% 2.11/1.37  
% 2.11/1.37  #Partial instantiations: 0
% 2.11/1.37  #Strategies tried      : 1
% 2.11/1.37  
% 2.11/1.37  Timing (in seconds)
% 2.11/1.37  ----------------------
% 2.20/1.37  Preprocessing        : 0.33
% 2.20/1.37  Parsing              : 0.18
% 2.20/1.37  CNF conversion       : 0.02
% 2.20/1.37  Main loop            : 0.15
% 2.20/1.37  Inferencing          : 0.05
% 2.20/1.37  Reduction            : 0.05
% 2.20/1.37  Demodulation         : 0.04
% 2.20/1.37  BG Simplification    : 0.02
% 2.20/1.37  Subsumption          : 0.03
% 2.20/1.37  Abstraction          : 0.01
% 2.20/1.37  MUC search           : 0.00
% 2.20/1.37  Cooper               : 0.00
% 2.20/1.37  Total                : 0.51
% 2.20/1.37  Index Insertion      : 0.00
% 2.20/1.37  Index Deletion       : 0.00
% 2.20/1.37  Index Matching       : 0.00
% 2.20/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
