%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:24 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   43 (  52 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 (  64 expanded)
%              Number of equality atoms :   23 (  38 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_50,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_40,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_70,plain,(
    ! [A_37,B_38] : k1_enumset1(A_37,A_37,B_38) = k2_tarski(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    ! [E_12,A_6,B_7] : r2_hidden(E_12,k1_enumset1(A_6,B_7,E_12)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_88,plain,(
    ! [B_39,A_40] : r2_hidden(B_39,k2_tarski(A_40,B_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_18])).

tff(c_91,plain,(
    ! [A_13] : r2_hidden(A_13,k1_tarski(A_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_88])).

tff(c_141,plain,(
    ! [A_62,C_63,B_64] :
      ( r2_hidden(A_62,C_63)
      | ~ r2_hidden(A_62,B_64)
      | r2_hidden(A_62,k5_xboole_0(B_64,C_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_92,plain,(
    ! [A_41,B_42] : r1_xboole_0(k3_xboole_0(A_41,B_42),k5_xboole_0(A_41,B_42)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_95,plain,(
    r1_xboole_0(k1_tarski('#skF_3'),k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_92])).

tff(c_48,plain,(
    ! [A_23,B_24] :
      ( ~ r2_hidden(A_23,B_24)
      | ~ r1_xboole_0(k1_tarski(A_23),B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_106,plain,(
    ~ r2_hidden('#skF_3',k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_95,c_48])).

tff(c_150,plain,
    ( r2_hidden('#skF_3',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_141,c_106])).

tff(c_155,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_150])).

tff(c_42,plain,(
    ! [A_14,B_15] : k1_enumset1(A_14,A_14,B_15) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_156,plain,(
    ! [E_65,C_66,B_67,A_68] :
      ( E_65 = C_66
      | E_65 = B_67
      | E_65 = A_68
      | ~ r2_hidden(E_65,k1_enumset1(A_68,B_67,C_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_175,plain,(
    ! [E_69,B_70,A_71] :
      ( E_69 = B_70
      | E_69 = A_71
      | E_69 = A_71
      | ~ r2_hidden(E_69,k2_tarski(A_71,B_70)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_156])).

tff(c_189,plain,(
    ! [E_72,A_73] :
      ( E_72 = A_73
      | E_72 = A_73
      | E_72 = A_73
      | ~ r2_hidden(E_72,k1_tarski(A_73)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_175])).

tff(c_192,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_155,c_189])).

tff(c_199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_50,c_50,c_192])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:16:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.27  
% 1.99/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.27  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.99/1.27  
% 1.99/1.27  %Foreground sorts:
% 1.99/1.27  
% 1.99/1.27  
% 1.99/1.27  %Background operators:
% 1.99/1.27  
% 1.99/1.27  
% 1.99/1.27  %Foreground operators:
% 1.99/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.99/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.99/1.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.99/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.99/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.99/1.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 1.99/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.99/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.99/1.27  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.27  tff('#skF_4', type, '#skF_4': $i).
% 1.99/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.99/1.27  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 1.99/1.27  
% 2.09/1.28  tff(f_67, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 2.09/1.28  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.09/1.28  tff(f_53, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.09/1.28  tff(f_49, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.09/1.28  tff(f_32, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.09/1.28  tff(f_34, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l97_xboole_1)).
% 2.09/1.28  tff(f_62, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.09/1.28  tff(c_50, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.09/1.28  tff(c_40, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.09/1.28  tff(c_70, plain, (![A_37, B_38]: (k1_enumset1(A_37, A_37, B_38)=k2_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.09/1.28  tff(c_18, plain, (![E_12, A_6, B_7]: (r2_hidden(E_12, k1_enumset1(A_6, B_7, E_12)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.09/1.28  tff(c_88, plain, (![B_39, A_40]: (r2_hidden(B_39, k2_tarski(A_40, B_39)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_18])).
% 2.09/1.28  tff(c_91, plain, (![A_13]: (r2_hidden(A_13, k1_tarski(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_88])).
% 2.09/1.28  tff(c_141, plain, (![A_62, C_63, B_64]: (r2_hidden(A_62, C_63) | ~r2_hidden(A_62, B_64) | r2_hidden(A_62, k5_xboole_0(B_64, C_63)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.09/1.28  tff(c_52, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.09/1.28  tff(c_92, plain, (![A_41, B_42]: (r1_xboole_0(k3_xboole_0(A_41, B_42), k5_xboole_0(A_41, B_42)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.09/1.28  tff(c_95, plain, (r1_xboole_0(k1_tarski('#skF_3'), k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_52, c_92])).
% 2.09/1.28  tff(c_48, plain, (![A_23, B_24]: (~r2_hidden(A_23, B_24) | ~r1_xboole_0(k1_tarski(A_23), B_24))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.09/1.28  tff(c_106, plain, (~r2_hidden('#skF_3', k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_95, c_48])).
% 2.09/1.28  tff(c_150, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_141, c_106])).
% 2.09/1.28  tff(c_155, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_150])).
% 2.09/1.28  tff(c_42, plain, (![A_14, B_15]: (k1_enumset1(A_14, A_14, B_15)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.09/1.28  tff(c_156, plain, (![E_65, C_66, B_67, A_68]: (E_65=C_66 | E_65=B_67 | E_65=A_68 | ~r2_hidden(E_65, k1_enumset1(A_68, B_67, C_66)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.09/1.28  tff(c_175, plain, (![E_69, B_70, A_71]: (E_69=B_70 | E_69=A_71 | E_69=A_71 | ~r2_hidden(E_69, k2_tarski(A_71, B_70)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_156])).
% 2.09/1.28  tff(c_189, plain, (![E_72, A_73]: (E_72=A_73 | E_72=A_73 | E_72=A_73 | ~r2_hidden(E_72, k1_tarski(A_73)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_175])).
% 2.09/1.28  tff(c_192, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_155, c_189])).
% 2.09/1.28  tff(c_199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_50, c_50, c_192])).
% 2.09/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.28  
% 2.09/1.28  Inference rules
% 2.09/1.28  ----------------------
% 2.09/1.28  #Ref     : 0
% 2.09/1.28  #Sup     : 32
% 2.09/1.28  #Fact    : 0
% 2.09/1.28  #Define  : 0
% 2.09/1.28  #Split   : 0
% 2.09/1.28  #Chain   : 0
% 2.09/1.28  #Close   : 0
% 2.09/1.28  
% 2.09/1.28  Ordering : KBO
% 2.09/1.28  
% 2.09/1.28  Simplification rules
% 2.09/1.28  ----------------------
% 2.09/1.28  #Subsume      : 0
% 2.09/1.28  #Demod        : 4
% 2.09/1.28  #Tautology    : 24
% 2.09/1.28  #SimpNegUnit  : 1
% 2.09/1.28  #BackRed      : 0
% 2.09/1.28  
% 2.09/1.28  #Partial instantiations: 0
% 2.09/1.28  #Strategies tried      : 1
% 2.09/1.28  
% 2.09/1.28  Timing (in seconds)
% 2.09/1.28  ----------------------
% 2.09/1.29  Preprocessing        : 0.32
% 2.09/1.29  Parsing              : 0.17
% 2.09/1.29  CNF conversion       : 0.02
% 2.09/1.29  Main loop            : 0.16
% 2.09/1.29  Inferencing          : 0.06
% 2.09/1.29  Reduction            : 0.05
% 2.09/1.29  Demodulation         : 0.04
% 2.09/1.29  BG Simplification    : 0.01
% 2.09/1.29  Subsumption          : 0.03
% 2.09/1.29  Abstraction          : 0.01
% 2.09/1.29  MUC search           : 0.00
% 2.09/1.29  Cooper               : 0.00
% 2.09/1.29  Total                : 0.50
% 2.09/1.29  Index Insertion      : 0.00
% 2.09/1.29  Index Deletion       : 0.00
% 2.09/1.29  Index Matching       : 0.00
% 2.09/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
