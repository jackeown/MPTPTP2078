%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:44 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   44 (  71 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  98 expanded)
%              Number of equality atoms :   12 (  26 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_46,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_253,plain,(
    ! [A_62,B_63] : k2_xboole_0(k1_tarski(A_62),k1_tarski(B_63)) = k2_tarski(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_46,plain,(
    ! [A_25,B_26] : k2_xboole_0(k1_tarski(A_25),B_26) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_273,plain,(
    ! [A_62,B_63] : k2_tarski(A_62,B_63) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_46])).

tff(c_534,plain,(
    ! [A_81,B_82,C_83] :
      ( r1_tarski(k2_tarski(A_81,B_82),C_83)
      | ~ r2_hidden(B_82,C_83)
      | ~ r2_hidden(A_81,C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_28,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_243,plain,(
    ! [B_60,A_61] :
      ( B_60 = A_61
      | ~ r1_tarski(B_60,A_61)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_252,plain,(
    ! [A_11] :
      ( k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28,c_243])).

tff(c_538,plain,(
    ! [A_81,B_82] :
      ( k2_tarski(A_81,B_82) = k1_xboole_0
      | ~ r2_hidden(B_82,k1_xboole_0)
      | ~ r2_hidden(A_81,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_534,c_252])).

tff(c_558,plain,(
    ! [B_82,A_81] :
      ( ~ r2_hidden(B_82,k1_xboole_0)
      | ~ r2_hidden(A_81,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_273,c_538])).

tff(c_562,plain,(
    ! [A_81] : ~ r2_hidden(A_81,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_558])).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_224,plain,(
    ! [B_55,C_56,A_57] :
      ( r2_hidden(B_55,C_56)
      | ~ r1_tarski(k2_tarski(A_57,B_55),C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_233,plain,(
    ! [B_58,A_59] : r2_hidden(B_58,k2_tarski(A_59,B_58)) ),
    inference(resolution,[status(thm)],[c_26,c_224])).

tff(c_48,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_179,plain,(
    ! [D_41,A_42,B_43] :
      ( ~ r2_hidden(D_41,A_42)
      | r2_hidden(D_41,k2_xboole_0(A_42,B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_194,plain,(
    ! [D_41] :
      ( ~ r2_hidden(D_41,k2_tarski('#skF_3','#skF_4'))
      | r2_hidden(D_41,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_179])).

tff(c_241,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_233,c_194])).

tff(c_566,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_562,c_241])).

tff(c_567,plain,(
    ! [B_82] : ~ r2_hidden(B_82,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_558])).

tff(c_571,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_567,c_241])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:35:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.32  
% 2.10/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.33  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 2.10/1.33  
% 2.10/1.33  %Foreground sorts:
% 2.10/1.33  
% 2.10/1.33  
% 2.10/1.33  %Background operators:
% 2.10/1.33  
% 2.10/1.33  
% 2.10/1.33  %Foreground operators:
% 2.10/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.10/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.10/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.10/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.10/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.10/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.10/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.10/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.10/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.10/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.10/1.33  
% 2.10/1.34  tff(f_46, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.10/1.34  tff(f_63, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.10/1.34  tff(f_60, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.10/1.34  tff(f_44, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.10/1.34  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.10/1.34  tff(f_67, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.10/1.34  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.10/1.34  tff(c_253, plain, (![A_62, B_63]: (k2_xboole_0(k1_tarski(A_62), k1_tarski(B_63))=k2_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.10/1.34  tff(c_46, plain, (![A_25, B_26]: (k2_xboole_0(k1_tarski(A_25), B_26)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.10/1.34  tff(c_273, plain, (![A_62, B_63]: (k2_tarski(A_62, B_63)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_253, c_46])).
% 2.10/1.34  tff(c_534, plain, (![A_81, B_82, C_83]: (r1_tarski(k2_tarski(A_81, B_82), C_83) | ~r2_hidden(B_82, C_83) | ~r2_hidden(A_81, C_83))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.10/1.34  tff(c_28, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.10/1.34  tff(c_243, plain, (![B_60, A_61]: (B_60=A_61 | ~r1_tarski(B_60, A_61) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.10/1.34  tff(c_252, plain, (![A_11]: (k1_xboole_0=A_11 | ~r1_tarski(A_11, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_243])).
% 2.10/1.34  tff(c_538, plain, (![A_81, B_82]: (k2_tarski(A_81, B_82)=k1_xboole_0 | ~r2_hidden(B_82, k1_xboole_0) | ~r2_hidden(A_81, k1_xboole_0))), inference(resolution, [status(thm)], [c_534, c_252])).
% 2.10/1.34  tff(c_558, plain, (![B_82, A_81]: (~r2_hidden(B_82, k1_xboole_0) | ~r2_hidden(A_81, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_273, c_538])).
% 2.10/1.34  tff(c_562, plain, (![A_81]: (~r2_hidden(A_81, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_558])).
% 2.10/1.34  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.10/1.34  tff(c_224, plain, (![B_55, C_56, A_57]: (r2_hidden(B_55, C_56) | ~r1_tarski(k2_tarski(A_57, B_55), C_56))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.10/1.34  tff(c_233, plain, (![B_58, A_59]: (r2_hidden(B_58, k2_tarski(A_59, B_58)))), inference(resolution, [status(thm)], [c_26, c_224])).
% 2.10/1.34  tff(c_48, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.10/1.34  tff(c_179, plain, (![D_41, A_42, B_43]: (~r2_hidden(D_41, A_42) | r2_hidden(D_41, k2_xboole_0(A_42, B_43)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.10/1.34  tff(c_194, plain, (![D_41]: (~r2_hidden(D_41, k2_tarski('#skF_3', '#skF_4')) | r2_hidden(D_41, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_48, c_179])).
% 2.10/1.34  tff(c_241, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_233, c_194])).
% 2.10/1.34  tff(c_566, plain, $false, inference(negUnitSimplification, [status(thm)], [c_562, c_241])).
% 2.10/1.34  tff(c_567, plain, (![B_82]: (~r2_hidden(B_82, k1_xboole_0))), inference(splitRight, [status(thm)], [c_558])).
% 2.10/1.34  tff(c_571, plain, $false, inference(negUnitSimplification, [status(thm)], [c_567, c_241])).
% 2.10/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.34  
% 2.10/1.34  Inference rules
% 2.10/1.34  ----------------------
% 2.10/1.34  #Ref     : 0
% 2.10/1.34  #Sup     : 133
% 2.10/1.34  #Fact    : 0
% 2.10/1.34  #Define  : 0
% 2.10/1.34  #Split   : 1
% 2.10/1.34  #Chain   : 0
% 2.10/1.34  #Close   : 0
% 2.10/1.34  
% 2.10/1.34  Ordering : KBO
% 2.10/1.34  
% 2.10/1.34  Simplification rules
% 2.10/1.34  ----------------------
% 2.10/1.34  #Subsume      : 30
% 2.10/1.34  #Demod        : 32
% 2.10/1.34  #Tautology    : 70
% 2.10/1.34  #SimpNegUnit  : 7
% 2.10/1.34  #BackRed      : 10
% 2.10/1.34  
% 2.10/1.34  #Partial instantiations: 0
% 2.10/1.34  #Strategies tried      : 1
% 2.10/1.34  
% 2.10/1.34  Timing (in seconds)
% 2.10/1.34  ----------------------
% 2.10/1.34  Preprocessing        : 0.30
% 2.10/1.34  Parsing              : 0.16
% 2.10/1.34  CNF conversion       : 0.02
% 2.10/1.34  Main loop            : 0.27
% 2.55/1.34  Inferencing          : 0.09
% 2.55/1.34  Reduction            : 0.10
% 2.55/1.34  Demodulation         : 0.08
% 2.55/1.34  BG Simplification    : 0.01
% 2.55/1.34  Subsumption          : 0.05
% 2.55/1.34  Abstraction          : 0.02
% 2.55/1.34  MUC search           : 0.00
% 2.55/1.34  Cooper               : 0.00
% 2.55/1.34  Total                : 0.60
% 2.55/1.34  Index Insertion      : 0.00
% 2.55/1.34  Index Deletion       : 0.00
% 2.55/1.34  Index Matching       : 0.00
% 2.55/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
