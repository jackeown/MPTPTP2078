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
% DateTime   : Thu Dec  3 09:51:26 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   37 (  37 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   28 (  28 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_53,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_34,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_xboole_0)).

tff(c_53,plain,(
    ! [A_28] : k2_tarski(A_28,A_28) = k1_tarski(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    ! [D_16,B_12] : r2_hidden(D_16,k2_tarski(D_16,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_38,plain,(
    ! [B_22,A_23] :
      ( ~ r2_hidden(B_22,A_23)
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_42,plain,(
    ! [D_16,B_12] : ~ v1_xboole_0(k2_tarski(D_16,B_12)) ),
    inference(resolution,[status(thm)],[c_18,c_38])).

tff(c_61,plain,(
    ! [A_28] : ~ v1_xboole_0(k1_tarski(A_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_42])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_88,plain,(
    ! [B_34,A_35] : k2_xboole_0(B_34,A_35) = k2_xboole_0(A_35,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_109,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_36])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( ~ v1_xboole_0(k2_xboole_0(B_8,A_7))
      | v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_142,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_10])).

tff(c_146,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_142])).

tff(c_148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_146])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:17:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.16  
% 1.89/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.16  %$ r2_hidden > v1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 1.89/1.16  
% 1.89/1.16  %Foreground sorts:
% 1.89/1.16  
% 1.89/1.16  
% 1.89/1.16  %Background operators:
% 1.89/1.16  
% 1.89/1.16  
% 1.89/1.16  %Foreground operators:
% 1.89/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.89/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.89/1.16  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.89/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.89/1.16  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.89/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.89/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.89/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.89/1.16  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.89/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.89/1.16  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.89/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.89/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.89/1.16  
% 1.89/1.17  tff(f_53, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.89/1.17  tff(f_51, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.89/1.17  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.89/1.17  tff(f_34, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.89/1.17  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.89/1.17  tff(f_59, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.89/1.17  tff(f_40, axiom, (![A, B]: (~v1_xboole_0(A) => ~v1_xboole_0(k2_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_xboole_0)).
% 1.89/1.17  tff(c_53, plain, (![A_28]: (k2_tarski(A_28, A_28)=k1_tarski(A_28))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.89/1.17  tff(c_18, plain, (![D_16, B_12]: (r2_hidden(D_16, k2_tarski(D_16, B_12)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.89/1.17  tff(c_38, plain, (![B_22, A_23]: (~r2_hidden(B_22, A_23) | ~v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.89/1.17  tff(c_42, plain, (![D_16, B_12]: (~v1_xboole_0(k2_tarski(D_16, B_12)))), inference(resolution, [status(thm)], [c_18, c_38])).
% 1.89/1.17  tff(c_61, plain, (![A_28]: (~v1_xboole_0(k1_tarski(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_53, c_42])).
% 1.89/1.17  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.89/1.17  tff(c_88, plain, (![B_34, A_35]: (k2_xboole_0(B_34, A_35)=k2_xboole_0(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.89/1.17  tff(c_36, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.89/1.17  tff(c_109, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_88, c_36])).
% 1.89/1.17  tff(c_10, plain, (![B_8, A_7]: (~v1_xboole_0(k2_xboole_0(B_8, A_7)) | v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.89/1.17  tff(c_142, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_10])).
% 1.89/1.17  tff(c_146, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_142])).
% 1.89/1.17  tff(c_148, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_146])).
% 1.89/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.17  
% 1.89/1.17  Inference rules
% 1.89/1.17  ----------------------
% 1.89/1.17  #Ref     : 0
% 1.89/1.17  #Sup     : 29
% 1.89/1.17  #Fact    : 0
% 1.89/1.17  #Define  : 0
% 1.89/1.17  #Split   : 0
% 1.89/1.17  #Chain   : 0
% 1.89/1.17  #Close   : 0
% 1.89/1.17  
% 1.89/1.17  Ordering : KBO
% 1.89/1.17  
% 1.89/1.17  Simplification rules
% 1.89/1.17  ----------------------
% 1.89/1.17  #Subsume      : 2
% 1.89/1.17  #Demod        : 3
% 1.89/1.17  #Tautology    : 15
% 1.89/1.17  #SimpNegUnit  : 1
% 1.89/1.17  #BackRed      : 0
% 1.89/1.17  
% 1.89/1.17  #Partial instantiations: 0
% 1.89/1.17  #Strategies tried      : 1
% 1.89/1.17  
% 1.89/1.17  Timing (in seconds)
% 1.89/1.17  ----------------------
% 1.89/1.18  Preprocessing        : 0.30
% 1.89/1.18  Parsing              : 0.15
% 1.89/1.18  CNF conversion       : 0.02
% 1.89/1.18  Main loop            : 0.13
% 1.89/1.18  Inferencing          : 0.04
% 1.89/1.18  Reduction            : 0.05
% 1.89/1.18  Demodulation         : 0.04
% 1.89/1.18  BG Simplification    : 0.01
% 1.89/1.18  Subsumption          : 0.02
% 1.89/1.18  Abstraction          : 0.01
% 1.89/1.18  MUC search           : 0.00
% 1.89/1.18  Cooper               : 0.00
% 1.89/1.18  Total                : 0.46
% 1.89/1.18  Index Insertion      : 0.00
% 1.89/1.18  Index Deletion       : 0.00
% 1.89/1.18  Index Matching       : 0.00
% 1.89/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
