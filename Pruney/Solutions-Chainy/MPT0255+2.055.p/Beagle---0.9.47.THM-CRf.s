%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:46 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   34 (  34 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  25 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_49,axiom,(
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

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_xboole_0)).

tff(c_38,plain,(
    ! [D_24,B_25] : r2_hidden(D_24,k2_tarski(D_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_42,plain,(
    ! [D_24,B_25] : ~ v1_xboole_0(k2_tarski(D_24,B_25)) ),
    inference(resolution,[status(thm)],[c_38,c_4])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_36,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_59,plain,(
    ! [B_32,A_33] : k2_xboole_0(B_32,A_33) = k2_xboole_0(A_33,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_98,plain,(
    k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_59])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( ~ v1_xboole_0(k2_xboole_0(B_8,A_7))
      | v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_113,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_10])).

tff(c_117,plain,(
    v1_xboole_0(k2_tarski('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_113])).

tff(c_119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_117])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.34  % CPULimit   : 60
% 0.20/0.34  % DateTime   : Tue Dec  1 11:33:51 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.15  
% 1.67/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.15  %$ r2_hidden > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 1.67/1.15  
% 1.67/1.15  %Foreground sorts:
% 1.67/1.15  
% 1.67/1.15  
% 1.67/1.15  %Background operators:
% 1.67/1.15  
% 1.67/1.15  
% 1.67/1.15  %Foreground operators:
% 1.67/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.67/1.15  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.67/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.67/1.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.67/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.67/1.15  tff('#skF_5', type, '#skF_5': $i).
% 1.67/1.15  tff('#skF_6', type, '#skF_6': $i).
% 1.67/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.67/1.15  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.67/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.15  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.67/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.67/1.15  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.67/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.67/1.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.67/1.15  
% 1.67/1.16  tff(f_49, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.67/1.16  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.67/1.16  tff(f_34, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.67/1.16  tff(f_59, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 1.67/1.16  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.67/1.16  tff(f_40, axiom, (![A, B]: (~v1_xboole_0(A) => ~v1_xboole_0(k2_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_xboole_0)).
% 1.67/1.16  tff(c_38, plain, (![D_24, B_25]: (r2_hidden(D_24, k2_tarski(D_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.67/1.16  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.67/1.16  tff(c_42, plain, (![D_24, B_25]: (~v1_xboole_0(k2_tarski(D_24, B_25)))), inference(resolution, [status(thm)], [c_38, c_4])).
% 1.67/1.16  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.67/1.16  tff(c_36, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.67/1.16  tff(c_59, plain, (![B_32, A_33]: (k2_xboole_0(B_32, A_33)=k2_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.67/1.16  tff(c_98, plain, (k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_36, c_59])).
% 1.67/1.16  tff(c_10, plain, (![B_8, A_7]: (~v1_xboole_0(k2_xboole_0(B_8, A_7)) | v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.67/1.16  tff(c_113, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_98, c_10])).
% 1.67/1.16  tff(c_117, plain, (v1_xboole_0(k2_tarski('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_113])).
% 1.67/1.16  tff(c_119, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_117])).
% 1.67/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.16  
% 1.67/1.16  Inference rules
% 1.67/1.16  ----------------------
% 1.67/1.16  #Ref     : 0
% 1.67/1.16  #Sup     : 22
% 1.67/1.16  #Fact    : 0
% 1.67/1.16  #Define  : 0
% 1.67/1.16  #Split   : 0
% 1.67/1.16  #Chain   : 0
% 1.67/1.16  #Close   : 0
% 1.67/1.16  
% 1.67/1.16  Ordering : KBO
% 1.67/1.16  
% 1.67/1.16  Simplification rules
% 1.67/1.16  ----------------------
% 1.67/1.16  #Subsume      : 1
% 1.67/1.16  #Demod        : 2
% 1.67/1.16  #Tautology    : 11
% 1.67/1.16  #SimpNegUnit  : 1
% 1.67/1.16  #BackRed      : 0
% 1.67/1.16  
% 1.67/1.16  #Partial instantiations: 0
% 1.67/1.16  #Strategies tried      : 1
% 1.67/1.16  
% 1.67/1.16  Timing (in seconds)
% 1.67/1.16  ----------------------
% 1.67/1.16  Preprocessing        : 0.30
% 1.67/1.16  Parsing              : 0.16
% 1.67/1.16  CNF conversion       : 0.02
% 1.67/1.16  Main loop            : 0.10
% 1.67/1.16  Inferencing          : 0.03
% 1.67/1.16  Reduction            : 0.04
% 1.67/1.16  Demodulation         : 0.03
% 1.67/1.16  BG Simplification    : 0.01
% 1.67/1.16  Subsumption          : 0.02
% 1.67/1.16  Abstraction          : 0.01
% 1.67/1.16  MUC search           : 0.00
% 1.67/1.16  Cooper               : 0.00
% 1.67/1.16  Total                : 0.43
% 1.67/1.16  Index Insertion      : 0.00
% 1.67/1.16  Index Deletion       : 0.00
% 1.67/1.16  Index Matching       : 0.00
% 1.67/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
