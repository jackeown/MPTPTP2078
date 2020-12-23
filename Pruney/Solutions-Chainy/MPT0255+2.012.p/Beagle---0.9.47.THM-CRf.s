%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:40 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   47 (  48 expanded)
%              Number of leaves         :   30 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   40 (  42 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_51,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_22,plain,(
    ! [D_22,B_18] : r2_hidden(D_22,k2_tarski(D_22,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_49,plain,(
    ! [B_39,A_40] :
      ( ~ r2_hidden(B_39,A_40)
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53,plain,(
    ! [D_22,B_18] : ~ v1_xboole_0(k2_tarski(D_22,B_18)) ),
    inference(resolution,[status(thm)],[c_22,c_49])).

tff(c_12,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    ! [B_16,A_15] : k2_tarski(B_16,A_15) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_44,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_45,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_5'),'#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_44])).

tff(c_14,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_149,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,B_53) = A_52
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_157,plain,(
    ! [A_13,B_14] : k3_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = A_13 ),
    inference(resolution,[status(thm)],[c_14,c_149])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_193,plain,(
    ! [A_58,B_59,C_60] :
      ( ~ r1_xboole_0(A_58,B_59)
      | ~ r2_hidden(C_60,k3_xboole_0(A_58,B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_363,plain,(
    ! [A_71,B_72] :
      ( ~ r1_xboole_0(A_71,B_72)
      | v1_xboole_0(k3_xboole_0(A_71,B_72)) ) ),
    inference(resolution,[status(thm)],[c_4,c_193])).

tff(c_399,plain,(
    ! [A_76,B_77] :
      ( ~ r1_xboole_0(A_76,k2_xboole_0(A_76,B_77))
      | v1_xboole_0(A_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_363])).

tff(c_411,plain,
    ( ~ r1_xboole_0(k2_tarski('#skF_6','#skF_5'),k1_xboole_0)
    | v1_xboole_0(k2_tarski('#skF_6','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_399])).

tff(c_415,plain,(
    v1_xboole_0(k2_tarski('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_411])).

tff(c_417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_415])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:28:53 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.51  
% 2.49/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.52  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2
% 2.49/1.52  
% 2.49/1.52  %Foreground sorts:
% 2.49/1.52  
% 2.49/1.52  
% 2.49/1.52  %Background operators:
% 2.49/1.52  
% 2.49/1.52  
% 2.49/1.52  %Foreground operators:
% 2.49/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.52  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.49/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.49/1.52  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.49/1.52  tff('#skF_7', type, '#skF_7': $i).
% 2.49/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.49/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.49/1.52  tff('#skF_5', type, '#skF_5': $i).
% 2.49/1.52  tff('#skF_6', type, '#skF_6': $i).
% 2.49/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.49/1.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.49/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.52  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.49/1.52  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.49/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.49/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.49/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.49/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.49/1.52  
% 2.67/1.54  tff(f_64, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.67/1.54  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.67/1.54  tff(f_51, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.67/1.54  tff(f_55, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.67/1.54  tff(f_76, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.67/1.54  tff(f_53, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.67/1.54  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.67/1.54  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.67/1.54  tff(c_22, plain, (![D_22, B_18]: (r2_hidden(D_22, k2_tarski(D_22, B_18)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.67/1.54  tff(c_49, plain, (![B_39, A_40]: (~r2_hidden(B_39, A_40) | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.67/1.54  tff(c_53, plain, (![D_22, B_18]: (~v1_xboole_0(k2_tarski(D_22, B_18)))), inference(resolution, [status(thm)], [c_22, c_49])).
% 2.67/1.54  tff(c_12, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.67/1.54  tff(c_16, plain, (![B_16, A_15]: (k2_tarski(B_16, A_15)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.67/1.54  tff(c_44, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.67/1.54  tff(c_45, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_5'), '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_44])).
% 2.67/1.54  tff(c_14, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.67/1.54  tff(c_149, plain, (![A_52, B_53]: (k3_xboole_0(A_52, B_53)=A_52 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.67/1.54  tff(c_157, plain, (![A_13, B_14]: (k3_xboole_0(A_13, k2_xboole_0(A_13, B_14))=A_13)), inference(resolution, [status(thm)], [c_14, c_149])).
% 2.67/1.54  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.67/1.54  tff(c_193, plain, (![A_58, B_59, C_60]: (~r1_xboole_0(A_58, B_59) | ~r2_hidden(C_60, k3_xboole_0(A_58, B_59)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.67/1.54  tff(c_363, plain, (![A_71, B_72]: (~r1_xboole_0(A_71, B_72) | v1_xboole_0(k3_xboole_0(A_71, B_72)))), inference(resolution, [status(thm)], [c_4, c_193])).
% 2.67/1.54  tff(c_399, plain, (![A_76, B_77]: (~r1_xboole_0(A_76, k2_xboole_0(A_76, B_77)) | v1_xboole_0(A_76))), inference(superposition, [status(thm), theory('equality')], [c_157, c_363])).
% 2.67/1.54  tff(c_411, plain, (~r1_xboole_0(k2_tarski('#skF_6', '#skF_5'), k1_xboole_0) | v1_xboole_0(k2_tarski('#skF_6', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_45, c_399])).
% 2.67/1.54  tff(c_415, plain, (v1_xboole_0(k2_tarski('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_411])).
% 2.67/1.54  tff(c_417, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_415])).
% 2.67/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.54  
% 2.67/1.54  Inference rules
% 2.67/1.54  ----------------------
% 2.67/1.54  #Ref     : 0
% 2.67/1.54  #Sup     : 92
% 2.67/1.54  #Fact    : 0
% 2.67/1.54  #Define  : 0
% 2.67/1.54  #Split   : 0
% 2.67/1.54  #Chain   : 0
% 2.67/1.54  #Close   : 0
% 2.67/1.54  
% 2.67/1.54  Ordering : KBO
% 2.67/1.54  
% 2.67/1.54  Simplification rules
% 2.67/1.54  ----------------------
% 2.67/1.54  #Subsume      : 4
% 2.67/1.54  #Demod        : 28
% 2.67/1.54  #Tautology    : 62
% 2.67/1.54  #SimpNegUnit  : 2
% 2.67/1.54  #BackRed      : 0
% 2.67/1.54  
% 2.67/1.54  #Partial instantiations: 0
% 2.67/1.54  #Strategies tried      : 1
% 2.67/1.54  
% 2.67/1.54  Timing (in seconds)
% 2.67/1.54  ----------------------
% 2.67/1.54  Preprocessing        : 0.45
% 2.67/1.54  Parsing              : 0.20
% 2.67/1.54  CNF conversion       : 0.04
% 2.67/1.54  Main loop            : 0.33
% 2.67/1.54  Inferencing          : 0.11
% 2.67/1.54  Reduction            : 0.12
% 2.67/1.54  Demodulation         : 0.10
% 2.67/1.54  BG Simplification    : 0.02
% 2.67/1.54  Subsumption          : 0.05
% 2.67/1.54  Abstraction          : 0.02
% 2.67/1.54  MUC search           : 0.00
% 2.67/1.54  Cooper               : 0.00
% 2.74/1.54  Total                : 0.82
% 2.74/1.54  Index Insertion      : 0.00
% 2.74/1.54  Index Deletion       : 0.00
% 2.74/1.54  Index Matching       : 0.00
% 2.74/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
