%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:11 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   32 (  39 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   31 (  47 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_22,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_59,plain,(
    ! [B_30,A_31] :
      ( B_30 = A_31
      | ~ r1_tarski(B_30,A_31)
      | ~ r1_tarski(A_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,
    ( k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_59])).

tff(c_135,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_138,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_135])).

tff(c_142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_138])).

tff(c_143,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_46,plain,(
    ! [A_22,C_23,B_24] :
      ( r2_hidden(A_22,C_23)
      | ~ r1_tarski(k2_tarski(A_22,B_24),C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_55,plain,(
    ! [A_22,B_24,B_7] : r2_hidden(A_22,k2_xboole_0(k2_tarski(A_22,B_24),B_7)) ),
    inference(resolution,[status(thm)],[c_10,c_46])).

tff(c_162,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_55])).

tff(c_170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_162])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:35:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.20  
% 1.78/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.20  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1
% 1.78/1.20  
% 1.78/1.20  %Foreground sorts:
% 1.78/1.20  
% 1.78/1.20  
% 1.78/1.20  %Background operators:
% 1.78/1.20  
% 1.78/1.20  
% 1.78/1.20  %Foreground operators:
% 1.78/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.78/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.78/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.78/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.78/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.78/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.78/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.78/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.20  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.78/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.78/1.20  
% 1.78/1.21  tff(f_52, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 1.78/1.21  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.78/1.21  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.78/1.21  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.78/1.21  tff(f_47, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.78/1.21  tff(c_22, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.78/1.21  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.78/1.21  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.78/1.21  tff(c_24, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.78/1.21  tff(c_59, plain, (![B_30, A_31]: (B_30=A_31 | ~r1_tarski(B_30, A_31) | ~r1_tarski(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.78/1.21  tff(c_66, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_59])).
% 1.78/1.21  tff(c_135, plain, (~r1_tarski('#skF_3', k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_66])).
% 1.78/1.21  tff(c_138, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_8, c_135])).
% 1.78/1.21  tff(c_142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_138])).
% 1.78/1.21  tff(c_143, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_66])).
% 1.78/1.21  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.78/1.21  tff(c_46, plain, (![A_22, C_23, B_24]: (r2_hidden(A_22, C_23) | ~r1_tarski(k2_tarski(A_22, B_24), C_23))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.78/1.21  tff(c_55, plain, (![A_22, B_24, B_7]: (r2_hidden(A_22, k2_xboole_0(k2_tarski(A_22, B_24), B_7)))), inference(resolution, [status(thm)], [c_10, c_46])).
% 1.78/1.21  tff(c_162, plain, (r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_143, c_55])).
% 1.78/1.21  tff(c_170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_162])).
% 1.78/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.21  
% 1.78/1.21  Inference rules
% 1.78/1.21  ----------------------
% 1.78/1.21  #Ref     : 0
% 1.78/1.21  #Sup     : 31
% 1.78/1.21  #Fact    : 0
% 1.78/1.21  #Define  : 0
% 1.78/1.21  #Split   : 1
% 1.78/1.21  #Chain   : 0
% 1.78/1.21  #Close   : 0
% 1.78/1.21  
% 1.78/1.21  Ordering : KBO
% 1.78/1.21  
% 1.78/1.21  Simplification rules
% 1.78/1.21  ----------------------
% 1.78/1.21  #Subsume      : 0
% 1.78/1.21  #Demod        : 6
% 1.78/1.21  #Tautology    : 11
% 1.78/1.21  #SimpNegUnit  : 1
% 1.78/1.21  #BackRed      : 1
% 1.78/1.21  
% 1.78/1.21  #Partial instantiations: 0
% 1.78/1.21  #Strategies tried      : 1
% 1.78/1.21  
% 1.78/1.21  Timing (in seconds)
% 1.78/1.21  ----------------------
% 1.78/1.21  Preprocessing        : 0.29
% 1.78/1.21  Parsing              : 0.15
% 1.78/1.21  CNF conversion       : 0.02
% 1.78/1.21  Main loop            : 0.15
% 1.78/1.22  Inferencing          : 0.05
% 1.78/1.22  Reduction            : 0.05
% 1.78/1.22  Demodulation         : 0.04
% 1.78/1.22  BG Simplification    : 0.01
% 1.78/1.22  Subsumption          : 0.03
% 1.78/1.22  Abstraction          : 0.01
% 1.78/1.22  MUC search           : 0.00
% 1.78/1.22  Cooper               : 0.00
% 1.78/1.22  Total                : 0.46
% 1.78/1.22  Index Insertion      : 0.00
% 1.78/1.22  Index Deletion       : 0.00
% 1.78/1.22  Index Matching       : 0.00
% 1.78/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
