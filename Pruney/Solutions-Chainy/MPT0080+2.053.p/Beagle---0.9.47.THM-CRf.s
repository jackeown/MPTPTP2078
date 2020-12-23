%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:56 EST 2020

% Result     : Theorem 5.74s
% Output     : CNFRefutation 5.79s
% Verified   : 
% Statistics : Number of formulae       :   36 (  38 expanded)
%              Number of leaves         :   19 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 (  52 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_33,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(A_21,B_22)
      | k4_xboole_0(A_21,B_22) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_37,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_33,c_18])).

tff(c_22,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_245,plain,(
    ! [A_41,B_42,C_43] :
      ( r1_tarski(k4_xboole_0(A_41,B_42),C_43)
      | ~ r1_tarski(A_41,k2_xboole_0(B_42,C_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_145,plain,(
    ! [A_31,C_32,B_33] :
      ( r1_xboole_0(A_31,C_32)
      | ~ r1_xboole_0(B_33,C_32)
      | ~ r1_tarski(A_31,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_152,plain,(
    ! [A_34] :
      ( r1_xboole_0(A_34,'#skF_3')
      | ~ r1_tarski(A_34,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20,c_145])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( ~ r1_xboole_0(B_15,A_14)
      | ~ r1_tarski(B_15,A_14)
      | v1_xboole_0(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_161,plain,(
    ! [A_34] :
      ( ~ r1_tarski(A_34,'#skF_3')
      | v1_xboole_0(A_34)
      | ~ r1_tarski(A_34,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_152,c_16])).

tff(c_4714,plain,(
    ! [A_353,B_354] :
      ( v1_xboole_0(k4_xboole_0(A_353,B_354))
      | ~ r1_tarski(k4_xboole_0(A_353,B_354),'#skF_1')
      | ~ r1_tarski(A_353,k2_xboole_0(B_354,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_245,c_161])).

tff(c_4797,plain,(
    ! [B_359] :
      ( v1_xboole_0(k4_xboole_0('#skF_1',B_359))
      | ~ r1_tarski('#skF_1',k2_xboole_0(B_359,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_10,c_4714])).

tff(c_4805,plain,(
    v1_xboole_0(k4_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_4797])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4808,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4805,c_2])).

tff(c_4812,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_4808])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:15:40 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.74/2.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.74/2.12  
% 5.74/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.79/2.12  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.79/2.12  
% 5.79/2.12  %Foreground sorts:
% 5.79/2.12  
% 5.79/2.12  
% 5.79/2.12  %Background operators:
% 5.79/2.12  
% 5.79/2.12  
% 5.79/2.12  %Foreground operators:
% 5.79/2.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.79/2.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.79/2.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.79/2.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.79/2.12  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.79/2.12  tff('#skF_2', type, '#skF_2': $i).
% 5.79/2.12  tff('#skF_3', type, '#skF_3': $i).
% 5.79/2.12  tff('#skF_1', type, '#skF_1': $i).
% 5.79/2.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.79/2.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.79/2.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.79/2.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.79/2.12  
% 5.79/2.13  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.79/2.13  tff(f_64, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 5.79/2.13  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.79/2.13  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 5.79/2.13  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 5.79/2.13  tff(f_57, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 5.79/2.13  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.79/2.13  tff(c_33, plain, (![A_21, B_22]: (r1_tarski(A_21, B_22) | k4_xboole_0(A_21, B_22)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.79/2.13  tff(c_18, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.79/2.13  tff(c_37, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_33, c_18])).
% 5.79/2.13  tff(c_22, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.79/2.13  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.79/2.13  tff(c_245, plain, (![A_41, B_42, C_43]: (r1_tarski(k4_xboole_0(A_41, B_42), C_43) | ~r1_tarski(A_41, k2_xboole_0(B_42, C_43)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.79/2.13  tff(c_20, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.79/2.13  tff(c_145, plain, (![A_31, C_32, B_33]: (r1_xboole_0(A_31, C_32) | ~r1_xboole_0(B_33, C_32) | ~r1_tarski(A_31, B_33))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.79/2.13  tff(c_152, plain, (![A_34]: (r1_xboole_0(A_34, '#skF_3') | ~r1_tarski(A_34, '#skF_1'))), inference(resolution, [status(thm)], [c_20, c_145])).
% 5.79/2.13  tff(c_16, plain, (![B_15, A_14]: (~r1_xboole_0(B_15, A_14) | ~r1_tarski(B_15, A_14) | v1_xboole_0(B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.79/2.13  tff(c_161, plain, (![A_34]: (~r1_tarski(A_34, '#skF_3') | v1_xboole_0(A_34) | ~r1_tarski(A_34, '#skF_1'))), inference(resolution, [status(thm)], [c_152, c_16])).
% 5.79/2.13  tff(c_4714, plain, (![A_353, B_354]: (v1_xboole_0(k4_xboole_0(A_353, B_354)) | ~r1_tarski(k4_xboole_0(A_353, B_354), '#skF_1') | ~r1_tarski(A_353, k2_xboole_0(B_354, '#skF_3')))), inference(resolution, [status(thm)], [c_245, c_161])).
% 5.79/2.13  tff(c_4797, plain, (![B_359]: (v1_xboole_0(k4_xboole_0('#skF_1', B_359)) | ~r1_tarski('#skF_1', k2_xboole_0(B_359, '#skF_3')))), inference(resolution, [status(thm)], [c_10, c_4714])).
% 5.79/2.13  tff(c_4805, plain, (v1_xboole_0(k4_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_4797])).
% 5.79/2.13  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.79/2.13  tff(c_4808, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_4805, c_2])).
% 5.79/2.13  tff(c_4812, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37, c_4808])).
% 5.79/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.79/2.13  
% 5.79/2.13  Inference rules
% 5.79/2.13  ----------------------
% 5.79/2.13  #Ref     : 0
% 5.79/2.13  #Sup     : 1163
% 5.79/2.13  #Fact    : 0
% 5.79/2.13  #Define  : 0
% 5.79/2.13  #Split   : 23
% 5.79/2.13  #Chain   : 0
% 5.79/2.13  #Close   : 0
% 5.79/2.13  
% 5.79/2.13  Ordering : KBO
% 5.79/2.13  
% 5.79/2.13  Simplification rules
% 5.79/2.13  ----------------------
% 5.79/2.13  #Subsume      : 253
% 5.79/2.13  #Demod        : 688
% 5.79/2.13  #Tautology    : 503
% 5.79/2.13  #SimpNegUnit  : 1
% 5.79/2.13  #BackRed      : 21
% 5.79/2.13  
% 5.79/2.13  #Partial instantiations: 0
% 5.79/2.13  #Strategies tried      : 1
% 5.79/2.13  
% 5.79/2.13  Timing (in seconds)
% 5.79/2.13  ----------------------
% 5.79/2.13  Preprocessing        : 0.26
% 5.79/2.13  Parsing              : 0.15
% 5.79/2.13  CNF conversion       : 0.02
% 5.79/2.13  Main loop            : 1.09
% 5.79/2.13  Inferencing          : 0.38
% 5.79/2.13  Reduction            : 0.33
% 5.79/2.13  Demodulation         : 0.22
% 5.79/2.13  BG Simplification    : 0.03
% 5.79/2.13  Subsumption          : 0.27
% 5.79/2.13  Abstraction          : 0.04
% 5.79/2.13  MUC search           : 0.00
% 5.79/2.13  Cooper               : 0.00
% 5.79/2.13  Total                : 1.38
% 5.79/2.13  Index Insertion      : 0.00
% 5.79/2.13  Index Deletion       : 0.00
% 5.79/2.13  Index Matching       : 0.00
% 5.79/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
