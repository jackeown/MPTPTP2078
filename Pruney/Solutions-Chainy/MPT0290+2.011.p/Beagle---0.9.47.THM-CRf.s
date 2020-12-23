%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:34 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   38 (  47 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   34 (  50 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k3_tarski(k3_xboole_0(A,B)),k3_xboole_0(k3_tarski(A),k3_tarski(B))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_zfmisc_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : k2_xboole_0(A_4,k3_xboole_0(A_4,B_5)) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] : k2_xboole_0(k3_xboole_0(A_6,B_7),k3_xboole_0(A_6,C_8)) = k3_xboole_0(A_6,k2_xboole_0(B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11] : r1_tarski(k2_xboole_0(k3_xboole_0(A_9,B_10),k3_xboole_0(A_9,C_11)),k2_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_65,plain,(
    ! [A_32,B_33,C_34] : r1_tarski(k3_xboole_0(A_32,k2_xboole_0(B_33,C_34)),k2_xboole_0(B_33,C_34)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_68,plain,(
    ! [A_32,A_4,B_5] : r1_tarski(k3_xboole_0(A_32,A_4),k2_xboole_0(A_4,k3_xboole_0(A_4,B_5))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_65])).

tff(c_72,plain,(
    ! [A_32,A_4] : r1_tarski(k3_xboole_0(A_32,A_4),A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_68])).

tff(c_16,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(k3_tarski(A_18),k3_tarski(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_39,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_48,plain,(
    ! [A_26,B_27] : r1_tarski(k3_xboole_0(A_26,B_27),A_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_10])).

tff(c_94,plain,(
    ! [A_39,B_40,C_41] :
      ( r1_tarski(A_39,k3_xboole_0(B_40,C_41))
      | ~ r1_tarski(A_39,C_41)
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k3_tarski('#skF_1'),k3_tarski('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_98,plain,
    ( ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_tarski('#skF_2'))
    | ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_94,c_18])).

tff(c_156,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_tarski('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_159,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_156])).

tff(c_163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_159])).

tff(c_164,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_168,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_164])).

tff(c_172,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_168])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:49:50 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.26  
% 1.91/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.26  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_1
% 1.91/1.26  
% 1.91/1.26  %Foreground sorts:
% 1.91/1.26  
% 1.91/1.26  
% 1.91/1.26  %Background operators:
% 1.91/1.26  
% 1.91/1.26  
% 1.91/1.26  %Foreground operators:
% 1.91/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.91/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.91/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.91/1.26  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.91/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.91/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.91/1.26  
% 1.91/1.27  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 1.91/1.27  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 1.91/1.27  tff(f_37, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 1.91/1.27  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 1.91/1.27  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.91/1.27  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.91/1.27  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 1.91/1.27  tff(f_50, negated_conjecture, ~(![A, B]: r1_tarski(k3_tarski(k3_xboole_0(A, B)), k3_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_zfmisc_1)).
% 1.91/1.27  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, k3_xboole_0(A_4, B_5))=A_4)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.91/1.27  tff(c_6, plain, (![A_6, B_7, C_8]: (k2_xboole_0(k3_xboole_0(A_6, B_7), k3_xboole_0(A_6, C_8))=k3_xboole_0(A_6, k2_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.91/1.27  tff(c_8, plain, (![A_9, B_10, C_11]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_9, B_10), k3_xboole_0(A_9, C_11)), k2_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.91/1.27  tff(c_65, plain, (![A_32, B_33, C_34]: (r1_tarski(k3_xboole_0(A_32, k2_xboole_0(B_33, C_34)), k2_xboole_0(B_33, C_34)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 1.91/1.27  tff(c_68, plain, (![A_32, A_4, B_5]: (r1_tarski(k3_xboole_0(A_32, A_4), k2_xboole_0(A_4, k3_xboole_0(A_4, B_5))))), inference(superposition, [status(thm), theory('equality')], [c_4, c_65])).
% 1.91/1.27  tff(c_72, plain, (![A_32, A_4]: (r1_tarski(k3_xboole_0(A_32, A_4), A_4))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_68])).
% 1.91/1.27  tff(c_16, plain, (![A_18, B_19]: (r1_tarski(k3_tarski(A_18), k3_tarski(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.91/1.27  tff(c_39, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.91/1.27  tff(c_10, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.91/1.27  tff(c_48, plain, (![A_26, B_27]: (r1_tarski(k3_xboole_0(A_26, B_27), A_26))), inference(superposition, [status(thm), theory('equality')], [c_39, c_10])).
% 1.91/1.27  tff(c_94, plain, (![A_39, B_40, C_41]: (r1_tarski(A_39, k3_xboole_0(B_40, C_41)) | ~r1_tarski(A_39, C_41) | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.91/1.27  tff(c_18, plain, (~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k3_tarski('#skF_1'), k3_tarski('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.91/1.27  tff(c_98, plain, (~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_tarski('#skF_2')) | ~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_94, c_18])).
% 1.91/1.27  tff(c_156, plain, (~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_tarski('#skF_1'))), inference(splitLeft, [status(thm)], [c_98])).
% 1.91/1.27  tff(c_159, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_16, c_156])).
% 1.91/1.27  tff(c_163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_159])).
% 1.91/1.27  tff(c_164, plain, (~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_98])).
% 1.91/1.27  tff(c_168, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_16, c_164])).
% 1.91/1.27  tff(c_172, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_168])).
% 1.91/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.27  
% 1.91/1.27  Inference rules
% 1.91/1.27  ----------------------
% 1.91/1.27  #Ref     : 0
% 1.91/1.27  #Sup     : 33
% 1.91/1.27  #Fact    : 0
% 1.91/1.27  #Define  : 0
% 1.91/1.27  #Split   : 1
% 1.91/1.27  #Chain   : 0
% 1.91/1.27  #Close   : 0
% 1.91/1.27  
% 1.91/1.27  Ordering : KBO
% 1.91/1.27  
% 1.91/1.27  Simplification rules
% 1.91/1.27  ----------------------
% 1.91/1.27  #Subsume      : 0
% 1.91/1.27  #Demod        : 9
% 1.91/1.27  #Tautology    : 14
% 1.91/1.27  #SimpNegUnit  : 0
% 1.91/1.27  #BackRed      : 0
% 1.91/1.27  
% 1.91/1.27  #Partial instantiations: 0
% 1.91/1.27  #Strategies tried      : 1
% 1.91/1.27  
% 1.91/1.27  Timing (in seconds)
% 1.91/1.27  ----------------------
% 1.91/1.28  Preprocessing        : 0.29
% 1.91/1.28  Parsing              : 0.16
% 1.91/1.28  CNF conversion       : 0.02
% 1.91/1.28  Main loop            : 0.16
% 1.91/1.28  Inferencing          : 0.06
% 1.91/1.28  Reduction            : 0.05
% 1.91/1.28  Demodulation         : 0.04
% 1.91/1.28  BG Simplification    : 0.01
% 1.91/1.28  Subsumption          : 0.03
% 1.91/1.28  Abstraction          : 0.01
% 1.91/1.28  MUC search           : 0.00
% 1.91/1.28  Cooper               : 0.00
% 1.91/1.28  Total                : 0.48
% 1.91/1.28  Index Insertion      : 0.00
% 1.91/1.28  Index Deletion       : 0.00
% 1.91/1.28  Index Matching       : 0.00
% 1.91/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
