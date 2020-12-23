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
% DateTime   : Thu Dec  3 09:53:34 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   37 (  49 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   34 (  53 expanded)
%              Number of equality atoms :    7 (  12 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k3_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_45,axiom,(
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

tff(f_48,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k3_tarski(k3_xboole_0(A,B)),k3_xboole_0(k3_tarski(A),k3_tarski(B))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_zfmisc_1)).

tff(c_27,plain,(
    ! [A_21,B_22] : k3_xboole_0(A_21,k2_xboole_0(A_21,B_22)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k3_xboole_0(A_6,B_7)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_33,plain,(
    ! [A_21] : k2_xboole_0(A_21,A_21) = A_21 ),
    inference(superposition,[status(thm),theory(equality)],[c_27,c_6])).

tff(c_151,plain,(
    ! [A_36,B_37,C_38] : r1_tarski(k2_xboole_0(k3_xboole_0(A_36,B_37),k3_xboole_0(A_36,C_38)),k2_xboole_0(B_37,C_38)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_170,plain,(
    ! [A_36,B_37] : r1_tarski(k3_xboole_0(A_36,B_37),k2_xboole_0(B_37,B_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_151])).

tff(c_184,plain,(
    ! [A_36,B_37] : r1_tarski(k3_xboole_0(A_36,B_37),B_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_170])).

tff(c_14,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(k3_tarski(A_15),k3_tarski(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_67,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_76,plain,(
    ! [A_25,B_26] : r1_tarski(k3_xboole_0(A_25,B_26),A_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_10])).

tff(c_214,plain,(
    ! [A_43,B_44,C_45] :
      ( r1_tarski(A_43,k3_xboole_0(B_44,C_45))
      | ~ r1_tarski(A_43,C_45)
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k3_tarski('#skF_1'),k3_tarski('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_227,plain,
    ( ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_tarski('#skF_2'))
    | ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_214,c_16])).

tff(c_462,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_tarski('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_227])).

tff(c_465,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_462])).

tff(c_469,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_465])).

tff(c_470,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_474,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_470])).

tff(c_478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_474])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n021.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 11:01:34 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.24  
% 2.18/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.24  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k3_tarski > #skF_2 > #skF_1
% 2.18/1.24  
% 2.18/1.24  %Foreground sorts:
% 2.18/1.24  
% 2.18/1.24  
% 2.18/1.24  %Background operators:
% 2.18/1.24  
% 2.18/1.24  
% 2.18/1.24  %Foreground operators:
% 2.18/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.18/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.18/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.18/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.18/1.24  
% 2.18/1.25  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.18/1.25  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.18/1.25  tff(f_37, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 2.18/1.25  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 2.18/1.25  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.18/1.25  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.18/1.25  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.18/1.25  tff(f_48, negated_conjecture, ~(![A, B]: r1_tarski(k3_tarski(k3_xboole_0(A, B)), k3_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_zfmisc_1)).
% 2.18/1.25  tff(c_27, plain, (![A_21, B_22]: (k3_xboole_0(A_21, k2_xboole_0(A_21, B_22))=A_21)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.18/1.25  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k3_xboole_0(A_6, B_7))=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.18/1.25  tff(c_33, plain, (![A_21]: (k2_xboole_0(A_21, A_21)=A_21)), inference(superposition, [status(thm), theory('equality')], [c_27, c_6])).
% 2.18/1.25  tff(c_151, plain, (![A_36, B_37, C_38]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_36, B_37), k3_xboole_0(A_36, C_38)), k2_xboole_0(B_37, C_38)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.18/1.25  tff(c_170, plain, (![A_36, B_37]: (r1_tarski(k3_xboole_0(A_36, B_37), k2_xboole_0(B_37, B_37)))), inference(superposition, [status(thm), theory('equality')], [c_33, c_151])).
% 2.18/1.25  tff(c_184, plain, (![A_36, B_37]: (r1_tarski(k3_xboole_0(A_36, B_37), B_37))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_170])).
% 2.18/1.25  tff(c_14, plain, (![A_15, B_16]: (r1_tarski(k3_tarski(A_15), k3_tarski(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.18/1.25  tff(c_67, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.18/1.25  tff(c_10, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.18/1.25  tff(c_76, plain, (![A_25, B_26]: (r1_tarski(k3_xboole_0(A_25, B_26), A_25))), inference(superposition, [status(thm), theory('equality')], [c_67, c_10])).
% 2.18/1.25  tff(c_214, plain, (![A_43, B_44, C_45]: (r1_tarski(A_43, k3_xboole_0(B_44, C_45)) | ~r1_tarski(A_43, C_45) | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.18/1.25  tff(c_16, plain, (~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k3_tarski('#skF_1'), k3_tarski('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.18/1.25  tff(c_227, plain, (~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_tarski('#skF_2')) | ~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_214, c_16])).
% 2.18/1.25  tff(c_462, plain, (~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_tarski('#skF_1'))), inference(splitLeft, [status(thm)], [c_227])).
% 2.18/1.25  tff(c_465, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_14, c_462])).
% 2.18/1.25  tff(c_469, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_465])).
% 2.18/1.25  tff(c_470, plain, (~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_227])).
% 2.18/1.25  tff(c_474, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_14, c_470])).
% 2.18/1.25  tff(c_478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_184, c_474])).
% 2.18/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.25  
% 2.18/1.25  Inference rules
% 2.18/1.25  ----------------------
% 2.18/1.25  #Ref     : 0
% 2.18/1.25  #Sup     : 114
% 2.18/1.25  #Fact    : 0
% 2.18/1.25  #Define  : 0
% 2.18/1.25  #Split   : 1
% 2.18/1.25  #Chain   : 0
% 2.18/1.25  #Close   : 0
% 2.18/1.25  
% 2.18/1.25  Ordering : KBO
% 2.18/1.25  
% 2.18/1.25  Simplification rules
% 2.18/1.25  ----------------------
% 2.18/1.25  #Subsume      : 0
% 2.18/1.25  #Demod        : 97
% 2.18/1.25  #Tautology    : 72
% 2.18/1.25  #SimpNegUnit  : 0
% 2.18/1.25  #BackRed      : 0
% 2.18/1.25  
% 2.18/1.25  #Partial instantiations: 0
% 2.18/1.25  #Strategies tried      : 1
% 2.18/1.25  
% 2.18/1.25  Timing (in seconds)
% 2.18/1.25  ----------------------
% 2.18/1.25  Preprocessing        : 0.26
% 2.18/1.25  Parsing              : 0.15
% 2.18/1.25  CNF conversion       : 0.01
% 2.18/1.25  Main loop            : 0.25
% 2.18/1.25  Inferencing          : 0.10
% 2.18/1.25  Reduction            : 0.08
% 2.18/1.25  Demodulation         : 0.07
% 2.18/1.25  BG Simplification    : 0.01
% 2.18/1.25  Subsumption          : 0.05
% 2.18/1.25  Abstraction          : 0.01
% 2.18/1.25  MUC search           : 0.00
% 2.18/1.25  Cooper               : 0.00
% 2.18/1.26  Total                : 0.53
% 2.18/1.26  Index Insertion      : 0.00
% 2.18/1.26  Index Deletion       : 0.00
% 2.18/1.26  Index Matching       : 0.00
% 2.18/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
