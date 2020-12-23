%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:53 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :   40 (  44 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :   50 (  60 expanded)
%              Number of equality atoms :   18 (  20 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(k3_tarski(A),B)
          & r2_hidden(C,A) )
       => r1_tarski(C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

tff(f_41,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_46,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | k4_xboole_0(A_18,B_19) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_59,plain,(
    k4_xboole_0('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_22])).

tff(c_24,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(k1_tarski(A_9),B_10) = k1_xboole_0
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | k4_xboole_0(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_11] : k3_tarski(k1_tarski(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    r1_tarski(k3_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_76,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(k3_tarski(A_24),k3_tarski(B_25))
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = k1_xboole_0
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_165,plain,(
    ! [A_41,B_42] :
      ( k4_xboole_0(k3_tarski(A_41),k3_tarski(B_42)) = k1_xboole_0
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(resolution,[status(thm)],[c_76,c_10])).

tff(c_6,plain,(
    ! [C_5,B_4,A_3] :
      ( r1_tarski(k4_xboole_0(C_5,B_4),k4_xboole_0(C_5,A_3))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1121,plain,(
    ! [A_119,B_120,B_121] :
      ( r1_tarski(k4_xboole_0(k3_tarski(A_119),B_120),k1_xboole_0)
      | ~ r1_tarski(k3_tarski(B_121),B_120)
      | ~ r1_tarski(A_119,B_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_6])).

tff(c_1175,plain,(
    ! [A_124] :
      ( r1_tarski(k4_xboole_0(k3_tarski(A_124),'#skF_2'),k1_xboole_0)
      | ~ r1_tarski(A_124,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_1121])).

tff(c_12,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1207,plain,(
    ! [A_125] :
      ( k4_xboole_0(k3_tarski(A_125),'#skF_2') = k1_xboole_0
      | ~ r1_tarski(A_125,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1175,c_12])).

tff(c_1286,plain,(
    ! [A_127] :
      ( k4_xboole_0(A_127,'#skF_2') = k1_xboole_0
      | ~ r1_tarski(k1_tarski(A_127),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1207])).

tff(c_1777,plain,(
    ! [A_151] :
      ( k4_xboole_0(A_151,'#skF_2') = k1_xboole_0
      | k4_xboole_0(k1_tarski(A_151),'#skF_1') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_1286])).

tff(c_1783,plain,(
    ! [A_152] :
      ( k4_xboole_0(A_152,'#skF_2') = k1_xboole_0
      | ~ r2_hidden(A_152,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1777])).

tff(c_1786,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_1783])).

tff(c_1790,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_1786])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n002.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 14:24:36 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.82/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.67  
% 3.82/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.67  %$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.82/1.67  
% 3.82/1.67  %Foreground sorts:
% 3.82/1.67  
% 3.82/1.67  
% 3.82/1.67  %Background operators:
% 3.82/1.67  
% 3.82/1.67  
% 3.82/1.67  %Foreground operators:
% 3.82/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.82/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.82/1.67  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.82/1.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.82/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.82/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.82/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.82/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.82/1.67  tff('#skF_1', type, '#skF_1': $i).
% 3.82/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.82/1.67  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.82/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.82/1.67  
% 3.82/1.68  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 3.82/1.68  tff(f_58, negated_conjecture, ~(![A, B, C]: ((r1_tarski(k3_tarski(A), B) & r2_hidden(C, A)) => r1_tarski(C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_setfam_1)).
% 3.82/1.68  tff(f_45, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 3.82/1.68  tff(f_47, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 3.82/1.68  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 3.82/1.68  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_xboole_1)).
% 3.82/1.68  tff(f_41, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.82/1.68  tff(c_46, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | k4_xboole_0(A_18, B_19)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.82/1.68  tff(c_22, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.82/1.68  tff(c_59, plain, (k4_xboole_0('#skF_3', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_22])).
% 3.82/1.68  tff(c_24, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.82/1.68  tff(c_16, plain, (![A_9, B_10]: (k4_xboole_0(k1_tarski(A_9), B_10)=k1_xboole_0 | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.82/1.68  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | k4_xboole_0(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.82/1.68  tff(c_18, plain, (![A_11]: (k3_tarski(k1_tarski(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.82/1.68  tff(c_26, plain, (r1_tarski(k3_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.82/1.68  tff(c_76, plain, (![A_24, B_25]: (r1_tarski(k3_tarski(A_24), k3_tarski(B_25)) | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.82/1.68  tff(c_10, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=k1_xboole_0 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.82/1.68  tff(c_165, plain, (![A_41, B_42]: (k4_xboole_0(k3_tarski(A_41), k3_tarski(B_42))=k1_xboole_0 | ~r1_tarski(A_41, B_42))), inference(resolution, [status(thm)], [c_76, c_10])).
% 3.82/1.68  tff(c_6, plain, (![C_5, B_4, A_3]: (r1_tarski(k4_xboole_0(C_5, B_4), k4_xboole_0(C_5, A_3)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.82/1.68  tff(c_1121, plain, (![A_119, B_120, B_121]: (r1_tarski(k4_xboole_0(k3_tarski(A_119), B_120), k1_xboole_0) | ~r1_tarski(k3_tarski(B_121), B_120) | ~r1_tarski(A_119, B_121))), inference(superposition, [status(thm), theory('equality')], [c_165, c_6])).
% 3.82/1.68  tff(c_1175, plain, (![A_124]: (r1_tarski(k4_xboole_0(k3_tarski(A_124), '#skF_2'), k1_xboole_0) | ~r1_tarski(A_124, '#skF_1'))), inference(resolution, [status(thm)], [c_26, c_1121])).
% 3.82/1.68  tff(c_12, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.82/1.68  tff(c_1207, plain, (![A_125]: (k4_xboole_0(k3_tarski(A_125), '#skF_2')=k1_xboole_0 | ~r1_tarski(A_125, '#skF_1'))), inference(resolution, [status(thm)], [c_1175, c_12])).
% 3.82/1.68  tff(c_1286, plain, (![A_127]: (k4_xboole_0(A_127, '#skF_2')=k1_xboole_0 | ~r1_tarski(k1_tarski(A_127), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1207])).
% 3.82/1.68  tff(c_1777, plain, (![A_151]: (k4_xboole_0(A_151, '#skF_2')=k1_xboole_0 | k4_xboole_0(k1_tarski(A_151), '#skF_1')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_1286])).
% 3.82/1.68  tff(c_1783, plain, (![A_152]: (k4_xboole_0(A_152, '#skF_2')=k1_xboole_0 | ~r2_hidden(A_152, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1777])).
% 3.82/1.68  tff(c_1786, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_1783])).
% 3.82/1.68  tff(c_1790, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_1786])).
% 3.82/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.68  
% 3.82/1.68  Inference rules
% 3.82/1.68  ----------------------
% 3.82/1.68  #Ref     : 0
% 3.82/1.68  #Sup     : 445
% 3.82/1.68  #Fact    : 0
% 3.82/1.68  #Define  : 0
% 3.82/1.68  #Split   : 15
% 3.82/1.68  #Chain   : 0
% 3.82/1.68  #Close   : 0
% 3.82/1.68  
% 3.82/1.68  Ordering : KBO
% 3.82/1.68  
% 3.82/1.68  Simplification rules
% 3.82/1.68  ----------------------
% 3.82/1.68  #Subsume      : 102
% 3.82/1.68  #Demod        : 18
% 3.82/1.68  #Tautology    : 64
% 3.82/1.68  #SimpNegUnit  : 2
% 3.82/1.68  #BackRed      : 1
% 3.82/1.68  
% 3.82/1.68  #Partial instantiations: 0
% 3.82/1.68  #Strategies tried      : 1
% 3.82/1.68  
% 3.82/1.68  Timing (in seconds)
% 3.82/1.68  ----------------------
% 3.82/1.68  Preprocessing        : 0.27
% 3.82/1.68  Parsing              : 0.15
% 3.82/1.68  CNF conversion       : 0.02
% 3.82/1.68  Main loop            : 0.64
% 3.82/1.68  Inferencing          : 0.22
% 3.82/1.68  Reduction            : 0.16
% 3.82/1.68  Demodulation         : 0.10
% 3.82/1.68  BG Simplification    : 0.02
% 3.82/1.68  Subsumption          : 0.19
% 3.82/1.68  Abstraction          : 0.02
% 3.82/1.68  MUC search           : 0.00
% 3.82/1.69  Cooper               : 0.00
% 3.82/1.69  Total                : 0.94
% 3.82/1.69  Index Insertion      : 0.00
% 3.82/1.69  Index Deletion       : 0.00
% 3.82/1.69  Index Matching       : 0.00
% 3.82/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
