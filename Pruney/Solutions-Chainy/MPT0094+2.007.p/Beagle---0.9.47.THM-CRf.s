%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:34 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   22 (  23 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   18 (  20 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => k2_xboole_0(k4_xboole_0(C,A),B) = k4_xboole_0(k2_xboole_0(C,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k4_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,C),k4_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

tff(c_12,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_13,plain,(
    ! [B_8,A_9] :
      ( r1_xboole_0(B_8,A_9)
      | ~ r1_xboole_0(A_9,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    r1_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_13])).

tff(c_21,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = A_10
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    k4_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_16,c_21])).

tff(c_63,plain,(
    ! [A_18,C_19,B_20] : k2_xboole_0(k4_xboole_0(A_18,C_19),k4_xboole_0(B_20,C_19)) = k4_xboole_0(k2_xboole_0(A_18,B_20),C_19) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [A_18] : k4_xboole_0(k2_xboole_0(A_18,'#skF_2'),'#skF_1') = k2_xboole_0(k4_xboole_0(A_18,'#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_63])).

tff(c_10,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3','#skF_2'),'#skF_1') != k2_xboole_0(k4_xboole_0('#skF_3','#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:59:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.16  
% 1.59/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.16  %$ r1_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.59/1.16  
% 1.59/1.16  %Foreground sorts:
% 1.59/1.16  
% 1.59/1.16  
% 1.59/1.16  %Background operators:
% 1.59/1.16  
% 1.59/1.16  
% 1.59/1.16  %Foreground operators:
% 1.59/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.59/1.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.59/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.59/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.59/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.59/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.59/1.16  
% 1.59/1.17  tff(f_40, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => (k2_xboole_0(k4_xboole_0(C, A), B) = k4_xboole_0(k2_xboole_0(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_xboole_1)).
% 1.59/1.17  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.59/1.17  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.59/1.17  tff(f_31, axiom, (![A, B, C]: (k4_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 1.59/1.17  tff(c_12, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.59/1.17  tff(c_13, plain, (![B_8, A_9]: (r1_xboole_0(B_8, A_9) | ~r1_xboole_0(A_9, B_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.59/1.17  tff(c_16, plain, (r1_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_12, c_13])).
% 1.59/1.17  tff(c_21, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=A_10 | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.59/1.17  tff(c_28, plain, (k4_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_16, c_21])).
% 1.59/1.17  tff(c_63, plain, (![A_18, C_19, B_20]: (k2_xboole_0(k4_xboole_0(A_18, C_19), k4_xboole_0(B_20, C_19))=k4_xboole_0(k2_xboole_0(A_18, B_20), C_19))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.59/1.17  tff(c_75, plain, (![A_18]: (k4_xboole_0(k2_xboole_0(A_18, '#skF_2'), '#skF_1')=k2_xboole_0(k4_xboole_0(A_18, '#skF_1'), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_63])).
% 1.59/1.17  tff(c_10, plain, (k4_xboole_0(k2_xboole_0('#skF_3', '#skF_2'), '#skF_1')!=k2_xboole_0(k4_xboole_0('#skF_3', '#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.59/1.17  tff(c_130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_10])).
% 1.59/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.17  
% 1.59/1.17  Inference rules
% 1.59/1.17  ----------------------
% 1.59/1.17  #Ref     : 0
% 1.59/1.17  #Sup     : 32
% 1.59/1.17  #Fact    : 0
% 1.59/1.17  #Define  : 0
% 1.59/1.17  #Split   : 0
% 1.59/1.17  #Chain   : 0
% 1.59/1.17  #Close   : 0
% 1.59/1.17  
% 1.59/1.17  Ordering : KBO
% 1.59/1.17  
% 1.59/1.17  Simplification rules
% 1.59/1.17  ----------------------
% 1.59/1.17  #Subsume      : 1
% 1.59/1.17  #Demod        : 8
% 1.59/1.17  #Tautology    : 16
% 1.59/1.17  #SimpNegUnit  : 0
% 1.59/1.17  #BackRed      : 1
% 1.59/1.17  
% 1.59/1.17  #Partial instantiations: 0
% 1.59/1.17  #Strategies tried      : 1
% 1.59/1.17  
% 1.59/1.17  Timing (in seconds)
% 1.59/1.17  ----------------------
% 1.59/1.17  Preprocessing        : 0.27
% 1.59/1.17  Parsing              : 0.15
% 1.59/1.17  CNF conversion       : 0.01
% 1.59/1.17  Main loop            : 0.12
% 1.59/1.17  Inferencing          : 0.05
% 1.59/1.17  Reduction            : 0.03
% 1.59/1.17  Demodulation         : 0.03
% 1.59/1.17  BG Simplification    : 0.01
% 1.59/1.17  Subsumption          : 0.02
% 1.59/1.17  Abstraction          : 0.01
% 1.59/1.17  MUC search           : 0.00
% 1.59/1.17  Cooper               : 0.00
% 1.59/1.17  Total                : 0.41
% 1.79/1.17  Index Insertion      : 0.00
% 1.79/1.17  Index Deletion       : 0.00
% 1.79/1.17  Index Matching       : 0.00
% 1.79/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
