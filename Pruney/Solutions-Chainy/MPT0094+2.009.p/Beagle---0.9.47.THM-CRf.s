%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:34 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   29 (  36 expanded)
%              Number of leaves         :   15 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :   27 (  38 expanded)
%              Number of equality atoms :   10 (  15 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => k2_xboole_0(k4_xboole_0(C,A),B) = k4_xboole_0(k2_xboole_0(C,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_xboole_1)).

tff(f_29,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,k4_xboole_0(B,C))
     => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_27,axiom,(
    ! [A,B,C] : k4_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,C),k4_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

tff(c_14,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_4] : r1_xboole_0(A_4,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = A_11
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_23,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(resolution,[status(thm)],[c_4,c_16])).

tff(c_43,plain,(
    ! [B_16,A_17,C_18] :
      ( r1_xboole_0(B_16,k4_xboole_0(A_17,C_18))
      | ~ r1_xboole_0(A_17,k4_xboole_0(B_16,C_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_50,plain,(
    ! [A_4,A_17] :
      ( r1_xboole_0(A_4,k4_xboole_0(A_17,k1_xboole_0))
      | ~ r1_xboole_0(A_17,A_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23,c_43])).

tff(c_53,plain,(
    ! [A_19,A_20] :
      ( r1_xboole_0(A_19,A_20)
      | ~ r1_xboole_0(A_20,A_19) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23,c_50])).

tff(c_62,plain,(
    r1_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_53])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = A_8
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_83,plain,(
    k4_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_62,c_8])).

tff(c_124,plain,(
    ! [A_25,C_26,B_27] : k2_xboole_0(k4_xboole_0(A_25,C_26),k4_xboole_0(B_27,C_26)) = k4_xboole_0(k2_xboole_0(A_25,B_27),C_26) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_136,plain,(
    ! [A_25] : k4_xboole_0(k2_xboole_0(A_25,'#skF_2'),'#skF_1') = k2_xboole_0(k4_xboole_0(A_25,'#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_124])).

tff(c_12,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3','#skF_2'),'#skF_1') != k2_xboole_0(k4_xboole_0('#skF_3','#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_484,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:33:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.33  
% 2.02/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.33  %$ r1_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.02/1.33  
% 2.02/1.33  %Foreground sorts:
% 2.02/1.33  
% 2.02/1.33  
% 2.02/1.33  %Background operators:
% 2.02/1.33  
% 2.02/1.33  
% 2.02/1.33  %Foreground operators:
% 2.02/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.02/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.02/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.02/1.33  
% 2.02/1.34  tff(f_42, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => (k2_xboole_0(k4_xboole_0(C, A), B) = k4_xboole_0(k2_xboole_0(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_xboole_1)).
% 2.02/1.34  tff(f_29, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.02/1.34  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.02/1.34  tff(f_33, axiom, (![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 2.02/1.34  tff(f_27, axiom, (![A, B, C]: (k4_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_xboole_1)).
% 2.02/1.34  tff(c_14, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.02/1.34  tff(c_4, plain, (![A_4]: (r1_xboole_0(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.02/1.34  tff(c_16, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=A_11 | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.02/1.34  tff(c_23, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(resolution, [status(thm)], [c_4, c_16])).
% 2.02/1.34  tff(c_43, plain, (![B_16, A_17, C_18]: (r1_xboole_0(B_16, k4_xboole_0(A_17, C_18)) | ~r1_xboole_0(A_17, k4_xboole_0(B_16, C_18)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.02/1.34  tff(c_50, plain, (![A_4, A_17]: (r1_xboole_0(A_4, k4_xboole_0(A_17, k1_xboole_0)) | ~r1_xboole_0(A_17, A_4))), inference(superposition, [status(thm), theory('equality')], [c_23, c_43])).
% 2.02/1.34  tff(c_53, plain, (![A_19, A_20]: (r1_xboole_0(A_19, A_20) | ~r1_xboole_0(A_20, A_19))), inference(demodulation, [status(thm), theory('equality')], [c_23, c_50])).
% 2.02/1.34  tff(c_62, plain, (r1_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_14, c_53])).
% 2.02/1.34  tff(c_8, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=A_8 | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.02/1.34  tff(c_83, plain, (k4_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_62, c_8])).
% 2.02/1.34  tff(c_124, plain, (![A_25, C_26, B_27]: (k2_xboole_0(k4_xboole_0(A_25, C_26), k4_xboole_0(B_27, C_26))=k4_xboole_0(k2_xboole_0(A_25, B_27), C_26))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.02/1.34  tff(c_136, plain, (![A_25]: (k4_xboole_0(k2_xboole_0(A_25, '#skF_2'), '#skF_1')=k2_xboole_0(k4_xboole_0(A_25, '#skF_1'), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_83, c_124])).
% 2.02/1.34  tff(c_12, plain, (k4_xboole_0(k2_xboole_0('#skF_3', '#skF_2'), '#skF_1')!=k2_xboole_0(k4_xboole_0('#skF_3', '#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.02/1.34  tff(c_484, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_136, c_12])).
% 2.02/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.34  
% 2.02/1.34  Inference rules
% 2.02/1.34  ----------------------
% 2.02/1.34  #Ref     : 0
% 2.02/1.34  #Sup     : 127
% 2.02/1.34  #Fact    : 0
% 2.02/1.34  #Define  : 0
% 2.02/1.34  #Split   : 0
% 2.02/1.34  #Chain   : 0
% 2.02/1.34  #Close   : 0
% 2.02/1.34  
% 2.02/1.34  Ordering : KBO
% 2.02/1.34  
% 2.02/1.34  Simplification rules
% 2.02/1.34  ----------------------
% 2.02/1.34  #Subsume      : 13
% 2.02/1.34  #Demod        : 41
% 2.02/1.34  #Tautology    : 48
% 2.02/1.34  #SimpNegUnit  : 0
% 2.02/1.34  #BackRed      : 1
% 2.02/1.34  
% 2.02/1.34  #Partial instantiations: 0
% 2.02/1.34  #Strategies tried      : 1
% 2.02/1.34  
% 2.02/1.34  Timing (in seconds)
% 2.02/1.34  ----------------------
% 2.02/1.34  Preprocessing        : 0.25
% 2.02/1.34  Parsing              : 0.13
% 2.02/1.34  CNF conversion       : 0.01
% 2.02/1.34  Main loop            : 0.27
% 2.02/1.34  Inferencing          : 0.10
% 2.02/1.34  Reduction            : 0.08
% 2.02/1.34  Demodulation         : 0.06
% 2.02/1.34  BG Simplification    : 0.01
% 2.02/1.34  Subsumption          : 0.06
% 2.02/1.34  Abstraction          : 0.01
% 2.02/1.34  MUC search           : 0.00
% 2.02/1.34  Cooper               : 0.00
% 2.02/1.34  Total                : 0.54
% 2.02/1.34  Index Insertion      : 0.00
% 2.02/1.34  Index Deletion       : 0.00
% 2.02/1.34  Index Matching       : 0.00
% 2.02/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
