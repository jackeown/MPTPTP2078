%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:58 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   40 (  43 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   33 (  38 expanded)
%              Number of equality atoms :   25 (  27 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
          & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_16,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k2_xboole_0(A_8,B_9)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_64,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_82,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_64])).

tff(c_86,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_82])).

tff(c_173,plain,(
    ! [A_33,B_34,C_35] : k4_xboole_0(k4_xboole_0(A_33,B_34),C_35) = k4_xboole_0(A_33,k2_xboole_0(B_34,C_35)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_221,plain,(
    ! [A_4,C_35] : k4_xboole_0(A_4,k2_xboole_0(A_4,C_35)) = k4_xboole_0(k1_xboole_0,C_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_173])).

tff(c_255,plain,(
    ! [C_35] : k4_xboole_0(k1_xboole_0,C_35) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_221])).

tff(c_20,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_46,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = k1_xboole_0
      | ~ r1_xboole_0(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_50,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_46])).

tff(c_481,plain,(
    ! [A_42,B_43,C_44] : k4_xboole_0(k3_xboole_0(A_42,B_43),C_44) = k3_xboole_0(A_42,k4_xboole_0(B_43,C_44)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_545,plain,(
    ! [C_44] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_44)) = k4_xboole_0(k1_xboole_0,C_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_481])).

tff(c_572,plain,(
    ! [C_45] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_45)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_545])).

tff(c_597,plain,(
    ! [B_13] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',B_13)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_572])).

tff(c_55,plain,(
    ! [A_23,B_24] :
      ( r1_xboole_0(A_23,B_24)
      | k3_xboole_0(A_23,B_24) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    ~ r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_63,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_55,c_22])).

tff(c_657,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_597,c_63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:28:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.22  
% 2.10/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.22  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.25/1.22  
% 2.25/1.22  %Foreground sorts:
% 2.25/1.22  
% 2.25/1.22  
% 2.25/1.22  %Background operators:
% 2.25/1.22  
% 2.25/1.22  
% 2.25/1.22  %Foreground operators:
% 2.25/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.25/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.25/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.25/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.25/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.25/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.25/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.25/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.25/1.22  
% 2.29/1.23  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.29/1.23  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.29/1.23  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.29/1.23  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.29/1.23  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.29/1.23  tff(f_50, negated_conjecture, ~(![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_xboole_1)).
% 2.29/1.23  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.29/1.23  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.29/1.23  tff(c_16, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.29/1.23  tff(c_12, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k2_xboole_0(A_8, B_9))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.29/1.23  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.29/1.23  tff(c_8, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.29/1.23  tff(c_64, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.29/1.23  tff(c_82, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_64])).
% 2.29/1.23  tff(c_86, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_82])).
% 2.29/1.23  tff(c_173, plain, (![A_33, B_34, C_35]: (k4_xboole_0(k4_xboole_0(A_33, B_34), C_35)=k4_xboole_0(A_33, k2_xboole_0(B_34, C_35)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.29/1.23  tff(c_221, plain, (![A_4, C_35]: (k4_xboole_0(A_4, k2_xboole_0(A_4, C_35))=k4_xboole_0(k1_xboole_0, C_35))), inference(superposition, [status(thm), theory('equality')], [c_86, c_173])).
% 2.29/1.23  tff(c_255, plain, (![C_35]: (k4_xboole_0(k1_xboole_0, C_35)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_221])).
% 2.29/1.23  tff(c_20, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.29/1.23  tff(c_46, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=k1_xboole_0 | ~r1_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.29/1.23  tff(c_50, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_46])).
% 2.29/1.23  tff(c_481, plain, (![A_42, B_43, C_44]: (k4_xboole_0(k3_xboole_0(A_42, B_43), C_44)=k3_xboole_0(A_42, k4_xboole_0(B_43, C_44)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.29/1.23  tff(c_545, plain, (![C_44]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_44))=k4_xboole_0(k1_xboole_0, C_44))), inference(superposition, [status(thm), theory('equality')], [c_50, c_481])).
% 2.29/1.23  tff(c_572, plain, (![C_45]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_45))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_255, c_545])).
% 2.29/1.23  tff(c_597, plain, (![B_13]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', B_13))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_572])).
% 2.29/1.23  tff(c_55, plain, (![A_23, B_24]: (r1_xboole_0(A_23, B_24) | k3_xboole_0(A_23, B_24)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.29/1.23  tff(c_22, plain, (~r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.29/1.23  tff(c_63, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_55, c_22])).
% 2.29/1.23  tff(c_657, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_597, c_63])).
% 2.29/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.23  
% 2.29/1.23  Inference rules
% 2.29/1.23  ----------------------
% 2.29/1.23  #Ref     : 0
% 2.29/1.23  #Sup     : 153
% 2.29/1.23  #Fact    : 0
% 2.29/1.23  #Define  : 0
% 2.29/1.23  #Split   : 0
% 2.29/1.23  #Chain   : 0
% 2.29/1.23  #Close   : 0
% 2.29/1.23  
% 2.29/1.23  Ordering : KBO
% 2.29/1.23  
% 2.29/1.23  Simplification rules
% 2.29/1.23  ----------------------
% 2.29/1.23  #Subsume      : 0
% 2.29/1.23  #Demod        : 87
% 2.29/1.23  #Tautology    : 96
% 2.29/1.23  #SimpNegUnit  : 0
% 2.29/1.23  #BackRed      : 1
% 2.29/1.23  
% 2.29/1.23  #Partial instantiations: 0
% 2.29/1.23  #Strategies tried      : 1
% 2.29/1.23  
% 2.29/1.23  Timing (in seconds)
% 2.29/1.23  ----------------------
% 2.29/1.24  Preprocessing        : 0.29
% 2.29/1.24  Parsing              : 0.16
% 2.29/1.24  CNF conversion       : 0.02
% 2.29/1.24  Main loop            : 0.24
% 2.29/1.24  Inferencing          : 0.09
% 2.29/1.24  Reduction            : 0.09
% 2.29/1.24  Demodulation         : 0.07
% 2.29/1.24  BG Simplification    : 0.01
% 2.29/1.24  Subsumption          : 0.03
% 2.29/1.24  Abstraction          : 0.02
% 2.29/1.24  MUC search           : 0.00
% 2.29/1.24  Cooper               : 0.00
% 2.29/1.24  Total                : 0.56
% 2.29/1.24  Index Insertion      : 0.00
% 2.29/1.24  Index Deletion       : 0.00
% 2.29/1.24  Index Matching       : 0.00
% 2.29/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
