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
% DateTime   : Thu Dec  3 09:58:26 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   41 (  69 expanded)
%              Number of leaves         :   19 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   48 ( 101 expanded)
%              Number of equality atoms :    6 (  18 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k2_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k6_subset_1(k2_relat_1(A),k2_relat_1(B)),k2_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k2_relat_1(A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_20,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_100,plain,(
    ! [A_44,B_45] :
      ( k2_xboole_0(k2_relat_1(A_44),k2_relat_1(B_45)) = k2_relat_1(k2_xboole_0(A_44,B_45))
      | ~ v1_relat_1(B_45)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_47,plain,(
    ! [A_30,B_31,C_32] :
      ( r1_tarski(A_30,k2_xboole_0(B_31,C_32))
      | ~ r1_tarski(k4_xboole_0(A_30,B_31),C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_55,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(B_2,A_1)) ),
    inference(resolution,[status(thm)],[c_2,c_47])).

tff(c_160,plain,(
    ! [B_50,A_51] :
      ( r1_tarski(k2_relat_1(B_50),k2_relat_1(k2_xboole_0(A_51,B_50)))
      | ~ v1_relat_1(B_50)
      | ~ v1_relat_1(A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_55])).

tff(c_12,plain,(
    ! [A_13,B_14] :
      ( v1_relat_1(k4_xboole_0(A_13,B_14))
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    ! [A_27,B_28,C_29] :
      ( r1_tarski(k4_xboole_0(A_27,B_28),C_29)
      | ~ r1_tarski(A_27,k2_xboole_0(B_28,C_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_11,B_12] : k6_subset_1(A_11,B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ~ r1_tarski(k6_subset_1(k2_relat_1('#skF_1'),k2_relat_1('#skF_2')),k2_relat_1(k6_subset_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_21,plain,(
    ~ r1_tarski(k4_xboole_0(k2_relat_1('#skF_1'),k2_relat_1('#skF_2')),k2_relat_1(k4_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_16])).

tff(c_46,plain,(
    ~ r1_tarski(k2_relat_1('#skF_1'),k2_xboole_0(k2_relat_1('#skF_2'),k2_relat_1(k4_xboole_0('#skF_1','#skF_2')))) ),
    inference(resolution,[status(thm)],[c_42,c_21])).

tff(c_118,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1(k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_2'))))
    | ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_46])).

tff(c_124,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1(k2_xboole_0('#skF_2','#skF_1')))
    | ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_4,c_118])).

tff(c_150,plain,(
    ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_153,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_150])).

tff(c_157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_153])).

tff(c_158,plain,(
    ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1(k2_xboole_0('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_163,plain,
    ( ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_160,c_158])).

tff(c_173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_163])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:02:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.29  
% 2.05/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.30  %$ r1_tarski > v1_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k2_relat_1 > #skF_2 > #skF_1
% 2.05/1.30  
% 2.05/1.30  %Foreground sorts:
% 2.05/1.30  
% 2.05/1.30  
% 2.05/1.30  %Background operators:
% 2.05/1.30  
% 2.05/1.30  
% 2.05/1.30  %Foreground operators:
% 2.05/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.05/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.05/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.05/1.30  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.05/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.05/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.05/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.05/1.30  
% 2.05/1.31  tff(f_58, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k2_relat_1(A), k2_relat_1(B)), k2_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_relat_1)).
% 2.05/1.31  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_relat_1)).
% 2.05/1.31  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.05/1.31  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 2.05/1.31  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_relat_1)).
% 2.05/1.31  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.05/1.31  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.05/1.31  tff(f_39, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.05/1.31  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.05/1.31  tff(c_20, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.05/1.31  tff(c_100, plain, (![A_44, B_45]: (k2_xboole_0(k2_relat_1(A_44), k2_relat_1(B_45))=k2_relat_1(k2_xboole_0(A_44, B_45)) | ~v1_relat_1(B_45) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.05/1.31  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.05/1.31  tff(c_47, plain, (![A_30, B_31, C_32]: (r1_tarski(A_30, k2_xboole_0(B_31, C_32)) | ~r1_tarski(k4_xboole_0(A_30, B_31), C_32))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.05/1.31  tff(c_55, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(B_2, A_1)))), inference(resolution, [status(thm)], [c_2, c_47])).
% 2.05/1.31  tff(c_160, plain, (![B_50, A_51]: (r1_tarski(k2_relat_1(B_50), k2_relat_1(k2_xboole_0(A_51, B_50))) | ~v1_relat_1(B_50) | ~v1_relat_1(A_51))), inference(superposition, [status(thm), theory('equality')], [c_100, c_55])).
% 2.05/1.31  tff(c_12, plain, (![A_13, B_14]: (v1_relat_1(k4_xboole_0(A_13, B_14)) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.05/1.31  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.05/1.31  tff(c_42, plain, (![A_27, B_28, C_29]: (r1_tarski(k4_xboole_0(A_27, B_28), C_29) | ~r1_tarski(A_27, k2_xboole_0(B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.05/1.31  tff(c_10, plain, (![A_11, B_12]: (k6_subset_1(A_11, B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.05/1.31  tff(c_16, plain, (~r1_tarski(k6_subset_1(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')), k2_relat_1(k6_subset_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.05/1.31  tff(c_21, plain, (~r1_tarski(k4_xboole_0(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')), k2_relat_1(k4_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_16])).
% 2.05/1.31  tff(c_46, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_xboole_0(k2_relat_1('#skF_2'), k2_relat_1(k4_xboole_0('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_42, c_21])).
% 2.05/1.31  tff(c_118, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1(k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_2')))) | ~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_100, c_46])).
% 2.05/1.31  tff(c_124, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1(k2_xboole_0('#skF_2', '#skF_1'))) | ~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_4, c_118])).
% 2.05/1.31  tff(c_150, plain, (~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_124])).
% 2.05/1.31  tff(c_153, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_12, c_150])).
% 2.05/1.31  tff(c_157, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_153])).
% 2.05/1.31  tff(c_158, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1(k2_xboole_0('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_124])).
% 2.05/1.31  tff(c_163, plain, (~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_160, c_158])).
% 2.05/1.31  tff(c_173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_163])).
% 2.05/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.31  
% 2.05/1.31  Inference rules
% 2.05/1.31  ----------------------
% 2.05/1.31  #Ref     : 0
% 2.05/1.31  #Sup     : 34
% 2.05/1.31  #Fact    : 0
% 2.05/1.31  #Define  : 0
% 2.05/1.31  #Split   : 1
% 2.05/1.31  #Chain   : 0
% 2.05/1.31  #Close   : 0
% 2.05/1.31  
% 2.05/1.31  Ordering : KBO
% 2.05/1.31  
% 2.05/1.31  Simplification rules
% 2.05/1.31  ----------------------
% 2.05/1.31  #Subsume      : 0
% 2.05/1.31  #Demod        : 9
% 2.05/1.31  #Tautology    : 9
% 2.05/1.31  #SimpNegUnit  : 0
% 2.05/1.31  #BackRed      : 0
% 2.05/1.31  
% 2.05/1.31  #Partial instantiations: 0
% 2.05/1.31  #Strategies tried      : 1
% 2.05/1.31  
% 2.05/1.31  Timing (in seconds)
% 2.05/1.31  ----------------------
% 2.05/1.31  Preprocessing        : 0.32
% 2.05/1.31  Parsing              : 0.17
% 2.05/1.31  CNF conversion       : 0.02
% 2.05/1.31  Main loop            : 0.17
% 2.05/1.31  Inferencing          : 0.06
% 2.05/1.31  Reduction            : 0.05
% 2.05/1.31  Demodulation         : 0.04
% 2.05/1.31  BG Simplification    : 0.01
% 2.05/1.31  Subsumption          : 0.03
% 2.05/1.31  Abstraction          : 0.01
% 2.05/1.31  MUC search           : 0.00
% 2.05/1.31  Cooper               : 0.00
% 2.05/1.31  Total                : 0.52
% 2.05/1.31  Index Insertion      : 0.00
% 2.05/1.31  Index Deletion       : 0.00
% 2.05/1.31  Index Matching       : 0.00
% 2.05/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
