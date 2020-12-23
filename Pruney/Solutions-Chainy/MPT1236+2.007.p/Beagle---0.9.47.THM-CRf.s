%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:36 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   31 (  50 expanded)
%              Number of leaves         :   16 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   35 (  68 expanded)
%              Number of equality atoms :   11 (  23 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > k1_struct_0 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_51,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => k1_tops_1(A,k1_struct_0(A)) = k1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tops_1)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => v1_xboole_0(k1_tops_1(A,k1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_tops_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_14,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_16,plain,(
    ! [A_7] :
      ( k1_struct_0(A_7) = k1_xboole_0
      | ~ l1_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_21,plain,(
    ! [A_8] :
      ( k1_struct_0(A_8) = k1_xboole_0
      | ~ l1_pre_topc(A_8) ) ),
    inference(resolution,[status(thm)],[c_8,c_16])).

tff(c_25,plain,(
    k1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_21])).

tff(c_12,plain,(
    k1_tops_1('#skF_1',k1_struct_0('#skF_1')) != k1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26,plain,(
    k1_tops_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_25,c_12])).

tff(c_35,plain,(
    ! [A_11] :
      ( v1_xboole_0(k1_tops_1(A_11,k1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_40,plain,
    ( v1_xboole_0(k1_tops_1('#skF_1',k1_xboole_0))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_25,c_35])).

tff(c_43,plain,(
    v1_xboole_0(k1_tops_1('#skF_1',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_40])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_31,plain,(
    ! [B_9,A_10] :
      ( ~ v1_xboole_0(B_9)
      | B_9 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_34,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(resolution,[status(thm)],[c_2,c_31])).

tff(c_56,plain,(
    k1_tops_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_43,c_34])).

tff(c_62,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.09  
% 1.62/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.09  %$ v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > k1_struct_0 > k1_xboole_0 > #skF_1
% 1.62/1.09  
% 1.62/1.09  %Foreground sorts:
% 1.62/1.09  
% 1.62/1.09  
% 1.62/1.09  %Background operators:
% 1.62/1.09  
% 1.62/1.09  
% 1.62/1.09  %Foreground operators:
% 1.62/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.62/1.09  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.62/1.09  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 1.62/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.09  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.62/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.09  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 1.62/1.09  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.62/1.09  
% 1.62/1.10  tff(f_51, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (k1_tops_1(A, k1_struct_0(A)) = k1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_tops_1)).
% 1.62/1.10  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 1.62/1.10  tff(f_38, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_struct_0)).
% 1.62/1.10  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => v1_xboole_0(k1_tops_1(A, k1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_tops_1)).
% 1.62/1.10  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.62/1.10  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 1.62/1.10  tff(c_14, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.62/1.10  tff(c_8, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.62/1.10  tff(c_16, plain, (![A_7]: (k1_struct_0(A_7)=k1_xboole_0 | ~l1_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.62/1.10  tff(c_21, plain, (![A_8]: (k1_struct_0(A_8)=k1_xboole_0 | ~l1_pre_topc(A_8))), inference(resolution, [status(thm)], [c_8, c_16])).
% 1.62/1.10  tff(c_25, plain, (k1_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_21])).
% 1.62/1.10  tff(c_12, plain, (k1_tops_1('#skF_1', k1_struct_0('#skF_1'))!=k1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.62/1.10  tff(c_26, plain, (k1_tops_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_25, c_25, c_12])).
% 1.62/1.10  tff(c_35, plain, (![A_11]: (v1_xboole_0(k1_tops_1(A_11, k1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.62/1.10  tff(c_40, plain, (v1_xboole_0(k1_tops_1('#skF_1', k1_xboole_0)) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_25, c_35])).
% 1.62/1.10  tff(c_43, plain, (v1_xboole_0(k1_tops_1('#skF_1', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_40])).
% 1.62/1.10  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.62/1.10  tff(c_31, plain, (![B_9, A_10]: (~v1_xboole_0(B_9) | B_9=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.62/1.10  tff(c_34, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(resolution, [status(thm)], [c_2, c_31])).
% 1.62/1.10  tff(c_56, plain, (k1_tops_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_43, c_34])).
% 1.62/1.10  tff(c_62, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_56])).
% 1.62/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.10  
% 1.62/1.10  Inference rules
% 1.62/1.10  ----------------------
% 1.62/1.10  #Ref     : 0
% 1.62/1.10  #Sup     : 11
% 1.62/1.10  #Fact    : 0
% 1.62/1.10  #Define  : 0
% 1.62/1.10  #Split   : 0
% 1.62/1.10  #Chain   : 0
% 1.62/1.10  #Close   : 0
% 1.62/1.10  
% 1.62/1.10  Ordering : KBO
% 1.62/1.10  
% 1.62/1.10  Simplification rules
% 1.62/1.10  ----------------------
% 1.62/1.10  #Subsume      : 0
% 1.62/1.10  #Demod        : 3
% 1.62/1.10  #Tautology    : 3
% 1.62/1.10  #SimpNegUnit  : 1
% 1.62/1.10  #BackRed      : 1
% 1.62/1.10  
% 1.62/1.10  #Partial instantiations: 0
% 1.62/1.10  #Strategies tried      : 1
% 1.62/1.10  
% 1.62/1.10  Timing (in seconds)
% 1.62/1.10  ----------------------
% 1.62/1.10  Preprocessing        : 0.24
% 1.62/1.10  Parsing              : 0.14
% 1.62/1.10  CNF conversion       : 0.01
% 1.62/1.10  Main loop            : 0.09
% 1.62/1.10  Inferencing          : 0.05
% 1.62/1.10  Reduction            : 0.02
% 1.62/1.10  Demodulation         : 0.02
% 1.62/1.10  BG Simplification    : 0.01
% 1.62/1.10  Subsumption          : 0.01
% 1.62/1.10  Abstraction          : 0.00
% 1.62/1.10  MUC search           : 0.00
% 1.62/1.10  Cooper               : 0.00
% 1.62/1.10  Total                : 0.36
% 1.62/1.10  Index Insertion      : 0.00
% 1.62/1.10  Index Deletion       : 0.00
% 1.62/1.10  Index Matching       : 0.00
% 1.62/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
