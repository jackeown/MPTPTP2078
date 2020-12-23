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
% DateTime   : Thu Dec  3 10:20:36 EST 2020

% Result     : Theorem 1.47s
% Output     : CNFRefutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   28 (  47 expanded)
%              Number of leaves         :   15 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   29 (  62 expanded)
%              Number of equality atoms :   10 (  22 expanded)
%              Maximal formula depth    :    4 (   3 average)
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

tff(f_46,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => k1_tops_1(A,k1_struct_0(A)) = k1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tops_1)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => v1_xboole_0(k1_tops_1(A,k1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_tops_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_12,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [A_3] :
      ( l1_struct_0(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_15,plain,(
    ! [A_7] :
      ( k1_struct_0(A_7) = k1_xboole_0
      | ~ l1_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [A_8] :
      ( k1_struct_0(A_8) = k1_xboole_0
      | ~ l1_pre_topc(A_8) ) ),
    inference(resolution,[status(thm)],[c_6,c_15])).

tff(c_24,plain,(
    k1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_20])).

tff(c_10,plain,(
    k1_tops_1('#skF_1',k1_struct_0('#skF_1')) != k1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_25,plain,(
    k1_tops_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_10])).

tff(c_30,plain,(
    ! [A_9] :
      ( v1_xboole_0(k1_tops_1(A_9,k1_struct_0(A_9)))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_36,plain,
    ( v1_xboole_0(k1_tops_1('#skF_1',k1_xboole_0))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_30])).

tff(c_39,plain,(
    v1_xboole_0(k1_tops_1('#skF_1',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_36])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    k1_tops_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_39,c_2])).

tff(c_46,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:09:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.47/1.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.47/1.03  
% 1.47/1.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.47/1.03  %$ v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > k1_struct_0 > k1_xboole_0 > #skF_1
% 1.47/1.03  
% 1.47/1.03  %Foreground sorts:
% 1.47/1.03  
% 1.47/1.03  
% 1.47/1.03  %Background operators:
% 1.47/1.03  
% 1.47/1.03  
% 1.47/1.03  %Foreground operators:
% 1.47/1.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.47/1.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.47/1.03  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.47/1.03  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 1.47/1.03  tff('#skF_1', type, '#skF_1': $i).
% 1.47/1.03  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.47/1.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.47/1.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.47/1.03  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 1.47/1.03  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.47/1.03  
% 1.47/1.04  tff(f_46, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (k1_tops_1(A, k1_struct_0(A)) = k1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_tops_1)).
% 1.47/1.04  tff(f_37, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 1.47/1.04  tff(f_33, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_struct_0)).
% 1.47/1.04  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => v1_xboole_0(k1_tops_1(A, k1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_tops_1)).
% 1.47/1.04  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.47/1.04  tff(c_12, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.47/1.04  tff(c_6, plain, (![A_3]: (l1_struct_0(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.47/1.04  tff(c_15, plain, (![A_7]: (k1_struct_0(A_7)=k1_xboole_0 | ~l1_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.47/1.04  tff(c_20, plain, (![A_8]: (k1_struct_0(A_8)=k1_xboole_0 | ~l1_pre_topc(A_8))), inference(resolution, [status(thm)], [c_6, c_15])).
% 1.47/1.04  tff(c_24, plain, (k1_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_20])).
% 1.47/1.04  tff(c_10, plain, (k1_tops_1('#skF_1', k1_struct_0('#skF_1'))!=k1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.47/1.04  tff(c_25, plain, (k1_tops_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_10])).
% 1.47/1.04  tff(c_30, plain, (![A_9]: (v1_xboole_0(k1_tops_1(A_9, k1_struct_0(A_9))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.47/1.04  tff(c_36, plain, (v1_xboole_0(k1_tops_1('#skF_1', k1_xboole_0)) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24, c_30])).
% 1.47/1.04  tff(c_39, plain, (v1_xboole_0(k1_tops_1('#skF_1', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_36])).
% 1.47/1.04  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.47/1.04  tff(c_42, plain, (k1_tops_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_39, c_2])).
% 1.47/1.04  tff(c_46, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25, c_42])).
% 1.47/1.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.47/1.04  
% 1.47/1.04  Inference rules
% 1.47/1.04  ----------------------
% 1.47/1.04  #Ref     : 0
% 1.47/1.04  #Sup     : 7
% 1.47/1.04  #Fact    : 0
% 1.47/1.04  #Define  : 0
% 1.47/1.04  #Split   : 0
% 1.47/1.04  #Chain   : 0
% 1.47/1.04  #Close   : 0
% 1.47/1.04  
% 1.47/1.04  Ordering : KBO
% 1.47/1.04  
% 1.47/1.04  Simplification rules
% 1.47/1.04  ----------------------
% 1.47/1.04  #Subsume      : 0
% 1.47/1.04  #Demod        : 3
% 1.47/1.04  #Tautology    : 2
% 1.47/1.04  #SimpNegUnit  : 1
% 1.47/1.04  #BackRed      : 1
% 1.47/1.04  
% 1.47/1.04  #Partial instantiations: 0
% 1.47/1.04  #Strategies tried      : 1
% 1.47/1.04  
% 1.47/1.04  Timing (in seconds)
% 1.47/1.04  ----------------------
% 1.47/1.04  Preprocessing        : 0.25
% 1.47/1.04  Parsing              : 0.14
% 1.47/1.04  CNF conversion       : 0.01
% 1.47/1.04  Main loop            : 0.08
% 1.47/1.04  Inferencing          : 0.04
% 1.47/1.04  Reduction            : 0.02
% 1.47/1.04  Demodulation         : 0.01
% 1.47/1.04  BG Simplification    : 0.01
% 1.47/1.04  Subsumption          : 0.01
% 1.47/1.04  Abstraction          : 0.00
% 1.47/1.04  MUC search           : 0.00
% 1.47/1.04  Cooper               : 0.00
% 1.47/1.04  Total                : 0.35
% 1.47/1.04  Index Insertion      : 0.00
% 1.47/1.04  Index Deletion       : 0.00
% 1.47/1.04  Index Matching       : 0.00
% 1.47/1.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
