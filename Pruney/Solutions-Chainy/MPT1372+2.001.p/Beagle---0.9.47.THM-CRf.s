%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:01 EST 2020

% Result     : Theorem 1.54s
% Output     : CNFRefutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   30 (  40 expanded)
%              Number of leaves         :   15 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   38 (  68 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v8_struct_0 > v2_pre_topc > v1_finset_1 > v1_compts_1 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v8_struct_0,type,(
    v8_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_compts_1,type,(
    v1_compts_1: $i > $o )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(f_56,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ( v1_finset_1(u1_struct_0(A))
         => v1_compts_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_compts_1)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_37,axiom,(
    ! [A] :
      ( ( ~ v8_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_finset_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_struct_0)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ( v8_struct_0(A)
          & v2_pre_topc(A) )
       => ( v2_pre_topc(A)
          & v1_compts_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_compts_1)).

tff(c_10,plain,(
    ~ v1_compts_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    v1_finset_1(u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18,plain,(
    ! [A_5] :
      ( ~ v1_finset_1(u1_struct_0(A_5))
      | ~ l1_struct_0(A_5)
      | v8_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,
    ( ~ l1_struct_0('#skF_1')
    | v8_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_18])).

tff(c_23,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_26,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_23])).

tff(c_30,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_26])).

tff(c_31,plain,(
    v8_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_33,plain,(
    ! [A_6] :
      ( v1_compts_1(A_6)
      | ~ v2_pre_topc(A_6)
      | ~ v8_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_36,plain,
    ( v1_compts_1('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_31,c_33])).

tff(c_39,plain,(
    v1_compts_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16,c_36])).

tff(c_41,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:40:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.54/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.54/1.10  
% 1.54/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.54/1.10  %$ v8_struct_0 > v2_pre_topc > v1_finset_1 > v1_compts_1 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > #skF_1
% 1.54/1.10  
% 1.54/1.10  %Foreground sorts:
% 1.54/1.10  
% 1.54/1.10  
% 1.54/1.10  %Background operators:
% 1.54/1.10  
% 1.54/1.10  
% 1.54/1.10  %Foreground operators:
% 1.54/1.10  tff(v8_struct_0, type, v8_struct_0: $i > $o).
% 1.54/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.54/1.10  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.54/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.54/1.10  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.54/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.54/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.54/1.10  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.54/1.10  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.54/1.10  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 1.54/1.10  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 1.54/1.10  
% 1.54/1.11  tff(f_56, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_finset_1(u1_struct_0(A)) => v1_compts_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_compts_1)).
% 1.54/1.11  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 1.54/1.11  tff(f_37, axiom, (![A]: ((~v8_struct_0(A) & l1_struct_0(A)) => ~v1_finset_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_struct_0)).
% 1.54/1.11  tff(f_47, axiom, (![A]: (l1_pre_topc(A) => ((v8_struct_0(A) & v2_pre_topc(A)) => (v2_pre_topc(A) & v1_compts_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_compts_1)).
% 1.54/1.11  tff(c_10, plain, (~v1_compts_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.54/1.11  tff(c_14, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.54/1.11  tff(c_16, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.54/1.11  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.54/1.11  tff(c_12, plain, (v1_finset_1(u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.54/1.11  tff(c_18, plain, (![A_5]: (~v1_finset_1(u1_struct_0(A_5)) | ~l1_struct_0(A_5) | v8_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.54/1.11  tff(c_22, plain, (~l1_struct_0('#skF_1') | v8_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_12, c_18])).
% 1.54/1.11  tff(c_23, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_22])).
% 1.54/1.11  tff(c_26, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2, c_23])).
% 1.54/1.11  tff(c_30, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_26])).
% 1.54/1.11  tff(c_31, plain, (v8_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_22])).
% 1.54/1.11  tff(c_33, plain, (![A_6]: (v1_compts_1(A_6) | ~v2_pre_topc(A_6) | ~v8_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.54/1.11  tff(c_36, plain, (v1_compts_1('#skF_1') | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_31, c_33])).
% 1.54/1.11  tff(c_39, plain, (v1_compts_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16, c_36])).
% 1.54/1.11  tff(c_41, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_39])).
% 1.54/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.54/1.11  
% 1.54/1.11  Inference rules
% 1.54/1.11  ----------------------
% 1.54/1.11  #Ref     : 0
% 1.54/1.11  #Sup     : 3
% 1.54/1.11  #Fact    : 0
% 1.54/1.11  #Define  : 0
% 1.54/1.11  #Split   : 1
% 1.54/1.11  #Chain   : 0
% 1.54/1.11  #Close   : 0
% 1.54/1.11  
% 1.54/1.11  Ordering : KBO
% 1.54/1.11  
% 1.54/1.11  Simplification rules
% 1.54/1.11  ----------------------
% 1.54/1.11  #Subsume      : 0
% 1.54/1.11  #Demod        : 3
% 1.54/1.11  #Tautology    : 1
% 1.54/1.11  #SimpNegUnit  : 1
% 1.54/1.11  #BackRed      : 0
% 1.54/1.11  
% 1.54/1.11  #Partial instantiations: 0
% 1.54/1.11  #Strategies tried      : 1
% 1.54/1.11  
% 1.54/1.11  Timing (in seconds)
% 1.54/1.11  ----------------------
% 1.54/1.11  Preprocessing        : 0.23
% 1.54/1.11  Parsing              : 0.13
% 1.54/1.11  CNF conversion       : 0.02
% 1.54/1.11  Main loop            : 0.08
% 1.54/1.11  Inferencing          : 0.04
% 1.54/1.11  Reduction            : 0.02
% 1.54/1.11  Demodulation         : 0.01
% 1.54/1.11  BG Simplification    : 0.01
% 1.54/1.11  Subsumption          : 0.01
% 1.54/1.11  Abstraction          : 0.00
% 1.54/1.11  MUC search           : 0.00
% 1.54/1.11  Cooper               : 0.00
% 1.54/1.11  Total                : 0.34
% 1.54/1.11  Index Insertion      : 0.00
% 1.54/1.11  Index Deletion       : 0.00
% 1.54/1.11  Index Matching       : 0.00
% 1.54/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
