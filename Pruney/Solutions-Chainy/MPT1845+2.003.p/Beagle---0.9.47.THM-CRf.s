%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:52 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   26 (  30 expanded)
%              Number of leaves         :   14 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  52 expanded)
%              Number of equality atoms :    2 (   6 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_pre_topc > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_51,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                & v2_pre_topc(A) )
             => v2_pre_topc(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tex_2)).

tff(f_33,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
       => v2_pre_topc(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_pre_topc)).

tff(c_10,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [A_1] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)))
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ~ v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [A_2] :
      ( v2_pre_topc(A_2)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(A_2),u1_pre_topc(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_27,plain,
    ( v2_pre_topc('#skF_2')
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_6])).

tff(c_37,plain,
    ( v2_pre_topc('#skF_2')
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_27])).

tff(c_38,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_37])).

tff(c_46,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_38])).

tff(c_50,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_16,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:19:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.11  
% 1.65/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.11  %$ v2_pre_topc > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_1
% 1.65/1.11  
% 1.65/1.11  %Foreground sorts:
% 1.65/1.11  
% 1.65/1.11  
% 1.65/1.11  %Background operators:
% 1.65/1.11  
% 1.65/1.11  
% 1.65/1.11  %Foreground operators:
% 1.65/1.11  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 1.65/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.11  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 1.65/1.11  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.65/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.11  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 1.65/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.11  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.65/1.11  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.65/1.11  
% 1.65/1.12  tff(f_51, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & v2_pre_topc(A)) => v2_pre_topc(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tex_2)).
% 1.65/1.12  tff(f_33, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_pre_topc)).
% 1.65/1.12  tff(f_39, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => v2_pre_topc(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_pre_topc)).
% 1.65/1.12  tff(c_10, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.65/1.12  tff(c_16, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.65/1.12  tff(c_2, plain, (![A_1]: (v2_pre_topc(g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.65/1.12  tff(c_8, plain, (~v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.65/1.12  tff(c_14, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.65/1.12  tff(c_12, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.65/1.12  tff(c_6, plain, (![A_2]: (v2_pre_topc(A_2) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(A_2), u1_pre_topc(A_2))) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.65/1.12  tff(c_27, plain, (v2_pre_topc('#skF_2') | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12, c_6])).
% 1.65/1.12  tff(c_37, plain, (v2_pre_topc('#skF_2') | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_27])).
% 1.65/1.12  tff(c_38, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_8, c_37])).
% 1.65/1.12  tff(c_46, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2, c_38])).
% 1.65/1.12  tff(c_50, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_16, c_46])).
% 1.65/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.12  
% 1.65/1.12  Inference rules
% 1.65/1.12  ----------------------
% 1.65/1.12  #Ref     : 0
% 1.65/1.12  #Sup     : 7
% 1.65/1.12  #Fact    : 0
% 1.65/1.12  #Define  : 0
% 1.65/1.12  #Split   : 0
% 1.65/1.12  #Chain   : 0
% 1.65/1.12  #Close   : 0
% 1.65/1.12  
% 1.65/1.12  Ordering : KBO
% 1.65/1.12  
% 1.65/1.12  Simplification rules
% 1.65/1.12  ----------------------
% 1.65/1.12  #Subsume      : 2
% 1.65/1.12  #Demod        : 5
% 1.65/1.12  #Tautology    : 3
% 1.65/1.12  #SimpNegUnit  : 1
% 1.65/1.12  #BackRed      : 0
% 1.65/1.12  
% 1.65/1.12  #Partial instantiations: 0
% 1.65/1.12  #Strategies tried      : 1
% 1.65/1.12  
% 1.65/1.12  Timing (in seconds)
% 1.65/1.12  ----------------------
% 1.65/1.12  Preprocessing        : 0.28
% 1.65/1.12  Parsing              : 0.15
% 1.65/1.12  CNF conversion       : 0.02
% 1.65/1.12  Main loop            : 0.09
% 1.65/1.12  Inferencing          : 0.04
% 1.65/1.12  Reduction            : 0.02
% 1.65/1.12  Demodulation         : 0.02
% 1.65/1.12  BG Simplification    : 0.01
% 1.65/1.12  Subsumption          : 0.01
% 1.65/1.12  Abstraction          : 0.00
% 1.65/1.12  MUC search           : 0.00
% 1.65/1.12  Cooper               : 0.00
% 1.65/1.12  Total                : 0.38
% 1.65/1.12  Index Insertion      : 0.00
% 1.65/1.12  Index Deletion       : 0.00
% 1.65/1.12  Index Matching       : 0.00
% 1.65/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
