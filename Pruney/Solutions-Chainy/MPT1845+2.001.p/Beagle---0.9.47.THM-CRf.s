%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:51 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   33 (  42 expanded)
%              Number of leaves         :   15 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :   56 (  92 expanded)
%              Number of equality atoms :    2 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_pre_topc > v2_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                & v2_pre_topc(A) )
             => v2_pre_topc(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tex_2)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(c_10,plain,(
    ~ v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [A_7] :
      ( m1_pre_topc(A_7,A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_47,plain,(
    ! [A_15,B_16] :
      ( m1_pre_topc(A_15,g1_pre_topc(u1_struct_0(B_16),u1_pre_topc(B_16)))
      | ~ m1_pre_topc(A_15,B_16)
      | ~ l1_pre_topc(B_16)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_60,plain,(
    ! [A_15] :
      ( m1_pre_topc(A_15,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_pre_topc(A_15,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_47])).

tff(c_75,plain,(
    ! [A_18] :
      ( m1_pre_topc(A_18,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_pre_topc(A_18,'#skF_2')
      | ~ l1_pre_topc(A_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_60])).

tff(c_4,plain,(
    ! [A_4,B_6] :
      ( m1_pre_topc(A_4,B_6)
      | ~ m1_pre_topc(A_4,g1_pre_topc(u1_struct_0(B_6),u1_pre_topc(B_6)))
      | ~ l1_pre_topc(B_6)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_81,plain,(
    ! [A_18] :
      ( m1_pre_topc(A_18,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_pre_topc(A_18,'#skF_2')
      | ~ l1_pre_topc(A_18) ) ),
    inference(resolution,[status(thm)],[c_75,c_4])).

tff(c_90,plain,(
    ! [A_19] :
      ( m1_pre_topc(A_19,'#skF_1')
      | ~ m1_pre_topc(A_19,'#skF_2')
      | ~ l1_pre_topc(A_19) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_81])).

tff(c_97,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_90])).

tff(c_101,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_97])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v2_pre_topc(B_3)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_131,plain,
    ( v2_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_101,c_2])).

tff(c_134,plain,(
    v2_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_18,c_131])).

tff(c_136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_134])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:04:30 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.15  
% 1.66/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.15  %$ m1_pre_topc > v2_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_1
% 1.66/1.15  
% 1.66/1.15  %Foreground sorts:
% 1.66/1.15  
% 1.66/1.15  
% 1.66/1.15  %Background operators:
% 1.66/1.15  
% 1.66/1.15  
% 1.66/1.15  %Foreground operators:
% 1.66/1.15  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 1.66/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.15  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 1.66/1.15  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.66/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.15  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 1.66/1.15  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.66/1.15  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.66/1.15  
% 1.66/1.16  tff(f_59, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & v2_pre_topc(A)) => v2_pre_topc(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tex_2)).
% 1.66/1.16  tff(f_47, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 1.66/1.16  tff(f_43, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 1.66/1.16  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 1.66/1.16  tff(c_10, plain, (~v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.66/1.16  tff(c_12, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.66/1.16  tff(c_18, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.66/1.16  tff(c_16, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.66/1.16  tff(c_8, plain, (![A_7]: (m1_pre_topc(A_7, A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.66/1.16  tff(c_14, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.66/1.16  tff(c_47, plain, (![A_15, B_16]: (m1_pre_topc(A_15, g1_pre_topc(u1_struct_0(B_16), u1_pre_topc(B_16))) | ~m1_pre_topc(A_15, B_16) | ~l1_pre_topc(B_16) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.66/1.16  tff(c_60, plain, (![A_15]: (m1_pre_topc(A_15, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_pre_topc(A_15, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_15))), inference(superposition, [status(thm), theory('equality')], [c_14, c_47])).
% 1.66/1.16  tff(c_75, plain, (![A_18]: (m1_pre_topc(A_18, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_pre_topc(A_18, '#skF_2') | ~l1_pre_topc(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_60])).
% 1.66/1.16  tff(c_4, plain, (![A_4, B_6]: (m1_pre_topc(A_4, B_6) | ~m1_pre_topc(A_4, g1_pre_topc(u1_struct_0(B_6), u1_pre_topc(B_6))) | ~l1_pre_topc(B_6) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.66/1.16  tff(c_81, plain, (![A_18]: (m1_pre_topc(A_18, '#skF_1') | ~l1_pre_topc('#skF_1') | ~m1_pre_topc(A_18, '#skF_2') | ~l1_pre_topc(A_18))), inference(resolution, [status(thm)], [c_75, c_4])).
% 1.66/1.16  tff(c_90, plain, (![A_19]: (m1_pre_topc(A_19, '#skF_1') | ~m1_pre_topc(A_19, '#skF_2') | ~l1_pre_topc(A_19))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_81])).
% 1.66/1.16  tff(c_97, plain, (m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_8, c_90])).
% 1.66/1.16  tff(c_101, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_97])).
% 1.66/1.16  tff(c_2, plain, (![B_3, A_1]: (v2_pre_topc(B_3) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.66/1.16  tff(c_131, plain, (v2_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_101, c_2])).
% 1.66/1.16  tff(c_134, plain, (v2_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_18, c_131])).
% 1.66/1.16  tff(c_136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_134])).
% 1.66/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.16  
% 1.66/1.16  Inference rules
% 1.66/1.16  ----------------------
% 1.66/1.16  #Ref     : 0
% 1.66/1.16  #Sup     : 22
% 1.66/1.16  #Fact    : 0
% 1.66/1.16  #Define  : 0
% 1.66/1.16  #Split   : 1
% 1.66/1.16  #Chain   : 0
% 1.66/1.16  #Close   : 0
% 1.66/1.16  
% 1.66/1.16  Ordering : KBO
% 1.66/1.16  
% 1.66/1.16  Simplification rules
% 1.66/1.16  ----------------------
% 1.66/1.16  #Subsume      : 5
% 1.66/1.16  #Demod        : 13
% 1.66/1.16  #Tautology    : 6
% 1.66/1.16  #SimpNegUnit  : 1
% 1.66/1.16  #BackRed      : 0
% 1.66/1.16  
% 1.66/1.16  #Partial instantiations: 0
% 1.66/1.16  #Strategies tried      : 1
% 1.66/1.16  
% 1.66/1.16  Timing (in seconds)
% 1.66/1.16  ----------------------
% 1.66/1.17  Preprocessing        : 0.27
% 1.66/1.17  Parsing              : 0.15
% 1.66/1.17  CNF conversion       : 0.02
% 1.66/1.17  Main loop            : 0.14
% 1.66/1.17  Inferencing          : 0.06
% 1.66/1.17  Reduction            : 0.04
% 1.66/1.17  Demodulation         : 0.03
% 1.66/1.17  BG Simplification    : 0.01
% 1.66/1.17  Subsumption          : 0.03
% 1.66/1.17  Abstraction          : 0.01
% 1.66/1.17  MUC search           : 0.00
% 1.66/1.17  Cooper               : 0.00
% 1.66/1.17  Total                : 0.44
% 1.66/1.17  Index Insertion      : 0.00
% 1.66/1.17  Index Deletion       : 0.00
% 1.66/1.17  Index Matching       : 0.00
% 1.66/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
