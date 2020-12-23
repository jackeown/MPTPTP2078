%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:40 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   32 (  41 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   60 ( 104 expanded)
%              Number of equality atoms :    7 (  14 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tsep_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

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

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => k1_tsep_1(A,B,B) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).

tff(f_32,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( m1_pre_topc(B,C)
              <=> k1_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tsep_1)).

tff(c_20,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_14,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_10,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k1_tsep_1('#skF_1','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_16,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_12,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    ! [B_14,A_15] :
      ( l1_pre_topc(B_14)
      | ~ m1_pre_topc(B_14,A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_22])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_28])).

tff(c_18,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    ! [A_11] :
      ( m1_pre_topc(A_11,A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_34,plain,(
    ! [A_19,B_20,C_21] :
      ( k1_tsep_1(A_19,B_20,C_21) = g1_pre_topc(u1_struct_0(C_21),u1_pre_topc(C_21))
      | ~ m1_pre_topc(B_20,C_21)
      | ~ m1_pre_topc(C_21,A_19)
      | v2_struct_0(C_21)
      | ~ m1_pre_topc(B_20,A_19)
      | v2_struct_0(B_20)
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_78,plain,(
    ! [A_23,A_24] :
      ( k1_tsep_1(A_23,A_24,A_24) = g1_pre_topc(u1_struct_0(A_24),u1_pre_topc(A_24))
      | ~ m1_pre_topc(A_24,A_23)
      | v2_struct_0(A_24)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23)
      | ~ l1_pre_topc(A_24) ) ),
    inference(resolution,[status(thm)],[c_8,c_34])).

tff(c_84,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k1_tsep_1('#skF_1','#skF_2','#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_78])).

tff(c_92,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k1_tsep_1('#skF_1','#skF_2','#skF_2')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_18,c_16,c_84])).

tff(c_94,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_14,c_10,c_92])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:38:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.19  
% 1.86/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.19  %$ m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tsep_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_1
% 1.86/1.19  
% 1.86/1.19  %Foreground sorts:
% 1.86/1.19  
% 1.86/1.19  
% 1.86/1.19  %Background operators:
% 1.86/1.19  
% 1.86/1.19  
% 1.86/1.19  %Foreground operators:
% 1.86/1.19  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.86/1.19  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 1.86/1.19  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 1.86/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.19  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 1.86/1.19  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.86/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.86/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.19  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 1.86/1.19  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.86/1.19  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.86/1.19  
% 1.94/1.20  tff(f_75, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (k1_tsep_1(A, B, B) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_tmap_1)).
% 1.94/1.20  tff(f_32, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 1.94/1.20  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 1.94/1.20  tff(f_55, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) <=> (k1_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tsep_1)).
% 1.94/1.20  tff(c_20, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.94/1.20  tff(c_14, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.94/1.20  tff(c_10, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k1_tsep_1('#skF_1', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.94/1.20  tff(c_16, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.94/1.20  tff(c_12, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.94/1.20  tff(c_22, plain, (![B_14, A_15]: (l1_pre_topc(B_14) | ~m1_pre_topc(B_14, A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.94/1.20  tff(c_28, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_22])).
% 1.94/1.20  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_28])).
% 1.94/1.20  tff(c_18, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.94/1.20  tff(c_8, plain, (![A_11]: (m1_pre_topc(A_11, A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.94/1.20  tff(c_34, plain, (![A_19, B_20, C_21]: (k1_tsep_1(A_19, B_20, C_21)=g1_pre_topc(u1_struct_0(C_21), u1_pre_topc(C_21)) | ~m1_pre_topc(B_20, C_21) | ~m1_pre_topc(C_21, A_19) | v2_struct_0(C_21) | ~m1_pre_topc(B_20, A_19) | v2_struct_0(B_20) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.94/1.20  tff(c_78, plain, (![A_23, A_24]: (k1_tsep_1(A_23, A_24, A_24)=g1_pre_topc(u1_struct_0(A_24), u1_pre_topc(A_24)) | ~m1_pre_topc(A_24, A_23) | v2_struct_0(A_24) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23) | ~l1_pre_topc(A_24))), inference(resolution, [status(thm)], [c_8, c_34])).
% 1.94/1.20  tff(c_84, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k1_tsep_1('#skF_1', '#skF_2', '#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_78])).
% 1.94/1.20  tff(c_92, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k1_tsep_1('#skF_1', '#skF_2', '#skF_2') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_18, c_16, c_84])).
% 1.94/1.20  tff(c_94, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_14, c_10, c_92])).
% 1.94/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.20  
% 1.94/1.20  Inference rules
% 1.94/1.20  ----------------------
% 1.94/1.20  #Ref     : 0
% 1.94/1.20  #Sup     : 12
% 1.94/1.20  #Fact    : 0
% 1.94/1.20  #Define  : 0
% 1.94/1.20  #Split   : 1
% 1.94/1.20  #Chain   : 0
% 1.94/1.20  #Close   : 0
% 1.94/1.20  
% 1.94/1.20  Ordering : KBO
% 1.94/1.20  
% 1.94/1.20  Simplification rules
% 1.94/1.20  ----------------------
% 1.94/1.20  #Subsume      : 0
% 1.94/1.20  #Demod        : 12
% 1.94/1.20  #Tautology    : 2
% 1.94/1.20  #SimpNegUnit  : 6
% 1.94/1.20  #BackRed      : 0
% 1.94/1.20  
% 1.94/1.20  #Partial instantiations: 0
% 1.94/1.20  #Strategies tried      : 1
% 1.94/1.20  
% 1.94/1.20  Timing (in seconds)
% 1.94/1.20  ----------------------
% 1.94/1.20  Preprocessing        : 0.29
% 1.94/1.20  Parsing              : 0.16
% 1.94/1.20  CNF conversion       : 0.02
% 1.94/1.20  Main loop            : 0.14
% 1.94/1.20  Inferencing          : 0.06
% 1.94/1.20  Reduction            : 0.04
% 1.94/1.20  Demodulation         : 0.03
% 1.94/1.20  BG Simplification    : 0.01
% 1.94/1.20  Subsumption          : 0.03
% 1.94/1.20  Abstraction          : 0.01
% 1.94/1.20  MUC search           : 0.00
% 1.94/1.20  Cooper               : 0.00
% 1.94/1.20  Total                : 0.45
% 1.94/1.20  Index Insertion      : 0.00
% 1.94/1.20  Index Deletion       : 0.00
% 1.94/1.20  Index Matching       : 0.00
% 1.94/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
