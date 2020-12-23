%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:21 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   35 (  87 expanded)
%              Number of leaves         :   15 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 ( 272 expanded)
%              Number of equality atoms :    7 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > m1_subset_1 > v5_orders_2 > l1_orders_2 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( ( v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ~ ( r1_orders_2(A,B,C)
                    & r2_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_orders_2)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_orders_2(A,B,C)
              <=> ( r1_orders_2(A,B,C)
                  & B != C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ~ ( r2_orders_2(A,B,C)
                  & r2_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_orders_2)).

tff(c_20,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_18,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_14,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_16,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10,plain,(
    r2_orders_2('#skF_1','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12,plain,(
    r1_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_28,plain,(
    ! [A_24,B_25,C_26] :
      ( r2_orders_2(A_24,B_25,C_26)
      | C_26 = B_25
      | ~ r1_orders_2(A_24,B_25,C_26)
      | ~ m1_subset_1(C_26,u1_struct_0(A_24))
      | ~ m1_subset_1(B_25,u1_struct_0(A_24))
      | ~ l1_orders_2(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_32,plain,(
    ! [B_25] :
      ( r2_orders_2('#skF_1',B_25,'#skF_3')
      | B_25 = '#skF_3'
      | ~ r1_orders_2('#skF_1',B_25,'#skF_3')
      | ~ m1_subset_1(B_25,u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_28])).

tff(c_51,plain,(
    ! [B_28] :
      ( r2_orders_2('#skF_1',B_28,'#skF_3')
      | B_28 = '#skF_3'
      | ~ r1_orders_2('#skF_1',B_28,'#skF_3')
      | ~ m1_subset_1(B_28,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_32])).

tff(c_54,plain,
    ( r2_orders_2('#skF_1','#skF_2','#skF_3')
    | '#skF_2' = '#skF_3'
    | ~ r1_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_51])).

tff(c_60,plain,
    ( r2_orders_2('#skF_1','#skF_2','#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_54])).

tff(c_63,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_66,plain,(
    r2_orders_2('#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_10])).

tff(c_8,plain,(
    ! [A_8,C_14,B_12] :
      ( ~ r2_orders_2(A_8,C_14,B_12)
      | ~ r2_orders_2(A_8,B_12,C_14)
      | ~ m1_subset_1(C_14,u1_struct_0(A_8))
      | ~ m1_subset_1(B_12,u1_struct_0(A_8))
      | ~ l1_orders_2(A_8)
      | ~ v5_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_77,plain,
    ( ~ r2_orders_2('#skF_1','#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_8])).

tff(c_85,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_14,c_66,c_77])).

tff(c_86,plain,(
    r2_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_93,plain,(
    ! [A_32,C_33,B_34] :
      ( ~ r2_orders_2(A_32,C_33,B_34)
      | ~ r2_orders_2(A_32,B_34,C_33)
      | ~ m1_subset_1(C_33,u1_struct_0(A_32))
      | ~ m1_subset_1(B_34,u1_struct_0(A_32))
      | ~ l1_orders_2(A_32)
      | ~ v5_orders_2(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_95,plain,
    ( ~ r2_orders_2('#skF_1','#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_86,c_93])).

tff(c_101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_14,c_16,c_10,c_95])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:05:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.15  
% 1.83/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.15  %$ r2_orders_2 > r1_orders_2 > m1_subset_1 > v5_orders_2 > l1_orders_2 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1
% 1.83/1.15  
% 1.83/1.15  %Foreground sorts:
% 1.83/1.15  
% 1.83/1.15  
% 1.83/1.15  %Background operators:
% 1.83/1.15  
% 1.83/1.15  
% 1.83/1.15  %Foreground operators:
% 1.83/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.15  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 1.83/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.83/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.83/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.83/1.15  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 1.83/1.15  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.83/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.15  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 1.83/1.15  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.83/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.83/1.15  
% 1.83/1.16  tff(f_71, negated_conjecture, ~(![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r1_orders_2(A, B, C) & r2_orders_2(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_orders_2)).
% 1.83/1.16  tff(f_40, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 1.83/1.16  tff(f_55, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_orders_2(A, B, C) & r2_orders_2(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_orders_2)).
% 1.83/1.16  tff(c_20, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.83/1.16  tff(c_18, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.83/1.16  tff(c_14, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.83/1.16  tff(c_16, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.83/1.16  tff(c_10, plain, (r2_orders_2('#skF_1', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.83/1.16  tff(c_12, plain, (r1_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.83/1.16  tff(c_28, plain, (![A_24, B_25, C_26]: (r2_orders_2(A_24, B_25, C_26) | C_26=B_25 | ~r1_orders_2(A_24, B_25, C_26) | ~m1_subset_1(C_26, u1_struct_0(A_24)) | ~m1_subset_1(B_25, u1_struct_0(A_24)) | ~l1_orders_2(A_24))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.83/1.16  tff(c_32, plain, (![B_25]: (r2_orders_2('#skF_1', B_25, '#skF_3') | B_25='#skF_3' | ~r1_orders_2('#skF_1', B_25, '#skF_3') | ~m1_subset_1(B_25, u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_28])).
% 1.83/1.16  tff(c_51, plain, (![B_28]: (r2_orders_2('#skF_1', B_28, '#skF_3') | B_28='#skF_3' | ~r1_orders_2('#skF_1', B_28, '#skF_3') | ~m1_subset_1(B_28, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_32])).
% 1.83/1.16  tff(c_54, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_3') | '#skF_2'='#skF_3' | ~r1_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_16, c_51])).
% 1.83/1.16  tff(c_60, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_3') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_54])).
% 1.83/1.16  tff(c_63, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_60])).
% 1.83/1.16  tff(c_66, plain, (r2_orders_2('#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_10])).
% 1.83/1.16  tff(c_8, plain, (![A_8, C_14, B_12]: (~r2_orders_2(A_8, C_14, B_12) | ~r2_orders_2(A_8, B_12, C_14) | ~m1_subset_1(C_14, u1_struct_0(A_8)) | ~m1_subset_1(B_12, u1_struct_0(A_8)) | ~l1_orders_2(A_8) | ~v5_orders_2(A_8))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.83/1.16  tff(c_77, plain, (~r2_orders_2('#skF_1', '#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_66, c_8])).
% 1.83/1.16  tff(c_85, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_14, c_66, c_77])).
% 1.83/1.16  tff(c_86, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_60])).
% 1.83/1.16  tff(c_93, plain, (![A_32, C_33, B_34]: (~r2_orders_2(A_32, C_33, B_34) | ~r2_orders_2(A_32, B_34, C_33) | ~m1_subset_1(C_33, u1_struct_0(A_32)) | ~m1_subset_1(B_34, u1_struct_0(A_32)) | ~l1_orders_2(A_32) | ~v5_orders_2(A_32))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.83/1.16  tff(c_95, plain, (~r2_orders_2('#skF_1', '#skF_3', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_86, c_93])).
% 1.83/1.16  tff(c_101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_14, c_16, c_10, c_95])).
% 1.83/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.16  
% 1.83/1.16  Inference rules
% 1.83/1.16  ----------------------
% 1.83/1.16  #Ref     : 0
% 1.83/1.16  #Sup     : 15
% 1.83/1.16  #Fact    : 0
% 1.83/1.16  #Define  : 0
% 1.83/1.16  #Split   : 1
% 1.83/1.16  #Chain   : 0
% 1.83/1.16  #Close   : 0
% 1.83/1.16  
% 1.83/1.16  Ordering : KBO
% 1.83/1.16  
% 1.83/1.16  Simplification rules
% 1.83/1.16  ----------------------
% 1.83/1.16  #Subsume      : 1
% 1.83/1.16  #Demod        : 30
% 1.83/1.16  #Tautology    : 8
% 1.83/1.16  #SimpNegUnit  : 0
% 1.83/1.16  #BackRed      : 5
% 1.83/1.16  
% 1.83/1.16  #Partial instantiations: 0
% 1.83/1.16  #Strategies tried      : 1
% 1.83/1.16  
% 1.83/1.16  Timing (in seconds)
% 1.83/1.16  ----------------------
% 1.83/1.16  Preprocessing        : 0.27
% 1.83/1.16  Parsing              : 0.15
% 1.83/1.16  CNF conversion       : 0.02
% 1.83/1.16  Main loop            : 0.13
% 1.83/1.16  Inferencing          : 0.05
% 1.83/1.16  Reduction            : 0.04
% 1.83/1.16  Demodulation         : 0.03
% 1.83/1.16  BG Simplification    : 0.01
% 1.83/1.16  Subsumption          : 0.03
% 1.83/1.16  Abstraction          : 0.01
% 1.83/1.16  MUC search           : 0.00
% 1.83/1.16  Cooper               : 0.00
% 1.83/1.16  Total                : 0.43
% 1.83/1.16  Index Insertion      : 0.00
% 1.83/1.16  Index Deletion       : 0.00
% 1.83/1.16  Index Matching       : 0.00
% 1.83/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
