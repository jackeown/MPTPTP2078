%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:21 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   39 (  80 expanded)
%              Number of leaves         :   15 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   79 ( 245 expanded)
%              Number of equality atoms :   12 (  20 expanded)
%              Maximal formula depth    :   11 (   4 average)
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

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( ( v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ~ ( r1_orders_2(A,B,C)
                    & r2_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( r1_orders_2(A,B,C)
                  & r1_orders_2(A,C,B) )
               => B = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_orders_2)).

tff(c_18,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_14,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    r1_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_16,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

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

tff(c_10,plain,(
    r2_orders_2('#skF_1','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_66,plain,(
    r2_orders_2('#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_10])).

tff(c_4,plain,(
    ! [A_1,C_7] :
      ( ~ r2_orders_2(A_1,C_7,C_7)
      | ~ m1_subset_1(C_7,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_85,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_4])).

tff(c_92,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_14,c_85])).

tff(c_94,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_20,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22,plain,(
    ! [A_21,B_22,C_23] :
      ( r1_orders_2(A_21,B_22,C_23)
      | ~ r2_orders_2(A_21,B_22,C_23)
      | ~ m1_subset_1(C_23,u1_struct_0(A_21))
      | ~ m1_subset_1(B_22,u1_struct_0(A_21))
      | ~ l1_orders_2(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_24,plain,
    ( r1_orders_2('#skF_1','#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_22])).

tff(c_27,plain,(
    r1_orders_2('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_14,c_16,c_24])).

tff(c_100,plain,(
    ! [C_32,B_33,A_34] :
      ( C_32 = B_33
      | ~ r1_orders_2(A_34,C_32,B_33)
      | ~ r1_orders_2(A_34,B_33,C_32)
      | ~ m1_subset_1(C_32,u1_struct_0(A_34))
      | ~ m1_subset_1(B_33,u1_struct_0(A_34))
      | ~ l1_orders_2(A_34)
      | ~ v5_orders_2(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_102,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_orders_2('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_27,c_100])).

tff(c_107,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_14,c_12,c_102])).

tff(c_109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_107])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:11:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.15  
% 1.64/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.16  %$ r2_orders_2 > r1_orders_2 > m1_subset_1 > v5_orders_2 > l1_orders_2 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1
% 1.64/1.16  
% 1.64/1.16  %Foreground sorts:
% 1.64/1.16  
% 1.64/1.16  
% 1.64/1.16  %Background operators:
% 1.64/1.16  
% 1.64/1.16  
% 1.64/1.16  %Foreground operators:
% 1.64/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.16  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 1.64/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.16  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 1.64/1.16  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.64/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.16  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 1.64/1.16  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.64/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.64/1.16  
% 1.64/1.17  tff(f_72, negated_conjecture, ~(![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r1_orders_2(A, B, C) & r2_orders_2(A, C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_orders_2)).
% 1.64/1.17  tff(f_40, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 1.64/1.17  tff(f_56, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((r1_orders_2(A, B, C) & r1_orders_2(A, C, B)) => (B = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_orders_2)).
% 1.64/1.17  tff(c_18, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.64/1.17  tff(c_14, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.64/1.17  tff(c_12, plain, (r1_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.64/1.17  tff(c_16, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.64/1.17  tff(c_28, plain, (![A_24, B_25, C_26]: (r2_orders_2(A_24, B_25, C_26) | C_26=B_25 | ~r1_orders_2(A_24, B_25, C_26) | ~m1_subset_1(C_26, u1_struct_0(A_24)) | ~m1_subset_1(B_25, u1_struct_0(A_24)) | ~l1_orders_2(A_24))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.64/1.17  tff(c_32, plain, (![B_25]: (r2_orders_2('#skF_1', B_25, '#skF_3') | B_25='#skF_3' | ~r1_orders_2('#skF_1', B_25, '#skF_3') | ~m1_subset_1(B_25, u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_28])).
% 1.64/1.17  tff(c_51, plain, (![B_28]: (r2_orders_2('#skF_1', B_28, '#skF_3') | B_28='#skF_3' | ~r1_orders_2('#skF_1', B_28, '#skF_3') | ~m1_subset_1(B_28, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_32])).
% 1.64/1.17  tff(c_54, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_3') | '#skF_2'='#skF_3' | ~r1_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_16, c_51])).
% 1.64/1.17  tff(c_60, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_3') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_54])).
% 1.64/1.17  tff(c_63, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_60])).
% 1.64/1.17  tff(c_10, plain, (r2_orders_2('#skF_1', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.64/1.17  tff(c_66, plain, (r2_orders_2('#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_10])).
% 1.64/1.17  tff(c_4, plain, (![A_1, C_7]: (~r2_orders_2(A_1, C_7, C_7) | ~m1_subset_1(C_7, u1_struct_0(A_1)) | ~l1_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.64/1.17  tff(c_85, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_66, c_4])).
% 1.64/1.17  tff(c_92, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_14, c_85])).
% 1.64/1.17  tff(c_94, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_60])).
% 1.64/1.17  tff(c_20, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.64/1.17  tff(c_22, plain, (![A_21, B_22, C_23]: (r1_orders_2(A_21, B_22, C_23) | ~r2_orders_2(A_21, B_22, C_23) | ~m1_subset_1(C_23, u1_struct_0(A_21)) | ~m1_subset_1(B_22, u1_struct_0(A_21)) | ~l1_orders_2(A_21))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.64/1.17  tff(c_24, plain, (r1_orders_2('#skF_1', '#skF_3', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_10, c_22])).
% 1.64/1.17  tff(c_27, plain, (r1_orders_2('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_14, c_16, c_24])).
% 1.64/1.17  tff(c_100, plain, (![C_32, B_33, A_34]: (C_32=B_33 | ~r1_orders_2(A_34, C_32, B_33) | ~r1_orders_2(A_34, B_33, C_32) | ~m1_subset_1(C_32, u1_struct_0(A_34)) | ~m1_subset_1(B_33, u1_struct_0(A_34)) | ~l1_orders_2(A_34) | ~v5_orders_2(A_34))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.64/1.17  tff(c_102, plain, ('#skF_2'='#skF_3' | ~r1_orders_2('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_27, c_100])).
% 1.64/1.17  tff(c_107, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_16, c_14, c_12, c_102])).
% 1.64/1.17  tff(c_109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_107])).
% 1.64/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.17  
% 1.64/1.17  Inference rules
% 1.64/1.17  ----------------------
% 1.64/1.17  #Ref     : 0
% 1.64/1.17  #Sup     : 15
% 1.64/1.17  #Fact    : 0
% 1.64/1.17  #Define  : 0
% 1.64/1.17  #Split   : 1
% 1.64/1.17  #Chain   : 0
% 1.64/1.17  #Close   : 0
% 1.64/1.17  
% 1.64/1.17  Ordering : KBO
% 1.64/1.17  
% 1.64/1.17  Simplification rules
% 1.64/1.17  ----------------------
% 1.64/1.17  #Subsume      : 1
% 1.64/1.17  #Demod        : 35
% 1.64/1.17  #Tautology    : 10
% 1.64/1.17  #SimpNegUnit  : 1
% 1.64/1.17  #BackRed      : 5
% 1.64/1.17  
% 1.64/1.17  #Partial instantiations: 0
% 1.64/1.17  #Strategies tried      : 1
% 1.64/1.17  
% 1.64/1.17  Timing (in seconds)
% 1.64/1.17  ----------------------
% 1.64/1.17  Preprocessing        : 0.28
% 1.64/1.17  Parsing              : 0.16
% 1.64/1.17  CNF conversion       : 0.02
% 1.64/1.17  Main loop            : 0.14
% 1.64/1.17  Inferencing          : 0.06
% 1.64/1.17  Reduction            : 0.04
% 1.64/1.17  Demodulation         : 0.03
% 1.64/1.17  BG Simplification    : 0.01
% 1.64/1.17  Subsumption          : 0.03
% 1.64/1.17  Abstraction          : 0.01
% 1.64/1.17  MUC search           : 0.00
% 1.64/1.17  Cooper               : 0.00
% 1.64/1.17  Total                : 0.44
% 1.64/1.17  Index Insertion      : 0.00
% 1.64/1.17  Index Deletion       : 0.00
% 1.64/1.17  Index Matching       : 0.00
% 1.64/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
