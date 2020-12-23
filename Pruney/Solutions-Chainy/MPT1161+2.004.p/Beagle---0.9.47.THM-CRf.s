%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:47 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   35 (  69 expanded)
%              Number of leaves         :   20 (  39 expanded)
%              Depth                    :    6
%              Number of atoms          :   65 ( 252 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ r2_hidden(B,k3_orders_2(A,C,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_orders_2)).

tff(f_66,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r2_hidden(B,k3_orders_2(A,D,C))
                  <=> ( r2_orders_2(A,B,C)
                      & r2_hidden(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_40,axiom,(
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

tff(c_18,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_16,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_14,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_24,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_22,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_20,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_12,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_10,plain,(
    r2_hidden('#skF_2',k3_orders_2('#skF_1','#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_33,plain,(
    ! [A_34,B_35,C_36,D_37] :
      ( r2_orders_2(A_34,B_35,C_36)
      | ~ r2_hidden(B_35,k3_orders_2(A_34,D_37,C_36))
      | ~ m1_subset_1(D_37,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ m1_subset_1(C_36,u1_struct_0(A_34))
      | ~ m1_subset_1(B_35,u1_struct_0(A_34))
      | ~ l1_orders_2(A_34)
      | ~ v5_orders_2(A_34)
      | ~ v4_orders_2(A_34)
      | ~ v3_orders_2(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_35,plain,
    ( r2_orders_2('#skF_1','#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_33])).

tff(c_38,plain,
    ( r2_orders_2('#skF_1','#skF_2','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_16,c_14,c_12,c_35])).

tff(c_39,plain,(
    r2_orders_2('#skF_1','#skF_2','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_38])).

tff(c_2,plain,(
    ! [A_1,C_7,B_5] :
      ( ~ r2_orders_2(A_1,C_7,B_5)
      | ~ r2_orders_2(A_1,B_5,C_7)
      | ~ m1_subset_1(C_7,u1_struct_0(A_1))
      | ~ m1_subset_1(B_5,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1)
      | ~ v5_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_41,plain,
    ( ~ r2_orders_2('#skF_1','#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_39,c_2])).

tff(c_45,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_14,c_39,c_41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:46:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.11  
% 1.72/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.12  %$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.72/1.12  
% 1.72/1.12  %Foreground sorts:
% 1.72/1.12  
% 1.72/1.12  
% 1.72/1.12  %Background operators:
% 1.72/1.12  
% 1.72/1.12  
% 1.72/1.12  %Foreground operators:
% 1.72/1.12  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.72/1.12  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 1.72/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.72/1.12  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 1.72/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.72/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.72/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.72/1.12  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 1.72/1.12  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 1.72/1.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.72/1.12  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.72/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.12  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 1.72/1.12  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.72/1.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.72/1.12  
% 1.72/1.13  tff(f_87, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~r2_hidden(B, k3_orders_2(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_orders_2)).
% 1.72/1.13  tff(f_66, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 1.72/1.13  tff(f_40, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_orders_2(A, B, C) & r2_orders_2(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_orders_2)).
% 1.72/1.13  tff(c_18, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 1.72/1.13  tff(c_16, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 1.72/1.13  tff(c_14, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 1.72/1.13  tff(c_24, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 1.72/1.13  tff(c_22, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 1.72/1.13  tff(c_20, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 1.72/1.13  tff(c_12, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 1.72/1.13  tff(c_10, plain, (r2_hidden('#skF_2', k3_orders_2('#skF_1', '#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 1.72/1.13  tff(c_33, plain, (![A_34, B_35, C_36, D_37]: (r2_orders_2(A_34, B_35, C_36) | ~r2_hidden(B_35, k3_orders_2(A_34, D_37, C_36)) | ~m1_subset_1(D_37, k1_zfmisc_1(u1_struct_0(A_34))) | ~m1_subset_1(C_36, u1_struct_0(A_34)) | ~m1_subset_1(B_35, u1_struct_0(A_34)) | ~l1_orders_2(A_34) | ~v5_orders_2(A_34) | ~v4_orders_2(A_34) | ~v3_orders_2(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.72/1.13  tff(c_35, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_10, c_33])).
% 1.72/1.13  tff(c_38, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_18, c_16, c_14, c_12, c_35])).
% 1.72/1.13  tff(c_39, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_24, c_38])).
% 1.72/1.13  tff(c_2, plain, (![A_1, C_7, B_5]: (~r2_orders_2(A_1, C_7, B_5) | ~r2_orders_2(A_1, B_5, C_7) | ~m1_subset_1(C_7, u1_struct_0(A_1)) | ~m1_subset_1(B_5, u1_struct_0(A_1)) | ~l1_orders_2(A_1) | ~v5_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.72/1.13  tff(c_41, plain, (~r2_orders_2('#skF_1', '#skF_2', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_39, c_2])).
% 1.72/1.13  tff(c_45, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_14, c_39, c_41])).
% 1.72/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.13  
% 1.72/1.13  Inference rules
% 1.72/1.13  ----------------------
% 1.72/1.13  #Ref     : 0
% 1.72/1.13  #Sup     : 3
% 1.72/1.13  #Fact    : 0
% 1.72/1.13  #Define  : 0
% 1.72/1.13  #Split   : 0
% 1.72/1.13  #Chain   : 0
% 1.72/1.13  #Close   : 0
% 1.72/1.13  
% 1.72/1.13  Ordering : KBO
% 1.72/1.13  
% 1.72/1.13  Simplification rules
% 1.72/1.13  ----------------------
% 1.72/1.13  #Subsume      : 0
% 1.72/1.13  #Demod        : 16
% 1.72/1.13  #Tautology    : 0
% 1.72/1.13  #SimpNegUnit  : 2
% 1.72/1.13  #BackRed      : 0
% 1.72/1.13  
% 1.72/1.13  #Partial instantiations: 0
% 1.72/1.13  #Strategies tried      : 1
% 1.72/1.13  
% 1.72/1.13  Timing (in seconds)
% 1.72/1.13  ----------------------
% 1.72/1.13  Preprocessing        : 0.27
% 1.72/1.13  Parsing              : 0.15
% 1.72/1.13  CNF conversion       : 0.02
% 1.72/1.13  Main loop            : 0.10
% 1.72/1.13  Inferencing          : 0.04
% 1.72/1.13  Reduction            : 0.03
% 1.72/1.13  Demodulation         : 0.02
% 1.72/1.13  BG Simplification    : 0.01
% 1.72/1.13  Subsumption          : 0.02
% 1.72/1.13  Abstraction          : 0.00
% 1.72/1.13  MUC search           : 0.00
% 1.72/1.13  Cooper               : 0.00
% 1.72/1.13  Total                : 0.40
% 1.72/1.13  Index Insertion      : 0.00
% 1.72/1.13  Index Deletion       : 0.00
% 1.72/1.13  Index Matching       : 0.00
% 1.72/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
