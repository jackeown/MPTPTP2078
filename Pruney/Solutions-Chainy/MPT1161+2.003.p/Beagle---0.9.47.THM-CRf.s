%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:46 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   41 (  62 expanded)
%              Number of leaves         :   22 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :   82 ( 201 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

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

tff(f_99,negated_conjecture,(
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

tff(f_37,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,B,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

tff(f_78,axiom,(
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

tff(f_52,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ~ ( r1_orders_2(A,B,C)
                  & r2_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_orders_2)).

tff(c_20,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_18,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_16,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_24,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_27,plain,(
    ! [A_30,B_31] :
      ( r1_orders_2(A_30,B_31,B_31)
      | ~ m1_subset_1(B_31,u1_struct_0(A_30))
      | ~ l1_orders_2(A_30)
      | ~ v3_orders_2(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_29,plain,
    ( r1_orders_2('#skF_1','#skF_2','#skF_2')
    | ~ l1_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_27])).

tff(c_32,plain,
    ( r1_orders_2('#skF_1','#skF_2','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_18,c_29])).

tff(c_33,plain,(
    r1_orders_2('#skF_1','#skF_2','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_32])).

tff(c_22,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_14,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_12,plain,(
    r2_hidden('#skF_2',k3_orders_2('#skF_1','#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_42,plain,(
    ! [A_39,B_40,C_41,D_42] :
      ( r2_orders_2(A_39,B_40,C_41)
      | ~ r2_hidden(B_40,k3_orders_2(A_39,D_42,C_41))
      | ~ m1_subset_1(D_42,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ m1_subset_1(C_41,u1_struct_0(A_39))
      | ~ m1_subset_1(B_40,u1_struct_0(A_39))
      | ~ l1_orders_2(A_39)
      | ~ v5_orders_2(A_39)
      | ~ v4_orders_2(A_39)
      | ~ v3_orders_2(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_44,plain,
    ( r2_orders_2('#skF_1','#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_42])).

tff(c_47,plain,
    ( r2_orders_2('#skF_1','#skF_2','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_18,c_16,c_14,c_44])).

tff(c_48,plain,(
    r2_orders_2('#skF_1','#skF_2','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_47])).

tff(c_4,plain,(
    ! [A_4,C_10,B_8] :
      ( ~ r2_orders_2(A_4,C_10,B_8)
      | ~ r1_orders_2(A_4,B_8,C_10)
      | ~ m1_subset_1(C_10,u1_struct_0(A_4))
      | ~ m1_subset_1(B_8,u1_struct_0(A_4))
      | ~ l1_orders_2(A_4)
      | ~ v5_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_50,plain,
    ( ~ r1_orders_2('#skF_1','#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_4])).

tff(c_54,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_33,c_50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n001.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 17:48:30 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.15  
% 1.78/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.15  %$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.78/1.15  
% 1.78/1.15  %Foreground sorts:
% 1.78/1.15  
% 1.78/1.15  
% 1.78/1.15  %Background operators:
% 1.78/1.15  
% 1.78/1.15  
% 1.78/1.15  %Foreground operators:
% 1.78/1.15  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.78/1.15  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 1.78/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.78/1.15  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 1.78/1.15  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 1.78/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.78/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.78/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.78/1.15  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 1.78/1.15  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 1.78/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.78/1.15  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.78/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.15  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 1.78/1.15  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.78/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.78/1.15  
% 1.78/1.16  tff(f_99, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~r2_hidden(B, k3_orders_2(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_orders_2)).
% 1.78/1.16  tff(f_37, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_orders_2)).
% 1.78/1.16  tff(f_78, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 1.78/1.16  tff(f_52, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r1_orders_2(A, B, C) & r2_orders_2(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_orders_2)).
% 1.78/1.16  tff(c_20, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 1.78/1.16  tff(c_18, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 1.78/1.16  tff(c_16, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 1.78/1.16  tff(c_26, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 1.78/1.16  tff(c_24, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 1.78/1.16  tff(c_27, plain, (![A_30, B_31]: (r1_orders_2(A_30, B_31, B_31) | ~m1_subset_1(B_31, u1_struct_0(A_30)) | ~l1_orders_2(A_30) | ~v3_orders_2(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.78/1.16  tff(c_29, plain, (r1_orders_2('#skF_1', '#skF_2', '#skF_2') | ~l1_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_27])).
% 1.78/1.16  tff(c_32, plain, (r1_orders_2('#skF_1', '#skF_2', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_18, c_29])).
% 1.78/1.16  tff(c_33, plain, (r1_orders_2('#skF_1', '#skF_2', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_26, c_32])).
% 1.78/1.16  tff(c_22, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 1.78/1.16  tff(c_14, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 1.78/1.16  tff(c_12, plain, (r2_hidden('#skF_2', k3_orders_2('#skF_1', '#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 1.78/1.16  tff(c_42, plain, (![A_39, B_40, C_41, D_42]: (r2_orders_2(A_39, B_40, C_41) | ~r2_hidden(B_40, k3_orders_2(A_39, D_42, C_41)) | ~m1_subset_1(D_42, k1_zfmisc_1(u1_struct_0(A_39))) | ~m1_subset_1(C_41, u1_struct_0(A_39)) | ~m1_subset_1(B_40, u1_struct_0(A_39)) | ~l1_orders_2(A_39) | ~v5_orders_2(A_39) | ~v4_orders_2(A_39) | ~v3_orders_2(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.78/1.16  tff(c_44, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_12, c_42])).
% 1.78/1.16  tff(c_47, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_18, c_16, c_14, c_44])).
% 1.78/1.16  tff(c_48, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_26, c_47])).
% 1.78/1.16  tff(c_4, plain, (![A_4, C_10, B_8]: (~r2_orders_2(A_4, C_10, B_8) | ~r1_orders_2(A_4, B_8, C_10) | ~m1_subset_1(C_10, u1_struct_0(A_4)) | ~m1_subset_1(B_8, u1_struct_0(A_4)) | ~l1_orders_2(A_4) | ~v5_orders_2(A_4))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.78/1.16  tff(c_50, plain, (~r1_orders_2('#skF_1', '#skF_2', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_48, c_4])).
% 1.78/1.16  tff(c_54, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_16, c_33, c_50])).
% 1.78/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.16  
% 1.78/1.16  Inference rules
% 1.78/1.16  ----------------------
% 1.78/1.16  #Ref     : 0
% 1.78/1.16  #Sup     : 4
% 1.78/1.16  #Fact    : 0
% 1.78/1.16  #Define  : 0
% 1.78/1.16  #Split   : 0
% 1.78/1.16  #Chain   : 0
% 1.78/1.16  #Close   : 0
% 1.78/1.16  
% 1.78/1.16  Ordering : KBO
% 1.78/1.16  
% 1.78/1.16  Simplification rules
% 1.78/1.16  ----------------------
% 1.78/1.16  #Subsume      : 0
% 1.78/1.16  #Demod        : 18
% 1.78/1.16  #Tautology    : 0
% 1.78/1.16  #SimpNegUnit  : 3
% 1.78/1.16  #BackRed      : 0
% 1.78/1.16  
% 1.78/1.16  #Partial instantiations: 0
% 1.78/1.16  #Strategies tried      : 1
% 1.78/1.16  
% 1.78/1.16  Timing (in seconds)
% 1.78/1.16  ----------------------
% 1.78/1.16  Preprocessing        : 0.28
% 1.95/1.17  Parsing              : 0.15
% 1.95/1.17  CNF conversion       : 0.02
% 1.95/1.17  Main loop            : 0.11
% 1.95/1.17  Inferencing          : 0.05
% 1.95/1.17  Reduction            : 0.03
% 1.95/1.17  Demodulation         : 0.03
% 1.95/1.17  BG Simplification    : 0.01
% 1.95/1.17  Subsumption          : 0.02
% 1.95/1.17  Abstraction          : 0.00
% 1.95/1.17  MUC search           : 0.00
% 1.95/1.17  Cooper               : 0.00
% 1.95/1.17  Total                : 0.41
% 1.95/1.17  Index Insertion      : 0.00
% 1.95/1.17  Index Deletion       : 0.00
% 1.95/1.17  Index Matching       : 0.00
% 1.95/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
