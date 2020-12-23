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
% DateTime   : Thu Dec  3 10:25:39 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   45 (  77 expanded)
%              Number of leaves         :   20 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :   54 ( 139 expanded)
%              Number of equality atoms :    3 (  18 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_2 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > u1_orders_2 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ( v1_tops_2(B,A)
            <=> m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_yellow_1)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> r1_tarski(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_6] : u1_struct_0(k2_yellow_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_1')))))
    | ~ v1_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_27,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_pre_topc('#skF_1')))
    | ~ v1_tops_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_20])).

tff(c_57,plain,(
    ~ v1_tops_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_27])).

tff(c_16,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_26,plain,
    ( v1_tops_2('#skF_2','#skF_1')
    | m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_1'))))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_28,plain,
    ( v1_tops_2('#skF_2','#skF_1')
    | m1_subset_1('#skF_2',k1_zfmisc_1(u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_26])).

tff(c_58,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_62,plain,(
    r1_tarski('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(resolution,[status(thm)],[c_58,c_2])).

tff(c_14,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_88,plain,(
    ! [B_18,A_19] :
      ( v1_tops_2(B_18,A_19)
      | ~ r1_tarski(B_18,u1_pre_topc(A_19))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_19))))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_95,plain,
    ( v1_tops_2('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2',u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_88])).

tff(c_102,plain,(
    v1_tops_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_62,c_95])).

tff(c_104,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_102])).

tff(c_105,plain,(
    v1_tops_2('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_105])).

tff(c_108,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_27])).

tff(c_114,plain,(
    ~ r1_tarski('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(resolution,[status(thm)],[c_4,c_108])).

tff(c_109,plain,(
    v1_tops_2('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_27])).

tff(c_115,plain,(
    ! [B_20,A_21] :
      ( r1_tarski(B_20,u1_pre_topc(A_21))
      | ~ v1_tops_2(B_20,A_21)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_21))))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_122,plain,
    ( r1_tarski('#skF_2',u1_pre_topc('#skF_1'))
    | ~ v1_tops_2('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_115])).

tff(c_129,plain,(
    r1_tarski('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_109,c_122])).

tff(c_131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_129])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n017.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 19:47:01 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.22  
% 1.88/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.22  %$ v1_tops_2 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > u1_orders_2 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > #skF_2 > #skF_1
% 1.88/1.22  
% 1.88/1.22  %Foreground sorts:
% 1.88/1.22  
% 1.88/1.22  
% 1.88/1.22  %Background operators:
% 1.88/1.22  
% 1.88/1.22  
% 1.88/1.22  %Foreground operators:
% 1.88/1.22  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 1.88/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.22  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 1.88/1.22  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 1.88/1.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.88/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.88/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.22  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 1.88/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.22  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.88/1.22  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 1.88/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.88/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.88/1.22  
% 1.88/1.23  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.88/1.23  tff(f_42, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 1.88/1.23  tff(f_54, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_yellow_1)).
% 1.88/1.23  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> r1_tarski(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_tops_2)).
% 1.88/1.23  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.88/1.23  tff(c_10, plain, (![A_6]: (u1_struct_0(k2_yellow_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.88/1.23  tff(c_20, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_1'))))) | ~v1_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.88/1.23  tff(c_27, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_pre_topc('#skF_1'))) | ~v1_tops_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_20])).
% 1.88/1.23  tff(c_57, plain, (~v1_tops_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_27])).
% 1.88/1.23  tff(c_16, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.88/1.23  tff(c_26, plain, (v1_tops_2('#skF_2', '#skF_1') | m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc('#skF_1')))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.88/1.23  tff(c_28, plain, (v1_tops_2('#skF_2', '#skF_1') | m1_subset_1('#skF_2', k1_zfmisc_1(u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_26])).
% 1.88/1.23  tff(c_58, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_28])).
% 1.88/1.23  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.88/1.23  tff(c_62, plain, (r1_tarski('#skF_2', u1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_58, c_2])).
% 1.88/1.23  tff(c_14, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.88/1.23  tff(c_88, plain, (![B_18, A_19]: (v1_tops_2(B_18, A_19) | ~r1_tarski(B_18, u1_pre_topc(A_19)) | ~m1_subset_1(B_18, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_19)))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.88/1.23  tff(c_95, plain, (v1_tops_2('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_88])).
% 1.88/1.23  tff(c_102, plain, (v1_tops_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_62, c_95])).
% 1.88/1.23  tff(c_104, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_102])).
% 1.88/1.23  tff(c_105, plain, (v1_tops_2('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_28])).
% 1.88/1.23  tff(c_107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_105])).
% 1.88/1.23  tff(c_108, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_27])).
% 1.88/1.23  tff(c_114, plain, (~r1_tarski('#skF_2', u1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_4, c_108])).
% 1.88/1.23  tff(c_109, plain, (v1_tops_2('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_27])).
% 1.88/1.23  tff(c_115, plain, (![B_20, A_21]: (r1_tarski(B_20, u1_pre_topc(A_21)) | ~v1_tops_2(B_20, A_21) | ~m1_subset_1(B_20, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_21)))) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.88/1.23  tff(c_122, plain, (r1_tarski('#skF_2', u1_pre_topc('#skF_1')) | ~v1_tops_2('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_115])).
% 1.88/1.23  tff(c_129, plain, (r1_tarski('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_109, c_122])).
% 1.88/1.23  tff(c_131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_129])).
% 1.88/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.23  
% 1.88/1.23  Inference rules
% 1.88/1.23  ----------------------
% 1.88/1.23  #Ref     : 0
% 1.88/1.23  #Sup     : 19
% 1.88/1.23  #Fact    : 0
% 1.88/1.23  #Define  : 0
% 1.88/1.23  #Split   : 2
% 1.88/1.23  #Chain   : 0
% 1.88/1.23  #Close   : 0
% 1.88/1.23  
% 1.88/1.23  Ordering : KBO
% 1.88/1.23  
% 1.88/1.23  Simplification rules
% 1.88/1.23  ----------------------
% 1.88/1.23  #Subsume      : 2
% 1.88/1.23  #Demod        : 11
% 1.88/1.23  #Tautology    : 8
% 1.88/1.23  #SimpNegUnit  : 3
% 1.88/1.23  #BackRed      : 0
% 1.88/1.23  
% 1.88/1.23  #Partial instantiations: 0
% 1.88/1.23  #Strategies tried      : 1
% 1.88/1.23  
% 1.88/1.23  Timing (in seconds)
% 1.88/1.23  ----------------------
% 1.88/1.23  Preprocessing        : 0.29
% 1.88/1.23  Parsing              : 0.16
% 1.88/1.23  CNF conversion       : 0.02
% 1.88/1.23  Main loop            : 0.13
% 1.88/1.23  Inferencing          : 0.05
% 1.88/1.23  Reduction            : 0.04
% 1.88/1.23  Demodulation         : 0.03
% 1.88/1.23  BG Simplification    : 0.01
% 1.88/1.23  Subsumption          : 0.02
% 1.88/1.23  Abstraction          : 0.01
% 1.88/1.23  MUC search           : 0.00
% 1.88/1.23  Cooper               : 0.00
% 1.88/1.23  Total                : 0.45
% 1.88/1.23  Index Insertion      : 0.00
% 1.88/1.23  Index Deletion       : 0.00
% 1.88/1.23  Index Matching       : 0.00
% 1.88/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
