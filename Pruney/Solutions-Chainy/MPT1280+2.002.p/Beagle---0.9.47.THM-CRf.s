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
% DateTime   : Thu Dec  3 10:22:13 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   41 (  70 expanded)
%              Number of leaves         :   20 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   60 ( 140 expanded)
%              Number of equality atoms :    9 (  25 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v5_tops_1,type,(
    v5_tops_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v5_tops_1(B,A)
             => k2_tops_1(A,k1_tops_1(A,B)) = k2_tops_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_tops_1)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k2_tops_1(A,k1_tops_1(A,B)),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_tops_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k2_tops_1(A,k2_pre_topc(A,B)),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14,plain,(
    ! [A_8,B_10] :
      ( r1_tarski(k2_tops_1(A_8,k1_tops_1(A_8,B_10)),k2_tops_1(A_8,B_10))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k1_tops_1(A_6,B_7),k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_20,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_39,plain,(
    ! [A_22,B_23] :
      ( k2_pre_topc(A_22,k1_tops_1(A_22,B_23)) = B_23
      | ~ v5_tops_1(B_23,A_22)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_43,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_39])).

tff(c_47,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_43])).

tff(c_58,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(k2_tops_1(A_26,k2_pre_topc(A_26,B_27)),k2_tops_1(A_26,B_27))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_63,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_58])).

tff(c_66,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_63])).

tff(c_67,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_70,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_67])).

tff(c_74,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_70])).

tff(c_75,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_97,plain,
    ( k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_75,c_2])).

tff(c_100,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_97])).

tff(c_103,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_100])).

tff(c_107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_103])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 15:07:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.26  
% 1.91/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.26  %$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.91/1.26  
% 1.91/1.26  %Foreground sorts:
% 1.91/1.26  
% 1.91/1.26  
% 1.91/1.26  %Background operators:
% 1.91/1.26  
% 1.91/1.26  
% 1.91/1.26  %Foreground operators:
% 1.91/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.26  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 1.91/1.26  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.91/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.26  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 1.91/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.91/1.26  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.91/1.26  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 1.91/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.91/1.26  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 1.91/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.91/1.26  
% 1.91/1.27  tff(f_70, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => (k2_tops_1(A, k1_tops_1(A, B)) = k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_tops_1)).
% 1.91/1.27  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_tops_1(A, k1_tops_1(A, B)), k2_tops_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_tops_1)).
% 1.91/1.27  tff(f_46, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 1.91/1.27  tff(f_40, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tops_1)).
% 1.91/1.27  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_tops_1(A, k2_pre_topc(A, B)), k2_tops_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_tops_1)).
% 1.91/1.27  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.91/1.27  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.91/1.27  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.91/1.27  tff(c_14, plain, (![A_8, B_10]: (r1_tarski(k2_tops_1(A_8, k1_tops_1(A_8, B_10)), k2_tops_1(A_8, B_10)) | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.91/1.27  tff(c_18, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.91/1.27  tff(c_12, plain, (![A_6, B_7]: (m1_subset_1(k1_tops_1(A_6, B_7), k1_zfmisc_1(u1_struct_0(A_6))) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.91/1.27  tff(c_20, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.91/1.27  tff(c_39, plain, (![A_22, B_23]: (k2_pre_topc(A_22, k1_tops_1(A_22, B_23))=B_23 | ~v5_tops_1(B_23, A_22) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.91/1.27  tff(c_43, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_39])).
% 1.91/1.27  tff(c_47, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_43])).
% 1.91/1.27  tff(c_58, plain, (![A_26, B_27]: (r1_tarski(k2_tops_1(A_26, k2_pre_topc(A_26, B_27)), k2_tops_1(A_26, B_27)) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.91/1.27  tff(c_63, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_47, c_58])).
% 1.91/1.27  tff(c_66, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_63])).
% 1.91/1.27  tff(c_67, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_66])).
% 1.91/1.27  tff(c_70, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_67])).
% 1.91/1.27  tff(c_74, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_70])).
% 1.91/1.27  tff(c_75, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_66])).
% 1.91/1.27  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.91/1.27  tff(c_97, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_75, c_2])).
% 1.91/1.27  tff(c_100, plain, (~r1_tarski(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_18, c_97])).
% 1.91/1.27  tff(c_103, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_100])).
% 1.91/1.27  tff(c_107, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_103])).
% 1.91/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.27  
% 1.91/1.27  Inference rules
% 1.91/1.27  ----------------------
% 1.91/1.27  #Ref     : 0
% 1.91/1.27  #Sup     : 16
% 1.91/1.27  #Fact    : 0
% 1.91/1.27  #Define  : 0
% 1.91/1.27  #Split   : 1
% 1.91/1.27  #Chain   : 0
% 1.91/1.27  #Close   : 0
% 1.91/1.27  
% 1.91/1.27  Ordering : KBO
% 1.91/1.27  
% 1.91/1.27  Simplification rules
% 1.91/1.27  ----------------------
% 1.91/1.27  #Subsume      : 0
% 1.91/1.27  #Demod        : 15
% 1.91/1.27  #Tautology    : 5
% 1.91/1.27  #SimpNegUnit  : 1
% 1.91/1.27  #BackRed      : 0
% 1.91/1.27  
% 1.91/1.27  #Partial instantiations: 0
% 1.91/1.27  #Strategies tried      : 1
% 1.91/1.27  
% 1.91/1.27  Timing (in seconds)
% 1.91/1.27  ----------------------
% 1.91/1.28  Preprocessing        : 0.31
% 1.91/1.28  Parsing              : 0.17
% 1.91/1.28  CNF conversion       : 0.02
% 1.91/1.28  Main loop            : 0.13
% 1.91/1.28  Inferencing          : 0.05
% 1.91/1.28  Reduction            : 0.04
% 1.91/1.28  Demodulation         : 0.03
% 1.91/1.28  BG Simplification    : 0.01
% 1.91/1.28  Subsumption          : 0.03
% 1.91/1.28  Abstraction          : 0.01
% 1.91/1.28  MUC search           : 0.00
% 2.07/1.28  Cooper               : 0.00
% 2.07/1.28  Total                : 0.47
% 2.07/1.28  Index Insertion      : 0.00
% 2.07/1.28  Index Deletion       : 0.00
% 2.07/1.28  Index Matching       : 0.00
% 2.07/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
