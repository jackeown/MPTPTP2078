%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:13 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   47 (  78 expanded)
%              Number of leaves         :   22 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :   68 ( 153 expanded)
%              Number of equality atoms :   13 (  30 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

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

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v5_tops_1(B,A)
             => k2_tops_1(A,k1_tops_1(A,B)) = k2_tops_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_tops_1)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k2_tops_1(A,k1_tops_1(A,B)),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_tops_1)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k2_tops_1(A,k2_pre_topc(A,B)),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tops_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_14,plain,(
    ! [A_9,B_11] :
      ( r1_tarski(k2_tops_1(A_9,k1_tops_1(A_9,B_11)),k2_tops_1(A_9,B_11))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_37,plain,(
    ! [A_25,B_26] :
      ( k2_pre_topc(A_25,k1_tops_1(A_25,B_26)) = B_26
      | ~ v5_tops_1(B_26,A_25)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_42,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_37])).

tff(c_46,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_42])).

tff(c_51,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(k2_tops_1(A_27,k2_pre_topc(A_27,B_28)),k2_tops_1(A_27,B_28))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_56,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_51])).

tff(c_59,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_56])).

tff(c_70,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_59])).

tff(c_71,plain,(
    ! [A_33,B_34] :
      ( k7_subset_1(u1_struct_0(A_33),B_34,k2_tops_1(A_33,B_34)) = k1_tops_1(A_33,B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_76,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_71])).

tff(c_80,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_76])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5] :
      ( m1_subset_1(k7_subset_1(A_3,B_4,C_5),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_84,plain,
    ( m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_8])).

tff(c_88,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_84])).

tff(c_90,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_88])).

tff(c_91,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_59])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_99,plain,
    ( k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_91,c_2])).

tff(c_102,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_99])).

tff(c_105,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_102])).

tff(c_109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_105])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:29:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.25  
% 1.98/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.25  %$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.98/1.25  
% 1.98/1.25  %Foreground sorts:
% 1.98/1.25  
% 1.98/1.25  
% 1.98/1.25  %Background operators:
% 1.98/1.25  
% 1.98/1.25  
% 1.98/1.25  %Foreground operators:
% 1.98/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.25  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 1.98/1.25  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.98/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.98/1.25  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 1.98/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.25  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 1.98/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.98/1.25  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 1.98/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.98/1.25  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 1.98/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.25  
% 1.98/1.26  tff(f_75, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => (k2_tops_1(A, k1_tops_1(A, B)) = k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_tops_1)).
% 1.98/1.26  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_tops_1(A, k1_tops_1(A, B)), k2_tops_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_tops_1)).
% 1.98/1.26  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tops_1)).
% 1.98/1.26  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_tops_1(A, k2_pre_topc(A, B)), k2_tops_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_tops_1)).
% 1.98/1.26  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 1.98/1.26  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 1.98/1.26  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.98/1.26  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.98/1.26  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.98/1.26  tff(c_14, plain, (![A_9, B_11]: (r1_tarski(k2_tops_1(A_9, k1_tops_1(A_9, B_11)), k2_tops_1(A_9, B_11)) | ~m1_subset_1(B_11, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.98/1.26  tff(c_20, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.98/1.26  tff(c_22, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.98/1.26  tff(c_37, plain, (![A_25, B_26]: (k2_pre_topc(A_25, k1_tops_1(A_25, B_26))=B_26 | ~v5_tops_1(B_26, A_25) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.98/1.26  tff(c_42, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_37])).
% 1.98/1.26  tff(c_46, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_42])).
% 1.98/1.26  tff(c_51, plain, (![A_27, B_28]: (r1_tarski(k2_tops_1(A_27, k2_pre_topc(A_27, B_28)), k2_tops_1(A_27, B_28)) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.98/1.26  tff(c_56, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_46, c_51])).
% 1.98/1.26  tff(c_59, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_56])).
% 1.98/1.26  tff(c_70, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_59])).
% 1.98/1.26  tff(c_71, plain, (![A_33, B_34]: (k7_subset_1(u1_struct_0(A_33), B_34, k2_tops_1(A_33, B_34))=k1_tops_1(A_33, B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.98/1.26  tff(c_76, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_71])).
% 1.98/1.26  tff(c_80, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_76])).
% 1.98/1.26  tff(c_8, plain, (![A_3, B_4, C_5]: (m1_subset_1(k7_subset_1(A_3, B_4, C_5), k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.98/1.26  tff(c_84, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_80, c_8])).
% 1.98/1.26  tff(c_88, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_84])).
% 1.98/1.26  tff(c_90, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_88])).
% 1.98/1.26  tff(c_91, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_59])).
% 1.98/1.26  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.98/1.26  tff(c_99, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_91, c_2])).
% 1.98/1.26  tff(c_102, plain, (~r1_tarski(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_20, c_99])).
% 1.98/1.26  tff(c_105, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_102])).
% 1.98/1.26  tff(c_109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_105])).
% 1.98/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.26  
% 1.98/1.26  Inference rules
% 1.98/1.26  ----------------------
% 1.98/1.26  #Ref     : 0
% 1.98/1.26  #Sup     : 17
% 1.98/1.26  #Fact    : 0
% 1.98/1.26  #Define  : 0
% 1.98/1.26  #Split   : 1
% 1.98/1.26  #Chain   : 0
% 1.98/1.26  #Close   : 0
% 1.98/1.26  
% 1.98/1.26  Ordering : KBO
% 1.98/1.26  
% 1.98/1.26  Simplification rules
% 1.98/1.26  ----------------------
% 1.98/1.26  #Subsume      : 0
% 1.98/1.26  #Demod        : 13
% 1.98/1.26  #Tautology    : 6
% 1.98/1.26  #SimpNegUnit  : 2
% 1.98/1.26  #BackRed      : 0
% 1.98/1.26  
% 1.98/1.26  #Partial instantiations: 0
% 1.98/1.26  #Strategies tried      : 1
% 1.98/1.26  
% 1.98/1.26  Timing (in seconds)
% 1.98/1.26  ----------------------
% 1.98/1.26  Preprocessing        : 0.31
% 1.98/1.26  Parsing              : 0.17
% 1.98/1.26  CNF conversion       : 0.02
% 1.98/1.26  Main loop            : 0.14
% 1.98/1.26  Inferencing          : 0.05
% 1.98/1.26  Reduction            : 0.04
% 1.98/1.26  Demodulation         : 0.03
% 1.98/1.26  BG Simplification    : 0.01
% 1.98/1.26  Subsumption          : 0.03
% 1.98/1.27  Abstraction          : 0.01
% 1.98/1.27  MUC search           : 0.00
% 1.98/1.27  Cooper               : 0.00
% 1.98/1.27  Total                : 0.48
% 1.98/1.27  Index Insertion      : 0.00
% 1.98/1.27  Index Deletion       : 0.00
% 1.98/1.27  Index Matching       : 0.00
% 1.98/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
