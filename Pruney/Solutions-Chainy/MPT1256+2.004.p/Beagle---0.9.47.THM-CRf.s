%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:57 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   48 (  92 expanded)
%              Number of leaves         :   21 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :   67 ( 167 expanded)
%              Number of equality atoms :   15 (  25 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => r1_tarski(k2_tops_1(A,k2_pre_topc(A,B)),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tops_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k2_tops_1(A,k1_tops_1(A,B)),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_tops_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(c_14,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_18,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_77,plain,(
    ! [A_25,B_26] :
      ( k2_tops_1(A_25,k3_subset_1(u1_struct_0(A_25),B_26)) = k2_tops_1(A_25,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_84,plain,
    ( k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_77])).

tff(c_89,plain,(
    k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_84])).

tff(c_94,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(k2_tops_1(A_27,k1_tops_1(A_27,B_28)),k2_tops_1(A_27,B_28))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_97,plain,
    ( r1_tarski(k2_tops_1('#skF_1',k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_94])).

tff(c_99,plain,
    ( r1_tarski(k2_tops_1('#skF_1',k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_97])).

tff(c_171,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_213,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2,c_171])).

tff(c_217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_213])).

tff(c_219,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_20,plain,(
    ! [A_19,B_20] :
      ( k3_subset_1(A_19,k3_subset_1(A_19,B_20)) = B_20
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_16,c_20])).

tff(c_100,plain,(
    ! [A_29,B_30] :
      ( k3_subset_1(u1_struct_0(A_29),k2_pre_topc(A_29,k3_subset_1(u1_struct_0(A_29),B_30))) = k1_tops_1(A_29,B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_125,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_100])).

tff(c_129,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_125])).

tff(c_230,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_129])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k2_pre_topc(A_5,B_6),k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_85,plain,(
    ! [A_5,B_6] :
      ( k2_tops_1(A_5,k3_subset_1(u1_struct_0(A_5),k2_pre_topc(A_5,B_6))) = k2_tops_1(A_5,k2_pre_topc(A_5,B_6))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_77])).

tff(c_234,plain,
    ( k2_tops_1('#skF_1',k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_85])).

tff(c_250,plain,(
    k2_tops_1('#skF_1',k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_234])).

tff(c_218,plain,(
    r1_tarski(k2_tops_1('#skF_1',k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),k2_tops_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_273,plain,(
    r1_tarski(k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_218])).

tff(c_275,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_273])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:45:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.25  
% 2.24/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.26  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.24/1.26  
% 2.24/1.26  %Foreground sorts:
% 2.24/1.26  
% 2.24/1.26  
% 2.24/1.26  %Background operators:
% 2.24/1.26  
% 2.24/1.26  
% 2.24/1.26  %Foreground operators:
% 2.24/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.26  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.24/1.26  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.24/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.24/1.26  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.24/1.26  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.24/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.24/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.24/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.24/1.26  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.24/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.24/1.26  
% 2.24/1.27  tff(f_68, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_tops_1(A, k2_pre_topc(A, B)), k2_tops_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_tops_1)).
% 2.24/1.27  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.24/1.27  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_1)).
% 2.24/1.27  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_tops_1(A, k1_tops_1(A, B)), k2_tops_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_tops_1)).
% 2.24/1.27  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.24/1.27  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 2.24/1.27  tff(f_39, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.24/1.27  tff(c_14, plain, (~r1_tarski(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.24/1.27  tff(c_18, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.24/1.27  tff(c_16, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.24/1.27  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.24/1.27  tff(c_77, plain, (![A_25, B_26]: (k2_tops_1(A_25, k3_subset_1(u1_struct_0(A_25), B_26))=k2_tops_1(A_25, B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.24/1.27  tff(c_84, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_77])).
% 2.24/1.27  tff(c_89, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_84])).
% 2.24/1.27  tff(c_94, plain, (![A_27, B_28]: (r1_tarski(k2_tops_1(A_27, k1_tops_1(A_27, B_28)), k2_tops_1(A_27, B_28)) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.24/1.27  tff(c_97, plain, (r1_tarski(k2_tops_1('#skF_1', k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_89, c_94])).
% 2.24/1.27  tff(c_99, plain, (r1_tarski(k2_tops_1('#skF_1', k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_97])).
% 2.24/1.27  tff(c_171, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_99])).
% 2.24/1.27  tff(c_213, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_2, c_171])).
% 2.24/1.27  tff(c_217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_213])).
% 2.24/1.27  tff(c_219, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_99])).
% 2.24/1.27  tff(c_20, plain, (![A_19, B_20]: (k3_subset_1(A_19, k3_subset_1(A_19, B_20))=B_20 | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.24/1.27  tff(c_26, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_16, c_20])).
% 2.24/1.27  tff(c_100, plain, (![A_29, B_30]: (k3_subset_1(u1_struct_0(A_29), k2_pre_topc(A_29, k3_subset_1(u1_struct_0(A_29), B_30)))=k1_tops_1(A_29, B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.24/1.27  tff(c_125, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_26, c_100])).
% 2.24/1.27  tff(c_129, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_125])).
% 2.24/1.27  tff(c_230, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_219, c_129])).
% 2.24/1.27  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(k2_pre_topc(A_5, B_6), k1_zfmisc_1(u1_struct_0(A_5))) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.24/1.27  tff(c_85, plain, (![A_5, B_6]: (k2_tops_1(A_5, k3_subset_1(u1_struct_0(A_5), k2_pre_topc(A_5, B_6)))=k2_tops_1(A_5, k2_pre_topc(A_5, B_6)) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(resolution, [status(thm)], [c_6, c_77])).
% 2.24/1.27  tff(c_234, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_230, c_85])).
% 2.24/1.27  tff(c_250, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_234])).
% 2.24/1.27  tff(c_218, plain, (r1_tarski(k2_tops_1('#skF_1', k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), k2_tops_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_99])).
% 2.24/1.27  tff(c_273, plain, (r1_tarski(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_250, c_218])).
% 2.24/1.27  tff(c_275, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_273])).
% 2.24/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.27  
% 2.24/1.27  Inference rules
% 2.24/1.27  ----------------------
% 2.24/1.27  #Ref     : 0
% 2.24/1.27  #Sup     : 65
% 2.24/1.27  #Fact    : 0
% 2.24/1.27  #Define  : 0
% 2.24/1.27  #Split   : 1
% 2.24/1.27  #Chain   : 0
% 2.24/1.27  #Close   : 0
% 2.24/1.27  
% 2.24/1.27  Ordering : KBO
% 2.24/1.27  
% 2.24/1.27  Simplification rules
% 2.24/1.27  ----------------------
% 2.24/1.27  #Subsume      : 6
% 2.24/1.27  #Demod        : 28
% 2.24/1.27  #Tautology    : 32
% 2.24/1.27  #SimpNegUnit  : 1
% 2.24/1.27  #BackRed      : 1
% 2.24/1.27  
% 2.24/1.27  #Partial instantiations: 0
% 2.24/1.27  #Strategies tried      : 1
% 2.24/1.27  
% 2.24/1.27  Timing (in seconds)
% 2.24/1.27  ----------------------
% 2.24/1.27  Preprocessing        : 0.28
% 2.24/1.27  Parsing              : 0.16
% 2.24/1.27  CNF conversion       : 0.02
% 2.24/1.27  Main loop            : 0.23
% 2.24/1.27  Inferencing          : 0.09
% 2.24/1.27  Reduction            : 0.07
% 2.24/1.27  Demodulation         : 0.05
% 2.24/1.27  BG Simplification    : 0.01
% 2.24/1.27  Subsumption          : 0.05
% 2.24/1.27  Abstraction          : 0.01
% 2.24/1.27  MUC search           : 0.00
% 2.24/1.27  Cooper               : 0.00
% 2.24/1.27  Total                : 0.54
% 2.24/1.27  Index Insertion      : 0.00
% 2.24/1.27  Index Deletion       : 0.00
% 2.24/1.27  Index Matching       : 0.00
% 2.24/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
