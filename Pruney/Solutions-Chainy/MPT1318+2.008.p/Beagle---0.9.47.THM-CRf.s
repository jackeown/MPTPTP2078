%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:05 EST 2020

% Result     : Theorem 3.88s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :   46 (  63 expanded)
%              Number of leaves         :   21 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   64 ( 109 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_subset_1 > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => m1_subset_1(k9_subset_1(u1_struct_0(A),B,C),k1_zfmisc_1(u1_struct_0(k1_pre_topc(A,C)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_tops_2)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_49,plain,(
    ! [A_34,C_35,B_36] :
      ( k9_subset_1(A_34,C_35,B_36) = k9_subset_1(A_34,B_36,C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_158,plain,(
    ! [B_43] : k9_subset_1(u1_struct_0('#skF_1'),B_43,'#skF_2') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_43) ),
    inference(resolution,[status(thm)],[c_22,c_49])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6] :
      ( m1_subset_1(k9_subset_1(A_4,B_5,C_6),k1_zfmisc_1(A_4))
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_184,plain,(
    ! [B_43] :
      ( m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_43),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_4])).

tff(c_202,plain,(
    ! [B_43] : m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_43),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_184])).

tff(c_61,plain,(
    ! [B_36] : k9_subset_1(u1_struct_0('#skF_1'),B_36,'#skF_2') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_36) ),
    inference(resolution,[status(thm)],[c_22,c_49])).

tff(c_708,plain,(
    ! [A_68,B_69,C_70] :
      ( r1_tarski(k3_subset_1(A_68,B_69),k3_subset_1(A_68,k9_subset_1(A_68,B_69,C_70)))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(A_68))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [B_8,C_10,A_7] :
      ( r1_tarski(B_8,C_10)
      | ~ r1_tarski(k3_subset_1(A_7,C_10),k3_subset_1(A_7,B_8))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1655,plain,(
    ! [A_99,B_100,C_101] :
      ( r1_tarski(k9_subset_1(A_99,B_100,C_101),B_100)
      | ~ m1_subset_1(k9_subset_1(A_99,B_100,C_101),k1_zfmisc_1(A_99))
      | ~ m1_subset_1(C_101,k1_zfmisc_1(A_99))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_99)) ) ),
    inference(resolution,[status(thm)],[c_708,c_6])).

tff(c_1675,plain,(
    ! [B_36] :
      ( r1_tarski(k9_subset_1(u1_struct_0('#skF_1'),B_36,'#skF_2'),B_36)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_36),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_1655])).

tff(c_1714,plain,(
    ! [B_102] :
      ( r1_tarski(k9_subset_1(u1_struct_0('#skF_1'),B_102,'#skF_2'),B_102)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_202,c_1675])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_104,plain,(
    ! [A_40,B_41] :
      ( u1_struct_0(k1_pre_topc(A_40,B_41)) = B_41
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_115,plain,
    ( u1_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_104])).

tff(c_123,plain,(
    u1_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_115])).

tff(c_60,plain,(
    ! [B_36] : k9_subset_1(u1_struct_0('#skF_1'),B_36,'#skF_3') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_36) ),
    inference(resolution,[status(thm)],[c_20,c_49])).

tff(c_14,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    ~ m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_48,plain,(
    ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),u1_struct_0(k1_pre_topc('#skF_1','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_14,c_18])).

tff(c_62,plain,(
    ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2'),u1_struct_0(k1_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_48])).

tff(c_282,plain,(
    ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_62])).

tff(c_1723,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1714,c_282])).

tff(c_1741,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1723])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:51:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.88/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.88/1.63  
% 3.88/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.88/1.64  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_subset_1 > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.88/1.64  
% 3.88/1.64  %Foreground sorts:
% 3.88/1.64  
% 3.88/1.64  
% 3.88/1.64  %Background operators:
% 3.88/1.64  
% 3.88/1.64  
% 3.88/1.64  %Foreground operators:
% 3.88/1.64  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 3.88/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.88/1.64  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.88/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.88/1.64  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.88/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.88/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.88/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.88/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.88/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.88/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.88/1.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.88/1.64  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.88/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.88/1.64  
% 3.88/1.65  tff(f_71, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => m1_subset_1(k9_subset_1(u1_struct_0(A), B, C), k1_zfmisc_1(u1_struct_0(k1_pre_topc(A, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_tops_2)).
% 3.88/1.65  tff(f_29, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 3.88/1.65  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 3.88/1.65  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_subset_1)).
% 3.88/1.65  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 3.88/1.65  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_pre_topc)).
% 3.88/1.65  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.88/1.65  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.88/1.65  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.88/1.65  tff(c_49, plain, (![A_34, C_35, B_36]: (k9_subset_1(A_34, C_35, B_36)=k9_subset_1(A_34, B_36, C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.88/1.65  tff(c_158, plain, (![B_43]: (k9_subset_1(u1_struct_0('#skF_1'), B_43, '#skF_2')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_43))), inference(resolution, [status(thm)], [c_22, c_49])).
% 3.88/1.65  tff(c_4, plain, (![A_4, B_5, C_6]: (m1_subset_1(k9_subset_1(A_4, B_5, C_6), k1_zfmisc_1(A_4)) | ~m1_subset_1(C_6, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.88/1.65  tff(c_184, plain, (![B_43]: (m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_43), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_158, c_4])).
% 3.88/1.65  tff(c_202, plain, (![B_43]: (m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_43), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_184])).
% 3.88/1.65  tff(c_61, plain, (![B_36]: (k9_subset_1(u1_struct_0('#skF_1'), B_36, '#skF_2')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_36))), inference(resolution, [status(thm)], [c_22, c_49])).
% 3.88/1.65  tff(c_708, plain, (![A_68, B_69, C_70]: (r1_tarski(k3_subset_1(A_68, B_69), k3_subset_1(A_68, k9_subset_1(A_68, B_69, C_70))) | ~m1_subset_1(C_70, k1_zfmisc_1(A_68)) | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.88/1.65  tff(c_6, plain, (![B_8, C_10, A_7]: (r1_tarski(B_8, C_10) | ~r1_tarski(k3_subset_1(A_7, C_10), k3_subset_1(A_7, B_8)) | ~m1_subset_1(C_10, k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.88/1.65  tff(c_1655, plain, (![A_99, B_100, C_101]: (r1_tarski(k9_subset_1(A_99, B_100, C_101), B_100) | ~m1_subset_1(k9_subset_1(A_99, B_100, C_101), k1_zfmisc_1(A_99)) | ~m1_subset_1(C_101, k1_zfmisc_1(A_99)) | ~m1_subset_1(B_100, k1_zfmisc_1(A_99)))), inference(resolution, [status(thm)], [c_708, c_6])).
% 3.88/1.65  tff(c_1675, plain, (![B_36]: (r1_tarski(k9_subset_1(u1_struct_0('#skF_1'), B_36, '#skF_2'), B_36) | ~m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_36), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_61, c_1655])).
% 3.88/1.65  tff(c_1714, plain, (![B_102]: (r1_tarski(k9_subset_1(u1_struct_0('#skF_1'), B_102, '#skF_2'), B_102) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_202, c_1675])).
% 3.88/1.65  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.88/1.65  tff(c_104, plain, (![A_40, B_41]: (u1_struct_0(k1_pre_topc(A_40, B_41))=B_41 | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.88/1.65  tff(c_115, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_104])).
% 3.88/1.65  tff(c_123, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_115])).
% 3.88/1.65  tff(c_60, plain, (![B_36]: (k9_subset_1(u1_struct_0('#skF_1'), B_36, '#skF_3')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_36))), inference(resolution, [status(thm)], [c_20, c_49])).
% 3.88/1.65  tff(c_14, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.88/1.65  tff(c_18, plain, (~m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.88/1.65  tff(c_48, plain, (~r1_tarski(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_14, c_18])).
% 3.88/1.65  tff(c_62, plain, (~r1_tarski(k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_2'), u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_48])).
% 3.88/1.65  tff(c_282, plain, (~r1_tarski(k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_62])).
% 3.88/1.65  tff(c_1723, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1714, c_282])).
% 3.88/1.65  tff(c_1741, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_1723])).
% 3.88/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.88/1.65  
% 3.88/1.65  Inference rules
% 3.88/1.65  ----------------------
% 3.88/1.65  #Ref     : 0
% 3.88/1.65  #Sup     : 397
% 3.88/1.65  #Fact    : 0
% 3.88/1.65  #Define  : 0
% 3.88/1.65  #Split   : 2
% 3.88/1.65  #Chain   : 0
% 3.88/1.65  #Close   : 0
% 3.88/1.65  
% 3.88/1.65  Ordering : KBO
% 3.88/1.65  
% 3.88/1.65  Simplification rules
% 3.88/1.65  ----------------------
% 3.88/1.65  #Subsume      : 49
% 3.88/1.65  #Demod        : 222
% 3.88/1.65  #Tautology    : 154
% 3.88/1.65  #SimpNegUnit  : 0
% 3.88/1.65  #BackRed      : 2
% 3.88/1.65  
% 3.88/1.65  #Partial instantiations: 0
% 3.88/1.65  #Strategies tried      : 1
% 3.88/1.65  
% 3.88/1.65  Timing (in seconds)
% 3.88/1.65  ----------------------
% 3.88/1.65  Preprocessing        : 0.29
% 3.88/1.65  Parsing              : 0.17
% 3.88/1.65  CNF conversion       : 0.02
% 3.88/1.65  Main loop            : 0.60
% 3.88/1.65  Inferencing          : 0.21
% 3.88/1.65  Reduction            : 0.24
% 3.88/1.65  Demodulation         : 0.19
% 3.88/1.65  BG Simplification    : 0.03
% 3.88/1.65  Subsumption          : 0.09
% 3.88/1.65  Abstraction          : 0.04
% 3.88/1.65  MUC search           : 0.00
% 3.88/1.65  Cooper               : 0.00
% 3.88/1.65  Total                : 0.92
% 3.88/1.65  Index Insertion      : 0.00
% 3.88/1.65  Index Deletion       : 0.00
% 3.88/1.65  Index Matching       : 0.00
% 3.88/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
