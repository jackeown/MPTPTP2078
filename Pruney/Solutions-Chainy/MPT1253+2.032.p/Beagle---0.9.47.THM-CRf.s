%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:56 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   48 (  59 expanded)
%              Number of leaves         :   26 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   64 (  96 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(c_18,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k3_subset_1(A_5,B_6),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_132,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1(k2_pre_topc(A_37,B_38),k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] :
      ( k9_subset_1(A_7,B_8,C_9) = k3_xboole_0(B_8,C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_326,plain,(
    ! [A_53,B_54,B_55] :
      ( k9_subset_1(u1_struct_0(A_53),B_54,k2_pre_topc(A_53,B_55)) = k3_xboole_0(B_54,k2_pre_topc(A_53,B_55))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(resolution,[status(thm)],[c_132,c_8])).

tff(c_624,plain,(
    ! [A_79,B_80,B_81] :
      ( k9_subset_1(u1_struct_0(A_79),B_80,k2_pre_topc(A_79,k3_subset_1(u1_struct_0(A_79),B_81))) = k3_xboole_0(B_80,k2_pre_topc(A_79,k3_subset_1(u1_struct_0(A_79),B_81)))
      | ~ l1_pre_topc(A_79)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_79))) ) ),
    inference(resolution,[status(thm)],[c_6,c_326])).

tff(c_20,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_116,plain,(
    ! [A_35,B_36] :
      ( k2_pre_topc(A_35,B_36) = B_36
      | ~ v4_pre_topc(B_36,A_35)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_123,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_116])).

tff(c_127,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_123])).

tff(c_306,plain,(
    ! [A_51,B_52] :
      ( k9_subset_1(u1_struct_0(A_51),k2_pre_topc(A_51,B_52),k2_pre_topc(A_51,k3_subset_1(u1_struct_0(A_51),B_52))) = k2_tops_1(A_51,B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_315,plain,
    ( k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_306])).

tff(c_319,plain,(
    k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_315])).

tff(c_630,plain,
    ( k3_xboole_0('#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_624,c_319])).

tff(c_646,plain,(
    k3_xboole_0('#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_630])).

tff(c_26,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_35,plain,(
    ! [A_21,B_22] : r1_tarski(k3_xboole_0(A_21,B_22),A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2])).

tff(c_665,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_646,c_35])).

tff(c_672,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_665])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:49:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.44  
% 2.86/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.45  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.90/1.45  
% 2.90/1.45  %Foreground sorts:
% 2.90/1.45  
% 2.90/1.45  
% 2.90/1.45  %Background operators:
% 2.90/1.45  
% 2.90/1.45  
% 2.90/1.45  %Foreground operators:
% 2.90/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.90/1.45  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.90/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.90/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.90/1.45  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.90/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.90/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.90/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.90/1.45  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.90/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.90/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.90/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.90/1.45  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.90/1.45  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.90/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.90/1.45  
% 2.90/1.46  tff(f_75, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 2.90/1.46  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.90/1.46  tff(f_43, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.90/1.46  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.90/1.46  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.90/1.46  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_1)).
% 2.90/1.46  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.90/1.46  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.90/1.46  tff(c_18, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.90/1.46  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.90/1.46  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.90/1.46  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(k3_subset_1(A_5, B_6), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.90/1.46  tff(c_132, plain, (![A_37, B_38]: (m1_subset_1(k2_pre_topc(A_37, B_38), k1_zfmisc_1(u1_struct_0(A_37))) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_37))) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.90/1.46  tff(c_8, plain, (![A_7, B_8, C_9]: (k9_subset_1(A_7, B_8, C_9)=k3_xboole_0(B_8, C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.90/1.46  tff(c_326, plain, (![A_53, B_54, B_55]: (k9_subset_1(u1_struct_0(A_53), B_54, k2_pre_topc(A_53, B_55))=k3_xboole_0(B_54, k2_pre_topc(A_53, B_55)) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53))), inference(resolution, [status(thm)], [c_132, c_8])).
% 2.90/1.46  tff(c_624, plain, (![A_79, B_80, B_81]: (k9_subset_1(u1_struct_0(A_79), B_80, k2_pre_topc(A_79, k3_subset_1(u1_struct_0(A_79), B_81)))=k3_xboole_0(B_80, k2_pre_topc(A_79, k3_subset_1(u1_struct_0(A_79), B_81))) | ~l1_pre_topc(A_79) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_79))))), inference(resolution, [status(thm)], [c_6, c_326])).
% 2.90/1.46  tff(c_20, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.90/1.46  tff(c_116, plain, (![A_35, B_36]: (k2_pre_topc(A_35, B_36)=B_36 | ~v4_pre_topc(B_36, A_35) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.90/1.46  tff(c_123, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_116])).
% 2.90/1.46  tff(c_127, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_123])).
% 2.90/1.46  tff(c_306, plain, (![A_51, B_52]: (k9_subset_1(u1_struct_0(A_51), k2_pre_topc(A_51, B_52), k2_pre_topc(A_51, k3_subset_1(u1_struct_0(A_51), B_52)))=k2_tops_1(A_51, B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.90/1.46  tff(c_315, plain, (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_127, c_306])).
% 2.90/1.46  tff(c_319, plain, (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_315])).
% 2.90/1.46  tff(c_630, plain, (k3_xboole_0('#skF_2', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_624, c_319])).
% 2.90/1.46  tff(c_646, plain, (k3_xboole_0('#skF_2', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_630])).
% 2.90/1.46  tff(c_26, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.90/1.46  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.90/1.46  tff(c_35, plain, (![A_21, B_22]: (r1_tarski(k3_xboole_0(A_21, B_22), A_21))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2])).
% 2.90/1.46  tff(c_665, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_646, c_35])).
% 2.90/1.46  tff(c_672, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_665])).
% 2.90/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.46  
% 2.90/1.46  Inference rules
% 2.90/1.46  ----------------------
% 2.90/1.46  #Ref     : 0
% 2.90/1.46  #Sup     : 162
% 2.90/1.46  #Fact    : 0
% 2.90/1.46  #Define  : 0
% 2.90/1.46  #Split   : 0
% 2.90/1.46  #Chain   : 0
% 2.90/1.46  #Close   : 0
% 2.90/1.46  
% 2.90/1.46  Ordering : KBO
% 2.90/1.46  
% 2.90/1.46  Simplification rules
% 2.90/1.46  ----------------------
% 2.90/1.46  #Subsume      : 0
% 2.90/1.46  #Demod        : 124
% 2.90/1.46  #Tautology    : 99
% 2.90/1.46  #SimpNegUnit  : 1
% 2.90/1.46  #BackRed      : 0
% 2.90/1.46  
% 2.90/1.46  #Partial instantiations: 0
% 2.90/1.46  #Strategies tried      : 1
% 2.90/1.46  
% 2.90/1.46  Timing (in seconds)
% 2.90/1.46  ----------------------
% 2.90/1.46  Preprocessing        : 0.28
% 2.90/1.46  Parsing              : 0.15
% 2.90/1.46  CNF conversion       : 0.02
% 2.90/1.46  Main loop            : 0.34
% 2.90/1.46  Inferencing          : 0.14
% 2.90/1.46  Reduction            : 0.12
% 2.90/1.46  Demodulation         : 0.09
% 2.90/1.46  BG Simplification    : 0.02
% 2.90/1.46  Subsumption          : 0.05
% 2.90/1.46  Abstraction          : 0.02
% 2.90/1.46  MUC search           : 0.00
% 2.90/1.46  Cooper               : 0.00
% 2.90/1.46  Total                : 0.65
% 2.90/1.46  Index Insertion      : 0.00
% 2.90/1.46  Index Deletion       : 0.00
% 2.90/1.46  Index Matching       : 0.00
% 2.90/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
