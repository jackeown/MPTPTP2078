%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:56 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   44 (  55 expanded)
%              Number of leaves         :   24 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   61 (  93 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(f_73,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_56,axiom,(
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

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_16,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k3_subset_1(A_3,B_4),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(k2_pre_topc(A_27,B_28),k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( k9_subset_1(A_5,B_6,C_7) = k3_xboole_0(B_6,C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_105,plain,(
    ! [A_35,B_36,B_37] :
      ( k9_subset_1(u1_struct_0(A_35),B_36,k2_pre_topc(A_35,B_37)) = k3_xboole_0(B_36,k2_pre_topc(A_35,B_37))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(resolution,[status(thm)],[c_57,c_6])).

tff(c_183,plain,(
    ! [A_54,B_55,B_56] :
      ( k9_subset_1(u1_struct_0(A_54),B_55,k2_pre_topc(A_54,k3_subset_1(u1_struct_0(A_54),B_56))) = k3_xboole_0(B_55,k2_pre_topc(A_54,k3_subset_1(u1_struct_0(A_54),B_56)))
      | ~ l1_pre_topc(A_54)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_54))) ) ),
    inference(resolution,[status(thm)],[c_4,c_105])).

tff(c_18,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_41,plain,(
    ! [A_25,B_26] :
      ( k2_pre_topc(A_25,B_26) = B_26
      | ~ v4_pre_topc(B_26,A_25)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_48,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_41])).

tff(c_52,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_48])).

tff(c_118,plain,(
    ! [A_38,B_39] :
      ( k9_subset_1(u1_struct_0(A_38),k2_pre_topc(A_38,B_39),k2_pre_topc(A_38,k3_subset_1(u1_struct_0(A_38),B_39))) = k2_tops_1(A_38,B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_127,plain,
    ( k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_118])).

tff(c_131,plain,(
    k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_127])).

tff(c_189,plain,
    ( k3_xboole_0('#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_131])).

tff(c_205,plain,(
    k3_xboole_0('#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22,c_189])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_212,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_2])).

tff(c_216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_212])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:15:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.22  
% 2.00/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.22  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.00/1.22  
% 2.00/1.22  %Foreground sorts:
% 2.00/1.22  
% 2.00/1.22  
% 2.00/1.22  %Background operators:
% 2.00/1.22  
% 2.00/1.22  
% 2.00/1.22  %Foreground operators:
% 2.00/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.22  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.00/1.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.00/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.00/1.22  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.00/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.00/1.22  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.00/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.22  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.00/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.00/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.00/1.22  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.00/1.22  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.00/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.00/1.22  
% 2.14/1.24  tff(f_73, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 2.14/1.24  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.14/1.24  tff(f_41, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.14/1.24  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.14/1.24  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.14/1.24  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_1)).
% 2.14/1.24  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.14/1.24  tff(c_16, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.14/1.24  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.14/1.24  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.14/1.24  tff(c_4, plain, (![A_3, B_4]: (m1_subset_1(k3_subset_1(A_3, B_4), k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.14/1.24  tff(c_57, plain, (![A_27, B_28]: (m1_subset_1(k2_pre_topc(A_27, B_28), k1_zfmisc_1(u1_struct_0(A_27))) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.14/1.24  tff(c_6, plain, (![A_5, B_6, C_7]: (k9_subset_1(A_5, B_6, C_7)=k3_xboole_0(B_6, C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.14/1.24  tff(c_105, plain, (![A_35, B_36, B_37]: (k9_subset_1(u1_struct_0(A_35), B_36, k2_pre_topc(A_35, B_37))=k3_xboole_0(B_36, k2_pre_topc(A_35, B_37)) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35))), inference(resolution, [status(thm)], [c_57, c_6])).
% 2.14/1.24  tff(c_183, plain, (![A_54, B_55, B_56]: (k9_subset_1(u1_struct_0(A_54), B_55, k2_pre_topc(A_54, k3_subset_1(u1_struct_0(A_54), B_56)))=k3_xboole_0(B_55, k2_pre_topc(A_54, k3_subset_1(u1_struct_0(A_54), B_56))) | ~l1_pre_topc(A_54) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_54))))), inference(resolution, [status(thm)], [c_4, c_105])).
% 2.14/1.24  tff(c_18, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.14/1.24  tff(c_41, plain, (![A_25, B_26]: (k2_pre_topc(A_25, B_26)=B_26 | ~v4_pre_topc(B_26, A_25) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.14/1.24  tff(c_48, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_41])).
% 2.14/1.24  tff(c_52, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_48])).
% 2.14/1.24  tff(c_118, plain, (![A_38, B_39]: (k9_subset_1(u1_struct_0(A_38), k2_pre_topc(A_38, B_39), k2_pre_topc(A_38, k3_subset_1(u1_struct_0(A_38), B_39)))=k2_tops_1(A_38, B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.14/1.24  tff(c_127, plain, (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_52, c_118])).
% 2.14/1.24  tff(c_131, plain, (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_127])).
% 2.14/1.24  tff(c_189, plain, (k3_xboole_0('#skF_2', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_183, c_131])).
% 2.14/1.24  tff(c_205, plain, (k3_xboole_0('#skF_2', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22, c_189])).
% 2.14/1.24  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.14/1.24  tff(c_212, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_205, c_2])).
% 2.14/1.24  tff(c_216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_212])).
% 2.14/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.24  
% 2.14/1.24  Inference rules
% 2.14/1.24  ----------------------
% 2.14/1.24  #Ref     : 0
% 2.14/1.24  #Sup     : 46
% 2.14/1.24  #Fact    : 0
% 2.14/1.24  #Define  : 0
% 2.14/1.24  #Split   : 0
% 2.14/1.24  #Chain   : 0
% 2.14/1.24  #Close   : 0
% 2.14/1.24  
% 2.14/1.24  Ordering : KBO
% 2.14/1.24  
% 2.14/1.24  Simplification rules
% 2.14/1.24  ----------------------
% 2.14/1.24  #Subsume      : 0
% 2.14/1.24  #Demod        : 32
% 2.14/1.24  #Tautology    : 24
% 2.14/1.24  #SimpNegUnit  : 1
% 2.14/1.24  #BackRed      : 0
% 2.14/1.24  
% 2.14/1.24  #Partial instantiations: 0
% 2.14/1.24  #Strategies tried      : 1
% 2.14/1.24  
% 2.14/1.24  Timing (in seconds)
% 2.14/1.24  ----------------------
% 2.14/1.24  Preprocessing        : 0.29
% 2.14/1.24  Parsing              : 0.16
% 2.14/1.24  CNF conversion       : 0.02
% 2.14/1.24  Main loop            : 0.19
% 2.14/1.24  Inferencing          : 0.08
% 2.14/1.24  Reduction            : 0.05
% 2.14/1.24  Demodulation         : 0.04
% 2.14/1.24  BG Simplification    : 0.01
% 2.14/1.24  Subsumption          : 0.03
% 2.14/1.24  Abstraction          : 0.01
% 2.14/1.24  MUC search           : 0.00
% 2.14/1.24  Cooper               : 0.00
% 2.14/1.24  Total                : 0.50
% 2.14/1.24  Index Insertion      : 0.00
% 2.14/1.24  Index Deletion       : 0.00
% 2.14/1.24  Index Matching       : 0.00
% 2.14/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
