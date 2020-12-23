%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:56 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 134 expanded)
%              Number of leaves         :   24 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :   86 ( 320 expanded)
%              Number of equality atoms :    9 (  36 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_subset_1 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_66,axiom,(
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

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_18,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k2_tops_1(A_19,B_20),k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k2_pre_topc(A_11,B_12),k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_22,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_29,plain,(
    ! [A_26,B_27] :
      ( k2_pre_topc(A_26,B_27) = B_27
      | ~ v4_pre_topc(B_27,A_26)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_39,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_29])).

tff(c_44,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_39])).

tff(c_96,plain,(
    ! [A_45,B_46] :
      ( k9_subset_1(u1_struct_0(A_45),k2_pre_topc(A_45,B_46),k2_pre_topc(A_45,k3_subset_1(u1_struct_0(A_45),B_46))) = k2_tops_1(A_45,B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_108,plain,
    ( k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_96])).

tff(c_112,plain,(
    k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_108])).

tff(c_85,plain,(
    ! [A_38,B_39,C_40] :
      ( r1_tarski(k3_subset_1(A_38,B_39),k3_subset_1(A_38,k9_subset_1(A_38,B_39,C_40)))
      | ~ m1_subset_1(C_40,k1_zfmisc_1(A_38))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [B_4,C_6,A_3] :
      ( r1_tarski(B_4,C_6)
      | ~ r1_tarski(k3_subset_1(A_3,C_6),k3_subset_1(A_3,B_4))
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_122,plain,(
    ! [A_47,B_48,C_49] :
      ( r1_tarski(k9_subset_1(A_47,B_48,C_49),B_48)
      | ~ m1_subset_1(k9_subset_1(A_47,B_48,C_49),k1_zfmisc_1(A_47))
      | ~ m1_subset_1(C_49,k1_zfmisc_1(A_47))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_47)) ) ),
    inference(resolution,[status(thm)],[c_85,c_4])).

tff(c_124,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),'#skF_2')
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_122])).

tff(c_128,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_112,c_124])).

tff(c_129,plain,
    ( ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_128])).

tff(c_130,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_133,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_130])).

tff(c_136,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_133])).

tff(c_139,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2,c_136])).

tff(c_143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_139])).

tff(c_144,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_148,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_144])).

tff(c_152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_148])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:48:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.27  
% 2.14/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.27  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_subset_1 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.14/1.27  
% 2.14/1.27  %Foreground sorts:
% 2.14/1.27  
% 2.14/1.27  
% 2.14/1.27  %Background operators:
% 2.14/1.27  
% 2.14/1.27  
% 2.14/1.27  %Foreground operators:
% 2.14/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.27  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.14/1.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.14/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.27  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.14/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.27  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.14/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.27  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.14/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.14/1.27  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.14/1.27  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.14/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.27  
% 2.14/1.29  tff(f_89, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 2.14/1.29  tff(f_79, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 2.14/1.29  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.14/1.29  tff(f_51, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.14/1.29  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.14/1.29  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_1)).
% 2.14/1.29  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_subset_1)).
% 2.14/1.29  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 2.14/1.29  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.14/1.29  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.14/1.29  tff(c_18, plain, (![A_19, B_20]: (m1_subset_1(k2_tops_1(A_19, B_20), k1_zfmisc_1(u1_struct_0(A_19))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.14/1.29  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.14/1.29  tff(c_10, plain, (![A_11, B_12]: (m1_subset_1(k2_pre_topc(A_11, B_12), k1_zfmisc_1(u1_struct_0(A_11))) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.14/1.29  tff(c_20, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.14/1.29  tff(c_22, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.14/1.29  tff(c_29, plain, (![A_26, B_27]: (k2_pre_topc(A_26, B_27)=B_27 | ~v4_pre_topc(B_27, A_26) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.14/1.29  tff(c_39, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_29])).
% 2.14/1.29  tff(c_44, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_39])).
% 2.14/1.29  tff(c_96, plain, (![A_45, B_46]: (k9_subset_1(u1_struct_0(A_45), k2_pre_topc(A_45, B_46), k2_pre_topc(A_45, k3_subset_1(u1_struct_0(A_45), B_46)))=k2_tops_1(A_45, B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.14/1.29  tff(c_108, plain, (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_44, c_96])).
% 2.14/1.29  tff(c_112, plain, (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_108])).
% 2.14/1.29  tff(c_85, plain, (![A_38, B_39, C_40]: (r1_tarski(k3_subset_1(A_38, B_39), k3_subset_1(A_38, k9_subset_1(A_38, B_39, C_40))) | ~m1_subset_1(C_40, k1_zfmisc_1(A_38)) | ~m1_subset_1(B_39, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.14/1.29  tff(c_4, plain, (![B_4, C_6, A_3]: (r1_tarski(B_4, C_6) | ~r1_tarski(k3_subset_1(A_3, C_6), k3_subset_1(A_3, B_4)) | ~m1_subset_1(C_6, k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.14/1.29  tff(c_122, plain, (![A_47, B_48, C_49]: (r1_tarski(k9_subset_1(A_47, B_48, C_49), B_48) | ~m1_subset_1(k9_subset_1(A_47, B_48, C_49), k1_zfmisc_1(A_47)) | ~m1_subset_1(C_49, k1_zfmisc_1(A_47)) | ~m1_subset_1(B_48, k1_zfmisc_1(A_47)))), inference(resolution, [status(thm)], [c_85, c_4])).
% 2.14/1.29  tff(c_124, plain, (r1_tarski(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), '#skF_2') | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_112, c_122])).
% 2.14/1.29  tff(c_128, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_112, c_124])).
% 2.14/1.29  tff(c_129, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_20, c_128])).
% 2.14/1.29  tff(c_130, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_129])).
% 2.14/1.29  tff(c_133, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_10, c_130])).
% 2.14/1.29  tff(c_136, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_133])).
% 2.14/1.29  tff(c_139, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_2, c_136])).
% 2.14/1.29  tff(c_143, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_139])).
% 2.14/1.29  tff(c_144, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_129])).
% 2.14/1.29  tff(c_148, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_144])).
% 2.14/1.29  tff(c_152, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_148])).
% 2.14/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.29  
% 2.14/1.29  Inference rules
% 2.14/1.29  ----------------------
% 2.14/1.29  #Ref     : 0
% 2.14/1.29  #Sup     : 26
% 2.14/1.29  #Fact    : 0
% 2.14/1.29  #Define  : 0
% 2.14/1.29  #Split   : 1
% 2.14/1.29  #Chain   : 0
% 2.14/1.29  #Close   : 0
% 2.14/1.29  
% 2.14/1.29  Ordering : KBO
% 2.14/1.29  
% 2.14/1.29  Simplification rules
% 2.14/1.29  ----------------------
% 2.14/1.29  #Subsume      : 0
% 2.14/1.29  #Demod        : 21
% 2.14/1.29  #Tautology    : 10
% 2.14/1.29  #SimpNegUnit  : 1
% 2.14/1.29  #BackRed      : 0
% 2.14/1.29  
% 2.14/1.29  #Partial instantiations: 0
% 2.14/1.29  #Strategies tried      : 1
% 2.14/1.29  
% 2.14/1.29  Timing (in seconds)
% 2.14/1.29  ----------------------
% 2.14/1.29  Preprocessing        : 0.31
% 2.14/1.29  Parsing              : 0.18
% 2.14/1.29  CNF conversion       : 0.02
% 2.14/1.29  Main loop            : 0.18
% 2.14/1.29  Inferencing          : 0.07
% 2.14/1.29  Reduction            : 0.05
% 2.14/1.29  Demodulation         : 0.04
% 2.14/1.29  BG Simplification    : 0.01
% 2.14/1.29  Subsumption          : 0.03
% 2.14/1.29  Abstraction          : 0.01
% 2.14/1.29  MUC search           : 0.00
% 2.14/1.29  Cooper               : 0.00
% 2.14/1.29  Total                : 0.52
% 2.14/1.29  Index Insertion      : 0.00
% 2.14/1.29  Index Deletion       : 0.00
% 2.14/1.29  Index Matching       : 0.00
% 2.14/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
