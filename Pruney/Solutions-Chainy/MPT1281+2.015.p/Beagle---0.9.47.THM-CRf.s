%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:15 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   62 (  95 expanded)
%              Number of leaves         :   37 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :   67 ( 158 expanded)
%              Number of equality atoms :   18 (  26 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k7_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v5_tops_1,type,(
    v5_tops_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v5_tops_1(B,A)
             => r1_tarski(k2_tops_1(A,B),k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tops_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_40,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_198,plain,(
    ! [A_98,B_99] :
      ( k2_pre_topc(A_98,k1_tops_1(A_98,B_99)) = B_99
      | ~ v5_tops_1(B_99,A_98)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_202,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_198])).

tff(c_206,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_202])).

tff(c_38,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_207,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_38])).

tff(c_46,plain,(
    ! [B_57,A_58] : k2_xboole_0(B_57,A_58) = k2_xboole_0(A_58,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_61,plain,(
    ! [A_58,B_57] : r1_tarski(A_58,k2_xboole_0(B_57,A_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_8])).

tff(c_150,plain,(
    ! [A_79,B_80,C_81] :
      ( k7_subset_1(A_79,B_80,C_81) = k4_xboole_0(B_80,C_81)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_153,plain,(
    ! [C_81] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_81) = k4_xboole_0('#skF_2',C_81) ),
    inference(resolution,[status(thm)],[c_42,c_150])).

tff(c_34,plain,(
    ! [A_49,B_50] :
      ( m1_subset_1(k1_tops_1(A_49,B_50),k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_185,plain,(
    ! [A_96,B_97] :
      ( k2_pre_topc(A_96,k2_pre_topc(A_96,B_97)) = k2_pre_topc(A_96,B_97)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_246,plain,(
    ! [A_111,B_112] :
      ( k2_pre_topc(A_111,k2_pre_topc(A_111,k1_tops_1(A_111,B_112))) = k2_pre_topc(A_111,k1_tops_1(A_111,B_112))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111) ) ),
    inference(resolution,[status(thm)],[c_34,c_185])).

tff(c_250,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_246])).

tff(c_254,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_206,c_206,c_250])).

tff(c_36,plain,(
    ! [A_51,B_53] :
      ( k7_subset_1(u1_struct_0(A_51),k2_pre_topc(A_51,B_53),k1_tops_1(A_51,B_53)) = k2_tops_1(A_51,B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_259,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_36])).

tff(c_263,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_153,c_259])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_tarski(k4_xboole_0(A_5,B_6),C_7)
      | ~ r1_tarski(A_5,k2_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_272,plain,(
    ! [C_113] :
      ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),C_113)
      | ~ r1_tarski('#skF_2',k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),C_113)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_6])).

tff(c_276,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_61,c_272])).

tff(c_288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_276])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:11:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.24  
% 2.21/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.24  %$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k7_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 2.21/1.24  
% 2.21/1.24  %Foreground sorts:
% 2.21/1.24  
% 2.21/1.24  
% 2.21/1.24  %Background operators:
% 2.21/1.24  
% 2.21/1.24  
% 2.21/1.24  %Foreground operators:
% 2.21/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.21/1.24  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.21/1.24  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.21/1.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.21/1.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.21/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.21/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.21/1.24  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.21/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.21/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.24  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.21/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.24  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.21/1.24  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.24  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 2.21/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.21/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.21/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.21/1.24  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.21/1.24  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.21/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.21/1.24  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.21/1.24  
% 2.21/1.26  tff(f_93, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => r1_tarski(k2_tops_1(A, B), k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tops_1)).
% 2.21/1.26  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tops_1)).
% 2.21/1.26  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.21/1.26  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.21/1.26  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.21/1.26  tff(f_76, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 2.21/1.26  tff(f_61, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 2.21/1.26  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 2.21/1.26  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.21/1.26  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.21/1.26  tff(c_40, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.21/1.26  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.21/1.26  tff(c_198, plain, (![A_98, B_99]: (k2_pre_topc(A_98, k1_tops_1(A_98, B_99))=B_99 | ~v5_tops_1(B_99, A_98) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.21/1.26  tff(c_202, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_198])).
% 2.21/1.26  tff(c_206, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_202])).
% 2.21/1.26  tff(c_38, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.21/1.26  tff(c_207, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_206, c_38])).
% 2.21/1.26  tff(c_46, plain, (![B_57, A_58]: (k2_xboole_0(B_57, A_58)=k2_xboole_0(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.21/1.26  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.21/1.26  tff(c_61, plain, (![A_58, B_57]: (r1_tarski(A_58, k2_xboole_0(B_57, A_58)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_8])).
% 2.21/1.26  tff(c_150, plain, (![A_79, B_80, C_81]: (k7_subset_1(A_79, B_80, C_81)=k4_xboole_0(B_80, C_81) | ~m1_subset_1(B_80, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.21/1.26  tff(c_153, plain, (![C_81]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_81)=k4_xboole_0('#skF_2', C_81))), inference(resolution, [status(thm)], [c_42, c_150])).
% 2.21/1.26  tff(c_34, plain, (![A_49, B_50]: (m1_subset_1(k1_tops_1(A_49, B_50), k1_zfmisc_1(u1_struct_0(A_49))) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.21/1.26  tff(c_185, plain, (![A_96, B_97]: (k2_pre_topc(A_96, k2_pre_topc(A_96, B_97))=k2_pre_topc(A_96, B_97) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.21/1.26  tff(c_246, plain, (![A_111, B_112]: (k2_pre_topc(A_111, k2_pre_topc(A_111, k1_tops_1(A_111, B_112)))=k2_pre_topc(A_111, k1_tops_1(A_111, B_112)) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_pre_topc(A_111))), inference(resolution, [status(thm)], [c_34, c_185])).
% 2.21/1.26  tff(c_250, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_246])).
% 2.21/1.26  tff(c_254, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_206, c_206, c_250])).
% 2.21/1.26  tff(c_36, plain, (![A_51, B_53]: (k7_subset_1(u1_struct_0(A_51), k2_pre_topc(A_51, B_53), k1_tops_1(A_51, B_53))=k2_tops_1(A_51, B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.21/1.26  tff(c_259, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_254, c_36])).
% 2.21/1.26  tff(c_263, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_153, c_259])).
% 2.21/1.26  tff(c_6, plain, (![A_5, B_6, C_7]: (r1_tarski(k4_xboole_0(A_5, B_6), C_7) | ~r1_tarski(A_5, k2_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.21/1.26  tff(c_272, plain, (![C_113]: (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), C_113) | ~r1_tarski('#skF_2', k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), C_113)))), inference(superposition, [status(thm), theory('equality')], [c_263, c_6])).
% 2.21/1.26  tff(c_276, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_61, c_272])).
% 2.21/1.26  tff(c_288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_207, c_276])).
% 2.21/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.26  
% 2.21/1.26  Inference rules
% 2.21/1.26  ----------------------
% 2.21/1.26  #Ref     : 0
% 2.21/1.26  #Sup     : 58
% 2.21/1.26  #Fact    : 0
% 2.21/1.26  #Define  : 0
% 2.21/1.26  #Split   : 0
% 2.21/1.26  #Chain   : 0
% 2.21/1.26  #Close   : 0
% 2.21/1.26  
% 2.21/1.26  Ordering : KBO
% 2.21/1.26  
% 2.21/1.26  Simplification rules
% 2.21/1.26  ----------------------
% 2.21/1.26  #Subsume      : 0
% 2.21/1.26  #Demod        : 20
% 2.21/1.26  #Tautology    : 43
% 2.21/1.26  #SimpNegUnit  : 1
% 2.21/1.26  #BackRed      : 1
% 2.21/1.26  
% 2.21/1.26  #Partial instantiations: 0
% 2.21/1.26  #Strategies tried      : 1
% 2.21/1.26  
% 2.21/1.26  Timing (in seconds)
% 2.21/1.26  ----------------------
% 2.21/1.26  Preprocessing        : 0.32
% 2.21/1.26  Parsing              : 0.17
% 2.21/1.26  CNF conversion       : 0.02
% 2.21/1.26  Main loop            : 0.18
% 2.21/1.26  Inferencing          : 0.07
% 2.21/1.26  Reduction            : 0.06
% 2.21/1.26  Demodulation         : 0.04
% 2.21/1.26  BG Simplification    : 0.02
% 2.21/1.26  Subsumption          : 0.03
% 2.21/1.26  Abstraction          : 0.01
% 2.21/1.26  MUC search           : 0.00
% 2.21/1.26  Cooper               : 0.00
% 2.21/1.26  Total                : 0.53
% 2.21/1.26  Index Insertion      : 0.00
% 2.21/1.26  Index Deletion       : 0.00
% 2.21/1.26  Index Matching       : 0.00
% 2.21/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
