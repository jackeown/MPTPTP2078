%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:41 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 198 expanded)
%              Number of leaves         :   31 (  82 expanded)
%              Depth                    :   11
%              Number of atoms          :  131 ( 485 expanded)
%              Number of equality atoms :   36 (  84 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v1_tops_1(B,A)
                    & v1_tops_1(C,A)
                    & v3_pre_topc(C,A) )
                 => v1_tops_1(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_tops_1)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( v3_pre_topc(C,A)
                 => k2_pre_topc(A,C) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),C,B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tops_1)).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_16,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_73,plain,(
    ! [A_32] :
      ( u1_struct_0(A_32) = k2_struct_0(A_32)
      | ~ l1_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_78,plain,(
    ! [A_33] :
      ( u1_struct_0(A_33) = k2_struct_0(A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(resolution,[status(thm)],[c_16,c_73])).

tff(c_82,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_78])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_84,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_32])).

tff(c_105,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | ~ m1_subset_1(A_36,k1_zfmisc_1(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_113,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_84,c_105])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(k3_xboole_0(A_1,C_3),B_2)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_411,plain,(
    ! [B_80,A_81] :
      ( v1_tops_1(B_80,A_81)
      | k2_pre_topc(A_81,B_80) != k2_struct_0(A_81)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_418,plain,(
    ! [B_80] :
      ( v1_tops_1(B_80,'#skF_1')
      | k2_pre_topc('#skF_1',B_80) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_411])).

tff(c_422,plain,(
    ! [B_82] :
      ( v1_tops_1(B_82,'#skF_1')
      | k2_pre_topc('#skF_1',B_82) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_418])).

tff(c_440,plain,(
    ! [A_83] :
      ( v1_tops_1(A_83,'#skF_1')
      | k2_pre_topc('#skF_1',A_83) != k2_struct_0('#skF_1')
      | ~ r1_tarski(A_83,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_12,c_422])).

tff(c_479,plain,(
    ! [A_86,C_87] :
      ( v1_tops_1(k3_xboole_0(A_86,C_87),'#skF_1')
      | k2_pre_topc('#skF_1',k3_xboole_0(A_86,C_87)) != k2_struct_0('#skF_1')
      | ~ r1_tarski(A_86,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_2,c_440])).

tff(c_4,plain,(
    ! [B_5,A_4] : k2_tarski(B_5,A_4) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_90,plain,(
    ! [A_34,B_35] : k1_setfam_1(k2_tarski(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_119,plain,(
    ! [A_40,B_41] : k1_setfam_1(k2_tarski(A_40,B_41)) = k3_xboole_0(B_41,A_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_90])).

tff(c_8,plain,(
    ! [A_9,B_10] : k1_setfam_1(k2_tarski(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_125,plain,(
    ! [B_41,A_40] : k3_xboole_0(B_41,A_40) = k3_xboole_0(A_40,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_8])).

tff(c_190,plain,(
    ! [A_50,B_51,C_52] :
      ( k9_subset_1(A_50,B_51,C_52) = k3_xboole_0(B_51,C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_199,plain,(
    ! [B_51] : k9_subset_1(k2_struct_0('#skF_1'),B_51,'#skF_3') = k3_xboole_0(B_51,'#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_190])).

tff(c_24,plain,(
    ~ v1_tops_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_83,plain,(
    ~ v1_tops_1(k9_subset_1(k2_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_24])).

tff(c_209,plain,(
    ~ v1_tops_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_83])).

tff(c_210,plain,(
    ~ v1_tops_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_209])).

tff(c_482,plain,
    ( k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k2_struct_0('#skF_1')
    | ~ r1_tarski('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_479,c_210])).

tff(c_491,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_482])).

tff(c_30,plain,(
    v1_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_85,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_34])).

tff(c_198,plain,(
    ! [B_51] : k9_subset_1(k2_struct_0('#skF_1'),B_51,'#skF_2') = k3_xboole_0(B_51,'#skF_2') ),
    inference(resolution,[status(thm)],[c_85,c_190])).

tff(c_26,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28,plain,(
    v1_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_271,plain,(
    ! [A_66,B_67] :
      ( k2_pre_topc(A_66,B_67) = k2_struct_0(A_66)
      | ~ v1_tops_1(B_67,A_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_278,plain,(
    ! [B_67] :
      ( k2_pre_topc('#skF_1',B_67) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_67,'#skF_1')
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_271])).

tff(c_282,plain,(
    ! [B_68] :
      ( k2_pre_topc('#skF_1',B_68) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_68,'#skF_1')
      | ~ m1_subset_1(B_68,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_278])).

tff(c_292,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_282])).

tff(c_299,plain,(
    k2_pre_topc('#skF_1','#skF_3') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_292])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_543,plain,(
    ! [A_96,C_97,B_98] :
      ( k2_pre_topc(A_96,k9_subset_1(u1_struct_0(A_96),C_97,B_98)) = k2_pre_topc(A_96,C_97)
      | ~ v3_pre_topc(C_97,A_96)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ v1_tops_1(B_98,A_96)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96)
      | ~ v2_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_548,plain,(
    ! [C_97,B_98] :
      ( k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),C_97,B_98)) = k2_pre_topc('#skF_1',C_97)
      | ~ v3_pre_topc(C_97,'#skF_1')
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ v1_tops_1(B_98,'#skF_1')
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_543])).

tff(c_693,plain,(
    ! [C_107,B_108] :
      ( k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),C_107,B_108)) = k2_pre_topc('#skF_1',C_107)
      | ~ v3_pre_topc(C_107,'#skF_1')
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ v1_tops_1(B_108,'#skF_1')
      | ~ m1_subset_1(B_108,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_82,c_82,c_548])).

tff(c_700,plain,(
    ! [B_108] :
      ( k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),'#skF_3',B_108)) = k2_pre_topc('#skF_1','#skF_3')
      | ~ v3_pre_topc('#skF_3','#skF_1')
      | ~ v1_tops_1(B_108,'#skF_1')
      | ~ m1_subset_1(B_108,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_84,c_693])).

tff(c_1871,plain,(
    ! [B_122] :
      ( k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),'#skF_3',B_122)) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_122,'#skF_1')
      | ~ m1_subset_1(B_122,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_299,c_700])).

tff(c_1878,plain,
    ( k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_85,c_1871])).

tff(c_1885,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_198,c_1878])).

tff(c_1887,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_491,c_1885])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n021.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 15:42:49 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.01/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.01/1.70  
% 4.01/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.01/1.70  %$ v3_pre_topc > v1_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 4.01/1.70  
% 4.01/1.70  %Foreground sorts:
% 4.01/1.70  
% 4.01/1.70  
% 4.01/1.70  %Background operators:
% 4.01/1.70  
% 4.01/1.70  
% 4.01/1.70  %Foreground operators:
% 4.01/1.70  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.01/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.01/1.70  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.01/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.01/1.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.01/1.70  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 4.01/1.70  tff('#skF_2', type, '#skF_2': $i).
% 4.01/1.70  tff('#skF_3', type, '#skF_3': $i).
% 4.01/1.70  tff('#skF_1', type, '#skF_1': $i).
% 4.01/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.01/1.70  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.01/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.01/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.01/1.70  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.01/1.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.01/1.70  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.01/1.70  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.01/1.70  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.01/1.70  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.01/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.01/1.70  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.01/1.70  
% 4.01/1.71  tff(f_93, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v1_tops_1(B, A) & v1_tops_1(C, A)) & v3_pre_topc(C, A)) => v1_tops_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_tops_1)).
% 4.01/1.71  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.01/1.71  tff(f_45, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.01/1.71  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.01/1.71  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 4.01/1.71  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 4.01/1.71  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.01/1.71  tff(f_37, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.01/1.71  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.01/1.71  tff(f_74, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(C, A) => (k2_pre_topc(A, C) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), C, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tops_1)).
% 4.01/1.71  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.01/1.71  tff(c_16, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.01/1.71  tff(c_73, plain, (![A_32]: (u1_struct_0(A_32)=k2_struct_0(A_32) | ~l1_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.01/1.71  tff(c_78, plain, (![A_33]: (u1_struct_0(A_33)=k2_struct_0(A_33) | ~l1_pre_topc(A_33))), inference(resolution, [status(thm)], [c_16, c_73])).
% 4.01/1.71  tff(c_82, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_78])).
% 4.01/1.71  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.01/1.71  tff(c_84, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_32])).
% 4.01/1.71  tff(c_105, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | ~m1_subset_1(A_36, k1_zfmisc_1(B_37)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.01/1.71  tff(c_113, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_84, c_105])).
% 4.01/1.71  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(k3_xboole_0(A_1, C_3), B_2) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.01/1.71  tff(c_12, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.01/1.71  tff(c_411, plain, (![B_80, A_81]: (v1_tops_1(B_80, A_81) | k2_pre_topc(A_81, B_80)!=k2_struct_0(A_81) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.01/1.71  tff(c_418, plain, (![B_80]: (v1_tops_1(B_80, '#skF_1') | k2_pre_topc('#skF_1', B_80)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_80, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_411])).
% 4.01/1.71  tff(c_422, plain, (![B_82]: (v1_tops_1(B_82, '#skF_1') | k2_pre_topc('#skF_1', B_82)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_82, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_418])).
% 4.01/1.71  tff(c_440, plain, (![A_83]: (v1_tops_1(A_83, '#skF_1') | k2_pre_topc('#skF_1', A_83)!=k2_struct_0('#skF_1') | ~r1_tarski(A_83, k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_12, c_422])).
% 4.01/1.71  tff(c_479, plain, (![A_86, C_87]: (v1_tops_1(k3_xboole_0(A_86, C_87), '#skF_1') | k2_pre_topc('#skF_1', k3_xboole_0(A_86, C_87))!=k2_struct_0('#skF_1') | ~r1_tarski(A_86, k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_2, c_440])).
% 4.01/1.71  tff(c_4, plain, (![B_5, A_4]: (k2_tarski(B_5, A_4)=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.01/1.71  tff(c_90, plain, (![A_34, B_35]: (k1_setfam_1(k2_tarski(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.01/1.71  tff(c_119, plain, (![A_40, B_41]: (k1_setfam_1(k2_tarski(A_40, B_41))=k3_xboole_0(B_41, A_40))), inference(superposition, [status(thm), theory('equality')], [c_4, c_90])).
% 4.01/1.71  tff(c_8, plain, (![A_9, B_10]: (k1_setfam_1(k2_tarski(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.01/1.71  tff(c_125, plain, (![B_41, A_40]: (k3_xboole_0(B_41, A_40)=k3_xboole_0(A_40, B_41))), inference(superposition, [status(thm), theory('equality')], [c_119, c_8])).
% 4.01/1.71  tff(c_190, plain, (![A_50, B_51, C_52]: (k9_subset_1(A_50, B_51, C_52)=k3_xboole_0(B_51, C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.01/1.71  tff(c_199, plain, (![B_51]: (k9_subset_1(k2_struct_0('#skF_1'), B_51, '#skF_3')=k3_xboole_0(B_51, '#skF_3'))), inference(resolution, [status(thm)], [c_84, c_190])).
% 4.01/1.71  tff(c_24, plain, (~v1_tops_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.01/1.71  tff(c_83, plain, (~v1_tops_1(k9_subset_1(k2_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_24])).
% 4.01/1.71  tff(c_209, plain, (~v1_tops_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_83])).
% 4.01/1.71  tff(c_210, plain, (~v1_tops_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_209])).
% 4.01/1.71  tff(c_482, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k2_struct_0('#skF_1') | ~r1_tarski('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_479, c_210])).
% 4.01/1.71  tff(c_491, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_482])).
% 4.01/1.71  tff(c_30, plain, (v1_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.01/1.71  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.01/1.71  tff(c_85, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_34])).
% 4.01/1.71  tff(c_198, plain, (![B_51]: (k9_subset_1(k2_struct_0('#skF_1'), B_51, '#skF_2')=k3_xboole_0(B_51, '#skF_2'))), inference(resolution, [status(thm)], [c_85, c_190])).
% 4.01/1.71  tff(c_26, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.01/1.71  tff(c_28, plain, (v1_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.01/1.71  tff(c_271, plain, (![A_66, B_67]: (k2_pre_topc(A_66, B_67)=k2_struct_0(A_66) | ~v1_tops_1(B_67, A_66) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.01/1.71  tff(c_278, plain, (![B_67]: (k2_pre_topc('#skF_1', B_67)=k2_struct_0('#skF_1') | ~v1_tops_1(B_67, '#skF_1') | ~m1_subset_1(B_67, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_271])).
% 4.01/1.71  tff(c_282, plain, (![B_68]: (k2_pre_topc('#skF_1', B_68)=k2_struct_0('#skF_1') | ~v1_tops_1(B_68, '#skF_1') | ~m1_subset_1(B_68, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_278])).
% 4.01/1.71  tff(c_292, plain, (k2_pre_topc('#skF_1', '#skF_3')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_84, c_282])).
% 4.01/1.71  tff(c_299, plain, (k2_pre_topc('#skF_1', '#skF_3')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_292])).
% 4.01/1.71  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.01/1.71  tff(c_543, plain, (![A_96, C_97, B_98]: (k2_pre_topc(A_96, k9_subset_1(u1_struct_0(A_96), C_97, B_98))=k2_pre_topc(A_96, C_97) | ~v3_pre_topc(C_97, A_96) | ~m1_subset_1(C_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~v1_tops_1(B_98, A_96) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96) | ~v2_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.01/1.71  tff(c_548, plain, (![C_97, B_98]: (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), C_97, B_98))=k2_pre_topc('#skF_1', C_97) | ~v3_pre_topc(C_97, '#skF_1') | ~m1_subset_1(C_97, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~v1_tops_1(B_98, '#skF_1') | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_543])).
% 4.01/1.71  tff(c_693, plain, (![C_107, B_108]: (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), C_107, B_108))=k2_pre_topc('#skF_1', C_107) | ~v3_pre_topc(C_107, '#skF_1') | ~m1_subset_1(C_107, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~v1_tops_1(B_108, '#skF_1') | ~m1_subset_1(B_108, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_82, c_82, c_548])).
% 4.01/1.71  tff(c_700, plain, (![B_108]: (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', B_108))=k2_pre_topc('#skF_1', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_1') | ~v1_tops_1(B_108, '#skF_1') | ~m1_subset_1(B_108, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_84, c_693])).
% 4.01/1.71  tff(c_1871, plain, (![B_122]: (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', B_122))=k2_struct_0('#skF_1') | ~v1_tops_1(B_122, '#skF_1') | ~m1_subset_1(B_122, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_299, c_700])).
% 4.01/1.71  tff(c_1878, plain, (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_85, c_1871])).
% 4.01/1.71  tff(c_1885, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_198, c_1878])).
% 4.01/1.71  tff(c_1887, plain, $false, inference(negUnitSimplification, [status(thm)], [c_491, c_1885])).
% 4.01/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.01/1.71  
% 4.01/1.71  Inference rules
% 4.01/1.71  ----------------------
% 4.01/1.71  #Ref     : 0
% 4.01/1.71  #Sup     : 474
% 4.01/1.71  #Fact    : 0
% 4.01/1.71  #Define  : 0
% 4.01/1.71  #Split   : 0
% 4.01/1.71  #Chain   : 0
% 4.01/1.71  #Close   : 0
% 4.01/1.71  
% 4.01/1.71  Ordering : KBO
% 4.01/1.71  
% 4.01/1.71  Simplification rules
% 4.01/1.71  ----------------------
% 4.01/1.71  #Subsume      : 78
% 4.01/1.71  #Demod        : 74
% 4.01/1.71  #Tautology    : 109
% 4.01/1.71  #SimpNegUnit  : 1
% 4.01/1.71  #BackRed      : 4
% 4.01/1.71  
% 4.01/1.71  #Partial instantiations: 0
% 4.01/1.71  #Strategies tried      : 1
% 4.01/1.71  
% 4.01/1.71  Timing (in seconds)
% 4.01/1.71  ----------------------
% 4.01/1.71  Preprocessing        : 0.33
% 4.01/1.71  Parsing              : 0.18
% 4.01/1.71  CNF conversion       : 0.02
% 4.01/1.71  Main loop            : 0.60
% 4.01/1.71  Inferencing          : 0.21
% 4.01/1.71  Reduction            : 0.24
% 4.01/1.72  Demodulation         : 0.20
% 4.01/1.72  BG Simplification    : 0.03
% 4.01/1.72  Subsumption          : 0.09
% 4.01/1.72  Abstraction          : 0.03
% 4.01/1.72  MUC search           : 0.00
% 4.01/1.72  Cooper               : 0.00
% 4.01/1.72  Total                : 0.96
% 4.01/1.72  Index Insertion      : 0.00
% 4.01/1.72  Index Deletion       : 0.00
% 4.01/1.72  Index Matching       : 0.00
% 4.01/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
