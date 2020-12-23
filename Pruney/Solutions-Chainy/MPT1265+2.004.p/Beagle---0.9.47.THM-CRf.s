%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:42 EST 2020

% Result     : Theorem 12.14s
% Output     : CNFRefutation 12.23s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 211 expanded)
%              Number of leaves         :   31 (  86 expanded)
%              Depth                    :   11
%              Number of atoms          :  132 ( 518 expanded)
%              Number of equality atoms :   36 (  90 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

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

tff(f_104,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_85,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).

tff(c_34,plain,(
    v1_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_18,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_77,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_82,plain,(
    ! [A_39] :
      ( u1_struct_0(A_39) = k2_struct_0(A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(resolution,[status(thm)],[c_18,c_77])).

tff(c_86,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_82])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_89,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_38])).

tff(c_30,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_32,plain,(
    v1_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_88,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_36])).

tff(c_468,plain,(
    ! [A_75,B_76] :
      ( k2_pre_topc(A_75,B_76) = k2_struct_0(A_75)
      | ~ v1_tops_1(B_76,A_75)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_475,plain,(
    ! [B_76] :
      ( k2_pre_topc('#skF_1',B_76) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_76,'#skF_1')
      | ~ m1_subset_1(B_76,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_468])).

tff(c_578,plain,(
    ! [B_81] :
      ( k2_pre_topc('#skF_1',B_81) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_81,'#skF_1')
      | ~ m1_subset_1(B_81,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_475])).

tff(c_588,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_88,c_578])).

tff(c_595,plain,(
    k2_pre_topc('#skF_1','#skF_3') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_588])).

tff(c_155,plain,(
    ! [A_50,B_51,C_52] :
      ( k9_subset_1(A_50,B_51,C_52) = k3_xboole_0(B_51,C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_164,plain,(
    ! [B_51] : k9_subset_1(k2_struct_0('#skF_1'),B_51,'#skF_3') = k3_xboole_0(B_51,'#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_155])).

tff(c_360,plain,(
    ! [A_68,C_69,B_70] :
      ( k9_subset_1(A_68,C_69,B_70) = k9_subset_1(A_68,B_70,C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_366,plain,(
    ! [B_70] : k9_subset_1(k2_struct_0('#skF_1'),B_70,'#skF_3') = k9_subset_1(k2_struct_0('#skF_1'),'#skF_3',B_70) ),
    inference(resolution,[status(thm)],[c_88,c_360])).

tff(c_371,plain,(
    ! [B_70] : k9_subset_1(k2_struct_0('#skF_1'),'#skF_3',B_70) = k3_xboole_0(B_70,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_366])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_770,plain,(
    ! [A_95,C_96,B_97] :
      ( k2_pre_topc(A_95,k9_subset_1(u1_struct_0(A_95),C_96,B_97)) = k2_pre_topc(A_95,C_96)
      | ~ v3_pre_topc(C_96,A_95)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ v1_tops_1(B_97,A_95)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_775,plain,(
    ! [C_96,B_97] :
      ( k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),C_96,B_97)) = k2_pre_topc('#skF_1',C_96)
      | ~ v3_pre_topc(C_96,'#skF_1')
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ v1_tops_1(B_97,'#skF_1')
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_770])).

tff(c_804,plain,(
    ! [C_100,B_101] :
      ( k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),C_100,B_101)) = k2_pre_topc('#skF_1',C_100)
      | ~ v3_pre_topc(C_100,'#skF_1')
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ v1_tops_1(B_101,'#skF_1')
      | ~ m1_subset_1(B_101,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_86,c_86,c_775])).

tff(c_811,plain,(
    ! [B_101] :
      ( k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),'#skF_3',B_101)) = k2_pre_topc('#skF_1','#skF_3')
      | ~ v3_pre_topc('#skF_3','#skF_1')
      | ~ v1_tops_1(B_101,'#skF_1')
      | ~ m1_subset_1(B_101,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_88,c_804])).

tff(c_901,plain,(
    ! [B_107] :
      ( k2_pre_topc('#skF_1',k3_xboole_0(B_107,'#skF_3')) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_107,'#skF_1')
      | ~ m1_subset_1(B_107,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_595,c_371,c_811])).

tff(c_908,plain,
    ( k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_89,c_901])).

tff(c_915,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2,c_908])).

tff(c_94,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,B_41)
      | ~ m1_subset_1(A_40,k1_zfmisc_1(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_102,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_88,c_94])).

tff(c_115,plain,(
    ! [A_47,B_48] :
      ( k2_xboole_0(A_47,B_48) = B_48
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_126,plain,(
    k2_xboole_0('#skF_3',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_102,c_115])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : r1_tarski(k3_xboole_0(A_5,B_6),k2_xboole_0(A_5,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_131,plain,(
    ! [B_6] : r1_tarski(k3_xboole_0('#skF_3',B_6),k2_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_6])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_643,plain,(
    ! [B_84,A_85] :
      ( v1_tops_1(B_84,A_85)
      | k2_pre_topc(A_85,B_84) != k2_struct_0(A_85)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_650,plain,(
    ! [B_84] :
      ( v1_tops_1(B_84,'#skF_1')
      | k2_pre_topc('#skF_1',B_84) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_84,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_643])).

tff(c_701,plain,(
    ! [B_90] :
      ( v1_tops_1(B_90,'#skF_1')
      | k2_pre_topc('#skF_1',B_90) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_90,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_650])).

tff(c_1525,plain,(
    ! [A_140] :
      ( v1_tops_1(A_140,'#skF_1')
      | k2_pre_topc('#skF_1',A_140) != k2_struct_0('#skF_1')
      | ~ r1_tarski(A_140,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_14,c_701])).

tff(c_25409,plain,(
    ! [B_578] :
      ( v1_tops_1(k3_xboole_0('#skF_3',B_578),'#skF_1')
      | k2_pre_topc('#skF_1',k3_xboole_0('#skF_3',B_578)) != k2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_131,c_1525])).

tff(c_28,plain,(
    ~ v1_tops_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_87,plain,(
    ~ v1_tops_1(k9_subset_1(k2_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_28])).

tff(c_208,plain,(
    ~ v1_tops_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_87])).

tff(c_209,plain,(
    ~ v1_tops_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_208])).

tff(c_25415,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_25409,c_209])).

tff(c_25436,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_915,c_25415])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:45:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.14/5.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.14/5.62  
% 12.14/5.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.14/5.62  %$ v3_pre_topc > v1_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 12.14/5.62  
% 12.14/5.62  %Foreground sorts:
% 12.14/5.62  
% 12.14/5.62  
% 12.14/5.62  %Background operators:
% 12.14/5.62  
% 12.14/5.62  
% 12.14/5.62  %Foreground operators:
% 12.14/5.62  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 12.14/5.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.14/5.62  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.14/5.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.14/5.62  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 12.14/5.62  tff('#skF_2', type, '#skF_2': $i).
% 12.14/5.62  tff('#skF_3', type, '#skF_3': $i).
% 12.14/5.62  tff('#skF_1', type, '#skF_1': $i).
% 12.14/5.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.14/5.62  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 12.14/5.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.14/5.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.14/5.62  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 12.14/5.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.14/5.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.14/5.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.14/5.62  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 12.14/5.62  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 12.14/5.62  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 12.14/5.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.14/5.62  
% 12.23/5.63  tff(f_104, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v1_tops_1(B, A) & v1_tops_1(C, A)) & v3_pre_topc(C, A)) => v1_tops_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_tops_1)).
% 12.23/5.63  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 12.23/5.63  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 12.23/5.63  tff(f_49, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 12.23/5.63  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 12.23/5.63  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 12.23/5.63  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 12.23/5.63  tff(f_85, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(C, A) => (k2_pre_topc(A, C) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), C, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tops_1)).
% 12.23/5.63  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 12.23/5.63  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 12.23/5.63  tff(f_33, axiom, (![A, B, C]: r1_tarski(k3_xboole_0(A, B), k2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_xboole_1)).
% 12.23/5.63  tff(c_34, plain, (v1_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 12.23/5.63  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.23/5.63  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 12.23/5.63  tff(c_18, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.23/5.63  tff(c_77, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.23/5.63  tff(c_82, plain, (![A_39]: (u1_struct_0(A_39)=k2_struct_0(A_39) | ~l1_pre_topc(A_39))), inference(resolution, [status(thm)], [c_18, c_77])).
% 12.23/5.63  tff(c_86, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_82])).
% 12.23/5.63  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 12.23/5.63  tff(c_89, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_38])).
% 12.23/5.63  tff(c_30, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 12.23/5.63  tff(c_32, plain, (v1_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 12.23/5.63  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 12.23/5.63  tff(c_88, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_36])).
% 12.23/5.63  tff(c_468, plain, (![A_75, B_76]: (k2_pre_topc(A_75, B_76)=k2_struct_0(A_75) | ~v1_tops_1(B_76, A_75) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_69])).
% 12.23/5.63  tff(c_475, plain, (![B_76]: (k2_pre_topc('#skF_1', B_76)=k2_struct_0('#skF_1') | ~v1_tops_1(B_76, '#skF_1') | ~m1_subset_1(B_76, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_86, c_468])).
% 12.23/5.63  tff(c_578, plain, (![B_81]: (k2_pre_topc('#skF_1', B_81)=k2_struct_0('#skF_1') | ~v1_tops_1(B_81, '#skF_1') | ~m1_subset_1(B_81, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_475])).
% 12.23/5.63  tff(c_588, plain, (k2_pre_topc('#skF_1', '#skF_3')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_88, c_578])).
% 12.23/5.63  tff(c_595, plain, (k2_pre_topc('#skF_1', '#skF_3')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_588])).
% 12.23/5.63  tff(c_155, plain, (![A_50, B_51, C_52]: (k9_subset_1(A_50, B_51, C_52)=k3_xboole_0(B_51, C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.23/5.63  tff(c_164, plain, (![B_51]: (k9_subset_1(k2_struct_0('#skF_1'), B_51, '#skF_3')=k3_xboole_0(B_51, '#skF_3'))), inference(resolution, [status(thm)], [c_88, c_155])).
% 12.23/5.63  tff(c_360, plain, (![A_68, C_69, B_70]: (k9_subset_1(A_68, C_69, B_70)=k9_subset_1(A_68, B_70, C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.23/5.63  tff(c_366, plain, (![B_70]: (k9_subset_1(k2_struct_0('#skF_1'), B_70, '#skF_3')=k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', B_70))), inference(resolution, [status(thm)], [c_88, c_360])).
% 12.23/5.63  tff(c_371, plain, (![B_70]: (k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', B_70)=k3_xboole_0(B_70, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_366])).
% 12.23/5.63  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 12.23/5.63  tff(c_770, plain, (![A_95, C_96, B_97]: (k2_pre_topc(A_95, k9_subset_1(u1_struct_0(A_95), C_96, B_97))=k2_pre_topc(A_95, C_96) | ~v3_pre_topc(C_96, A_95) | ~m1_subset_1(C_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~v1_tops_1(B_97, A_95) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.23/5.63  tff(c_775, plain, (![C_96, B_97]: (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), C_96, B_97))=k2_pre_topc('#skF_1', C_96) | ~v3_pre_topc(C_96, '#skF_1') | ~m1_subset_1(C_96, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~v1_tops_1(B_97, '#skF_1') | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_86, c_770])).
% 12.23/5.63  tff(c_804, plain, (![C_100, B_101]: (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), C_100, B_101))=k2_pre_topc('#skF_1', C_100) | ~v3_pre_topc(C_100, '#skF_1') | ~m1_subset_1(C_100, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~v1_tops_1(B_101, '#skF_1') | ~m1_subset_1(B_101, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_86, c_86, c_775])).
% 12.23/5.63  tff(c_811, plain, (![B_101]: (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', B_101))=k2_pre_topc('#skF_1', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_1') | ~v1_tops_1(B_101, '#skF_1') | ~m1_subset_1(B_101, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_88, c_804])).
% 12.23/5.63  tff(c_901, plain, (![B_107]: (k2_pre_topc('#skF_1', k3_xboole_0(B_107, '#skF_3'))=k2_struct_0('#skF_1') | ~v1_tops_1(B_107, '#skF_1') | ~m1_subset_1(B_107, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_595, c_371, c_811])).
% 12.23/5.63  tff(c_908, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_89, c_901])).
% 12.23/5.63  tff(c_915, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2, c_908])).
% 12.23/5.63  tff(c_94, plain, (![A_40, B_41]: (r1_tarski(A_40, B_41) | ~m1_subset_1(A_40, k1_zfmisc_1(B_41)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.23/5.63  tff(c_102, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_88, c_94])).
% 12.23/5.63  tff(c_115, plain, (![A_47, B_48]: (k2_xboole_0(A_47, B_48)=B_48 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.23/5.63  tff(c_126, plain, (k2_xboole_0('#skF_3', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_102, c_115])).
% 12.23/5.63  tff(c_6, plain, (![A_5, B_6, C_7]: (r1_tarski(k3_xboole_0(A_5, B_6), k2_xboole_0(A_5, C_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.23/5.63  tff(c_131, plain, (![B_6]: (r1_tarski(k3_xboole_0('#skF_3', B_6), k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_126, c_6])).
% 12.23/5.63  tff(c_14, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.23/5.63  tff(c_643, plain, (![B_84, A_85]: (v1_tops_1(B_84, A_85) | k2_pre_topc(A_85, B_84)!=k2_struct_0(A_85) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_69])).
% 12.23/5.63  tff(c_650, plain, (![B_84]: (v1_tops_1(B_84, '#skF_1') | k2_pre_topc('#skF_1', B_84)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_84, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_86, c_643])).
% 12.23/5.63  tff(c_701, plain, (![B_90]: (v1_tops_1(B_90, '#skF_1') | k2_pre_topc('#skF_1', B_90)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_90, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_650])).
% 12.23/5.63  tff(c_1525, plain, (![A_140]: (v1_tops_1(A_140, '#skF_1') | k2_pre_topc('#skF_1', A_140)!=k2_struct_0('#skF_1') | ~r1_tarski(A_140, k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_701])).
% 12.23/5.63  tff(c_25409, plain, (![B_578]: (v1_tops_1(k3_xboole_0('#skF_3', B_578), '#skF_1') | k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', B_578))!=k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_131, c_1525])).
% 12.23/5.63  tff(c_28, plain, (~v1_tops_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 12.23/5.63  tff(c_87, plain, (~v1_tops_1(k9_subset_1(k2_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_28])).
% 12.23/5.63  tff(c_208, plain, (~v1_tops_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_87])).
% 12.23/5.63  tff(c_209, plain, (~v1_tops_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_208])).
% 12.23/5.63  tff(c_25415, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_25409, c_209])).
% 12.23/5.63  tff(c_25436, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_915, c_25415])).
% 12.23/5.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.23/5.63  
% 12.23/5.63  Inference rules
% 12.23/5.63  ----------------------
% 12.23/5.63  #Ref     : 0
% 12.23/5.63  #Sup     : 6229
% 12.23/5.63  #Fact    : 0
% 12.23/5.63  #Define  : 0
% 12.23/5.63  #Split   : 1
% 12.23/5.63  #Chain   : 0
% 12.23/5.63  #Close   : 0
% 12.23/5.63  
% 12.23/5.63  Ordering : KBO
% 12.23/5.63  
% 12.23/5.63  Simplification rules
% 12.23/5.63  ----------------------
% 12.23/5.63  #Subsume      : 236
% 12.23/5.63  #Demod        : 3009
% 12.23/5.63  #Tautology    : 2847
% 12.23/5.63  #SimpNegUnit  : 0
% 12.23/5.63  #BackRed      : 12
% 12.23/5.63  
% 12.23/5.63  #Partial instantiations: 0
% 12.23/5.63  #Strategies tried      : 1
% 12.23/5.63  
% 12.23/5.63  Timing (in seconds)
% 12.23/5.63  ----------------------
% 12.23/5.64  Preprocessing        : 0.33
% 12.23/5.64  Parsing              : 0.18
% 12.23/5.64  CNF conversion       : 0.02
% 12.23/5.64  Main loop            : 4.53
% 12.23/5.64  Inferencing          : 0.82
% 12.23/5.64  Reduction            : 2.76
% 12.23/5.64  Demodulation         : 2.52
% 12.23/5.64  BG Simplification    : 0.12
% 12.23/5.64  Subsumption          : 0.62
% 12.23/5.64  Abstraction          : 0.18
% 12.23/5.64  MUC search           : 0.00
% 12.23/5.64  Cooper               : 0.00
% 12.23/5.64  Total                : 4.90
% 12.23/5.64  Index Insertion      : 0.00
% 12.23/5.64  Index Deletion       : 0.00
% 12.23/5.64  Index Matching       : 0.00
% 12.23/5.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
