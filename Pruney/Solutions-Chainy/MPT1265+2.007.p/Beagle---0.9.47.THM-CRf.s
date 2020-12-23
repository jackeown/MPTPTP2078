%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:42 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 269 expanded)
%              Number of leaves         :   26 ( 108 expanded)
%              Depth                    :   12
%              Number of atoms          :  114 ( 797 expanded)
%              Number of equality atoms :   23 ( 113 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_118,negated_conjecture,(
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

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_99,axiom,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_78,plain,(
    ! [A_50,B_51,C_52] :
      ( k9_subset_1(A_50,B_51,C_52) = k3_xboole_0(B_51,C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_86,plain,(
    ! [B_51] : k9_subset_1(u1_struct_0('#skF_1'),B_51,'#skF_3') = k3_xboole_0(B_51,'#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_78])).

tff(c_133,plain,(
    ! [A_60,C_61,B_62] :
      ( k9_subset_1(A_60,C_61,B_62) = k9_subset_1(A_60,B_62,C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_137,plain,(
    ! [B_62] : k9_subset_1(u1_struct_0('#skF_1'),B_62,'#skF_3') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_62) ),
    inference(resolution,[status(thm)],[c_38,c_133])).

tff(c_145,plain,(
    ! [B_63] : k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_63) = k3_xboole_0(B_63,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_137])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_87,plain,(
    ! [B_51] : k9_subset_1(u1_struct_0('#skF_1'),B_51,'#skF_2') = k3_xboole_0(B_51,'#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_78])).

tff(c_160,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_87])).

tff(c_30,plain,(
    ~ v1_tops_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_99,plain,(
    ~ v1_tops_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_30])).

tff(c_180,plain,(
    ~ v1_tops_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_99])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_36,plain,(
    v1_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_32,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_34,plain,(
    v1_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_511,plain,(
    ! [A_84,B_85] :
      ( k2_pre_topc(A_84,B_85) = k2_struct_0(A_84)
      | ~ v1_tops_1(B_85,A_84)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_521,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_511])).

tff(c_529,plain,(
    k2_pre_topc('#skF_1','#skF_3') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_34,c_521])).

tff(c_142,plain,(
    ! [B_62] : k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_62) = k3_xboole_0(B_62,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_137])).

tff(c_828,plain,(
    ! [A_96,C_97,B_98] :
      ( k2_pre_topc(A_96,k9_subset_1(u1_struct_0(A_96),C_97,B_98)) = k2_pre_topc(A_96,C_97)
      | ~ v3_pre_topc(C_97,A_96)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ v1_tops_1(B_98,A_96)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96)
      | ~ v2_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_837,plain,(
    ! [B_98] :
      ( k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_98)) = k2_pre_topc('#skF_1','#skF_3')
      | ~ v3_pre_topc('#skF_3','#skF_1')
      | ~ v1_tops_1(B_98,'#skF_1')
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_828])).

tff(c_854,plain,(
    ! [B_99] :
      ( k2_pre_topc('#skF_1',k3_xboole_0(B_99,'#skF_3')) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_99,'#skF_1')
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_32,c_529,c_142,c_837])).

tff(c_871,plain,
    ( k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_854])).

tff(c_883,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_160,c_871])).

tff(c_47,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | ~ m1_subset_1(A_41,k1_zfmisc_1(B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_55,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_40,c_47])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k3_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_184,plain,(
    ! [B_4] :
      ( r1_tarski(k3_xboole_0('#skF_3','#skF_2'),B_4)
      | ~ r1_tarski('#skF_2',B_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_8])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_248,plain,(
    ! [B_66,A_67] :
      ( r1_tarski(B_66,k2_pre_topc(A_67,B_66))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_256,plain,(
    ! [A_12,A_67] :
      ( r1_tarski(A_12,k2_pre_topc(A_67,A_12))
      | ~ l1_pre_topc(A_67)
      | ~ r1_tarski(A_12,u1_struct_0(A_67)) ) ),
    inference(resolution,[status(thm)],[c_16,c_248])).

tff(c_901,plain,
    ( r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k2_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_883,c_256])).

tff(c_908,plain,
    ( r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k2_struct_0('#skF_1'))
    | ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_901])).

tff(c_1272,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_908])).

tff(c_1275,plain,(
    ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_184,c_1272])).

tff(c_1282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_1275])).

tff(c_1284,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_908])).

tff(c_611,plain,(
    ! [B_86,A_87] :
      ( v1_tops_1(B_86,A_87)
      | k2_pre_topc(A_87,B_86) != k2_struct_0(A_87)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_632,plain,(
    ! [A_12,A_87] :
      ( v1_tops_1(A_12,A_87)
      | k2_pre_topc(A_87,A_12) != k2_struct_0(A_87)
      | ~ l1_pre_topc(A_87)
      | ~ r1_tarski(A_12,u1_struct_0(A_87)) ) ),
    inference(resolution,[status(thm)],[c_16,c_611])).

tff(c_1369,plain,
    ( v1_tops_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k2_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1284,c_632])).

tff(c_1384,plain,(
    v1_tops_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_883,c_1369])).

tff(c_1386,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_1384])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:03:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.55  
% 3.49/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.55  %$ v3_pre_topc > v1_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.49/1.55  
% 3.49/1.55  %Foreground sorts:
% 3.49/1.55  
% 3.49/1.55  
% 3.49/1.55  %Background operators:
% 3.49/1.55  
% 3.49/1.55  
% 3.49/1.55  %Foreground operators:
% 3.49/1.55  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.49/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.55  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.49/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.49/1.55  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.49/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.49/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.49/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.49/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.49/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.55  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.49/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.49/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.49/1.55  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.49/1.55  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.49/1.55  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.49/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.49/1.55  
% 3.64/1.57  tff(f_118, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v1_tops_1(B, A) & v1_tops_1(C, A)) & v3_pre_topc(C, A)) => v1_tops_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_tops_1)).
% 3.64/1.57  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.64/1.57  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 3.64/1.57  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 3.64/1.57  tff(f_99, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(C, A) => (k2_pre_topc(A, C) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), C, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tops_1)).
% 3.64/1.57  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.64/1.57  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 3.64/1.57  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 3.64/1.57  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.64/1.57  tff(c_78, plain, (![A_50, B_51, C_52]: (k9_subset_1(A_50, B_51, C_52)=k3_xboole_0(B_51, C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.64/1.57  tff(c_86, plain, (![B_51]: (k9_subset_1(u1_struct_0('#skF_1'), B_51, '#skF_3')=k3_xboole_0(B_51, '#skF_3'))), inference(resolution, [status(thm)], [c_38, c_78])).
% 3.64/1.57  tff(c_133, plain, (![A_60, C_61, B_62]: (k9_subset_1(A_60, C_61, B_62)=k9_subset_1(A_60, B_62, C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.64/1.57  tff(c_137, plain, (![B_62]: (k9_subset_1(u1_struct_0('#skF_1'), B_62, '#skF_3')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_62))), inference(resolution, [status(thm)], [c_38, c_133])).
% 3.64/1.57  tff(c_145, plain, (![B_63]: (k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_63)=k3_xboole_0(B_63, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_137])).
% 3.64/1.57  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.64/1.57  tff(c_87, plain, (![B_51]: (k9_subset_1(u1_struct_0('#skF_1'), B_51, '#skF_2')=k3_xboole_0(B_51, '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_78])).
% 3.64/1.57  tff(c_160, plain, (k3_xboole_0('#skF_2', '#skF_3')=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_145, c_87])).
% 3.64/1.57  tff(c_30, plain, (~v1_tops_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.64/1.57  tff(c_99, plain, (~v1_tops_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_30])).
% 3.64/1.57  tff(c_180, plain, (~v1_tops_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_99])).
% 3.64/1.57  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.64/1.57  tff(c_36, plain, (v1_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.64/1.57  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.64/1.57  tff(c_32, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.64/1.57  tff(c_34, plain, (v1_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.64/1.57  tff(c_511, plain, (![A_84, B_85]: (k2_pre_topc(A_84, B_85)=k2_struct_0(A_84) | ~v1_tops_1(B_85, A_84) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.64/1.57  tff(c_521, plain, (k2_pre_topc('#skF_1', '#skF_3')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_511])).
% 3.64/1.57  tff(c_529, plain, (k2_pre_topc('#skF_1', '#skF_3')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_34, c_521])).
% 3.64/1.57  tff(c_142, plain, (![B_62]: (k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_62)=k3_xboole_0(B_62, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_137])).
% 3.64/1.57  tff(c_828, plain, (![A_96, C_97, B_98]: (k2_pre_topc(A_96, k9_subset_1(u1_struct_0(A_96), C_97, B_98))=k2_pre_topc(A_96, C_97) | ~v3_pre_topc(C_97, A_96) | ~m1_subset_1(C_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~v1_tops_1(B_98, A_96) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96) | ~v2_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.64/1.57  tff(c_837, plain, (![B_98]: (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_98))=k2_pre_topc('#skF_1', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_1') | ~v1_tops_1(B_98, '#skF_1') | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_828])).
% 3.64/1.57  tff(c_854, plain, (![B_99]: (k2_pre_topc('#skF_1', k3_xboole_0(B_99, '#skF_3'))=k2_struct_0('#skF_1') | ~v1_tops_1(B_99, '#skF_1') | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_32, c_529, c_142, c_837])).
% 3.64/1.57  tff(c_871, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_854])).
% 3.64/1.57  tff(c_883, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_160, c_871])).
% 3.64/1.57  tff(c_47, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | ~m1_subset_1(A_41, k1_zfmisc_1(B_42)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.64/1.57  tff(c_55, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_47])).
% 3.64/1.57  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(k3_xboole_0(A_3, C_5), B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.64/1.57  tff(c_184, plain, (![B_4]: (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), B_4) | ~r1_tarski('#skF_2', B_4))), inference(superposition, [status(thm), theory('equality')], [c_160, c_8])).
% 3.64/1.57  tff(c_16, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.64/1.57  tff(c_248, plain, (![B_66, A_67]: (r1_tarski(B_66, k2_pre_topc(A_67, B_66)) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.64/1.57  tff(c_256, plain, (![A_12, A_67]: (r1_tarski(A_12, k2_pre_topc(A_67, A_12)) | ~l1_pre_topc(A_67) | ~r1_tarski(A_12, u1_struct_0(A_67)))), inference(resolution, [status(thm)], [c_16, c_248])).
% 3.64/1.57  tff(c_901, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k2_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_883, c_256])).
% 3.64/1.57  tff(c_908, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k2_struct_0('#skF_1')) | ~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_901])).
% 3.64/1.57  tff(c_1272, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_908])).
% 3.64/1.57  tff(c_1275, plain, (~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_184, c_1272])).
% 3.64/1.57  tff(c_1282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_1275])).
% 3.64/1.57  tff(c_1284, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_908])).
% 3.64/1.57  tff(c_611, plain, (![B_86, A_87]: (v1_tops_1(B_86, A_87) | k2_pre_topc(A_87, B_86)!=k2_struct_0(A_87) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.64/1.57  tff(c_632, plain, (![A_12, A_87]: (v1_tops_1(A_12, A_87) | k2_pre_topc(A_87, A_12)!=k2_struct_0(A_87) | ~l1_pre_topc(A_87) | ~r1_tarski(A_12, u1_struct_0(A_87)))), inference(resolution, [status(thm)], [c_16, c_611])).
% 3.64/1.57  tff(c_1369, plain, (v1_tops_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k2_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1284, c_632])).
% 3.64/1.57  tff(c_1384, plain, (v1_tops_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_883, c_1369])).
% 3.64/1.57  tff(c_1386, plain, $false, inference(negUnitSimplification, [status(thm)], [c_180, c_1384])).
% 3.64/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.57  
% 3.64/1.57  Inference rules
% 3.64/1.57  ----------------------
% 3.64/1.57  #Ref     : 0
% 3.64/1.57  #Sup     : 306
% 3.64/1.57  #Fact    : 0
% 3.64/1.57  #Define  : 0
% 3.64/1.57  #Split   : 8
% 3.64/1.57  #Chain   : 0
% 3.64/1.57  #Close   : 0
% 3.64/1.57  
% 3.64/1.57  Ordering : KBO
% 3.64/1.57  
% 3.64/1.57  Simplification rules
% 3.64/1.57  ----------------------
% 3.64/1.57  #Subsume      : 10
% 3.64/1.57  #Demod        : 175
% 3.64/1.57  #Tautology    : 131
% 3.64/1.57  #SimpNegUnit  : 4
% 3.64/1.57  #BackRed      : 11
% 3.64/1.57  
% 3.64/1.57  #Partial instantiations: 0
% 3.64/1.57  #Strategies tried      : 1
% 3.64/1.57  
% 3.64/1.57  Timing (in seconds)
% 3.64/1.57  ----------------------
% 3.64/1.57  Preprocessing        : 0.33
% 3.64/1.57  Parsing              : 0.17
% 3.64/1.57  CNF conversion       : 0.02
% 3.64/1.57  Main loop            : 0.48
% 3.64/1.57  Inferencing          : 0.16
% 3.64/1.57  Reduction            : 0.16
% 3.64/1.57  Demodulation         : 0.11
% 3.64/1.57  BG Simplification    : 0.03
% 3.64/1.57  Subsumption          : 0.10
% 3.64/1.57  Abstraction          : 0.03
% 3.64/1.57  MUC search           : 0.00
% 3.64/1.57  Cooper               : 0.00
% 3.64/1.57  Total                : 0.84
% 3.64/1.57  Index Insertion      : 0.00
% 3.64/1.57  Index Deletion       : 0.00
% 3.64/1.57  Index Matching       : 0.00
% 3.64/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
