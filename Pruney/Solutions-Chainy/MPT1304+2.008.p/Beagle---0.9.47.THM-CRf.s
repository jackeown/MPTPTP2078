%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:50 EST 2020

% Result     : Theorem 8.48s
% Output     : CNFRefutation 8.72s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 108 expanded)
%              Number of leaves         :   29 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :   86 ( 176 expanded)
%              Number of equality atoms :   26 (  42 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( v1_tops_2(B,A)
                 => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tops_2)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( v1_tops_2(B,A)
               => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_tops_2)).

tff(c_26,plain,(
    v1_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_76,plain,(
    ! [A_45,B_46] :
      ( k4_xboole_0(A_45,B_46) = k3_subset_1(A_45,B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_89,plain,(
    ! [B_47,A_48] :
      ( k4_xboole_0(B_47,A_48) = k3_subset_1(B_47,A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(resolution,[status(thm)],[c_20,c_76])).

tff(c_101,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k4_xboole_0(A_1,B_2)) = k3_subset_1(A_1,k4_xboole_0(A_1,B_2)) ),
    inference(resolution,[status(thm)],[c_2,c_89])).

tff(c_106,plain,(
    ! [A_1,B_2] : k3_subset_1(A_1,k4_xboole_0(A_1,B_2)) = k3_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_101])).

tff(c_107,plain,(
    ! [A_49,B_50] :
      ( k3_subset_1(A_49,k3_subset_1(A_49,B_50)) = B_50
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_129,plain,(
    ! [B_53,A_54] :
      ( k3_subset_1(B_53,k3_subset_1(B_53,A_54)) = A_54
      | ~ r1_tarski(A_54,B_53) ) ),
    inference(resolution,[status(thm)],[c_20,c_107])).

tff(c_144,plain,(
    ! [A_1,B_2] :
      ( k3_subset_1(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2)
      | ~ r1_tarski(k4_xboole_0(A_1,B_2),A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_129])).

tff(c_150,plain,(
    ! [A_1,B_2] : k3_subset_1(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_144])).

tff(c_57,plain,(
    ! [A_41,B_42] : k4_xboole_0(A_41,k4_xboole_0(A_41,B_42)) = k3_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_66,plain,(
    ! [A_41,B_42] : r1_tarski(k3_xboole_0(A_41,B_42),A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_2])).

tff(c_102,plain,(
    ! [A_41,B_42] : k4_xboole_0(A_41,k3_xboole_0(A_41,B_42)) = k3_subset_1(A_41,k3_xboole_0(A_41,B_42)) ),
    inference(resolution,[status(thm)],[c_66,c_89])).

tff(c_344,plain,(
    ! [A_41,B_42] : k4_xboole_0(A_41,k3_xboole_0(A_41,B_42)) = k4_xboole_0(A_41,B_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_102])).

tff(c_60,plain,(
    ! [A_41,B_42] : k4_xboole_0(A_41,k3_xboole_0(A_41,B_42)) = k3_xboole_0(A_41,k4_xboole_0(A_41,B_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_4])).

tff(c_345,plain,(
    ! [A_41,B_42] : k3_xboole_0(A_41,k4_xboole_0(A_41,B_42)) = k4_xboole_0(A_41,B_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_60])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_519,plain,(
    ! [A_79,B_80,C_81] :
      ( k7_subset_1(A_79,B_80,C_81) = k4_xboole_0(B_80,C_81)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_587,plain,(
    ! [C_85] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_85) = k4_xboole_0('#skF_2',C_85) ),
    inference(resolution,[status(thm)],[c_30,c_519])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] :
      ( m1_subset_1(k7_subset_1(A_7,B_8,C_9),k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_596,plain,(
    ! [C_85] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_85),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_587,c_8])).

tff(c_604,plain,(
    ! [C_85] : m1_subset_1(k4_xboole_0('#skF_2',C_85),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_596])).

tff(c_531,plain,(
    ! [C_81] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_81) = k4_xboole_0('#skF_2',C_81) ),
    inference(resolution,[status(thm)],[c_30,c_519])).

tff(c_412,plain,(
    ! [A_71,B_72,C_73] :
      ( m1_subset_1(k7_subset_1(A_71,B_72,C_73),k1_zfmisc_1(A_71))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_15,B_16,C_17] :
      ( k9_subset_1(A_15,B_16,C_17) = k3_xboole_0(B_16,C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1413,plain,(
    ! [A_137,B_138,B_139,C_140] :
      ( k9_subset_1(A_137,B_138,k7_subset_1(A_137,B_139,C_140)) = k3_xboole_0(B_138,k7_subset_1(A_137,B_139,C_140))
      | ~ m1_subset_1(B_139,k1_zfmisc_1(A_137)) ) ),
    inference(resolution,[status(thm)],[c_412,c_14])).

tff(c_1437,plain,(
    ! [B_138,C_140] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_138,k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_140)) = k3_xboole_0(B_138,k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_140)) ),
    inference(resolution,[status(thm)],[c_30,c_1413])).

tff(c_1477,plain,(
    ! [B_143,C_144] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_143,k4_xboole_0('#skF_2',C_144)) = k3_xboole_0(B_143,k4_xboole_0('#skF_2',C_144)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_531,c_531,c_1437])).

tff(c_22,plain,(
    ! [A_22,B_26,C_28] :
      ( v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A_22)),B_26,C_28),A_22)
      | ~ v1_tops_2(B_26,A_22)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_22))))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_22))))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1483,plain,(
    ! [B_143,C_144] :
      ( v1_tops_2(k3_xboole_0(B_143,k4_xboole_0('#skF_2',C_144)),'#skF_1')
      | ~ v1_tops_2(B_143,'#skF_1')
      | ~ m1_subset_1(k4_xboole_0('#skF_2',C_144),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1(B_143,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1477,c_22])).

tff(c_13050,plain,(
    ! [B_506,C_507] :
      ( v1_tops_2(k3_xboole_0(B_506,k4_xboole_0('#skF_2',C_507)),'#skF_1')
      | ~ v1_tops_2(B_506,'#skF_1')
      | ~ m1_subset_1(B_506,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_604,c_1483])).

tff(c_13144,plain,(
    ! [C_507] :
      ( v1_tops_2(k3_xboole_0('#skF_2',k4_xboole_0('#skF_2',C_507)),'#skF_1')
      | ~ v1_tops_2('#skF_2','#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_13050])).

tff(c_13190,plain,(
    ! [C_507] : v1_tops_2(k4_xboole_0('#skF_2',C_507),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_345,c_13144])).

tff(c_24,plain,(
    ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_586,plain,(
    ~ v1_tops_2(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_531,c_24])).

tff(c_13197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13190,c_586])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:10:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.48/3.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.48/3.62  
% 8.48/3.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.48/3.62  %$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 8.48/3.62  
% 8.48/3.62  %Foreground sorts:
% 8.48/3.62  
% 8.48/3.62  
% 8.48/3.62  %Background operators:
% 8.48/3.62  
% 8.48/3.62  
% 8.48/3.62  %Foreground operators:
% 8.48/3.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.48/3.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.48/3.62  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 8.48/3.62  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.48/3.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.48/3.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.48/3.62  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 8.48/3.62  tff('#skF_2', type, '#skF_2': $i).
% 8.48/3.62  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 8.48/3.62  tff('#skF_3', type, '#skF_3': $i).
% 8.48/3.62  tff('#skF_1', type, '#skF_1': $i).
% 8.48/3.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.48/3.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.48/3.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.48/3.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.48/3.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.48/3.62  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 8.48/3.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.48/3.62  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.48/3.62  
% 8.72/3.63  tff(f_80, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_tops_2)).
% 8.72/3.63  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.72/3.63  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.72/3.63  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.72/3.63  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 8.72/3.63  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 8.72/3.63  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 8.72/3.63  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 8.72/3.63  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 8.72/3.63  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_tops_2)).
% 8.72/3.63  tff(c_26, plain, (v1_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.72/3.63  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.72/3.63  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.72/3.63  tff(c_20, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.72/3.63  tff(c_76, plain, (![A_45, B_46]: (k4_xboole_0(A_45, B_46)=k3_subset_1(A_45, B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.72/3.63  tff(c_89, plain, (![B_47, A_48]: (k4_xboole_0(B_47, A_48)=k3_subset_1(B_47, A_48) | ~r1_tarski(A_48, B_47))), inference(resolution, [status(thm)], [c_20, c_76])).
% 8.72/3.63  tff(c_101, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k4_xboole_0(A_1, B_2))=k3_subset_1(A_1, k4_xboole_0(A_1, B_2)))), inference(resolution, [status(thm)], [c_2, c_89])).
% 8.72/3.63  tff(c_106, plain, (![A_1, B_2]: (k3_subset_1(A_1, k4_xboole_0(A_1, B_2))=k3_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_101])).
% 8.72/3.63  tff(c_107, plain, (![A_49, B_50]: (k3_subset_1(A_49, k3_subset_1(A_49, B_50))=B_50 | ~m1_subset_1(B_50, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.72/3.63  tff(c_129, plain, (![B_53, A_54]: (k3_subset_1(B_53, k3_subset_1(B_53, A_54))=A_54 | ~r1_tarski(A_54, B_53))), inference(resolution, [status(thm)], [c_20, c_107])).
% 8.72/3.63  tff(c_144, plain, (![A_1, B_2]: (k3_subset_1(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2) | ~r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(superposition, [status(thm), theory('equality')], [c_106, c_129])).
% 8.72/3.63  tff(c_150, plain, (![A_1, B_2]: (k3_subset_1(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_144])).
% 8.72/3.63  tff(c_57, plain, (![A_41, B_42]: (k4_xboole_0(A_41, k4_xboole_0(A_41, B_42))=k3_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.72/3.63  tff(c_66, plain, (![A_41, B_42]: (r1_tarski(k3_xboole_0(A_41, B_42), A_41))), inference(superposition, [status(thm), theory('equality')], [c_57, c_2])).
% 8.72/3.63  tff(c_102, plain, (![A_41, B_42]: (k4_xboole_0(A_41, k3_xboole_0(A_41, B_42))=k3_subset_1(A_41, k3_xboole_0(A_41, B_42)))), inference(resolution, [status(thm)], [c_66, c_89])).
% 8.72/3.63  tff(c_344, plain, (![A_41, B_42]: (k4_xboole_0(A_41, k3_xboole_0(A_41, B_42))=k4_xboole_0(A_41, B_42))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_102])).
% 8.72/3.63  tff(c_60, plain, (![A_41, B_42]: (k4_xboole_0(A_41, k3_xboole_0(A_41, B_42))=k3_xboole_0(A_41, k4_xboole_0(A_41, B_42)))), inference(superposition, [status(thm), theory('equality')], [c_57, c_4])).
% 8.72/3.63  tff(c_345, plain, (![A_41, B_42]: (k3_xboole_0(A_41, k4_xboole_0(A_41, B_42))=k4_xboole_0(A_41, B_42))), inference(demodulation, [status(thm), theory('equality')], [c_344, c_60])).
% 8.72/3.63  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.72/3.63  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.72/3.63  tff(c_519, plain, (![A_79, B_80, C_81]: (k7_subset_1(A_79, B_80, C_81)=k4_xboole_0(B_80, C_81) | ~m1_subset_1(B_80, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.72/3.63  tff(c_587, plain, (![C_85]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_85)=k4_xboole_0('#skF_2', C_85))), inference(resolution, [status(thm)], [c_30, c_519])).
% 8.72/3.63  tff(c_8, plain, (![A_7, B_8, C_9]: (m1_subset_1(k7_subset_1(A_7, B_8, C_9), k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.72/3.63  tff(c_596, plain, (![C_85]: (m1_subset_1(k4_xboole_0('#skF_2', C_85), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_587, c_8])).
% 8.72/3.63  tff(c_604, plain, (![C_85]: (m1_subset_1(k4_xboole_0('#skF_2', C_85), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_596])).
% 8.72/3.63  tff(c_531, plain, (![C_81]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_81)=k4_xboole_0('#skF_2', C_81))), inference(resolution, [status(thm)], [c_30, c_519])).
% 8.72/3.63  tff(c_412, plain, (![A_71, B_72, C_73]: (m1_subset_1(k7_subset_1(A_71, B_72, C_73), k1_zfmisc_1(A_71)) | ~m1_subset_1(B_72, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.72/3.63  tff(c_14, plain, (![A_15, B_16, C_17]: (k9_subset_1(A_15, B_16, C_17)=k3_xboole_0(B_16, C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.72/3.63  tff(c_1413, plain, (![A_137, B_138, B_139, C_140]: (k9_subset_1(A_137, B_138, k7_subset_1(A_137, B_139, C_140))=k3_xboole_0(B_138, k7_subset_1(A_137, B_139, C_140)) | ~m1_subset_1(B_139, k1_zfmisc_1(A_137)))), inference(resolution, [status(thm)], [c_412, c_14])).
% 8.72/3.63  tff(c_1437, plain, (![B_138, C_140]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_138, k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_140))=k3_xboole_0(B_138, k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_140)))), inference(resolution, [status(thm)], [c_30, c_1413])).
% 8.72/3.63  tff(c_1477, plain, (![B_143, C_144]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_143, k4_xboole_0('#skF_2', C_144))=k3_xboole_0(B_143, k4_xboole_0('#skF_2', C_144)))), inference(demodulation, [status(thm), theory('equality')], [c_531, c_531, c_1437])).
% 8.72/3.63  tff(c_22, plain, (![A_22, B_26, C_28]: (v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A_22)), B_26, C_28), A_22) | ~v1_tops_2(B_26, A_22) | ~m1_subset_1(C_28, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_22)))) | ~m1_subset_1(B_26, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_22)))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.72/3.63  tff(c_1483, plain, (![B_143, C_144]: (v1_tops_2(k3_xboole_0(B_143, k4_xboole_0('#skF_2', C_144)), '#skF_1') | ~v1_tops_2(B_143, '#skF_1') | ~m1_subset_1(k4_xboole_0('#skF_2', C_144), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1(B_143, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1477, c_22])).
% 8.72/3.63  tff(c_13050, plain, (![B_506, C_507]: (v1_tops_2(k3_xboole_0(B_506, k4_xboole_0('#skF_2', C_507)), '#skF_1') | ~v1_tops_2(B_506, '#skF_1') | ~m1_subset_1(B_506, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_604, c_1483])).
% 8.72/3.63  tff(c_13144, plain, (![C_507]: (v1_tops_2(k3_xboole_0('#skF_2', k4_xboole_0('#skF_2', C_507)), '#skF_1') | ~v1_tops_2('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_30, c_13050])).
% 8.72/3.63  tff(c_13190, plain, (![C_507]: (v1_tops_2(k4_xboole_0('#skF_2', C_507), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_345, c_13144])).
% 8.72/3.63  tff(c_24, plain, (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.72/3.63  tff(c_586, plain, (~v1_tops_2(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_531, c_24])).
% 8.72/3.63  tff(c_13197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13190, c_586])).
% 8.72/3.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.72/3.63  
% 8.72/3.63  Inference rules
% 8.72/3.63  ----------------------
% 8.72/3.63  #Ref     : 0
% 8.72/3.63  #Sup     : 3204
% 8.72/3.63  #Fact    : 0
% 8.72/3.63  #Define  : 0
% 8.72/3.63  #Split   : 3
% 8.72/3.63  #Chain   : 0
% 8.72/3.63  #Close   : 0
% 8.72/3.63  
% 8.72/3.63  Ordering : KBO
% 8.72/3.63  
% 8.72/3.63  Simplification rules
% 8.72/3.63  ----------------------
% 8.72/3.63  #Subsume      : 68
% 8.72/3.63  #Demod        : 1419
% 8.72/3.63  #Tautology    : 874
% 8.72/3.63  #SimpNegUnit  : 0
% 8.72/3.63  #BackRed      : 5
% 8.72/3.63  
% 8.72/3.63  #Partial instantiations: 0
% 8.72/3.63  #Strategies tried      : 1
% 8.72/3.63  
% 8.72/3.63  Timing (in seconds)
% 8.72/3.63  ----------------------
% 8.72/3.64  Preprocessing        : 0.29
% 8.72/3.64  Parsing              : 0.16
% 8.72/3.64  CNF conversion       : 0.02
% 8.72/3.64  Main loop            : 2.48
% 8.72/3.64  Inferencing          : 0.62
% 8.72/3.64  Reduction            : 1.16
% 8.72/3.64  Demodulation         : 0.97
% 8.72/3.64  BG Simplification    : 0.09
% 8.72/3.64  Subsumption          : 0.46
% 8.72/3.64  Abstraction          : 0.13
% 8.72/3.64  MUC search           : 0.00
% 8.72/3.64  Cooper               : 0.00
% 8.72/3.64  Total                : 2.80
% 8.72/3.64  Index Insertion      : 0.00
% 8.72/3.64  Index Deletion       : 0.00
% 8.72/3.64  Index Matching       : 0.00
% 8.72/3.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
