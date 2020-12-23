%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:28 EST 2020

% Result     : Theorem 4.67s
% Output     : CNFRefutation 5.01s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 350 expanded)
%              Number of leaves         :   39 ( 135 expanded)
%              Depth                    :   15
%              Number of atoms          :  174 ( 553 expanded)
%              Number of equality atoms :   84 ( 246 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_37,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2746,plain,(
    ! [A_206,B_207,C_208] :
      ( k7_subset_1(A_206,B_207,C_208) = k4_xboole_0(B_207,C_208)
      | ~ m1_subset_1(B_207,k1_zfmisc_1(A_206)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2752,plain,(
    ! [C_208] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_208) = k4_xboole_0('#skF_2',C_208) ),
    inference(resolution,[status(thm)],[c_40,c_2746])).

tff(c_46,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_182,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1129,plain,(
    ! [B_111,A_112] :
      ( v4_pre_topc(B_111,A_112)
      | k2_pre_topc(A_112,B_111) != B_111
      | ~ v2_pre_topc(A_112)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1139,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1129])).

tff(c_1144,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_1139])).

tff(c_1145,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_1144])).

tff(c_461,plain,(
    ! [A_77,B_78,C_79] :
      ( k7_subset_1(A_77,B_78,C_79) = k4_xboole_0(B_78,C_79)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_468,plain,(
    ! [C_80] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_80) = k4_xboole_0('#skF_2',C_80) ),
    inference(resolution,[status(thm)],[c_40,c_461])).

tff(c_52,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_107,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_474,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_468,c_107])).

tff(c_126,plain,(
    ! [A_53,B_54] : k4_xboole_0(A_53,k4_xboole_0(A_53,B_54)) = k3_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_138,plain,(
    ! [A_53,B_54] : r1_tarski(k3_xboole_0(A_53,B_54),A_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_135,plain,(
    ! [A_53,B_54] : k2_xboole_0(k4_xboole_0(A_53,B_54),k3_xboole_0(A_53,B_54)) = k2_xboole_0(k4_xboole_0(A_53,B_54),A_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_8])).

tff(c_1214,plain,(
    ! [A_117,B_118] : k2_xboole_0(k4_xboole_0(A_117,B_118),k3_xboole_0(A_117,B_118)) = k2_xboole_0(A_117,k4_xboole_0(A_117,B_118)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_135])).

tff(c_1220,plain,(
    ! [A_117,B_118] : k2_xboole_0(k3_xboole_0(A_117,B_118),k4_xboole_0(A_117,B_118)) = k2_xboole_0(A_117,k4_xboole_0(A_117,B_118)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1214,c_2])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(A_24,k1_zfmisc_1(B_25))
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_156,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(A_59,B_60) = k3_subset_1(A_59,B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_218,plain,(
    ! [B_63,A_64] :
      ( k4_xboole_0(B_63,A_64) = k3_subset_1(B_63,A_64)
      | ~ r1_tarski(A_64,B_63) ) ),
    inference(resolution,[status(thm)],[c_26,c_156])).

tff(c_230,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_subset_1(A_5,k4_xboole_0(A_5,B_6)) ),
    inference(resolution,[status(thm)],[c_6,c_218])).

tff(c_238,plain,(
    ! [A_65,B_66] : k3_subset_1(A_65,k4_xboole_0(A_65,B_66)) = k3_xboole_0(A_65,B_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_230])).

tff(c_149,plain,(
    ! [A_57,B_58] :
      ( k3_subset_1(A_57,k3_subset_1(A_57,B_58)) = B_58
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_154,plain,(
    ! [B_25,A_24] :
      ( k3_subset_1(B_25,k3_subset_1(B_25,A_24)) = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(resolution,[status(thm)],[c_26,c_149])).

tff(c_244,plain,(
    ! [A_65,B_66] :
      ( k3_subset_1(A_65,k3_xboole_0(A_65,B_66)) = k4_xboole_0(A_65,B_66)
      | ~ r1_tarski(k4_xboole_0(A_65,B_66),A_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_154])).

tff(c_256,plain,(
    ! [A_65,B_66] : k3_subset_1(A_65,k3_xboole_0(A_65,B_66)) = k4_xboole_0(A_65,B_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_244])).

tff(c_233,plain,(
    ! [A_53,B_54] : k4_xboole_0(A_53,k3_xboole_0(A_53,B_54)) = k3_subset_1(A_53,k3_xboole_0(A_53,B_54)) ),
    inference(resolution,[status(thm)],[c_138,c_218])).

tff(c_348,plain,(
    ! [A_53,B_54] : k4_xboole_0(A_53,k3_xboole_0(A_53,B_54)) = k4_xboole_0(A_53,B_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_233])).

tff(c_141,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,k4_xboole_0(A_9,B_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_126])).

tff(c_349,plain,(
    ! [A_9,B_10] : k3_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_141])).

tff(c_1301,plain,(
    ! [A_121,B_122] : k2_xboole_0(k3_xboole_0(A_121,B_122),k4_xboole_0(A_121,B_122)) = k2_xboole_0(A_121,k4_xboole_0(A_121,B_122)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1214,c_2])).

tff(c_1346,plain,(
    ! [A_9,B_10] : k2_xboole_0(k3_xboole_0(A_9,k4_xboole_0(A_9,B_10)),k3_xboole_0(A_9,B_10)) = k2_xboole_0(A_9,k4_xboole_0(A_9,k4_xboole_0(A_9,B_10))) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1301])).

tff(c_1361,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k2_xboole_0(A_9,k3_xboole_0(A_9,B_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1220,c_2,c_349,c_10,c_1346])).

tff(c_1271,plain,(
    ! [A_117,B_118] : k2_xboole_0(k3_xboole_0(A_117,B_118),k4_xboole_0(A_117,B_118)) = k2_xboole_0(A_117,k4_xboole_0(A_117,B_118)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1214])).

tff(c_1419,plain,(
    ! [A_117,B_118] : k2_xboole_0(k3_xboole_0(A_117,B_118),k4_xboole_0(A_117,B_118)) = k2_xboole_0(A_117,k3_xboole_0(A_117,B_118)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1361,c_1271])).

tff(c_1074,plain,(
    ! [A_107,B_108,C_109] :
      ( k4_subset_1(A_107,B_108,C_109) = k2_xboole_0(B_108,C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(A_107))
      | ~ m1_subset_1(B_108,k1_zfmisc_1(A_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1740,plain,(
    ! [B_138,B_139,A_140] :
      ( k4_subset_1(B_138,B_139,A_140) = k2_xboole_0(B_139,A_140)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(B_138))
      | ~ r1_tarski(A_140,B_138) ) ),
    inference(resolution,[status(thm)],[c_26,c_1074])).

tff(c_1778,plain,(
    ! [B_142,A_143,A_144] :
      ( k4_subset_1(B_142,A_143,A_144) = k2_xboole_0(A_143,A_144)
      | ~ r1_tarski(A_144,B_142)
      | ~ r1_tarski(A_143,B_142) ) ),
    inference(resolution,[status(thm)],[c_26,c_1740])).

tff(c_1829,plain,(
    ! [A_146,A_147,B_148] :
      ( k4_subset_1(A_146,A_147,k4_xboole_0(A_146,B_148)) = k2_xboole_0(A_147,k4_xboole_0(A_146,B_148))
      | ~ r1_tarski(A_147,A_146) ) ),
    inference(resolution,[status(thm)],[c_6,c_1778])).

tff(c_237,plain,(
    ! [A_5,B_6] : k3_subset_1(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_230])).

tff(c_12,plain,(
    ! [A_11] : k2_subset_1(A_11) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [A_22,B_23] :
      ( k4_subset_1(A_22,B_23,k3_subset_1(A_22,B_23)) = k2_subset_1(A_22)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_565,plain,(
    ! [A_83,B_84] :
      ( k4_subset_1(A_83,B_84,k3_subset_1(A_83,B_84)) = A_83
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_83)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_22])).

tff(c_589,plain,(
    ! [B_88,A_89] :
      ( k4_subset_1(B_88,A_89,k3_subset_1(B_88,A_89)) = B_88
      | ~ r1_tarski(A_89,B_88) ) ),
    inference(resolution,[status(thm)],[c_26,c_565])).

tff(c_601,plain,(
    ! [A_5,B_6] :
      ( k4_subset_1(A_5,k4_xboole_0(A_5,B_6),k3_xboole_0(A_5,B_6)) = A_5
      | ~ r1_tarski(k4_xboole_0(A_5,B_6),A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_589])).

tff(c_616,plain,(
    ! [A_90,B_91] : k4_subset_1(A_90,k4_xboole_0(A_90,B_91),k3_xboole_0(A_90,B_91)) = A_90 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_601])).

tff(c_649,plain,(
    ! [A_9,B_10] : k4_subset_1(A_9,k3_xboole_0(A_9,B_10),k3_xboole_0(A_9,k4_xboole_0(A_9,B_10))) = A_9 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_616])).

tff(c_657,plain,(
    ! [A_9,B_10] : k4_subset_1(A_9,k3_xboole_0(A_9,B_10),k4_xboole_0(A_9,B_10)) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_649])).

tff(c_1836,plain,(
    ! [A_146,B_148] :
      ( k2_xboole_0(k3_xboole_0(A_146,B_148),k4_xboole_0(A_146,B_148)) = A_146
      | ~ r1_tarski(k3_xboole_0(A_146,B_148),A_146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1829,c_657])).

tff(c_1866,plain,(
    ! [A_146,B_148] : k2_xboole_0(A_146,k3_xboole_0(A_146,B_148)) = A_146 ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_1419,c_1836])).

tff(c_1952,plain,(
    ! [A_154,B_155] : k2_xboole_0(A_154,k4_xboole_0(A_154,B_155)) = A_154 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1866,c_1361])).

tff(c_1971,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_474,c_1952])).

tff(c_1183,plain,(
    ! [A_114,B_115] :
      ( k4_subset_1(u1_struct_0(A_114),B_115,k2_tops_1(A_114,B_115)) = k2_pre_topc(A_114,B_115)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1190,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1183])).

tff(c_1195,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1190])).

tff(c_933,plain,(
    ! [A_98,B_99] :
      ( m1_subset_1(k2_tops_1(A_98,B_99),k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_24,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | ~ m1_subset_1(A_24,k1_zfmisc_1(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_957,plain,(
    ! [A_98,B_99] :
      ( r1_tarski(k2_tops_1(A_98,B_99),u1_struct_0(A_98))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(resolution,[status(thm)],[c_933,c_24])).

tff(c_1750,plain,(
    ! [A_141] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_141) = k2_xboole_0('#skF_2',A_141)
      | ~ r1_tarski(A_141,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_40,c_1740])).

tff(c_1754,plain,(
    ! [B_99] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_99)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_99))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_957,c_1750])).

tff(c_2240,plain,(
    ! [B_163] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_163)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_163))
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1754])).

tff(c_2251,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_2240])).

tff(c_2257,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1971,c_1195,c_2251])).

tff(c_2259,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1145,c_2257])).

tff(c_2260,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_2391,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2260,c_107])).

tff(c_2393,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2753,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2752,c_2393])).

tff(c_2392,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_3082,plain,(
    ! [A_227,B_228] :
      ( k2_pre_topc(A_227,B_228) = B_228
      | ~ v4_pre_topc(B_228,A_227)
      | ~ m1_subset_1(B_228,k1_zfmisc_1(u1_struct_0(A_227)))
      | ~ l1_pre_topc(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3092,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_3082])).

tff(c_3097,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2392,c_3092])).

tff(c_3438,plain,(
    ! [A_247,B_248] :
      ( k7_subset_1(u1_struct_0(A_247),k2_pre_topc(A_247,B_248),k1_tops_1(A_247,B_248)) = k2_tops_1(A_247,B_248)
      | ~ m1_subset_1(B_248,k1_zfmisc_1(u1_struct_0(A_247)))
      | ~ l1_pre_topc(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3447,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3097,c_3438])).

tff(c_3451,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_2752,c_3447])).

tff(c_3453,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2753,c_3451])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:39:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.67/1.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.67/1.90  
% 4.67/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.67/1.90  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 4.67/1.90  
% 4.67/1.90  %Foreground sorts:
% 4.67/1.90  
% 4.67/1.90  
% 4.67/1.90  %Background operators:
% 4.67/1.90  
% 4.67/1.90  
% 4.67/1.90  %Foreground operators:
% 4.67/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.67/1.90  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.67/1.90  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.67/1.90  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.67/1.90  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.67/1.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.67/1.90  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.67/1.90  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.67/1.90  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.67/1.90  tff('#skF_2', type, '#skF_2': $i).
% 4.67/1.90  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.67/1.90  tff('#skF_1', type, '#skF_1': $i).
% 4.67/1.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.67/1.90  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.67/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.67/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.67/1.90  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.67/1.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.67/1.90  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.67/1.90  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.67/1.90  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.67/1.90  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.67/1.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.67/1.90  
% 5.01/1.92  tff(f_118, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 5.01/1.92  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.01/1.92  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.01/1.92  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.01/1.92  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.01/1.92  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.01/1.92  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.01/1.92  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.01/1.92  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 5.01/1.92  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 5.01/1.92  tff(f_51, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.01/1.92  tff(f_37, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.01/1.92  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 5.01/1.92  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 5.01/1.92  tff(f_84, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.01/1.92  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 5.01/1.92  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.01/1.92  tff(c_2746, plain, (![A_206, B_207, C_208]: (k7_subset_1(A_206, B_207, C_208)=k4_xboole_0(B_207, C_208) | ~m1_subset_1(B_207, k1_zfmisc_1(A_206)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.01/1.92  tff(c_2752, plain, (![C_208]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_208)=k4_xboole_0('#skF_2', C_208))), inference(resolution, [status(thm)], [c_40, c_2746])).
% 5.01/1.92  tff(c_46, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.01/1.92  tff(c_182, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 5.01/1.92  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.01/1.92  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.01/1.92  tff(c_1129, plain, (![B_111, A_112]: (v4_pre_topc(B_111, A_112) | k2_pre_topc(A_112, B_111)!=B_111 | ~v2_pre_topc(A_112) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.01/1.92  tff(c_1139, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1129])).
% 5.01/1.92  tff(c_1144, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_1139])).
% 5.01/1.92  tff(c_1145, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_182, c_1144])).
% 5.01/1.92  tff(c_461, plain, (![A_77, B_78, C_79]: (k7_subset_1(A_77, B_78, C_79)=k4_xboole_0(B_78, C_79) | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.01/1.92  tff(c_468, plain, (![C_80]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_80)=k4_xboole_0('#skF_2', C_80))), inference(resolution, [status(thm)], [c_40, c_461])).
% 5.01/1.92  tff(c_52, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.01/1.92  tff(c_107, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_52])).
% 5.01/1.92  tff(c_474, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_468, c_107])).
% 5.01/1.92  tff(c_126, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k4_xboole_0(A_53, B_54))=k3_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.01/1.92  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.01/1.92  tff(c_138, plain, (![A_53, B_54]: (r1_tarski(k3_xboole_0(A_53, B_54), A_53))), inference(superposition, [status(thm), theory('equality')], [c_126, c_6])).
% 5.01/1.92  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.01/1.92  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.01/1.92  tff(c_135, plain, (![A_53, B_54]: (k2_xboole_0(k4_xboole_0(A_53, B_54), k3_xboole_0(A_53, B_54))=k2_xboole_0(k4_xboole_0(A_53, B_54), A_53))), inference(superposition, [status(thm), theory('equality')], [c_126, c_8])).
% 5.01/1.92  tff(c_1214, plain, (![A_117, B_118]: (k2_xboole_0(k4_xboole_0(A_117, B_118), k3_xboole_0(A_117, B_118))=k2_xboole_0(A_117, k4_xboole_0(A_117, B_118)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_135])).
% 5.01/1.92  tff(c_1220, plain, (![A_117, B_118]: (k2_xboole_0(k3_xboole_0(A_117, B_118), k4_xboole_0(A_117, B_118))=k2_xboole_0(A_117, k4_xboole_0(A_117, B_118)))), inference(superposition, [status(thm), theory('equality')], [c_1214, c_2])).
% 5.01/1.92  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.01/1.92  tff(c_26, plain, (![A_24, B_25]: (m1_subset_1(A_24, k1_zfmisc_1(B_25)) | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.01/1.92  tff(c_156, plain, (![A_59, B_60]: (k4_xboole_0(A_59, B_60)=k3_subset_1(A_59, B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.01/1.92  tff(c_218, plain, (![B_63, A_64]: (k4_xboole_0(B_63, A_64)=k3_subset_1(B_63, A_64) | ~r1_tarski(A_64, B_63))), inference(resolution, [status(thm)], [c_26, c_156])).
% 5.01/1.92  tff(c_230, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_subset_1(A_5, k4_xboole_0(A_5, B_6)))), inference(resolution, [status(thm)], [c_6, c_218])).
% 5.01/1.92  tff(c_238, plain, (![A_65, B_66]: (k3_subset_1(A_65, k4_xboole_0(A_65, B_66))=k3_xboole_0(A_65, B_66))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_230])).
% 5.01/1.92  tff(c_149, plain, (![A_57, B_58]: (k3_subset_1(A_57, k3_subset_1(A_57, B_58))=B_58 | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.01/1.92  tff(c_154, plain, (![B_25, A_24]: (k3_subset_1(B_25, k3_subset_1(B_25, A_24))=A_24 | ~r1_tarski(A_24, B_25))), inference(resolution, [status(thm)], [c_26, c_149])).
% 5.01/1.92  tff(c_244, plain, (![A_65, B_66]: (k3_subset_1(A_65, k3_xboole_0(A_65, B_66))=k4_xboole_0(A_65, B_66) | ~r1_tarski(k4_xboole_0(A_65, B_66), A_65))), inference(superposition, [status(thm), theory('equality')], [c_238, c_154])).
% 5.01/1.92  tff(c_256, plain, (![A_65, B_66]: (k3_subset_1(A_65, k3_xboole_0(A_65, B_66))=k4_xboole_0(A_65, B_66))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_244])).
% 5.01/1.92  tff(c_233, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k3_xboole_0(A_53, B_54))=k3_subset_1(A_53, k3_xboole_0(A_53, B_54)))), inference(resolution, [status(thm)], [c_138, c_218])).
% 5.01/1.92  tff(c_348, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k3_xboole_0(A_53, B_54))=k4_xboole_0(A_53, B_54))), inference(demodulation, [status(thm), theory('equality')], [c_256, c_233])).
% 5.01/1.92  tff(c_141, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k3_xboole_0(A_9, k4_xboole_0(A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_126])).
% 5.01/1.92  tff(c_349, plain, (![A_9, B_10]: (k3_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(demodulation, [status(thm), theory('equality')], [c_348, c_141])).
% 5.01/1.92  tff(c_1301, plain, (![A_121, B_122]: (k2_xboole_0(k3_xboole_0(A_121, B_122), k4_xboole_0(A_121, B_122))=k2_xboole_0(A_121, k4_xboole_0(A_121, B_122)))), inference(superposition, [status(thm), theory('equality')], [c_1214, c_2])).
% 5.01/1.92  tff(c_1346, plain, (![A_9, B_10]: (k2_xboole_0(k3_xboole_0(A_9, k4_xboole_0(A_9, B_10)), k3_xboole_0(A_9, B_10))=k2_xboole_0(A_9, k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1301])).
% 5.01/1.92  tff(c_1361, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k2_xboole_0(A_9, k3_xboole_0(A_9, B_10)))), inference(demodulation, [status(thm), theory('equality')], [c_1220, c_2, c_349, c_10, c_1346])).
% 5.01/1.92  tff(c_1271, plain, (![A_117, B_118]: (k2_xboole_0(k3_xboole_0(A_117, B_118), k4_xboole_0(A_117, B_118))=k2_xboole_0(A_117, k4_xboole_0(A_117, B_118)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1214])).
% 5.01/1.92  tff(c_1419, plain, (![A_117, B_118]: (k2_xboole_0(k3_xboole_0(A_117, B_118), k4_xboole_0(A_117, B_118))=k2_xboole_0(A_117, k3_xboole_0(A_117, B_118)))), inference(demodulation, [status(thm), theory('equality')], [c_1361, c_1271])).
% 5.01/1.92  tff(c_1074, plain, (![A_107, B_108, C_109]: (k4_subset_1(A_107, B_108, C_109)=k2_xboole_0(B_108, C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(A_107)) | ~m1_subset_1(B_108, k1_zfmisc_1(A_107)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.01/1.92  tff(c_1740, plain, (![B_138, B_139, A_140]: (k4_subset_1(B_138, B_139, A_140)=k2_xboole_0(B_139, A_140) | ~m1_subset_1(B_139, k1_zfmisc_1(B_138)) | ~r1_tarski(A_140, B_138))), inference(resolution, [status(thm)], [c_26, c_1074])).
% 5.01/1.92  tff(c_1778, plain, (![B_142, A_143, A_144]: (k4_subset_1(B_142, A_143, A_144)=k2_xboole_0(A_143, A_144) | ~r1_tarski(A_144, B_142) | ~r1_tarski(A_143, B_142))), inference(resolution, [status(thm)], [c_26, c_1740])).
% 5.01/1.92  tff(c_1829, plain, (![A_146, A_147, B_148]: (k4_subset_1(A_146, A_147, k4_xboole_0(A_146, B_148))=k2_xboole_0(A_147, k4_xboole_0(A_146, B_148)) | ~r1_tarski(A_147, A_146))), inference(resolution, [status(thm)], [c_6, c_1778])).
% 5.01/1.92  tff(c_237, plain, (![A_5, B_6]: (k3_subset_1(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_230])).
% 5.01/1.92  tff(c_12, plain, (![A_11]: (k2_subset_1(A_11)=A_11)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.01/1.92  tff(c_22, plain, (![A_22, B_23]: (k4_subset_1(A_22, B_23, k3_subset_1(A_22, B_23))=k2_subset_1(A_22) | ~m1_subset_1(B_23, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.01/1.92  tff(c_565, plain, (![A_83, B_84]: (k4_subset_1(A_83, B_84, k3_subset_1(A_83, B_84))=A_83 | ~m1_subset_1(B_84, k1_zfmisc_1(A_83)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_22])).
% 5.01/1.92  tff(c_589, plain, (![B_88, A_89]: (k4_subset_1(B_88, A_89, k3_subset_1(B_88, A_89))=B_88 | ~r1_tarski(A_89, B_88))), inference(resolution, [status(thm)], [c_26, c_565])).
% 5.01/1.92  tff(c_601, plain, (![A_5, B_6]: (k4_subset_1(A_5, k4_xboole_0(A_5, B_6), k3_xboole_0(A_5, B_6))=A_5 | ~r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(superposition, [status(thm), theory('equality')], [c_237, c_589])).
% 5.01/1.92  tff(c_616, plain, (![A_90, B_91]: (k4_subset_1(A_90, k4_xboole_0(A_90, B_91), k3_xboole_0(A_90, B_91))=A_90)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_601])).
% 5.01/1.92  tff(c_649, plain, (![A_9, B_10]: (k4_subset_1(A_9, k3_xboole_0(A_9, B_10), k3_xboole_0(A_9, k4_xboole_0(A_9, B_10)))=A_9)), inference(superposition, [status(thm), theory('equality')], [c_10, c_616])).
% 5.01/1.92  tff(c_657, plain, (![A_9, B_10]: (k4_subset_1(A_9, k3_xboole_0(A_9, B_10), k4_xboole_0(A_9, B_10))=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_349, c_649])).
% 5.01/1.92  tff(c_1836, plain, (![A_146, B_148]: (k2_xboole_0(k3_xboole_0(A_146, B_148), k4_xboole_0(A_146, B_148))=A_146 | ~r1_tarski(k3_xboole_0(A_146, B_148), A_146))), inference(superposition, [status(thm), theory('equality')], [c_1829, c_657])).
% 5.01/1.92  tff(c_1866, plain, (![A_146, B_148]: (k2_xboole_0(A_146, k3_xboole_0(A_146, B_148))=A_146)), inference(demodulation, [status(thm), theory('equality')], [c_138, c_1419, c_1836])).
% 5.01/1.92  tff(c_1952, plain, (![A_154, B_155]: (k2_xboole_0(A_154, k4_xboole_0(A_154, B_155))=A_154)), inference(demodulation, [status(thm), theory('equality')], [c_1866, c_1361])).
% 5.01/1.92  tff(c_1971, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_474, c_1952])).
% 5.01/1.92  tff(c_1183, plain, (![A_114, B_115]: (k4_subset_1(u1_struct_0(A_114), B_115, k2_tops_1(A_114, B_115))=k2_pre_topc(A_114, B_115) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.01/1.92  tff(c_1190, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1183])).
% 5.01/1.92  tff(c_1195, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1190])).
% 5.01/1.92  tff(c_933, plain, (![A_98, B_99]: (m1_subset_1(k2_tops_1(A_98, B_99), k1_zfmisc_1(u1_struct_0(A_98))) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.01/1.92  tff(c_24, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | ~m1_subset_1(A_24, k1_zfmisc_1(B_25)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.01/1.92  tff(c_957, plain, (![A_98, B_99]: (r1_tarski(k2_tops_1(A_98, B_99), u1_struct_0(A_98)) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98))), inference(resolution, [status(thm)], [c_933, c_24])).
% 5.01/1.92  tff(c_1750, plain, (![A_141]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_141)=k2_xboole_0('#skF_2', A_141) | ~r1_tarski(A_141, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_40, c_1740])).
% 5.01/1.92  tff(c_1754, plain, (![B_99]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_99))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_99)) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_957, c_1750])).
% 5.01/1.92  tff(c_2240, plain, (![B_163]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_163))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_163)) | ~m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1754])).
% 5.01/1.92  tff(c_2251, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_2240])).
% 5.01/1.92  tff(c_2257, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1971, c_1195, c_2251])).
% 5.01/1.92  tff(c_2259, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1145, c_2257])).
% 5.01/1.92  tff(c_2260, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 5.01/1.92  tff(c_2391, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2260, c_107])).
% 5.01/1.92  tff(c_2393, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 5.01/1.92  tff(c_2753, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2752, c_2393])).
% 5.01/1.92  tff(c_2392, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 5.01/1.92  tff(c_3082, plain, (![A_227, B_228]: (k2_pre_topc(A_227, B_228)=B_228 | ~v4_pre_topc(B_228, A_227) | ~m1_subset_1(B_228, k1_zfmisc_1(u1_struct_0(A_227))) | ~l1_pre_topc(A_227))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.01/1.92  tff(c_3092, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_3082])).
% 5.01/1.92  tff(c_3097, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2392, c_3092])).
% 5.01/1.92  tff(c_3438, plain, (![A_247, B_248]: (k7_subset_1(u1_struct_0(A_247), k2_pre_topc(A_247, B_248), k1_tops_1(A_247, B_248))=k2_tops_1(A_247, B_248) | ~m1_subset_1(B_248, k1_zfmisc_1(u1_struct_0(A_247))) | ~l1_pre_topc(A_247))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.01/1.92  tff(c_3447, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3097, c_3438])).
% 5.01/1.92  tff(c_3451, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_2752, c_3447])).
% 5.01/1.92  tff(c_3453, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2753, c_3451])).
% 5.01/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.01/1.92  
% 5.01/1.92  Inference rules
% 5.01/1.92  ----------------------
% 5.01/1.92  #Ref     : 0
% 5.01/1.92  #Sup     : 845
% 5.01/1.92  #Fact    : 0
% 5.01/1.92  #Define  : 0
% 5.01/1.92  #Split   : 2
% 5.01/1.92  #Chain   : 0
% 5.01/1.92  #Close   : 0
% 5.01/1.92  
% 5.01/1.92  Ordering : KBO
% 5.01/1.92  
% 5.01/1.92  Simplification rules
% 5.01/1.92  ----------------------
% 5.01/1.92  #Subsume      : 16
% 5.01/1.92  #Demod        : 928
% 5.01/1.92  #Tautology    : 586
% 5.01/1.92  #SimpNegUnit  : 6
% 5.01/1.92  #BackRed      : 21
% 5.01/1.92  
% 5.01/1.92  #Partial instantiations: 0
% 5.01/1.92  #Strategies tried      : 1
% 5.01/1.92  
% 5.01/1.92  Timing (in seconds)
% 5.01/1.93  ----------------------
% 5.01/1.93  Preprocessing        : 0.34
% 5.01/1.93  Parsing              : 0.18
% 5.01/1.93  CNF conversion       : 0.02
% 5.01/1.93  Main loop            : 0.81
% 5.01/1.93  Inferencing          : 0.26
% 5.01/1.93  Reduction            : 0.35
% 5.01/1.93  Demodulation         : 0.28
% 5.01/1.93  BG Simplification    : 0.03
% 5.01/1.93  Subsumption          : 0.11
% 5.01/1.93  Abstraction          : 0.04
% 5.01/1.93  MUC search           : 0.00
% 5.01/1.93  Cooper               : 0.00
% 5.01/1.93  Total                : 1.20
% 5.01/1.93  Index Insertion      : 0.00
% 5.01/1.93  Index Deletion       : 0.00
% 5.01/1.93  Index Matching       : 0.00
% 5.01/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
