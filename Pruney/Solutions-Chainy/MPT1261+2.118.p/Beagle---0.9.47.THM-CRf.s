%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:28 EST 2020

% Result     : Theorem 5.02s
% Output     : CNFRefutation 5.02s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 346 expanded)
%              Number of leaves         :   41 ( 135 expanded)
%              Depth                    :   11
%              Number of atoms          :  186 ( 717 expanded)
%              Number of equality atoms :   79 ( 192 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_53,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_35,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_91,axiom,(
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

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2536,plain,(
    ! [A_180,B_181,C_182] :
      ( k7_subset_1(A_180,B_181,C_182) = k4_xboole_0(B_181,C_182)
      | ~ m1_subset_1(B_181,k1_zfmisc_1(A_180)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2542,plain,(
    ! [C_182] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_182) = k4_xboole_0('#skF_2',C_182) ),
    inference(resolution,[status(thm)],[c_40,c_2536])).

tff(c_46,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_200,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1160,plain,(
    ! [B_120,A_121] :
      ( v4_pre_topc(B_120,A_121)
      | k2_pre_topc(A_121,B_120) != B_120
      | ~ v2_pre_topc(A_121)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1170,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1160])).

tff(c_1175,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_1170])).

tff(c_1176,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_200,c_1175])).

tff(c_236,plain,(
    ! [A_64,B_65,C_66] :
      ( k7_subset_1(A_64,B_65,C_66) = k4_xboole_0(B_65,C_66)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_243,plain,(
    ! [C_67] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_67) = k4_xboole_0('#skF_2',C_67) ),
    inference(resolution,[status(thm)],[c_40,c_236])).

tff(c_52,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_111,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_249,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_111])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(A_24,k1_zfmisc_1(B_25))
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_146,plain,(
    ! [A_58,B_59] :
      ( k4_xboole_0(A_58,B_59) = k3_subset_1(A_58,B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_201,plain,(
    ! [B_62,A_63] :
      ( k4_xboole_0(B_62,A_63) = k3_subset_1(B_62,A_63)
      | ~ r1_tarski(A_63,B_62) ) ),
    inference(resolution,[status(thm)],[c_26,c_146])).

tff(c_288,plain,(
    ! [A_71,B_72] : k4_xboole_0(A_71,k4_xboole_0(A_71,B_72)) = k3_subset_1(A_71,k4_xboole_0(A_71,B_72)) ),
    inference(resolution,[status(thm)],[c_6,c_201])).

tff(c_300,plain,(
    ! [A_71,B_72] : r1_tarski(k3_subset_1(A_71,k4_xboole_0(A_71,B_72)),A_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_297,plain,(
    ! [A_71,B_72] : k2_xboole_0(k4_xboole_0(A_71,B_72),k3_subset_1(A_71,k4_xboole_0(A_71,B_72))) = k2_xboole_0(k4_xboole_0(A_71,B_72),A_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_8])).

tff(c_318,plain,(
    ! [A_71,B_72] : k2_xboole_0(k4_xboole_0(A_71,B_72),k3_subset_1(A_71,k4_xboole_0(A_71,B_72))) = k2_xboole_0(A_71,k4_xboole_0(A_71,B_72)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_297])).

tff(c_135,plain,(
    ! [A_56,B_57] :
      ( k3_subset_1(A_56,k3_subset_1(A_56,B_57)) = B_57
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_140,plain,(
    ! [B_25,A_24] :
      ( k3_subset_1(B_25,k3_subset_1(B_25,A_24)) = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(resolution,[status(thm)],[c_26,c_135])).

tff(c_10,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( k4_subset_1(A_20,B_21,k3_subset_1(A_20,B_21)) = k2_subset_1(A_20)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_381,plain,(
    ! [A_77,B_78] :
      ( k4_subset_1(A_77,B_78,k3_subset_1(A_77,B_78)) = A_77
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_20])).

tff(c_400,plain,(
    ! [B_79,A_80] :
      ( k4_subset_1(B_79,A_80,k3_subset_1(B_79,A_80)) = B_79
      | ~ r1_tarski(A_80,B_79) ) ),
    inference(resolution,[status(thm)],[c_26,c_381])).

tff(c_1420,plain,(
    ! [B_133,A_134] :
      ( k4_subset_1(B_133,k3_subset_1(B_133,A_134),A_134) = B_133
      | ~ r1_tarski(k3_subset_1(B_133,A_134),B_133)
      | ~ r1_tarski(A_134,B_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_400])).

tff(c_1436,plain,(
    ! [A_71,B_72] :
      ( k4_subset_1(A_71,k3_subset_1(A_71,k4_xboole_0(A_71,B_72)),k4_xboole_0(A_71,B_72)) = A_71
      | ~ r1_tarski(k4_xboole_0(A_71,B_72),A_71) ) ),
    inference(resolution,[status(thm)],[c_300,c_1420])).

tff(c_1775,plain,(
    ! [A_143,B_144] : k4_subset_1(A_143,k3_subset_1(A_143,k4_xboole_0(A_143,B_144)),k4_xboole_0(A_143,B_144)) = A_143 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1436])).

tff(c_867,plain,(
    ! [A_102,B_103,C_104] :
      ( k4_subset_1(A_102,B_103,C_104) = k2_xboole_0(B_103,C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(A_102))
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1032,plain,(
    ! [B_112,B_113,A_114] :
      ( k4_subset_1(B_112,B_113,A_114) = k2_xboole_0(B_113,A_114)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(B_112))
      | ~ r1_tarski(A_114,B_112) ) ),
    inference(resolution,[status(thm)],[c_26,c_867])).

tff(c_1090,plain,(
    ! [B_116,A_117,A_118] :
      ( k4_subset_1(B_116,A_117,A_118) = k2_xboole_0(A_117,A_118)
      | ~ r1_tarski(A_118,B_116)
      | ~ r1_tarski(A_117,B_116) ) ),
    inference(resolution,[status(thm)],[c_26,c_1032])).

tff(c_1132,plain,(
    ! [A_5,A_117,B_6] :
      ( k4_subset_1(A_5,A_117,k4_xboole_0(A_5,B_6)) = k2_xboole_0(A_117,k4_xboole_0(A_5,B_6))
      | ~ r1_tarski(A_117,A_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_1090])).

tff(c_1781,plain,(
    ! [A_143,B_144] :
      ( k2_xboole_0(k3_subset_1(A_143,k4_xboole_0(A_143,B_144)),k4_xboole_0(A_143,B_144)) = A_143
      | ~ r1_tarski(k3_subset_1(A_143,k4_xboole_0(A_143,B_144)),A_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1775,c_1132])).

tff(c_1844,plain,(
    ! [A_145,B_146] : k2_xboole_0(A_145,k4_xboole_0(A_145,B_146)) = A_145 ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_318,c_2,c_1781])).

tff(c_1866,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_1844])).

tff(c_1292,plain,(
    ! [A_128,B_129] :
      ( k4_subset_1(u1_struct_0(A_128),B_129,k2_tops_1(A_128,B_129)) = k2_pre_topc(A_128,B_129)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1299,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1292])).

tff(c_1304,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1299])).

tff(c_635,plain,(
    ! [A_92,B_93] :
      ( m1_subset_1(k2_tops_1(A_92,B_93),k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( k3_subset_1(A_12,k3_subset_1(A_12,B_13)) = B_13
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2342,plain,(
    ! [A_162,B_163] :
      ( k3_subset_1(u1_struct_0(A_162),k3_subset_1(u1_struct_0(A_162),k2_tops_1(A_162,B_163))) = k2_tops_1(A_162,B_163)
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ l1_pre_topc(A_162) ) ),
    inference(resolution,[status(thm)],[c_635,c_14])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = k3_subset_1(A_10,B_11)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2098,plain,(
    ! [A_159,B_160] :
      ( k4_xboole_0(u1_struct_0(A_159),k2_tops_1(A_159,B_160)) = k3_subset_1(u1_struct_0(A_159),k2_tops_1(A_159,B_160))
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ l1_pre_topc(A_159) ) ),
    inference(resolution,[status(thm)],[c_635,c_12])).

tff(c_2105,plain,
    ( k4_xboole_0(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_2098])).

tff(c_2110,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2105])).

tff(c_2170,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2110,c_300])).

tff(c_2348,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2342,c_2170])).

tff(c_2368,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_2348])).

tff(c_1041,plain,(
    ! [A_114] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_114) = k2_xboole_0('#skF_2',A_114)
      | ~ r1_tarski(A_114,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_40,c_1032])).

tff(c_2380,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2368,c_1041])).

tff(c_2397,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1866,c_1304,c_2380])).

tff(c_2399,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1176,c_2397])).

tff(c_2400,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_2429,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2400,c_111])).

tff(c_2430,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2475,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2430,c_46])).

tff(c_2543,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2542,c_2475])).

tff(c_3070,plain,(
    ! [A_221,B_222] :
      ( r1_tarski(k2_tops_1(A_221,B_222),B_222)
      | ~ v4_pre_topc(B_222,A_221)
      | ~ m1_subset_1(B_222,k1_zfmisc_1(u1_struct_0(A_221)))
      | ~ l1_pre_topc(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_3077,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_3070])).

tff(c_3082,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2430,c_3077])).

tff(c_2455,plain,(
    ! [A_172,B_173] :
      ( k4_xboole_0(A_172,B_173) = k3_subset_1(A_172,B_173)
      | ~ m1_subset_1(B_173,k1_zfmisc_1(A_172)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2462,plain,(
    ! [B_25,A_24] :
      ( k4_xboole_0(B_25,A_24) = k3_subset_1(B_25,A_24)
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(resolution,[status(thm)],[c_26,c_2455])).

tff(c_3089,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_3082,c_2462])).

tff(c_3616,plain,(
    ! [A_246,B_247] :
      ( k7_subset_1(u1_struct_0(A_246),B_247,k2_tops_1(A_246,B_247)) = k1_tops_1(A_246,B_247)
      | ~ m1_subset_1(B_247,k1_zfmisc_1(u1_struct_0(A_246)))
      | ~ l1_pre_topc(A_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_3623,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_3616])).

tff(c_3628,plain,(
    k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3089,c_2542,c_3623])).

tff(c_2490,plain,(
    ! [A_176,B_177] :
      ( k3_subset_1(A_176,k3_subset_1(A_176,B_177)) = B_177
      | ~ m1_subset_1(B_177,k1_zfmisc_1(A_176)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2495,plain,(
    ! [B_25,A_24] :
      ( k3_subset_1(B_25,k3_subset_1(B_25,A_24)) = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(resolution,[status(thm)],[c_26,c_2490])).

tff(c_3642,plain,
    ( k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3628,c_2495])).

tff(c_3648,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3082,c_3642])).

tff(c_3635,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3628,c_3089])).

tff(c_2476,plain,(
    ! [B_174,A_175] :
      ( k4_xboole_0(B_174,A_175) = k3_subset_1(B_174,A_175)
      | ~ r1_tarski(A_175,B_174) ) ),
    inference(resolution,[status(thm)],[c_26,c_2455])).

tff(c_2489,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_subset_1(A_5,k4_xboole_0(A_5,B_6)) ),
    inference(resolution,[status(thm)],[c_6,c_2476])).

tff(c_3709,plain,(
    k3_subset_1('#skF_2',k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3635,c_2489])).

tff(c_3724,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3635,c_3709])).

tff(c_3848,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3648,c_3724])).

tff(c_3849,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2543,c_3848])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:20:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.02/1.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.02/1.92  
% 5.02/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.02/1.92  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 5.02/1.92  
% 5.02/1.92  %Foreground sorts:
% 5.02/1.92  
% 5.02/1.92  
% 5.02/1.92  %Background operators:
% 5.02/1.92  
% 5.02/1.92  
% 5.02/1.92  %Foreground operators:
% 5.02/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.02/1.92  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.02/1.92  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.02/1.92  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.02/1.92  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.02/1.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.02/1.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.02/1.92  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.02/1.92  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.02/1.92  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.02/1.92  tff('#skF_2', type, '#skF_2': $i).
% 5.02/1.92  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.02/1.92  tff('#skF_1', type, '#skF_1': $i).
% 5.02/1.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.02/1.92  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.02/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.02/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.02/1.92  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.02/1.92  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.02/1.92  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.02/1.92  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.02/1.92  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.02/1.92  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.02/1.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.02/1.92  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.02/1.92  
% 5.02/1.94  tff(f_119, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 5.02/1.94  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.02/1.94  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.02/1.94  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.02/1.94  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.02/1.94  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 5.02/1.94  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.02/1.94  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.02/1.94  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 5.02/1.94  tff(f_35, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.02/1.94  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 5.02/1.94  tff(f_49, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.02/1.94  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 5.02/1.94  tff(f_84, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.02/1.94  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 5.02/1.94  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 5.02/1.94  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.02/1.94  tff(c_2536, plain, (![A_180, B_181, C_182]: (k7_subset_1(A_180, B_181, C_182)=k4_xboole_0(B_181, C_182) | ~m1_subset_1(B_181, k1_zfmisc_1(A_180)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.02/1.94  tff(c_2542, plain, (![C_182]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_182)=k4_xboole_0('#skF_2', C_182))), inference(resolution, [status(thm)], [c_40, c_2536])).
% 5.02/1.94  tff(c_46, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.02/1.94  tff(c_200, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 5.02/1.94  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.02/1.94  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.02/1.94  tff(c_1160, plain, (![B_120, A_121]: (v4_pre_topc(B_120, A_121) | k2_pre_topc(A_121, B_120)!=B_120 | ~v2_pre_topc(A_121) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.02/1.94  tff(c_1170, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1160])).
% 5.02/1.94  tff(c_1175, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_1170])).
% 5.02/1.94  tff(c_1176, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_200, c_1175])).
% 5.02/1.94  tff(c_236, plain, (![A_64, B_65, C_66]: (k7_subset_1(A_64, B_65, C_66)=k4_xboole_0(B_65, C_66) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.02/1.94  tff(c_243, plain, (![C_67]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_67)=k4_xboole_0('#skF_2', C_67))), inference(resolution, [status(thm)], [c_40, c_236])).
% 5.02/1.94  tff(c_52, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.02/1.94  tff(c_111, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_52])).
% 5.02/1.94  tff(c_249, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_243, c_111])).
% 5.02/1.94  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.02/1.94  tff(c_26, plain, (![A_24, B_25]: (m1_subset_1(A_24, k1_zfmisc_1(B_25)) | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.02/1.94  tff(c_146, plain, (![A_58, B_59]: (k4_xboole_0(A_58, B_59)=k3_subset_1(A_58, B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.02/1.94  tff(c_201, plain, (![B_62, A_63]: (k4_xboole_0(B_62, A_63)=k3_subset_1(B_62, A_63) | ~r1_tarski(A_63, B_62))), inference(resolution, [status(thm)], [c_26, c_146])).
% 5.02/1.94  tff(c_288, plain, (![A_71, B_72]: (k4_xboole_0(A_71, k4_xboole_0(A_71, B_72))=k3_subset_1(A_71, k4_xboole_0(A_71, B_72)))), inference(resolution, [status(thm)], [c_6, c_201])).
% 5.02/1.94  tff(c_300, plain, (![A_71, B_72]: (r1_tarski(k3_subset_1(A_71, k4_xboole_0(A_71, B_72)), A_71))), inference(superposition, [status(thm), theory('equality')], [c_288, c_6])).
% 5.02/1.94  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.02/1.94  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.02/1.94  tff(c_297, plain, (![A_71, B_72]: (k2_xboole_0(k4_xboole_0(A_71, B_72), k3_subset_1(A_71, k4_xboole_0(A_71, B_72)))=k2_xboole_0(k4_xboole_0(A_71, B_72), A_71))), inference(superposition, [status(thm), theory('equality')], [c_288, c_8])).
% 5.02/1.94  tff(c_318, plain, (![A_71, B_72]: (k2_xboole_0(k4_xboole_0(A_71, B_72), k3_subset_1(A_71, k4_xboole_0(A_71, B_72)))=k2_xboole_0(A_71, k4_xboole_0(A_71, B_72)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_297])).
% 5.02/1.94  tff(c_135, plain, (![A_56, B_57]: (k3_subset_1(A_56, k3_subset_1(A_56, B_57))=B_57 | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.02/1.94  tff(c_140, plain, (![B_25, A_24]: (k3_subset_1(B_25, k3_subset_1(B_25, A_24))=A_24 | ~r1_tarski(A_24, B_25))), inference(resolution, [status(thm)], [c_26, c_135])).
% 5.02/1.94  tff(c_10, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.02/1.94  tff(c_20, plain, (![A_20, B_21]: (k4_subset_1(A_20, B_21, k3_subset_1(A_20, B_21))=k2_subset_1(A_20) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.02/1.94  tff(c_381, plain, (![A_77, B_78]: (k4_subset_1(A_77, B_78, k3_subset_1(A_77, B_78))=A_77 | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_20])).
% 5.02/1.94  tff(c_400, plain, (![B_79, A_80]: (k4_subset_1(B_79, A_80, k3_subset_1(B_79, A_80))=B_79 | ~r1_tarski(A_80, B_79))), inference(resolution, [status(thm)], [c_26, c_381])).
% 5.02/1.94  tff(c_1420, plain, (![B_133, A_134]: (k4_subset_1(B_133, k3_subset_1(B_133, A_134), A_134)=B_133 | ~r1_tarski(k3_subset_1(B_133, A_134), B_133) | ~r1_tarski(A_134, B_133))), inference(superposition, [status(thm), theory('equality')], [c_140, c_400])).
% 5.02/1.94  tff(c_1436, plain, (![A_71, B_72]: (k4_subset_1(A_71, k3_subset_1(A_71, k4_xboole_0(A_71, B_72)), k4_xboole_0(A_71, B_72))=A_71 | ~r1_tarski(k4_xboole_0(A_71, B_72), A_71))), inference(resolution, [status(thm)], [c_300, c_1420])).
% 5.02/1.94  tff(c_1775, plain, (![A_143, B_144]: (k4_subset_1(A_143, k3_subset_1(A_143, k4_xboole_0(A_143, B_144)), k4_xboole_0(A_143, B_144))=A_143)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1436])).
% 5.02/1.94  tff(c_867, plain, (![A_102, B_103, C_104]: (k4_subset_1(A_102, B_103, C_104)=k2_xboole_0(B_103, C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(A_102)) | ~m1_subset_1(B_103, k1_zfmisc_1(A_102)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.02/1.94  tff(c_1032, plain, (![B_112, B_113, A_114]: (k4_subset_1(B_112, B_113, A_114)=k2_xboole_0(B_113, A_114) | ~m1_subset_1(B_113, k1_zfmisc_1(B_112)) | ~r1_tarski(A_114, B_112))), inference(resolution, [status(thm)], [c_26, c_867])).
% 5.02/1.94  tff(c_1090, plain, (![B_116, A_117, A_118]: (k4_subset_1(B_116, A_117, A_118)=k2_xboole_0(A_117, A_118) | ~r1_tarski(A_118, B_116) | ~r1_tarski(A_117, B_116))), inference(resolution, [status(thm)], [c_26, c_1032])).
% 5.02/1.94  tff(c_1132, plain, (![A_5, A_117, B_6]: (k4_subset_1(A_5, A_117, k4_xboole_0(A_5, B_6))=k2_xboole_0(A_117, k4_xboole_0(A_5, B_6)) | ~r1_tarski(A_117, A_5))), inference(resolution, [status(thm)], [c_6, c_1090])).
% 5.02/1.94  tff(c_1781, plain, (![A_143, B_144]: (k2_xboole_0(k3_subset_1(A_143, k4_xboole_0(A_143, B_144)), k4_xboole_0(A_143, B_144))=A_143 | ~r1_tarski(k3_subset_1(A_143, k4_xboole_0(A_143, B_144)), A_143))), inference(superposition, [status(thm), theory('equality')], [c_1775, c_1132])).
% 5.02/1.94  tff(c_1844, plain, (![A_145, B_146]: (k2_xboole_0(A_145, k4_xboole_0(A_145, B_146))=A_145)), inference(demodulation, [status(thm), theory('equality')], [c_300, c_318, c_2, c_1781])).
% 5.02/1.94  tff(c_1866, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_249, c_1844])).
% 5.02/1.94  tff(c_1292, plain, (![A_128, B_129]: (k4_subset_1(u1_struct_0(A_128), B_129, k2_tops_1(A_128, B_129))=k2_pre_topc(A_128, B_129) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.02/1.94  tff(c_1299, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1292])).
% 5.02/1.94  tff(c_1304, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1299])).
% 5.02/1.94  tff(c_635, plain, (![A_92, B_93]: (m1_subset_1(k2_tops_1(A_92, B_93), k1_zfmisc_1(u1_struct_0(A_92))) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.02/1.94  tff(c_14, plain, (![A_12, B_13]: (k3_subset_1(A_12, k3_subset_1(A_12, B_13))=B_13 | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.02/1.94  tff(c_2342, plain, (![A_162, B_163]: (k3_subset_1(u1_struct_0(A_162), k3_subset_1(u1_struct_0(A_162), k2_tops_1(A_162, B_163)))=k2_tops_1(A_162, B_163) | ~m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0(A_162))) | ~l1_pre_topc(A_162))), inference(resolution, [status(thm)], [c_635, c_14])).
% 5.02/1.94  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=k3_subset_1(A_10, B_11) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.02/1.94  tff(c_2098, plain, (![A_159, B_160]: (k4_xboole_0(u1_struct_0(A_159), k2_tops_1(A_159, B_160))=k3_subset_1(u1_struct_0(A_159), k2_tops_1(A_159, B_160)) | ~m1_subset_1(B_160, k1_zfmisc_1(u1_struct_0(A_159))) | ~l1_pre_topc(A_159))), inference(resolution, [status(thm)], [c_635, c_12])).
% 5.02/1.94  tff(c_2105, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_2098])).
% 5.02/1.94  tff(c_2110, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2105])).
% 5.02/1.94  tff(c_2170, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2110, c_300])).
% 5.02/1.94  tff(c_2348, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2342, c_2170])).
% 5.02/1.94  tff(c_2368, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_2348])).
% 5.02/1.94  tff(c_1041, plain, (![A_114]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_114)=k2_xboole_0('#skF_2', A_114) | ~r1_tarski(A_114, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_40, c_1032])).
% 5.02/1.94  tff(c_2380, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_2368, c_1041])).
% 5.02/1.94  tff(c_2397, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1866, c_1304, c_2380])).
% 5.02/1.94  tff(c_2399, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1176, c_2397])).
% 5.02/1.94  tff(c_2400, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 5.02/1.94  tff(c_2429, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2400, c_111])).
% 5.02/1.94  tff(c_2430, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 5.02/1.94  tff(c_2475, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2430, c_46])).
% 5.02/1.94  tff(c_2543, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2542, c_2475])).
% 5.02/1.94  tff(c_3070, plain, (![A_221, B_222]: (r1_tarski(k2_tops_1(A_221, B_222), B_222) | ~v4_pre_topc(B_222, A_221) | ~m1_subset_1(B_222, k1_zfmisc_1(u1_struct_0(A_221))) | ~l1_pre_topc(A_221))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.02/1.94  tff(c_3077, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_3070])).
% 5.02/1.94  tff(c_3082, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2430, c_3077])).
% 5.02/1.94  tff(c_2455, plain, (![A_172, B_173]: (k4_xboole_0(A_172, B_173)=k3_subset_1(A_172, B_173) | ~m1_subset_1(B_173, k1_zfmisc_1(A_172)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.02/1.94  tff(c_2462, plain, (![B_25, A_24]: (k4_xboole_0(B_25, A_24)=k3_subset_1(B_25, A_24) | ~r1_tarski(A_24, B_25))), inference(resolution, [status(thm)], [c_26, c_2455])).
% 5.02/1.94  tff(c_3089, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_3082, c_2462])).
% 5.02/1.94  tff(c_3616, plain, (![A_246, B_247]: (k7_subset_1(u1_struct_0(A_246), B_247, k2_tops_1(A_246, B_247))=k1_tops_1(A_246, B_247) | ~m1_subset_1(B_247, k1_zfmisc_1(u1_struct_0(A_246))) | ~l1_pre_topc(A_246))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.02/1.94  tff(c_3623, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_3616])).
% 5.02/1.94  tff(c_3628, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_3089, c_2542, c_3623])).
% 5.02/1.94  tff(c_2490, plain, (![A_176, B_177]: (k3_subset_1(A_176, k3_subset_1(A_176, B_177))=B_177 | ~m1_subset_1(B_177, k1_zfmisc_1(A_176)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.02/1.94  tff(c_2495, plain, (![B_25, A_24]: (k3_subset_1(B_25, k3_subset_1(B_25, A_24))=A_24 | ~r1_tarski(A_24, B_25))), inference(resolution, [status(thm)], [c_26, c_2490])).
% 5.02/1.94  tff(c_3642, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3628, c_2495])).
% 5.02/1.94  tff(c_3648, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3082, c_3642])).
% 5.02/1.94  tff(c_3635, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3628, c_3089])).
% 5.02/1.94  tff(c_2476, plain, (![B_174, A_175]: (k4_xboole_0(B_174, A_175)=k3_subset_1(B_174, A_175) | ~r1_tarski(A_175, B_174))), inference(resolution, [status(thm)], [c_26, c_2455])).
% 5.02/1.94  tff(c_2489, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_subset_1(A_5, k4_xboole_0(A_5, B_6)))), inference(resolution, [status(thm)], [c_6, c_2476])).
% 5.02/1.94  tff(c_3709, plain, (k3_subset_1('#skF_2', k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2')))=k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3635, c_2489])).
% 5.02/1.94  tff(c_3724, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3635, c_3709])).
% 5.02/1.94  tff(c_3848, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3648, c_3724])).
% 5.02/1.94  tff(c_3849, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2543, c_3848])).
% 5.02/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.02/1.94  
% 5.02/1.94  Inference rules
% 5.02/1.94  ----------------------
% 5.02/1.94  #Ref     : 0
% 5.02/1.94  #Sup     : 933
% 5.02/1.94  #Fact    : 0
% 5.02/1.94  #Define  : 0
% 5.02/1.94  #Split   : 2
% 5.02/1.94  #Chain   : 0
% 5.02/1.94  #Close   : 0
% 5.02/1.94  
% 5.02/1.94  Ordering : KBO
% 5.02/1.94  
% 5.02/1.94  Simplification rules
% 5.02/1.94  ----------------------
% 5.02/1.94  #Subsume      : 14
% 5.02/1.94  #Demod        : 780
% 5.02/1.94  #Tautology    : 461
% 5.02/1.94  #SimpNegUnit  : 5
% 5.02/1.94  #BackRed      : 27
% 5.02/1.94  
% 5.02/1.94  #Partial instantiations: 0
% 5.02/1.94  #Strategies tried      : 1
% 5.02/1.94  
% 5.02/1.94  Timing (in seconds)
% 5.02/1.94  ----------------------
% 5.02/1.95  Preprocessing        : 0.32
% 5.02/1.95  Parsing              : 0.17
% 5.02/1.95  CNF conversion       : 0.02
% 5.02/1.95  Main loop            : 0.86
% 5.02/1.95  Inferencing          : 0.27
% 5.02/1.95  Reduction            : 0.35
% 5.02/1.95  Demodulation         : 0.26
% 5.02/1.95  BG Simplification    : 0.04
% 5.02/1.95  Subsumption          : 0.12
% 5.02/1.95  Abstraction          : 0.05
% 5.02/1.95  MUC search           : 0.00
% 5.02/1.95  Cooper               : 0.00
% 5.02/1.95  Total                : 1.22
% 5.02/1.95  Index Insertion      : 0.00
% 5.02/1.95  Index Deletion       : 0.00
% 5.02/1.95  Index Matching       : 0.00
% 5.02/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
