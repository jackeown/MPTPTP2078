%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:14 EST 2020

% Result     : Theorem 11.69s
% Output     : CNFRefutation 11.84s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 718 expanded)
%              Number of leaves         :   56 ( 266 expanded)
%              Depth                    :   17
%              Number of atoms          :  250 (1456 expanded)
%              Number of equality atoms :  103 ( 443 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_164,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_117,axiom,(
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

tff(f_36,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_62,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_98,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_44,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_145,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_102,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_88,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_76,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_138,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_123,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_152,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_19458,plain,(
    ! [A_542,B_543,C_544] :
      ( k7_subset_1(A_542,B_543,C_544) = k4_xboole_0(B_543,C_544)
      | ~ m1_subset_1(B_543,k1_zfmisc_1(A_542)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_19477,plain,(
    ! [C_544] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_544) = k4_xboole_0('#skF_3',C_544) ),
    inference(resolution,[status(thm)],[c_68,c_19458])).

tff(c_80,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_145,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_74,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) != k2_tops_1('#skF_2','#skF_3')
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_263,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_70,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_72,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_3576,plain,(
    ! [B_234,A_235] :
      ( v4_pre_topc(B_234,A_235)
      | k2_pre_topc(A_235,B_234) != B_234
      | ~ v2_pre_topc(A_235)
      | ~ m1_subset_1(B_234,k1_zfmisc_1(u1_struct_0(A_235)))
      | ~ l1_pre_topc(A_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_3605,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | k2_pre_topc('#skF_2','#skF_3') != '#skF_3'
    | ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_3576])).

tff(c_3617,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | k2_pre_topc('#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_72,c_3605])).

tff(c_3618,plain,(
    k2_pre_topc('#skF_2','#skF_3') != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_263,c_3617])).

tff(c_1752,plain,(
    ! [A_175,B_176,C_177] :
      ( k7_subset_1(A_175,B_176,C_177) = k4_xboole_0(B_176,C_177)
      | ~ m1_subset_1(B_176,k1_zfmisc_1(A_175)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1937,plain,(
    ! [C_184] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_184) = k4_xboole_0('#skF_3',C_184) ),
    inference(resolution,[status(thm)],[c_68,c_1752])).

tff(c_1949,plain,(
    k4_xboole_0('#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_1937])).

tff(c_10,plain,(
    ! [A_8] : k2_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_26,plain,(
    ! [B_27,A_26] : k2_tarski(B_27,A_26) = k2_tarski(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_161,plain,(
    ! [A_82,B_83] : k1_setfam_1(k2_tarski(A_82,B_83)) = k3_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_314,plain,(
    ! [B_99,A_100] : k1_setfam_1(k2_tarski(B_99,A_100)) = k3_xboole_0(A_100,B_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_161])).

tff(c_48,plain,(
    ! [A_49,B_50] : k1_setfam_1(k2_tarski(A_49,B_50)) = k3_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_320,plain,(
    ! [B_99,A_100] : k3_xboole_0(B_99,A_100) = k3_xboole_0(A_100,B_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_48])).

tff(c_14,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1293,plain,(
    ! [A_159,B_160,C_161] :
      ( r1_tarski(k4_xboole_0(A_159,B_160),C_161)
      | ~ r1_tarski(A_159,k2_xboole_0(B_160,C_161)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_22,plain,(
    ! [A_22,B_23] : k2_xboole_0(k3_xboole_0(A_22,B_23),k4_xboole_0(A_22,B_23)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_146,plain,(
    ! [A_80,B_81] : k3_tarski(k2_tarski(A_80,B_81)) = k2_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_193,plain,(
    ! [A_92,B_93] : k3_tarski(k2_tarski(A_92,B_93)) = k2_xboole_0(B_93,A_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_146])).

tff(c_28,plain,(
    ! [A_28,B_29] : k3_tarski(k2_tarski(A_28,B_29)) = k2_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_199,plain,(
    ! [B_93,A_92] : k2_xboole_0(B_93,A_92) = k2_xboole_0(A_92,B_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_28])).

tff(c_462,plain,(
    ! [A_109,B_110] : k2_xboole_0(k3_xboole_0(A_109,B_110),k4_xboole_0(A_109,B_110)) = A_109 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_24,plain,(
    ! [A_24,B_25] : k2_xboole_0(A_24,k2_xboole_0(A_24,B_25)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_468,plain,(
    ! [A_109,B_110] : k2_xboole_0(k3_xboole_0(A_109,B_110),k4_xboole_0(A_109,B_110)) = k2_xboole_0(k3_xboole_0(A_109,B_110),A_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_462,c_24])).

tff(c_481,plain,(
    ! [A_111,B_112] : k2_xboole_0(A_111,k3_xboole_0(A_111,B_112)) = A_111 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_199,c_468])).

tff(c_216,plain,(
    ! [B_94,A_95] : k2_xboole_0(B_94,A_95) = k2_xboole_0(A_95,B_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_28])).

tff(c_236,plain,(
    ! [B_94] : k2_xboole_0(k1_xboole_0,B_94) = B_94 ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_10])).

tff(c_518,plain,(
    ! [B_116] : k3_xboole_0(k1_xboole_0,B_116) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_481,c_236])).

tff(c_654,plain,(
    ! [B_124] : k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,B_124)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_22])).

tff(c_673,plain,(
    ! [B_125] : k4_xboole_0(k1_xboole_0,B_125) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_654,c_236])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( k1_xboole_0 = A_14
      | ~ r1_tarski(A_14,k4_xboole_0(B_15,A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_681,plain,(
    ! [B_125] :
      ( k1_xboole_0 = B_125
      | ~ r1_tarski(B_125,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_673,c_16])).

tff(c_1305,plain,(
    ! [A_159,B_160] :
      ( k4_xboole_0(A_159,B_160) = k1_xboole_0
      | ~ r1_tarski(A_159,k2_xboole_0(B_160,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_1293,c_681])).

tff(c_1607,plain,(
    ! [A_171,B_172] :
      ( k4_xboole_0(A_171,B_172) = k1_xboole_0
      | ~ r1_tarski(A_171,B_172) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1305])).

tff(c_1857,plain,(
    ! [A_182,B_183] : k4_xboole_0(k4_xboole_0(A_182,B_183),A_182) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_1607])).

tff(c_1878,plain,(
    ! [A_182,B_183] : k2_xboole_0(k3_xboole_0(k4_xboole_0(A_182,B_183),A_182),k1_xboole_0) = k4_xboole_0(A_182,B_183) ),
    inference(superposition,[status(thm),theory(equality)],[c_1857,c_22])).

tff(c_16943,plain,(
    ! [A_438,B_439] : k3_xboole_0(A_438,k4_xboole_0(A_438,B_439)) = k4_xboole_0(A_438,B_439) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_320,c_1878])).

tff(c_479,plain,(
    ! [A_109,B_110] : k2_xboole_0(A_109,k3_xboole_0(A_109,B_110)) = A_109 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_199,c_468])).

tff(c_17302,plain,(
    ! [A_440,B_441] : k2_xboole_0(A_440,k4_xboole_0(A_440,B_441)) = A_440 ),
    inference(superposition,[status(thm),theory(equality)],[c_16943,c_479])).

tff(c_17539,plain,(
    k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1949,c_17302])).

tff(c_4060,plain,(
    ! [A_243,B_244] :
      ( k4_subset_1(u1_struct_0(A_243),B_244,k2_tops_1(A_243,B_244)) = k2_pre_topc(A_243,B_244)
      | ~ m1_subset_1(B_244,k1_zfmisc_1(u1_struct_0(A_243)))
      | ~ l1_pre_topc(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_4083,plain,
    ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_4060])).

tff(c_4098,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_4083])).

tff(c_455,plain,(
    ! [A_106,B_107] :
      ( r2_hidden('#skF_1'(A_106,B_107),A_106)
      | r1_tarski(A_106,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_460,plain,(
    ! [A_106] : r1_tarski(A_106,A_106) ),
    inference(resolution,[status(thm)],[c_455,c_4])).

tff(c_2504,plain,(
    r1_tarski(k2_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1949,c_14])).

tff(c_178,plain,(
    ! [A_88,B_89] :
      ( r1_tarski(A_88,B_89)
      | ~ m1_subset_1(A_88,k1_zfmisc_1(B_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_191,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_178])).

tff(c_508,plain,(
    ! [A_113,C_114,B_115] :
      ( r1_tarski(A_113,C_114)
      | ~ r1_tarski(B_115,C_114)
      | ~ r1_tarski(A_113,B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_650,plain,(
    ! [A_123] :
      ( r1_tarski(A_123,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_123,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_191,c_508])).

tff(c_12,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(A_9,C_11)
      | ~ r1_tarski(B_10,C_11)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_653,plain,(
    ! [A_9,A_123] :
      ( r1_tarski(A_9,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_9,A_123)
      | ~ r1_tarski(A_123,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_650,c_12])).

tff(c_2512,plain,
    ( r1_tarski(k2_tops_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'))
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_2504,c_653])).

tff(c_2518,plain,(
    r1_tarski(k2_tops_1('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_2512])).

tff(c_52,plain,(
    ! [A_51,B_52] :
      ( m1_subset_1(A_51,k1_zfmisc_1(B_52))
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2950,plain,(
    ! [A_213,B_214,C_215] :
      ( k4_subset_1(A_213,B_214,C_215) = k2_xboole_0(B_214,C_215)
      | ~ m1_subset_1(C_215,k1_zfmisc_1(A_213))
      | ~ m1_subset_1(B_214,k1_zfmisc_1(A_213)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_14570,plain,(
    ! [B_413,B_414,A_415] :
      ( k4_subset_1(B_413,B_414,A_415) = k2_xboole_0(B_414,A_415)
      | ~ m1_subset_1(B_414,k1_zfmisc_1(B_413))
      | ~ r1_tarski(A_415,B_413) ) ),
    inference(resolution,[status(thm)],[c_52,c_2950])).

tff(c_15122,plain,(
    ! [A_419] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',A_419) = k2_xboole_0('#skF_3',A_419)
      | ~ r1_tarski(A_419,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_68,c_14570])).

tff(c_15220,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2518,c_15122])).

tff(c_15288,plain,(
    k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4098,c_15220])).

tff(c_17869,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17539,c_15288])).

tff(c_17871,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3618,c_17869])).

tff(c_17872,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) != k2_tops_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_18059,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_17872])).

tff(c_18060,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_18165,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) != k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18060,c_74])).

tff(c_19627,plain,(
    k4_xboole_0('#skF_3',k1_tops_1('#skF_2','#skF_3')) != k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19477,c_18165])).

tff(c_20425,plain,(
    ! [A_581,B_582] :
      ( k2_pre_topc(A_581,B_582) = B_582
      | ~ v4_pre_topc(B_582,A_581)
      | ~ m1_subset_1(B_582,k1_zfmisc_1(u1_struct_0(A_581)))
      | ~ l1_pre_topc(A_581) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_20451,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_20425])).

tff(c_20460,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_18060,c_20451])).

tff(c_21622,plain,(
    ! [A_620,B_621] :
      ( k4_subset_1(u1_struct_0(A_620),B_621,k2_tops_1(A_620,B_621)) = k2_pre_topc(A_620,B_621)
      | ~ m1_subset_1(B_621,k1_zfmisc_1(u1_struct_0(A_620)))
      | ~ l1_pre_topc(A_620) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_21645,plain,
    ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_21622])).

tff(c_21660,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_20460,c_21645])).

tff(c_19110,plain,(
    ! [A_525,B_526] :
      ( k4_xboole_0(A_525,B_526) = k3_subset_1(A_525,B_526)
      | ~ m1_subset_1(B_526,k1_zfmisc_1(A_525)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_19136,plain,(
    k4_xboole_0(u1_struct_0('#skF_2'),'#skF_3') = k3_subset_1(u1_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_19110])).

tff(c_42,plain,(
    ! [A_42,B_43] : k6_subset_1(A_42,B_43) = k4_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_36,plain,(
    ! [A_35,B_36] : m1_subset_1(k6_subset_1(A_35,B_36),k1_zfmisc_1(A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_81,plain,(
    ! [A_35,B_36] : m1_subset_1(k4_xboole_0(A_35,B_36),k1_zfmisc_1(A_35)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36])).

tff(c_19190,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_19136,c_81])).

tff(c_21416,plain,(
    ! [A_615,B_616] :
      ( k2_tops_1(A_615,k3_subset_1(u1_struct_0(A_615),B_616)) = k2_tops_1(A_615,B_616)
      | ~ m1_subset_1(B_616,k1_zfmisc_1(u1_struct_0(A_615)))
      | ~ l1_pre_topc(A_615) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_21437,plain,
    ( k2_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k2_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_21416])).

tff(c_21451,plain,(
    k2_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_21437])).

tff(c_58,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(k2_tops_1(A_56,B_57),k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_21458,plain,
    ( m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_21451,c_58])).

tff(c_21462,plain,(
    m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_19190,c_21458])).

tff(c_50,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(A_51,B_52)
      | ~ m1_subset_1(A_51,k1_zfmisc_1(B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_21510,plain,(
    r1_tarski(k2_tops_1('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_21462,c_50])).

tff(c_20860,plain,(
    ! [A_596,B_597,C_598] :
      ( k4_subset_1(A_596,B_597,C_598) = k2_xboole_0(B_597,C_598)
      | ~ m1_subset_1(C_598,k1_zfmisc_1(A_596))
      | ~ m1_subset_1(B_597,k1_zfmisc_1(A_596)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_35313,plain,(
    ! [B_788,B_789,A_790] :
      ( k4_subset_1(B_788,B_789,A_790) = k2_xboole_0(B_789,A_790)
      | ~ m1_subset_1(B_789,k1_zfmisc_1(B_788))
      | ~ r1_tarski(A_790,B_788) ) ),
    inference(resolution,[status(thm)],[c_52,c_20860])).

tff(c_36040,plain,(
    ! [A_795] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',A_795) = k2_xboole_0('#skF_3',A_795)
      | ~ r1_tarski(A_795,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_68,c_35313])).

tff(c_36099,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_21510,c_36040])).

tff(c_36171,plain,(
    k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21660,c_36099])).

tff(c_19223,plain,(
    ! [A_531,B_532,C_533] :
      ( r1_tarski(A_531,k2_xboole_0(B_532,C_533))
      | ~ r1_tarski(k4_xboole_0(A_531,B_532),C_533) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_19268,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(B_13,A_12)) ),
    inference(resolution,[status(thm)],[c_14,c_19223])).

tff(c_36272,plain,(
    r1_tarski(k2_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36171,c_19268])).

tff(c_22043,plain,(
    ! [A_635,B_636] :
      ( k7_subset_1(u1_struct_0(A_635),B_636,k2_tops_1(A_635,B_636)) = k1_tops_1(A_635,B_636)
      | ~ m1_subset_1(B_636,k1_zfmisc_1(u1_struct_0(A_635)))
      | ~ l1_pre_topc(A_635) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_22066,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_22043])).

tff(c_22083,plain,(
    k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_19477,c_22066])).

tff(c_19134,plain,(
    ! [B_52,A_51] :
      ( k4_xboole_0(B_52,A_51) = k3_subset_1(B_52,A_51)
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(resolution,[status(thm)],[c_52,c_19110])).

tff(c_36300,plain,(
    k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k3_subset_1('#skF_3',k2_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_36272,c_19134])).

tff(c_36308,plain,(
    k3_subset_1('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22083,c_36300])).

tff(c_18738,plain,(
    ! [A_510,B_511] :
      ( k3_subset_1(A_510,k3_subset_1(A_510,B_511)) = B_511
      | ~ m1_subset_1(B_511,k1_zfmisc_1(A_510)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_18748,plain,(
    ! [B_52,A_51] :
      ( k3_subset_1(B_52,k3_subset_1(B_52,A_51)) = A_51
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(resolution,[status(thm)],[c_52,c_18738])).

tff(c_37161,plain,
    ( k3_subset_1('#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3')
    | ~ r1_tarski(k2_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36308,c_18748])).

tff(c_37172,plain,(
    k3_subset_1('#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36272,c_37161])).

tff(c_24623,plain,(
    ! [A_690,B_691] : k4_xboole_0(A_690,k4_xboole_0(A_690,B_691)) = k3_subset_1(A_690,k4_xboole_0(A_690,B_691)) ),
    inference(resolution,[status(thm)],[c_81,c_19110])).

tff(c_24951,plain,(
    ! [A_694,B_695] : m1_subset_1(k3_subset_1(A_694,k4_xboole_0(A_694,B_695)),k1_zfmisc_1(A_694)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24623,c_81])).

tff(c_25013,plain,(
    m1_subset_1(k3_subset_1('#skF_3',k1_tops_1('#skF_2','#skF_3')),k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_22083,c_24951])).

tff(c_37176,plain,(
    m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37172,c_25013])).

tff(c_34,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(k3_subset_1(A_33,B_34),k1_zfmisc_1(A_33))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_19129,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(A_33,k3_subset_1(A_33,B_34)) = k3_subset_1(A_33,k3_subset_1(A_33,B_34))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_33)) ) ),
    inference(resolution,[status(thm)],[c_34,c_19110])).

tff(c_37212,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3',k2_tops_1('#skF_2','#skF_3'))) = k3_subset_1('#skF_3',k3_subset_1('#skF_3',k2_tops_1('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_37176,c_19129])).

tff(c_37232,plain,(
    k4_xboole_0('#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37172,c_36308,c_36308,c_37212])).

tff(c_37234,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19627,c_37232])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:22:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.69/5.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.69/5.16  
% 11.69/5.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.69/5.16  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 11.69/5.16  
% 11.69/5.16  %Foreground sorts:
% 11.69/5.16  
% 11.69/5.16  
% 11.69/5.16  %Background operators:
% 11.69/5.16  
% 11.69/5.16  
% 11.69/5.16  %Foreground operators:
% 11.69/5.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.69/5.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.69/5.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.69/5.16  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 11.69/5.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.69/5.16  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.69/5.16  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.69/5.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.69/5.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.69/5.16  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 11.69/5.16  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 11.69/5.16  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 11.69/5.16  tff('#skF_2', type, '#skF_2': $i).
% 11.69/5.16  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 11.69/5.16  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 11.69/5.16  tff('#skF_3', type, '#skF_3': $i).
% 11.69/5.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.69/5.16  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 11.69/5.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.69/5.16  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.69/5.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.69/5.16  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.69/5.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.69/5.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.69/5.16  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.69/5.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.69/5.16  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 11.69/5.16  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 11.69/5.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.69/5.16  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 11.69/5.16  
% 11.84/5.19  tff(f_164, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 11.84/5.19  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 11.84/5.19  tff(f_117, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 11.84/5.19  tff(f_36, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 11.84/5.19  tff(f_62, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 11.84/5.19  tff(f_98, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 11.84/5.19  tff(f_44, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.84/5.19  tff(f_52, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 11.84/5.19  tff(f_58, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 11.84/5.19  tff(f_64, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 11.84/5.19  tff(f_60, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_1)).
% 11.84/5.19  tff(f_48, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 11.84/5.19  tff(f_145, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 11.84/5.19  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 11.84/5.19  tff(f_102, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.84/5.19  tff(f_42, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 11.84/5.19  tff(f_86, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 11.84/5.19  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 11.84/5.19  tff(f_88, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 11.84/5.19  tff(f_76, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 11.84/5.19  tff(f_138, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_1)).
% 11.84/5.19  tff(f_123, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 11.84/5.19  tff(f_56, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 11.84/5.19  tff(f_152, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 11.84/5.19  tff(f_80, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 11.84/5.19  tff(f_74, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 11.84/5.19  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 11.84/5.19  tff(c_19458, plain, (![A_542, B_543, C_544]: (k7_subset_1(A_542, B_543, C_544)=k4_xboole_0(B_543, C_544) | ~m1_subset_1(B_543, k1_zfmisc_1(A_542)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.84/5.19  tff(c_19477, plain, (![C_544]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_544)=k4_xboole_0('#skF_3', C_544))), inference(resolution, [status(thm)], [c_68, c_19458])).
% 11.84/5.19  tff(c_80, plain, (v4_pre_topc('#skF_3', '#skF_2') | k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_164])).
% 11.84/5.19  tff(c_145, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_80])).
% 11.84/5.19  tff(c_74, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))!=k2_tops_1('#skF_2', '#skF_3') | ~v4_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_164])).
% 11.84/5.19  tff(c_263, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_74])).
% 11.84/5.19  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_164])).
% 11.84/5.19  tff(c_72, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_164])).
% 11.84/5.19  tff(c_3576, plain, (![B_234, A_235]: (v4_pre_topc(B_234, A_235) | k2_pre_topc(A_235, B_234)!=B_234 | ~v2_pre_topc(A_235) | ~m1_subset_1(B_234, k1_zfmisc_1(u1_struct_0(A_235))) | ~l1_pre_topc(A_235))), inference(cnfTransformation, [status(thm)], [f_117])).
% 11.84/5.19  tff(c_3605, plain, (v4_pre_topc('#skF_3', '#skF_2') | k2_pre_topc('#skF_2', '#skF_3')!='#skF_3' | ~v2_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_68, c_3576])).
% 11.84/5.19  tff(c_3617, plain, (v4_pre_topc('#skF_3', '#skF_2') | k2_pre_topc('#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_72, c_3605])).
% 11.84/5.19  tff(c_3618, plain, (k2_pre_topc('#skF_2', '#skF_3')!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_263, c_3617])).
% 11.84/5.19  tff(c_1752, plain, (![A_175, B_176, C_177]: (k7_subset_1(A_175, B_176, C_177)=k4_xboole_0(B_176, C_177) | ~m1_subset_1(B_176, k1_zfmisc_1(A_175)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.84/5.19  tff(c_1937, plain, (![C_184]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_184)=k4_xboole_0('#skF_3', C_184))), inference(resolution, [status(thm)], [c_68, c_1752])).
% 11.84/5.19  tff(c_1949, plain, (k4_xboole_0('#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_145, c_1937])).
% 11.84/5.19  tff(c_10, plain, (![A_8]: (k2_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.84/5.19  tff(c_26, plain, (![B_27, A_26]: (k2_tarski(B_27, A_26)=k2_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.84/5.19  tff(c_161, plain, (![A_82, B_83]: (k1_setfam_1(k2_tarski(A_82, B_83))=k3_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.84/5.19  tff(c_314, plain, (![B_99, A_100]: (k1_setfam_1(k2_tarski(B_99, A_100))=k3_xboole_0(A_100, B_99))), inference(superposition, [status(thm), theory('equality')], [c_26, c_161])).
% 11.84/5.19  tff(c_48, plain, (![A_49, B_50]: (k1_setfam_1(k2_tarski(A_49, B_50))=k3_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.84/5.19  tff(c_320, plain, (![B_99, A_100]: (k3_xboole_0(B_99, A_100)=k3_xboole_0(A_100, B_99))), inference(superposition, [status(thm), theory('equality')], [c_314, c_48])).
% 11.84/5.19  tff(c_14, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.84/5.19  tff(c_1293, plain, (![A_159, B_160, C_161]: (r1_tarski(k4_xboole_0(A_159, B_160), C_161) | ~r1_tarski(A_159, k2_xboole_0(B_160, C_161)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.84/5.19  tff(c_22, plain, (![A_22, B_23]: (k2_xboole_0(k3_xboole_0(A_22, B_23), k4_xboole_0(A_22, B_23))=A_22)), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.84/5.19  tff(c_146, plain, (![A_80, B_81]: (k3_tarski(k2_tarski(A_80, B_81))=k2_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.84/5.19  tff(c_193, plain, (![A_92, B_93]: (k3_tarski(k2_tarski(A_92, B_93))=k2_xboole_0(B_93, A_92))), inference(superposition, [status(thm), theory('equality')], [c_26, c_146])).
% 11.84/5.19  tff(c_28, plain, (![A_28, B_29]: (k3_tarski(k2_tarski(A_28, B_29))=k2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.84/5.19  tff(c_199, plain, (![B_93, A_92]: (k2_xboole_0(B_93, A_92)=k2_xboole_0(A_92, B_93))), inference(superposition, [status(thm), theory('equality')], [c_193, c_28])).
% 11.84/5.19  tff(c_462, plain, (![A_109, B_110]: (k2_xboole_0(k3_xboole_0(A_109, B_110), k4_xboole_0(A_109, B_110))=A_109)), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.84/5.19  tff(c_24, plain, (![A_24, B_25]: (k2_xboole_0(A_24, k2_xboole_0(A_24, B_25))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.84/5.19  tff(c_468, plain, (![A_109, B_110]: (k2_xboole_0(k3_xboole_0(A_109, B_110), k4_xboole_0(A_109, B_110))=k2_xboole_0(k3_xboole_0(A_109, B_110), A_109))), inference(superposition, [status(thm), theory('equality')], [c_462, c_24])).
% 11.84/5.19  tff(c_481, plain, (![A_111, B_112]: (k2_xboole_0(A_111, k3_xboole_0(A_111, B_112))=A_111)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_199, c_468])).
% 11.84/5.19  tff(c_216, plain, (![B_94, A_95]: (k2_xboole_0(B_94, A_95)=k2_xboole_0(A_95, B_94))), inference(superposition, [status(thm), theory('equality')], [c_193, c_28])).
% 11.84/5.19  tff(c_236, plain, (![B_94]: (k2_xboole_0(k1_xboole_0, B_94)=B_94)), inference(superposition, [status(thm), theory('equality')], [c_216, c_10])).
% 11.84/5.19  tff(c_518, plain, (![B_116]: (k3_xboole_0(k1_xboole_0, B_116)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_481, c_236])).
% 11.84/5.19  tff(c_654, plain, (![B_124]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(k1_xboole_0, B_124))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_518, c_22])).
% 11.84/5.19  tff(c_673, plain, (![B_125]: (k4_xboole_0(k1_xboole_0, B_125)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_654, c_236])).
% 11.84/5.19  tff(c_16, plain, (![A_14, B_15]: (k1_xboole_0=A_14 | ~r1_tarski(A_14, k4_xboole_0(B_15, A_14)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.84/5.19  tff(c_681, plain, (![B_125]: (k1_xboole_0=B_125 | ~r1_tarski(B_125, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_673, c_16])).
% 11.84/5.19  tff(c_1305, plain, (![A_159, B_160]: (k4_xboole_0(A_159, B_160)=k1_xboole_0 | ~r1_tarski(A_159, k2_xboole_0(B_160, k1_xboole_0)))), inference(resolution, [status(thm)], [c_1293, c_681])).
% 11.84/5.19  tff(c_1607, plain, (![A_171, B_172]: (k4_xboole_0(A_171, B_172)=k1_xboole_0 | ~r1_tarski(A_171, B_172))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1305])).
% 11.84/5.19  tff(c_1857, plain, (![A_182, B_183]: (k4_xboole_0(k4_xboole_0(A_182, B_183), A_182)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_1607])).
% 11.84/5.19  tff(c_1878, plain, (![A_182, B_183]: (k2_xboole_0(k3_xboole_0(k4_xboole_0(A_182, B_183), A_182), k1_xboole_0)=k4_xboole_0(A_182, B_183))), inference(superposition, [status(thm), theory('equality')], [c_1857, c_22])).
% 11.84/5.19  tff(c_16943, plain, (![A_438, B_439]: (k3_xboole_0(A_438, k4_xboole_0(A_438, B_439))=k4_xboole_0(A_438, B_439))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_320, c_1878])).
% 11.84/5.19  tff(c_479, plain, (![A_109, B_110]: (k2_xboole_0(A_109, k3_xboole_0(A_109, B_110))=A_109)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_199, c_468])).
% 11.84/5.19  tff(c_17302, plain, (![A_440, B_441]: (k2_xboole_0(A_440, k4_xboole_0(A_440, B_441))=A_440)), inference(superposition, [status(thm), theory('equality')], [c_16943, c_479])).
% 11.84/5.19  tff(c_17539, plain, (k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1949, c_17302])).
% 11.84/5.19  tff(c_4060, plain, (![A_243, B_244]: (k4_subset_1(u1_struct_0(A_243), B_244, k2_tops_1(A_243, B_244))=k2_pre_topc(A_243, B_244) | ~m1_subset_1(B_244, k1_zfmisc_1(u1_struct_0(A_243))) | ~l1_pre_topc(A_243))), inference(cnfTransformation, [status(thm)], [f_145])).
% 11.84/5.19  tff(c_4083, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_68, c_4060])).
% 11.84/5.19  tff(c_4098, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_4083])).
% 11.84/5.19  tff(c_455, plain, (![A_106, B_107]: (r2_hidden('#skF_1'(A_106, B_107), A_106) | r1_tarski(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.84/5.19  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.84/5.19  tff(c_460, plain, (![A_106]: (r1_tarski(A_106, A_106))), inference(resolution, [status(thm)], [c_455, c_4])).
% 11.84/5.19  tff(c_2504, plain, (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1949, c_14])).
% 11.84/5.19  tff(c_178, plain, (![A_88, B_89]: (r1_tarski(A_88, B_89) | ~m1_subset_1(A_88, k1_zfmisc_1(B_89)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 11.84/5.19  tff(c_191, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_68, c_178])).
% 11.84/5.19  tff(c_508, plain, (![A_113, C_114, B_115]: (r1_tarski(A_113, C_114) | ~r1_tarski(B_115, C_114) | ~r1_tarski(A_113, B_115))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.84/5.19  tff(c_650, plain, (![A_123]: (r1_tarski(A_123, u1_struct_0('#skF_2')) | ~r1_tarski(A_123, '#skF_3'))), inference(resolution, [status(thm)], [c_191, c_508])).
% 11.84/5.19  tff(c_12, plain, (![A_9, C_11, B_10]: (r1_tarski(A_9, C_11) | ~r1_tarski(B_10, C_11) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.84/5.19  tff(c_653, plain, (![A_9, A_123]: (r1_tarski(A_9, u1_struct_0('#skF_2')) | ~r1_tarski(A_9, A_123) | ~r1_tarski(A_123, '#skF_3'))), inference(resolution, [status(thm)], [c_650, c_12])).
% 11.84/5.19  tff(c_2512, plain, (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2')) | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_2504, c_653])).
% 11.84/5.19  tff(c_2518, plain, (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_460, c_2512])).
% 11.84/5.19  tff(c_52, plain, (![A_51, B_52]: (m1_subset_1(A_51, k1_zfmisc_1(B_52)) | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_102])).
% 11.84/5.19  tff(c_2950, plain, (![A_213, B_214, C_215]: (k4_subset_1(A_213, B_214, C_215)=k2_xboole_0(B_214, C_215) | ~m1_subset_1(C_215, k1_zfmisc_1(A_213)) | ~m1_subset_1(B_214, k1_zfmisc_1(A_213)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.84/5.19  tff(c_14570, plain, (![B_413, B_414, A_415]: (k4_subset_1(B_413, B_414, A_415)=k2_xboole_0(B_414, A_415) | ~m1_subset_1(B_414, k1_zfmisc_1(B_413)) | ~r1_tarski(A_415, B_413))), inference(resolution, [status(thm)], [c_52, c_2950])).
% 11.84/5.19  tff(c_15122, plain, (![A_419]: (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', A_419)=k2_xboole_0('#skF_3', A_419) | ~r1_tarski(A_419, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_68, c_14570])).
% 11.84/5.19  tff(c_15220, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_2518, c_15122])).
% 11.84/5.19  tff(c_15288, plain, (k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4098, c_15220])).
% 11.84/5.19  tff(c_17869, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_17539, c_15288])).
% 11.84/5.19  tff(c_17871, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3618, c_17869])).
% 11.84/5.19  tff(c_17872, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))!=k2_tops_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_74])).
% 11.84/5.19  tff(c_18059, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_145, c_17872])).
% 11.84/5.19  tff(c_18060, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_80])).
% 11.84/5.19  tff(c_18165, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))!=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18060, c_74])).
% 11.84/5.19  tff(c_19627, plain, (k4_xboole_0('#skF_3', k1_tops_1('#skF_2', '#skF_3'))!=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_19477, c_18165])).
% 11.84/5.19  tff(c_20425, plain, (![A_581, B_582]: (k2_pre_topc(A_581, B_582)=B_582 | ~v4_pre_topc(B_582, A_581) | ~m1_subset_1(B_582, k1_zfmisc_1(u1_struct_0(A_581))) | ~l1_pre_topc(A_581))), inference(cnfTransformation, [status(thm)], [f_117])).
% 11.84/5.19  tff(c_20451, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_68, c_20425])).
% 11.84/5.19  tff(c_20460, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_18060, c_20451])).
% 11.84/5.19  tff(c_21622, plain, (![A_620, B_621]: (k4_subset_1(u1_struct_0(A_620), B_621, k2_tops_1(A_620, B_621))=k2_pre_topc(A_620, B_621) | ~m1_subset_1(B_621, k1_zfmisc_1(u1_struct_0(A_620))) | ~l1_pre_topc(A_620))), inference(cnfTransformation, [status(thm)], [f_145])).
% 11.84/5.19  tff(c_21645, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_68, c_21622])).
% 11.84/5.19  tff(c_21660, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_20460, c_21645])).
% 11.84/5.19  tff(c_19110, plain, (![A_525, B_526]: (k4_xboole_0(A_525, B_526)=k3_subset_1(A_525, B_526) | ~m1_subset_1(B_526, k1_zfmisc_1(A_525)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.84/5.19  tff(c_19136, plain, (k4_xboole_0(u1_struct_0('#skF_2'), '#skF_3')=k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_68, c_19110])).
% 11.84/5.19  tff(c_42, plain, (![A_42, B_43]: (k6_subset_1(A_42, B_43)=k4_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.84/5.19  tff(c_36, plain, (![A_35, B_36]: (m1_subset_1(k6_subset_1(A_35, B_36), k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.84/5.19  tff(c_81, plain, (![A_35, B_36]: (m1_subset_1(k4_xboole_0(A_35, B_36), k1_zfmisc_1(A_35)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36])).
% 11.84/5.19  tff(c_19190, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_19136, c_81])).
% 11.84/5.19  tff(c_21416, plain, (![A_615, B_616]: (k2_tops_1(A_615, k3_subset_1(u1_struct_0(A_615), B_616))=k2_tops_1(A_615, B_616) | ~m1_subset_1(B_616, k1_zfmisc_1(u1_struct_0(A_615))) | ~l1_pre_topc(A_615))), inference(cnfTransformation, [status(thm)], [f_138])).
% 11.84/5.19  tff(c_21437, plain, (k2_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k2_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_68, c_21416])).
% 11.84/5.19  tff(c_21451, plain, (k2_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_21437])).
% 11.84/5.19  tff(c_58, plain, (![A_56, B_57]: (m1_subset_1(k2_tops_1(A_56, B_57), k1_zfmisc_1(u1_struct_0(A_56))) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_123])).
% 11.84/5.19  tff(c_21458, plain, (m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_21451, c_58])).
% 11.84/5.19  tff(c_21462, plain, (m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_19190, c_21458])).
% 11.84/5.19  tff(c_50, plain, (![A_51, B_52]: (r1_tarski(A_51, B_52) | ~m1_subset_1(A_51, k1_zfmisc_1(B_52)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 11.84/5.19  tff(c_21510, plain, (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_21462, c_50])).
% 11.84/5.19  tff(c_20860, plain, (![A_596, B_597, C_598]: (k4_subset_1(A_596, B_597, C_598)=k2_xboole_0(B_597, C_598) | ~m1_subset_1(C_598, k1_zfmisc_1(A_596)) | ~m1_subset_1(B_597, k1_zfmisc_1(A_596)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.84/5.19  tff(c_35313, plain, (![B_788, B_789, A_790]: (k4_subset_1(B_788, B_789, A_790)=k2_xboole_0(B_789, A_790) | ~m1_subset_1(B_789, k1_zfmisc_1(B_788)) | ~r1_tarski(A_790, B_788))), inference(resolution, [status(thm)], [c_52, c_20860])).
% 11.84/5.19  tff(c_36040, plain, (![A_795]: (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', A_795)=k2_xboole_0('#skF_3', A_795) | ~r1_tarski(A_795, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_68, c_35313])).
% 11.84/5.19  tff(c_36099, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_21510, c_36040])).
% 11.84/5.19  tff(c_36171, plain, (k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_21660, c_36099])).
% 11.84/5.19  tff(c_19223, plain, (![A_531, B_532, C_533]: (r1_tarski(A_531, k2_xboole_0(B_532, C_533)) | ~r1_tarski(k4_xboole_0(A_531, B_532), C_533))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.84/5.19  tff(c_19268, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(B_13, A_12)))), inference(resolution, [status(thm)], [c_14, c_19223])).
% 11.84/5.19  tff(c_36272, plain, (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36171, c_19268])).
% 11.84/5.19  tff(c_22043, plain, (![A_635, B_636]: (k7_subset_1(u1_struct_0(A_635), B_636, k2_tops_1(A_635, B_636))=k1_tops_1(A_635, B_636) | ~m1_subset_1(B_636, k1_zfmisc_1(u1_struct_0(A_635))) | ~l1_pre_topc(A_635))), inference(cnfTransformation, [status(thm)], [f_152])).
% 11.84/5.19  tff(c_22066, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_68, c_22043])).
% 11.84/5.19  tff(c_22083, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_19477, c_22066])).
% 11.84/5.19  tff(c_19134, plain, (![B_52, A_51]: (k4_xboole_0(B_52, A_51)=k3_subset_1(B_52, A_51) | ~r1_tarski(A_51, B_52))), inference(resolution, [status(thm)], [c_52, c_19110])).
% 11.84/5.19  tff(c_36300, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k3_subset_1('#skF_3', k2_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_36272, c_19134])).
% 11.84/5.19  tff(c_36308, plain, (k3_subset_1('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22083, c_36300])).
% 11.84/5.19  tff(c_18738, plain, (![A_510, B_511]: (k3_subset_1(A_510, k3_subset_1(A_510, B_511))=B_511 | ~m1_subset_1(B_511, k1_zfmisc_1(A_510)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.84/5.19  tff(c_18748, plain, (![B_52, A_51]: (k3_subset_1(B_52, k3_subset_1(B_52, A_51))=A_51 | ~r1_tarski(A_51, B_52))), inference(resolution, [status(thm)], [c_52, c_18738])).
% 11.84/5.19  tff(c_37161, plain, (k3_subset_1('#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3') | ~r1_tarski(k2_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36308, c_18748])).
% 11.84/5.19  tff(c_37172, plain, (k3_subset_1('#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36272, c_37161])).
% 11.84/5.19  tff(c_24623, plain, (![A_690, B_691]: (k4_xboole_0(A_690, k4_xboole_0(A_690, B_691))=k3_subset_1(A_690, k4_xboole_0(A_690, B_691)))), inference(resolution, [status(thm)], [c_81, c_19110])).
% 11.84/5.19  tff(c_24951, plain, (![A_694, B_695]: (m1_subset_1(k3_subset_1(A_694, k4_xboole_0(A_694, B_695)), k1_zfmisc_1(A_694)))), inference(superposition, [status(thm), theory('equality')], [c_24623, c_81])).
% 11.84/5.19  tff(c_25013, plain, (m1_subset_1(k3_subset_1('#skF_3', k1_tops_1('#skF_2', '#skF_3')), k1_zfmisc_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_22083, c_24951])).
% 11.84/5.19  tff(c_37176, plain, (m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_37172, c_25013])).
% 11.84/5.19  tff(c_34, plain, (![A_33, B_34]: (m1_subset_1(k3_subset_1(A_33, B_34), k1_zfmisc_1(A_33)) | ~m1_subset_1(B_34, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.84/5.19  tff(c_19129, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k3_subset_1(A_33, B_34))=k3_subset_1(A_33, k3_subset_1(A_33, B_34)) | ~m1_subset_1(B_34, k1_zfmisc_1(A_33)))), inference(resolution, [status(thm)], [c_34, c_19110])).
% 11.84/5.19  tff(c_37212, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', k2_tops_1('#skF_2', '#skF_3')))=k3_subset_1('#skF_3', k3_subset_1('#skF_3', k2_tops_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_37176, c_19129])).
% 11.84/5.19  tff(c_37232, plain, (k4_xboole_0('#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_37172, c_36308, c_36308, c_37212])).
% 11.84/5.19  tff(c_37234, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19627, c_37232])).
% 11.84/5.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.84/5.19  
% 11.84/5.19  Inference rules
% 11.84/5.19  ----------------------
% 11.84/5.19  #Ref     : 0
% 11.84/5.19  #Sup     : 9054
% 11.84/5.19  #Fact    : 0
% 11.84/5.19  #Define  : 0
% 11.84/5.19  #Split   : 5
% 11.84/5.19  #Chain   : 0
% 11.84/5.19  #Close   : 0
% 11.84/5.19  
% 11.84/5.19  Ordering : KBO
% 11.84/5.19  
% 11.84/5.19  Simplification rules
% 11.84/5.19  ----------------------
% 11.84/5.19  #Subsume      : 418
% 11.84/5.19  #Demod        : 9013
% 11.84/5.19  #Tautology    : 6285
% 11.84/5.19  #SimpNegUnit  : 5
% 11.84/5.19  #BackRed      : 28
% 11.84/5.19  
% 11.84/5.19  #Partial instantiations: 0
% 11.84/5.19  #Strategies tried      : 1
% 11.84/5.19  
% 11.84/5.19  Timing (in seconds)
% 11.84/5.19  ----------------------
% 11.84/5.19  Preprocessing        : 0.34
% 11.84/5.19  Parsing              : 0.17
% 11.84/5.19  CNF conversion       : 0.03
% 11.84/5.19  Main loop            : 3.95
% 11.84/5.19  Inferencing          : 0.78
% 11.84/5.19  Reduction            : 2.14
% 11.84/5.19  Demodulation         : 1.84
% 11.84/5.19  BG Simplification    : 0.08
% 11.84/5.19  Subsumption          : 0.74
% 11.84/5.19  Abstraction          : 0.13
% 11.84/5.19  MUC search           : 0.00
% 11.84/5.19  Cooper               : 0.00
% 11.84/5.19  Total                : 4.35
% 11.84/5.19  Index Insertion      : 0.00
% 11.84/5.19  Index Deletion       : 0.00
% 11.84/5.19  Index Matching       : 0.00
% 11.84/5.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
