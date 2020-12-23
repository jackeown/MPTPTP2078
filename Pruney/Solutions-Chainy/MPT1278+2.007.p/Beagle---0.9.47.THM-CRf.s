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
% DateTime   : Thu Dec  3 10:22:09 EST 2020

% Result     : Theorem 4.38s
% Output     : CNFRefutation 4.50s
% Verified   : 
% Statistics : Number of formulae       :  153 (1997 expanded)
%              Number of leaves         :   44 ( 702 expanded)
%              Depth                    :   18
%              Number of atoms          :  294 (5235 expanded)
%              Number of equality atoms :   73 ( 998 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v3_pre_topc > v2_tops_1 > v1_tops_1 > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_149,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v3_pre_topc(B,A)
                & v3_tops_1(B,A) )
             => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_tops_1)).

tff(f_135,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_117,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_50,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_tops_1)).

tff(f_30,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_126,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_tops_1)).

tff(f_34,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).

tff(f_71,axiom,(
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

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_32,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_28,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_58,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_56,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_50,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_54,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_237,plain,(
    ! [B_66,A_67] :
      ( v2_tops_1(B_66,A_67)
      | ~ v3_tops_1(B_66,A_67)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_248,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_237])).

tff(c_257,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50,c_248])).

tff(c_489,plain,(
    ! [A_91,B_92] :
      ( k1_tops_1(A_91,B_92) = k1_xboole_0
      | ~ v2_tops_1(B_92,A_91)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_500,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_489])).

tff(c_509,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_257,c_500])).

tff(c_334,plain,(
    ! [A_74,B_75] :
      ( v3_pre_topc(k1_tops_1(A_74,B_75),A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_342,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_334])).

tff(c_350,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_342])).

tff(c_511,plain,(
    v3_pre_topc(k1_xboole_0,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_509,c_350])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_20,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_521,plain,(
    ! [B_94,A_95] :
      ( v3_tops_1(B_94,A_95)
      | ~ v1_xboole_0(B_94)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_536,plain,(
    ! [A_95] :
      ( v3_tops_1(k1_xboole_0,A_95)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95) ) ),
    inference(resolution,[status(thm)],[c_20,c_521])).

tff(c_544,plain,(
    ! [A_95] :
      ( v3_tops_1(k1_xboole_0,A_95)
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_536])).

tff(c_6,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_218,plain,(
    ! [A_64,B_65] :
      ( k4_xboole_0(A_64,B_65) = k3_subset_1(A_64,B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_230,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = k3_subset_1(A_13,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_218])).

tff(c_236,plain,(
    ! [A_13] : k3_subset_1(A_13,k1_xboole_0) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_230])).

tff(c_786,plain,(
    ! [A_117,B_118] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_117),B_118),A_117)
      | ~ v3_tops_1(B_118,A_117)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_794,plain,(
    ! [A_117] :
      ( v1_tops_1(u1_struct_0(A_117),A_117)
      | ~ v3_tops_1(k1_xboole_0,A_117)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_786])).

tff(c_809,plain,(
    ! [A_119] :
      ( v1_tops_1(u1_struct_0(A_119),A_119)
      | ~ v3_tops_1(k1_xboole_0,A_119)
      | ~ l1_pre_topc(A_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_794])).

tff(c_10,plain,(
    ! [A_5] : k2_subset_1(A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1(k2_subset_1(A_8),k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_59,plain,(
    ! [A_8] : m1_subset_1(A_8,k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14])).

tff(c_660,plain,(
    ! [A_109,B_110] :
      ( k2_pre_topc(A_109,B_110) = k2_struct_0(A_109)
      | ~ v1_tops_1(B_110,A_109)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_677,plain,(
    ! [A_109] :
      ( k2_pre_topc(A_109,u1_struct_0(A_109)) = k2_struct_0(A_109)
      | ~ v1_tops_1(u1_struct_0(A_109),A_109)
      | ~ l1_pre_topc(A_109) ) ),
    inference(resolution,[status(thm)],[c_59,c_660])).

tff(c_813,plain,(
    ! [A_119] :
      ( k2_pre_topc(A_119,u1_struct_0(A_119)) = k2_struct_0(A_119)
      | ~ v3_tops_1(k1_xboole_0,A_119)
      | ~ l1_pre_topc(A_119) ) ),
    inference(resolution,[status(thm)],[c_809,c_677])).

tff(c_873,plain,(
    ! [A_127,B_128] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_127),B_128),A_127)
      | ~ v3_pre_topc(B_128,A_127)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_881,plain,(
    ! [A_127] :
      ( v4_pre_topc(u1_struct_0(A_127),A_127)
      | ~ v3_pre_topc(k1_xboole_0,A_127)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_873])).

tff(c_968,plain,(
    ! [A_130] :
      ( v4_pre_topc(u1_struct_0(A_130),A_130)
      | ~ v3_pre_topc(k1_xboole_0,A_130)
      | ~ l1_pre_topc(A_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_881])).

tff(c_446,plain,(
    ! [A_87,B_88] :
      ( k2_pre_topc(A_87,B_88) = B_88
      | ~ v4_pre_topc(B_88,A_87)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_463,plain,(
    ! [A_87] :
      ( k2_pre_topc(A_87,u1_struct_0(A_87)) = u1_struct_0(A_87)
      | ~ v4_pre_topc(u1_struct_0(A_87),A_87)
      | ~ l1_pre_topc(A_87) ) ),
    inference(resolution,[status(thm)],[c_59,c_446])).

tff(c_974,plain,(
    ! [A_132] :
      ( k2_pre_topc(A_132,u1_struct_0(A_132)) = u1_struct_0(A_132)
      | ~ v3_pre_topc(k1_xboole_0,A_132)
      | ~ l1_pre_topc(A_132) ) ),
    inference(resolution,[status(thm)],[c_968,c_463])).

tff(c_1082,plain,(
    ! [A_140] :
      ( u1_struct_0(A_140) = k2_struct_0(A_140)
      | ~ v3_pre_topc(k1_xboole_0,A_140)
      | ~ l1_pre_topc(A_140)
      | ~ v3_tops_1(k1_xboole_0,A_140)
      | ~ l1_pre_topc(A_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_813,c_974])).

tff(c_1087,plain,(
    ! [A_141] :
      ( u1_struct_0(A_141) = k2_struct_0(A_141)
      | ~ v3_pre_topc(k1_xboole_0,A_141)
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141) ) ),
    inference(resolution,[status(thm)],[c_544,c_1082])).

tff(c_1090,plain,
    ( u1_struct_0('#skF_1') = k2_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_511,c_1087])).

tff(c_1093,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1090])).

tff(c_1110,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1093,c_54])).

tff(c_52,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_38,plain,(
    ! [A_28,B_30] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_28),B_30),A_28)
      | ~ v3_pre_topc(B_30,A_28)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1135,plain,(
    ! [B_30] :
      ( v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),B_30),'#skF_1')
      | ~ v3_pre_topc(B_30,'#skF_1')
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1093,c_38])).

tff(c_1988,plain,(
    ! [B_172] :
      ( v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),B_172),'#skF_1')
      | ~ v3_pre_topc(B_172,'#skF_1')
      | ~ m1_subset_1(B_172,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1093,c_1135])).

tff(c_44,plain,(
    ! [A_34,B_36] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_34),B_36),A_34)
      | ~ v3_tops_1(B_36,A_34)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k3_subset_1(A_9,B_10),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_603,plain,(
    ! [B_105,A_106] :
      ( v1_tops_1(B_105,A_106)
      | k2_pre_topc(A_106,B_105) != k2_struct_0(A_106)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_614,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_603])).

tff(c_623,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_614])).

tff(c_635,plain,(
    k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_623])).

tff(c_671,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_660])).

tff(c_680,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_671])).

tff(c_681,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_635,c_680])).

tff(c_159,plain,(
    ! [A_58,B_59] :
      ( k3_subset_1(A_58,k3_subset_1(A_58,B_59)) = B_59
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_167,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_54,c_159])).

tff(c_801,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_786])).

tff(c_807,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_801])).

tff(c_808,plain,
    ( ~ v3_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_681,c_807])).

tff(c_863,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_808])).

tff(c_866,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_16,c_863])).

tff(c_870,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_866])).

tff(c_872,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_808])).

tff(c_30,plain,(
    ! [B_25,A_23] :
      ( v1_tops_1(B_25,A_23)
      | k2_pre_topc(A_23,B_25) != k2_struct_0(A_23)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_904,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_872,c_30])).

tff(c_939,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_904])).

tff(c_1042,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_939])).

tff(c_32,plain,(
    ! [A_23,B_25] :
      ( k2_pre_topc(A_23,B_25) = k2_struct_0(A_23)
      | ~ v1_tops_1(B_25,A_23)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_901,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_872,c_32])).

tff(c_936,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_901])).

tff(c_1065,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1042,c_936])).

tff(c_1068,plain,
    ( ~ v3_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1065])).

tff(c_1072,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_1068])).

tff(c_1074,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_939])).

tff(c_1094,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1093,c_1074])).

tff(c_1102,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1093,c_1093,c_872])).

tff(c_24,plain,(
    ! [B_19,A_17] :
      ( v4_pre_topc(B_19,A_17)
      | k2_pre_topc(A_17,B_19) != B_19
      | ~ v2_pre_topc(A_17)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1150,plain,(
    ! [B_19] :
      ( v4_pre_topc(B_19,'#skF_1')
      | k2_pre_topc('#skF_1',B_19) != B_19
      | ~ v2_pre_topc('#skF_1')
      | ~ m1_subset_1(B_19,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1093,c_24])).

tff(c_1752,plain,(
    ! [B_162] :
      ( v4_pre_topc(B_162,'#skF_1')
      | k2_pre_topc('#skF_1',B_162) != B_162
      | ~ m1_subset_1(B_162,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_1150])).

tff(c_1755,plain,
    ( v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1102,c_1752])).

tff(c_1772,plain,
    ( v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1094,c_1755])).

tff(c_1840,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1772])).

tff(c_26,plain,(
    ! [A_17,B_19] :
      ( k2_pre_topc(A_17,B_19) = B_19
      | ~ v4_pre_topc(B_19,A_17)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1191,plain,(
    ! [B_19] :
      ( k2_pre_topc('#skF_1',B_19) = B_19
      | ~ v4_pre_topc(B_19,'#skF_1')
      | ~ m1_subset_1(B_19,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1093,c_26])).

tff(c_1781,plain,(
    ! [B_163] :
      ( k2_pre_topc('#skF_1',B_163) = B_163
      | ~ v4_pre_topc(B_163,'#skF_1')
      | ~ m1_subset_1(B_163,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1191])).

tff(c_1784,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')
    | ~ v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1102,c_1781])).

tff(c_1801,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') = k2_struct_0('#skF_1')
    | ~ v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1094,c_1784])).

tff(c_1867,plain,(
    ~ v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1840,c_1801])).

tff(c_1991,plain,
    ( ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1988,c_1867])).

tff(c_2010,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1110,c_52,c_1991])).

tff(c_2012,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1772])).

tff(c_234,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),'#skF_2') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_218])).

tff(c_8,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_306,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_xboole_0(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_8])).

tff(c_587,plain,(
    ! [A_103,B_104] :
      ( k4_xboole_0(A_103,k3_subset_1(A_103,B_104)) = k3_subset_1(A_103,k3_subset_1(A_103,B_104))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_103)) ) ),
    inference(resolution,[status(thm)],[c_16,c_218])).

tff(c_593,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_587])).

tff(c_600,plain,(
    k3_xboole_0(u1_struct_0('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_167,c_593])).

tff(c_626,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_306])).

tff(c_1105,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1093,c_1093,c_626])).

tff(c_2020,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2012,c_1105])).

tff(c_4,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_87,plain,(
    ! [A_46,B_47] : k4_xboole_0(A_46,k4_xboole_0(A_46,B_47)) = k3_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_102,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k3_xboole_0(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_87])).

tff(c_105,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_102])).

tff(c_2059,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2020,c_105])).

tff(c_2069,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_2059])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:54:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.38/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.50/1.81  
% 4.50/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.50/1.82  %$ v4_pre_topc > v3_tops_1 > v3_pre_topc > v2_tops_1 > v1_tops_1 > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.50/1.82  
% 4.50/1.82  %Foreground sorts:
% 4.50/1.82  
% 4.50/1.82  
% 4.50/1.82  %Background operators:
% 4.50/1.82  
% 4.50/1.82  
% 4.50/1.82  %Foreground operators:
% 4.50/1.82  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.50/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.50/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.50/1.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.50/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.50/1.82  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 4.50/1.82  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.50/1.82  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 4.50/1.82  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.50/1.82  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 4.50/1.82  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.50/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.50/1.82  tff('#skF_1', type, '#skF_1': $i).
% 4.50/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.50/1.82  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.50/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.50/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.50/1.82  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.50/1.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.50/1.82  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.50/1.82  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.50/1.82  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.50/1.82  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.50/1.82  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.50/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.50/1.82  
% 4.50/1.85  tff(f_149, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tops_1(B, A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_tops_1)).
% 4.50/1.85  tff(f_135, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_tops_1)).
% 4.50/1.85  tff(f_117, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 4.50/1.85  tff(f_99, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 4.50/1.85  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.50/1.85  tff(f_50, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.50/1.85  tff(f_82, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_tops_1)).
% 4.50/1.85  tff(f_30, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.50/1.85  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 4.50/1.85  tff(f_126, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_tops_1)).
% 4.50/1.85  tff(f_34, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.50/1.85  tff(f_40, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.50/1.85  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 4.50/1.85  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_tops_1)).
% 4.50/1.85  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.50/1.85  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.50/1.85  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.50/1.85  tff(f_32, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.50/1.85  tff(f_28, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.50/1.85  tff(c_48, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.50/1.85  tff(c_58, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.50/1.85  tff(c_56, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.50/1.85  tff(c_50, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.50/1.85  tff(c_54, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.50/1.85  tff(c_237, plain, (![B_66, A_67]: (v2_tops_1(B_66, A_67) | ~v3_tops_1(B_66, A_67) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.50/1.85  tff(c_248, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_237])).
% 4.50/1.85  tff(c_257, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50, c_248])).
% 4.50/1.85  tff(c_489, plain, (![A_91, B_92]: (k1_tops_1(A_91, B_92)=k1_xboole_0 | ~v2_tops_1(B_92, A_91) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.50/1.85  tff(c_500, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_489])).
% 4.50/1.85  tff(c_509, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_257, c_500])).
% 4.50/1.85  tff(c_334, plain, (![A_74, B_75]: (v3_pre_topc(k1_tops_1(A_74, B_75), A_74) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.50/1.85  tff(c_342, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_334])).
% 4.50/1.85  tff(c_350, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_342])).
% 4.50/1.85  tff(c_511, plain, (v3_pre_topc(k1_xboole_0, '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_509, c_350])).
% 4.50/1.85  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.50/1.85  tff(c_20, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.50/1.85  tff(c_521, plain, (![B_94, A_95]: (v3_tops_1(B_94, A_95) | ~v1_xboole_0(B_94) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.50/1.85  tff(c_536, plain, (![A_95]: (v3_tops_1(k1_xboole_0, A_95) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95))), inference(resolution, [status(thm)], [c_20, c_521])).
% 4.50/1.85  tff(c_544, plain, (![A_95]: (v3_tops_1(k1_xboole_0, A_95) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_536])).
% 4.50/1.85  tff(c_6, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.50/1.85  tff(c_218, plain, (![A_64, B_65]: (k4_xboole_0(A_64, B_65)=k3_subset_1(A_64, B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.50/1.85  tff(c_230, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=k3_subset_1(A_13, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_218])).
% 4.50/1.85  tff(c_236, plain, (![A_13]: (k3_subset_1(A_13, k1_xboole_0)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_230])).
% 4.50/1.85  tff(c_786, plain, (![A_117, B_118]: (v1_tops_1(k3_subset_1(u1_struct_0(A_117), B_118), A_117) | ~v3_tops_1(B_118, A_117) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.50/1.85  tff(c_794, plain, (![A_117]: (v1_tops_1(u1_struct_0(A_117), A_117) | ~v3_tops_1(k1_xboole_0, A_117) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117))), inference(superposition, [status(thm), theory('equality')], [c_236, c_786])).
% 4.50/1.85  tff(c_809, plain, (![A_119]: (v1_tops_1(u1_struct_0(A_119), A_119) | ~v3_tops_1(k1_xboole_0, A_119) | ~l1_pre_topc(A_119))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_794])).
% 4.50/1.85  tff(c_10, plain, (![A_5]: (k2_subset_1(A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.50/1.85  tff(c_14, plain, (![A_8]: (m1_subset_1(k2_subset_1(A_8), k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.50/1.85  tff(c_59, plain, (![A_8]: (m1_subset_1(A_8, k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14])).
% 4.50/1.85  tff(c_660, plain, (![A_109, B_110]: (k2_pre_topc(A_109, B_110)=k2_struct_0(A_109) | ~v1_tops_1(B_110, A_109) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.50/1.85  tff(c_677, plain, (![A_109]: (k2_pre_topc(A_109, u1_struct_0(A_109))=k2_struct_0(A_109) | ~v1_tops_1(u1_struct_0(A_109), A_109) | ~l1_pre_topc(A_109))), inference(resolution, [status(thm)], [c_59, c_660])).
% 4.50/1.85  tff(c_813, plain, (![A_119]: (k2_pre_topc(A_119, u1_struct_0(A_119))=k2_struct_0(A_119) | ~v3_tops_1(k1_xboole_0, A_119) | ~l1_pre_topc(A_119))), inference(resolution, [status(thm)], [c_809, c_677])).
% 4.50/1.85  tff(c_873, plain, (![A_127, B_128]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_127), B_128), A_127) | ~v3_pre_topc(B_128, A_127) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.50/1.85  tff(c_881, plain, (![A_127]: (v4_pre_topc(u1_struct_0(A_127), A_127) | ~v3_pre_topc(k1_xboole_0, A_127) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127))), inference(superposition, [status(thm), theory('equality')], [c_236, c_873])).
% 4.50/1.85  tff(c_968, plain, (![A_130]: (v4_pre_topc(u1_struct_0(A_130), A_130) | ~v3_pre_topc(k1_xboole_0, A_130) | ~l1_pre_topc(A_130))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_881])).
% 4.50/1.85  tff(c_446, plain, (![A_87, B_88]: (k2_pre_topc(A_87, B_88)=B_88 | ~v4_pre_topc(B_88, A_87) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.50/1.85  tff(c_463, plain, (![A_87]: (k2_pre_topc(A_87, u1_struct_0(A_87))=u1_struct_0(A_87) | ~v4_pre_topc(u1_struct_0(A_87), A_87) | ~l1_pre_topc(A_87))), inference(resolution, [status(thm)], [c_59, c_446])).
% 4.50/1.85  tff(c_974, plain, (![A_132]: (k2_pre_topc(A_132, u1_struct_0(A_132))=u1_struct_0(A_132) | ~v3_pre_topc(k1_xboole_0, A_132) | ~l1_pre_topc(A_132))), inference(resolution, [status(thm)], [c_968, c_463])).
% 4.50/1.85  tff(c_1082, plain, (![A_140]: (u1_struct_0(A_140)=k2_struct_0(A_140) | ~v3_pre_topc(k1_xboole_0, A_140) | ~l1_pre_topc(A_140) | ~v3_tops_1(k1_xboole_0, A_140) | ~l1_pre_topc(A_140))), inference(superposition, [status(thm), theory('equality')], [c_813, c_974])).
% 4.50/1.85  tff(c_1087, plain, (![A_141]: (u1_struct_0(A_141)=k2_struct_0(A_141) | ~v3_pre_topc(k1_xboole_0, A_141) | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141))), inference(resolution, [status(thm)], [c_544, c_1082])).
% 4.50/1.85  tff(c_1090, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_511, c_1087])).
% 4.50/1.85  tff(c_1093, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1090])).
% 4.50/1.85  tff(c_1110, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1093, c_54])).
% 4.50/1.85  tff(c_52, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.50/1.85  tff(c_38, plain, (![A_28, B_30]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_28), B_30), A_28) | ~v3_pre_topc(B_30, A_28) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.50/1.85  tff(c_1135, plain, (![B_30]: (v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), B_30), '#skF_1') | ~v3_pre_topc(B_30, '#skF_1') | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1093, c_38])).
% 4.50/1.85  tff(c_1988, plain, (![B_172]: (v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), B_172), '#skF_1') | ~v3_pre_topc(B_172, '#skF_1') | ~m1_subset_1(B_172, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1093, c_1135])).
% 4.50/1.85  tff(c_44, plain, (![A_34, B_36]: (v1_tops_1(k3_subset_1(u1_struct_0(A_34), B_36), A_34) | ~v3_tops_1(B_36, A_34) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.50/1.85  tff(c_16, plain, (![A_9, B_10]: (m1_subset_1(k3_subset_1(A_9, B_10), k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.50/1.85  tff(c_603, plain, (![B_105, A_106]: (v1_tops_1(B_105, A_106) | k2_pre_topc(A_106, B_105)!=k2_struct_0(A_106) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.50/1.85  tff(c_614, plain, (v1_tops_1('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_603])).
% 4.50/1.85  tff(c_623, plain, (v1_tops_1('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_614])).
% 4.50/1.85  tff(c_635, plain, (k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_623])).
% 4.50/1.85  tff(c_671, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_660])).
% 4.50/1.85  tff(c_680, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_671])).
% 4.50/1.85  tff(c_681, plain, (~v1_tops_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_635, c_680])).
% 4.50/1.85  tff(c_159, plain, (![A_58, B_59]: (k3_subset_1(A_58, k3_subset_1(A_58, B_59))=B_59 | ~m1_subset_1(B_59, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.50/1.85  tff(c_167, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_54, c_159])).
% 4.50/1.85  tff(c_801, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v3_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_167, c_786])).
% 4.50/1.85  tff(c_807, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v3_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_801])).
% 4.50/1.85  tff(c_808, plain, (~v3_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_681, c_807])).
% 4.50/1.85  tff(c_863, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_808])).
% 4.50/1.85  tff(c_866, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_16, c_863])).
% 4.50/1.85  tff(c_870, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_866])).
% 4.50/1.85  tff(c_872, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_808])).
% 4.50/1.85  tff(c_30, plain, (![B_25, A_23]: (v1_tops_1(B_25, A_23) | k2_pre_topc(A_23, B_25)!=k2_struct_0(A_23) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.50/1.85  tff(c_904, plain, (v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_872, c_30])).
% 4.50/1.85  tff(c_939, plain, (v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_904])).
% 4.50/1.85  tff(c_1042, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_939])).
% 4.50/1.85  tff(c_32, plain, (![A_23, B_25]: (k2_pre_topc(A_23, B_25)=k2_struct_0(A_23) | ~v1_tops_1(B_25, A_23) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.50/1.85  tff(c_901, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_872, c_32])).
% 4.50/1.85  tff(c_936, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_901])).
% 4.50/1.85  tff(c_1065, plain, (~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1042, c_936])).
% 4.50/1.85  tff(c_1068, plain, (~v3_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_1065])).
% 4.50/1.85  tff(c_1072, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_1068])).
% 4.50/1.85  tff(c_1074, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_939])).
% 4.50/1.85  tff(c_1094, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1093, c_1074])).
% 4.50/1.85  tff(c_1102, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1093, c_1093, c_872])).
% 4.50/1.85  tff(c_24, plain, (![B_19, A_17]: (v4_pre_topc(B_19, A_17) | k2_pre_topc(A_17, B_19)!=B_19 | ~v2_pre_topc(A_17) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.50/1.85  tff(c_1150, plain, (![B_19]: (v4_pre_topc(B_19, '#skF_1') | k2_pre_topc('#skF_1', B_19)!=B_19 | ~v2_pre_topc('#skF_1') | ~m1_subset_1(B_19, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1093, c_24])).
% 4.50/1.85  tff(c_1752, plain, (![B_162]: (v4_pre_topc(B_162, '#skF_1') | k2_pre_topc('#skF_1', B_162)!=B_162 | ~m1_subset_1(B_162, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_1150])).
% 4.50/1.85  tff(c_1755, plain, (v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_1102, c_1752])).
% 4.50/1.85  tff(c_1772, plain, (v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1094, c_1755])).
% 4.50/1.85  tff(c_1840, plain, (k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_1772])).
% 4.50/1.85  tff(c_26, plain, (![A_17, B_19]: (k2_pre_topc(A_17, B_19)=B_19 | ~v4_pre_topc(B_19, A_17) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.50/1.85  tff(c_1191, plain, (![B_19]: (k2_pre_topc('#skF_1', B_19)=B_19 | ~v4_pre_topc(B_19, '#skF_1') | ~m1_subset_1(B_19, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1093, c_26])).
% 4.50/1.85  tff(c_1781, plain, (![B_163]: (k2_pre_topc('#skF_1', B_163)=B_163 | ~v4_pre_topc(B_163, '#skF_1') | ~m1_subset_1(B_163, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1191])).
% 4.50/1.85  tff(c_1784, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2') | ~v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_1102, c_1781])).
% 4.50/1.85  tff(c_1801, plain, (k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')=k2_struct_0('#skF_1') | ~v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1094, c_1784])).
% 4.50/1.85  tff(c_1867, plain, (~v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1840, c_1801])).
% 4.50/1.85  tff(c_1991, plain, (~v3_pre_topc('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1988, c_1867])).
% 4.50/1.85  tff(c_2010, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1110, c_52, c_1991])).
% 4.50/1.85  tff(c_2012, plain, (k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_1772])).
% 4.50/1.85  tff(c_234, plain, (k4_xboole_0(u1_struct_0('#skF_1'), '#skF_2')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_54, c_218])).
% 4.50/1.85  tff(c_8, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.50/1.85  tff(c_306, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_xboole_0(u1_struct_0('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_234, c_8])).
% 4.50/1.85  tff(c_587, plain, (![A_103, B_104]: (k4_xboole_0(A_103, k3_subset_1(A_103, B_104))=k3_subset_1(A_103, k3_subset_1(A_103, B_104)) | ~m1_subset_1(B_104, k1_zfmisc_1(A_103)))), inference(resolution, [status(thm)], [c_16, c_218])).
% 4.50/1.85  tff(c_593, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_54, c_587])).
% 4.50/1.85  tff(c_600, plain, (k3_xboole_0(u1_struct_0('#skF_1'), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_306, c_167, c_593])).
% 4.50/1.85  tff(c_626, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_600, c_306])).
% 4.50/1.85  tff(c_1105, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1093, c_1093, c_626])).
% 4.50/1.85  tff(c_2020, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2012, c_1105])).
% 4.50/1.85  tff(c_4, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 4.50/1.85  tff(c_87, plain, (![A_46, B_47]: (k4_xboole_0(A_46, k4_xboole_0(A_46, B_47))=k3_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.50/1.85  tff(c_102, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k3_xboole_0(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_87])).
% 4.50/1.85  tff(c_105, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_102])).
% 4.50/1.85  tff(c_2059, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2020, c_105])).
% 4.50/1.85  tff(c_2069, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_2059])).
% 4.50/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.50/1.85  
% 4.50/1.85  Inference rules
% 4.50/1.85  ----------------------
% 4.50/1.85  #Ref     : 0
% 4.50/1.85  #Sup     : 412
% 4.50/1.85  #Fact    : 0
% 4.50/1.85  #Define  : 0
% 4.50/1.85  #Split   : 12
% 4.50/1.85  #Chain   : 0
% 4.50/1.85  #Close   : 0
% 4.50/1.85  
% 4.50/1.85  Ordering : KBO
% 4.50/1.85  
% 4.50/1.85  Simplification rules
% 4.50/1.85  ----------------------
% 4.50/1.85  #Subsume      : 61
% 4.50/1.85  #Demod        : 488
% 4.50/1.85  #Tautology    : 202
% 4.50/1.85  #SimpNegUnit  : 27
% 4.50/1.85  #BackRed      : 38
% 4.50/1.85  
% 4.50/1.85  #Partial instantiations: 0
% 4.50/1.85  #Strategies tried      : 1
% 4.50/1.85  
% 4.50/1.85  Timing (in seconds)
% 4.50/1.85  ----------------------
% 4.50/1.85  Preprocessing        : 0.35
% 4.50/1.85  Parsing              : 0.20
% 4.50/1.85  CNF conversion       : 0.02
% 4.50/1.85  Main loop            : 0.66
% 4.50/1.85  Inferencing          : 0.23
% 4.50/1.85  Reduction            : 0.24
% 4.50/1.85  Demodulation         : 0.17
% 4.50/1.85  BG Simplification    : 0.03
% 4.50/1.86  Subsumption          : 0.12
% 4.50/1.86  Abstraction          : 0.03
% 4.50/1.86  MUC search           : 0.00
% 4.50/1.86  Cooper               : 0.00
% 4.50/1.86  Total                : 1.08
% 4.50/1.86  Index Insertion      : 0.00
% 4.50/1.86  Index Deletion       : 0.00
% 4.50/1.86  Index Matching       : 0.00
% 4.50/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
