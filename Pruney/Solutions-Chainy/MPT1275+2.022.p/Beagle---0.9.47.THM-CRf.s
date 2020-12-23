%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:04 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 182 expanded)
%              Number of leaves         :   38 (  78 expanded)
%              Depth                    :   10
%              Number of atoms          :  167 ( 376 expanded)
%              Number of equality atoms :   46 (  95 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_131,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => ( v3_tops_1(B,A)
              <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_119,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v2_tops_1(B,A)
              & v4_pre_topc(B,A) )
           => v3_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_tops_1)).

tff(f_37,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_74,axiom,(
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

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_50,plain,
    ( k2_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_71,plain,(
    ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_46,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_329,plain,(
    ! [B_75,A_76] :
      ( v2_tops_1(B_75,A_76)
      | k1_tops_1(A_76,B_75) != k1_xboole_0
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_340,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_329])).

tff(c_349,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_340])).

tff(c_351,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_349])).

tff(c_431,plain,(
    ! [A_87,B_88] :
      ( k1_tops_1(A_87,B_88) = k1_xboole_0
      | ~ v2_tops_1(B_88,A_87)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_442,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_431])).

tff(c_451,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_442])).

tff(c_452,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_351,c_451])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_72,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_56])).

tff(c_477,plain,(
    ! [B_92,A_93] :
      ( v2_tops_1(B_92,A_93)
      | ~ r1_tarski(B_92,k2_tops_1(A_93,B_92))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_479,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_477])).

tff(c_481,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_6,c_479])).

tff(c_483,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_452,c_481])).

tff(c_484,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_349])).

tff(c_44,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_931,plain,(
    ! [B_129,A_130] :
      ( v3_tops_1(B_129,A_130)
      | ~ v4_pre_topc(B_129,A_130)
      | ~ v2_tops_1(B_129,A_130)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_946,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_931])).

tff(c_956,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_484,c_44,c_946])).

tff(c_958,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_956])).

tff(c_959,plain,(
    k2_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_10,plain,(
    ! [A_5] : k2_subset_1(A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1(k2_subset_1(A_8),k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_57,plain,(
    ! [A_8] : m1_subset_1(A_8,k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14])).

tff(c_989,plain,(
    ! [A_137,B_138] :
      ( m1_subset_1(k3_subset_1(A_137,B_138),k1_zfmisc_1(A_137))
      | ~ m1_subset_1(B_138,k1_zfmisc_1(A_137)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_993,plain,(
    ! [A_137,B_138] :
      ( r1_tarski(k3_subset_1(A_137,B_138),A_137)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(A_137)) ) ),
    inference(resolution,[status(thm)],[c_989,c_22])).

tff(c_998,plain,(
    ! [A_141,B_142] :
      ( k3_subset_1(A_141,k3_subset_1(A_141,B_142)) = B_142
      | ~ m1_subset_1(B_142,k1_zfmisc_1(A_141)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1010,plain,(
    ! [A_8] : k3_subset_1(A_8,k3_subset_1(A_8,A_8)) = A_8 ),
    inference(resolution,[status(thm)],[c_57,c_998])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k3_subset_1(A_9,B_10),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1096,plain,(
    ! [A_146,B_147] :
      ( k4_xboole_0(A_146,B_147) = k3_subset_1(A_146,B_147)
      | ~ m1_subset_1(B_147,k1_zfmisc_1(A_146)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1468,plain,(
    ! [A_191,B_192] :
      ( k4_xboole_0(A_191,k3_subset_1(A_191,B_192)) = k3_subset_1(A_191,k3_subset_1(A_191,B_192))
      | ~ m1_subset_1(B_192,k1_zfmisc_1(A_191)) ) ),
    inference(resolution,[status(thm)],[c_16,c_1096])).

tff(c_1476,plain,(
    ! [A_8] : k4_xboole_0(A_8,k3_subset_1(A_8,A_8)) = k3_subset_1(A_8,k3_subset_1(A_8,A_8)) ),
    inference(resolution,[status(thm)],[c_57,c_1468])).

tff(c_1490,plain,(
    ! [A_193] : k4_xboole_0(A_193,k3_subset_1(A_193,A_193)) = A_193 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1010,c_1476])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k4_xboole_0(B_4,A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1502,plain,(
    ! [A_194] :
      ( k3_subset_1(A_194,A_194) = k1_xboole_0
      | ~ r1_tarski(k3_subset_1(A_194,A_194),A_194) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1490,c_8])).

tff(c_1506,plain,(
    ! [B_138] :
      ( k3_subset_1(B_138,B_138) = k1_xboole_0
      | ~ m1_subset_1(B_138,k1_zfmisc_1(B_138)) ) ),
    inference(resolution,[status(thm)],[c_993,c_1502])).

tff(c_1509,plain,(
    ! [B_138] : k3_subset_1(B_138,B_138) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_1506])).

tff(c_1482,plain,(
    ! [A_8] : k4_xboole_0(A_8,k3_subset_1(A_8,A_8)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1010,c_1476])).

tff(c_1511,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1509,c_1482])).

tff(c_1133,plain,(
    ! [A_150,B_151,C_152] :
      ( k7_subset_1(A_150,B_151,C_152) = k4_xboole_0(B_151,C_152)
      | ~ m1_subset_1(B_151,k1_zfmisc_1(A_150)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1144,plain,(
    ! [C_152] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_152) = k4_xboole_0('#skF_2',C_152) ),
    inference(resolution,[status(thm)],[c_46,c_1133])).

tff(c_1272,plain,(
    ! [A_171,B_172] :
      ( k2_pre_topc(A_171,B_172) = B_172
      | ~ v4_pre_topc(B_172,A_171)
      | ~ m1_subset_1(B_172,k1_zfmisc_1(u1_struct_0(A_171)))
      | ~ l1_pre_topc(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1283,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_1272])).

tff(c_1292,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_1283])).

tff(c_960,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1192,plain,(
    ! [B_161,A_162] :
      ( v2_tops_1(B_161,A_162)
      | ~ v3_tops_1(B_161,A_162)
      | ~ m1_subset_1(B_161,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ l1_pre_topc(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1203,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_1192])).

tff(c_1212,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_960,c_1203])).

tff(c_1329,plain,(
    ! [A_178,B_179] :
      ( k1_tops_1(A_178,B_179) = k1_xboole_0
      | ~ v2_tops_1(B_179,A_178)
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ l1_pre_topc(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1340,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_1329])).

tff(c_1349,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1212,c_1340])).

tff(c_1759,plain,(
    ! [A_204,B_205] :
      ( k7_subset_1(u1_struct_0(A_204),k2_pre_topc(A_204,B_205),k1_tops_1(A_204,B_205)) = k2_tops_1(A_204,B_205)
      | ~ m1_subset_1(B_205,k1_zfmisc_1(u1_struct_0(A_204)))
      | ~ l1_pre_topc(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1768,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1349,c_1759])).

tff(c_1775,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1511,c_1144,c_1292,c_1768])).

tff(c_1777,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_959,c_1775])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:19:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.48/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.55  
% 3.48/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.55  %$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.48/1.55  
% 3.48/1.55  %Foreground sorts:
% 3.48/1.55  
% 3.48/1.55  
% 3.48/1.55  %Background operators:
% 3.48/1.55  
% 3.48/1.55  
% 3.48/1.55  %Foreground operators:
% 3.48/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.48/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.48/1.55  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.48/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.48/1.55  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.48/1.55  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.48/1.55  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 3.48/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.48/1.55  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.48/1.55  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.48/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.48/1.55  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.48/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.48/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.48/1.55  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.48/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.48/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.48/1.55  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.48/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.48/1.55  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.48/1.55  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.48/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.48/1.55  
% 3.48/1.57  tff(f_131, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_tops_1)).
% 3.48/1.57  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 3.48/1.57  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.48/1.57  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tops_1)).
% 3.48/1.57  tff(f_119, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tops_1(B, A) & v4_pre_topc(B, A)) => v3_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_tops_1)).
% 3.48/1.57  tff(f_37, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.48/1.57  tff(f_43, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.48/1.57  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.48/1.57  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.48/1.57  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.48/1.57  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.48/1.57  tff(f_35, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 3.48/1.57  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.48/1.57  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.48/1.57  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_tops_1)).
% 3.48/1.57  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 3.48/1.57  tff(c_50, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.48/1.57  tff(c_71, plain, (~v3_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_50])).
% 3.48/1.57  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.48/1.57  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.48/1.57  tff(c_329, plain, (![B_75, A_76]: (v2_tops_1(B_75, A_76) | k1_tops_1(A_76, B_75)!=k1_xboole_0 | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.48/1.57  tff(c_340, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_329])).
% 3.48/1.57  tff(c_349, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_340])).
% 3.48/1.57  tff(c_351, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_349])).
% 3.48/1.57  tff(c_431, plain, (![A_87, B_88]: (k1_tops_1(A_87, B_88)=k1_xboole_0 | ~v2_tops_1(B_88, A_87) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.48/1.57  tff(c_442, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_431])).
% 3.48/1.57  tff(c_451, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_442])).
% 3.48/1.57  tff(c_452, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_351, c_451])).
% 3.48/1.57  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.48/1.57  tff(c_56, plain, (v3_tops_1('#skF_2', '#skF_1') | k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.48/1.57  tff(c_72, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_71, c_56])).
% 3.48/1.57  tff(c_477, plain, (![B_92, A_93]: (v2_tops_1(B_92, A_93) | ~r1_tarski(B_92, k2_tops_1(A_93, B_92)) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.48/1.57  tff(c_479, plain, (v2_tops_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_72, c_477])).
% 3.48/1.57  tff(c_481, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_6, c_479])).
% 3.48/1.57  tff(c_483, plain, $false, inference(negUnitSimplification, [status(thm)], [c_452, c_481])).
% 3.48/1.57  tff(c_484, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_349])).
% 3.48/1.57  tff(c_44, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.48/1.57  tff(c_931, plain, (![B_129, A_130]: (v3_tops_1(B_129, A_130) | ~v4_pre_topc(B_129, A_130) | ~v2_tops_1(B_129, A_130) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.48/1.57  tff(c_946, plain, (v3_tops_1('#skF_2', '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_931])).
% 3.48/1.57  tff(c_956, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_484, c_44, c_946])).
% 3.48/1.57  tff(c_958, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_956])).
% 3.48/1.57  tff(c_959, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(splitRight, [status(thm)], [c_50])).
% 3.48/1.57  tff(c_10, plain, (![A_5]: (k2_subset_1(A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.48/1.57  tff(c_14, plain, (![A_8]: (m1_subset_1(k2_subset_1(A_8), k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.48/1.57  tff(c_57, plain, (![A_8]: (m1_subset_1(A_8, k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14])).
% 3.48/1.57  tff(c_989, plain, (![A_137, B_138]: (m1_subset_1(k3_subset_1(A_137, B_138), k1_zfmisc_1(A_137)) | ~m1_subset_1(B_138, k1_zfmisc_1(A_137)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.48/1.57  tff(c_22, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~m1_subset_1(A_16, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.48/1.57  tff(c_993, plain, (![A_137, B_138]: (r1_tarski(k3_subset_1(A_137, B_138), A_137) | ~m1_subset_1(B_138, k1_zfmisc_1(A_137)))), inference(resolution, [status(thm)], [c_989, c_22])).
% 3.48/1.57  tff(c_998, plain, (![A_141, B_142]: (k3_subset_1(A_141, k3_subset_1(A_141, B_142))=B_142 | ~m1_subset_1(B_142, k1_zfmisc_1(A_141)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.48/1.57  tff(c_1010, plain, (![A_8]: (k3_subset_1(A_8, k3_subset_1(A_8, A_8))=A_8)), inference(resolution, [status(thm)], [c_57, c_998])).
% 3.48/1.57  tff(c_16, plain, (![A_9, B_10]: (m1_subset_1(k3_subset_1(A_9, B_10), k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.48/1.57  tff(c_1096, plain, (![A_146, B_147]: (k4_xboole_0(A_146, B_147)=k3_subset_1(A_146, B_147) | ~m1_subset_1(B_147, k1_zfmisc_1(A_146)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.48/1.57  tff(c_1468, plain, (![A_191, B_192]: (k4_xboole_0(A_191, k3_subset_1(A_191, B_192))=k3_subset_1(A_191, k3_subset_1(A_191, B_192)) | ~m1_subset_1(B_192, k1_zfmisc_1(A_191)))), inference(resolution, [status(thm)], [c_16, c_1096])).
% 3.48/1.57  tff(c_1476, plain, (![A_8]: (k4_xboole_0(A_8, k3_subset_1(A_8, A_8))=k3_subset_1(A_8, k3_subset_1(A_8, A_8)))), inference(resolution, [status(thm)], [c_57, c_1468])).
% 3.48/1.57  tff(c_1490, plain, (![A_193]: (k4_xboole_0(A_193, k3_subset_1(A_193, A_193))=A_193)), inference(demodulation, [status(thm), theory('equality')], [c_1010, c_1476])).
% 3.48/1.57  tff(c_8, plain, (![A_3, B_4]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k4_xboole_0(B_4, A_3)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.48/1.57  tff(c_1502, plain, (![A_194]: (k3_subset_1(A_194, A_194)=k1_xboole_0 | ~r1_tarski(k3_subset_1(A_194, A_194), A_194))), inference(superposition, [status(thm), theory('equality')], [c_1490, c_8])).
% 3.48/1.57  tff(c_1506, plain, (![B_138]: (k3_subset_1(B_138, B_138)=k1_xboole_0 | ~m1_subset_1(B_138, k1_zfmisc_1(B_138)))), inference(resolution, [status(thm)], [c_993, c_1502])).
% 3.48/1.57  tff(c_1509, plain, (![B_138]: (k3_subset_1(B_138, B_138)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_57, c_1506])).
% 3.48/1.57  tff(c_1482, plain, (![A_8]: (k4_xboole_0(A_8, k3_subset_1(A_8, A_8))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_1010, c_1476])).
% 3.48/1.57  tff(c_1511, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_1509, c_1482])).
% 3.48/1.57  tff(c_1133, plain, (![A_150, B_151, C_152]: (k7_subset_1(A_150, B_151, C_152)=k4_xboole_0(B_151, C_152) | ~m1_subset_1(B_151, k1_zfmisc_1(A_150)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.48/1.57  tff(c_1144, plain, (![C_152]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_152)=k4_xboole_0('#skF_2', C_152))), inference(resolution, [status(thm)], [c_46, c_1133])).
% 3.48/1.57  tff(c_1272, plain, (![A_171, B_172]: (k2_pre_topc(A_171, B_172)=B_172 | ~v4_pre_topc(B_172, A_171) | ~m1_subset_1(B_172, k1_zfmisc_1(u1_struct_0(A_171))) | ~l1_pre_topc(A_171))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.48/1.57  tff(c_1283, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_1272])).
% 3.48/1.57  tff(c_1292, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_1283])).
% 3.48/1.57  tff(c_960, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 3.48/1.57  tff(c_1192, plain, (![B_161, A_162]: (v2_tops_1(B_161, A_162) | ~v3_tops_1(B_161, A_162) | ~m1_subset_1(B_161, k1_zfmisc_1(u1_struct_0(A_162))) | ~l1_pre_topc(A_162))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.48/1.57  tff(c_1203, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_1192])).
% 3.48/1.57  tff(c_1212, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_960, c_1203])).
% 3.48/1.57  tff(c_1329, plain, (![A_178, B_179]: (k1_tops_1(A_178, B_179)=k1_xboole_0 | ~v2_tops_1(B_179, A_178) | ~m1_subset_1(B_179, k1_zfmisc_1(u1_struct_0(A_178))) | ~l1_pre_topc(A_178))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.48/1.57  tff(c_1340, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_1329])).
% 3.48/1.57  tff(c_1349, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1212, c_1340])).
% 3.48/1.57  tff(c_1759, plain, (![A_204, B_205]: (k7_subset_1(u1_struct_0(A_204), k2_pre_topc(A_204, B_205), k1_tops_1(A_204, B_205))=k2_tops_1(A_204, B_205) | ~m1_subset_1(B_205, k1_zfmisc_1(u1_struct_0(A_204))) | ~l1_pre_topc(A_204))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.48/1.57  tff(c_1768, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1349, c_1759])).
% 3.48/1.57  tff(c_1775, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1511, c_1144, c_1292, c_1768])).
% 3.48/1.57  tff(c_1777, plain, $false, inference(negUnitSimplification, [status(thm)], [c_959, c_1775])).
% 3.48/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.57  
% 3.48/1.57  Inference rules
% 3.48/1.57  ----------------------
% 3.48/1.57  #Ref     : 0
% 3.48/1.57  #Sup     : 367
% 3.48/1.57  #Fact    : 0
% 3.48/1.57  #Define  : 0
% 3.48/1.57  #Split   : 9
% 3.48/1.57  #Chain   : 0
% 3.48/1.57  #Close   : 0
% 3.48/1.57  
% 3.48/1.57  Ordering : KBO
% 3.48/1.57  
% 3.48/1.57  Simplification rules
% 3.48/1.57  ----------------------
% 3.48/1.57  #Subsume      : 27
% 3.48/1.57  #Demod        : 182
% 3.48/1.57  #Tautology    : 180
% 3.48/1.57  #SimpNegUnit  : 8
% 3.48/1.57  #BackRed      : 8
% 3.48/1.57  
% 3.48/1.57  #Partial instantiations: 0
% 3.48/1.57  #Strategies tried      : 1
% 3.48/1.57  
% 3.48/1.57  Timing (in seconds)
% 3.48/1.57  ----------------------
% 3.48/1.57  Preprocessing        : 0.34
% 3.48/1.57  Parsing              : 0.18
% 3.48/1.57  CNF conversion       : 0.02
% 3.48/1.58  Main loop            : 0.48
% 3.48/1.58  Inferencing          : 0.17
% 3.48/1.58  Reduction            : 0.15
% 3.48/1.58  Demodulation         : 0.11
% 3.48/1.58  BG Simplification    : 0.02
% 3.48/1.58  Subsumption          : 0.09
% 3.48/1.58  Abstraction          : 0.03
% 3.48/1.58  MUC search           : 0.00
% 3.48/1.58  Cooper               : 0.00
% 3.48/1.58  Total                : 0.86
% 3.48/1.58  Index Insertion      : 0.00
% 3.48/1.58  Index Deletion       : 0.00
% 3.48/1.58  Index Matching       : 0.00
% 3.48/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
