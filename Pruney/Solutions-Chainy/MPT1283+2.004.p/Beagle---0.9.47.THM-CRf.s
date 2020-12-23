%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:21 EST 2020

% Result     : Theorem 6.08s
% Output     : CNFRefutation 6.08s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 361 expanded)
%              Number of leaves         :   32 ( 137 expanded)
%              Depth                    :   13
%              Number of atoms          :  163 ( 739 expanded)
%              Number of equality atoms :   35 ( 145 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_tops_1 > v5_tops_1 > v4_pre_topc > v3_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v6_tops_1,type,(
    v6_tops_1: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff(v5_tops_1,type,(
    v5_tops_1: ( $i * $i ) > $o )).

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

tff(f_117,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v3_pre_topc(B,A)
                & v4_pre_topc(B,A) )
             => ( v5_tops_1(B,A)
              <=> v6_tops_1(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_tops_1)).

tff(f_60,axiom,(
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

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_tops_1(B,A)
          <=> B = k1_tops_1(A,k2_pre_topc(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_tops_1(B,A)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_tops_1)).

tff(c_50,plain,
    ( v5_tops_1('#skF_2','#skF_1')
    | v6_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_62,plain,(
    v6_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_44,plain,
    ( ~ v6_tops_1('#skF_2','#skF_1')
    | ~ v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_64,plain,(
    ~ v5_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_44])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_36,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_238,plain,(
    ! [A_54,B_55] :
      ( k2_pre_topc(A_54,B_55) = B_55
      | ~ v4_pre_topc(B_55,A_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_262,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_238])).

tff(c_281,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_262])).

tff(c_975,plain,(
    ! [A_93,B_94] :
      ( k1_tops_1(A_93,k2_pre_topc(A_93,B_94)) = B_94
      | ~ v6_tops_1(B_94,A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1024,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = '#skF_2'
    | ~ v6_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_975])).

tff(c_1069,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_62,c_281,c_1024])).

tff(c_2739,plain,(
    ! [B_142,A_143] :
      ( v5_tops_1(B_142,A_143)
      | k2_pre_topc(A_143,k1_tops_1(A_143,B_142)) != B_142
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2743,plain,
    ( v5_tops_1('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1069,c_2739])).

tff(c_2748,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_281,c_2743])).

tff(c_2750,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2748])).

tff(c_2752,plain,(
    ~ v6_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2755,plain,(
    ! [A_144,B_145] :
      ( k4_xboole_0(A_144,B_145) = k3_subset_1(A_144,B_145)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(A_144)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2762,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),'#skF_2') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_2755])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_51,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6])).

tff(c_2805,plain,(
    ! [A_153,B_154,C_155] :
      ( k7_subset_1(A_153,B_154,C_155) = k4_xboole_0(B_154,C_155)
      | ~ m1_subset_1(B_154,k1_zfmisc_1(A_153)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2815,plain,(
    ! [A_156,C_157] : k7_subset_1(A_156,A_156,C_157) = k4_xboole_0(A_156,C_157) ),
    inference(resolution,[status(thm)],[c_51,c_2805])).

tff(c_8,plain,(
    ! [A_5,B_6,C_7] :
      ( m1_subset_1(k7_subset_1(A_5,B_6,C_7),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2821,plain,(
    ! [A_156,C_157] :
      ( m1_subset_1(k4_xboole_0(A_156,C_157),k1_zfmisc_1(A_156))
      | ~ m1_subset_1(A_156,k1_zfmisc_1(A_156)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2815,c_8])).

tff(c_2829,plain,(
    ! [A_158,C_159] : m1_subset_1(k4_xboole_0(A_158,C_159),k1_zfmisc_1(A_158)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_2821])).

tff(c_2839,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2762,c_2829])).

tff(c_4616,plain,(
    ! [A_236,B_237] :
      ( k2_pre_topc(A_236,k1_tops_1(A_236,B_237)) = B_237
      | ~ v5_tops_1(B_237,A_236)
      | ~ m1_subset_1(B_237,k1_zfmisc_1(u1_struct_0(A_236)))
      | ~ l1_pre_topc(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4670,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')
    | ~ v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2839,c_4616])).

tff(c_4741,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')
    | ~ v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_4670])).

tff(c_4802,plain,(
    ~ v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4741])).

tff(c_2928,plain,(
    ! [A_164,B_165] :
      ( k2_pre_topc(A_164,B_165) = B_165
      | ~ v4_pre_topc(B_165,A_164)
      | ~ m1_subset_1(B_165,k1_zfmisc_1(u1_struct_0(A_164)))
      | ~ l1_pre_topc(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2931,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2839,c_2928])).

tff(c_2959,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2931])).

tff(c_4053,plain,(
    ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2959])).

tff(c_38,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2777,plain,(
    ! [A_147,B_148] :
      ( k3_subset_1(A_147,k3_subset_1(A_147,B_148)) = B_148
      | ~ m1_subset_1(B_148,k1_zfmisc_1(A_147)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2782,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_40,c_2777])).

tff(c_4084,plain,(
    ! [B_213,A_214] :
      ( v4_pre_topc(B_213,A_214)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_214),B_213),A_214)
      | ~ m1_subset_1(B_213,k1_zfmisc_1(u1_struct_0(A_214)))
      | ~ l1_pre_topc(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_4100,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2782,c_4084])).

tff(c_4113,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2839,c_38,c_4100])).

tff(c_4115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4053,c_4113])).

tff(c_4116,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_2959])).

tff(c_2751,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_3165,plain,(
    ! [B_175,A_176] :
      ( v6_tops_1(B_175,A_176)
      | ~ v5_tops_1(k3_subset_1(u1_struct_0(A_176),B_175),A_176)
      | ~ m1_subset_1(B_175,k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ l1_pre_topc(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3172,plain,
    ( v6_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2782,c_3165])).

tff(c_3180,plain,(
    v6_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2839,c_2751,c_3172])).

tff(c_4811,plain,(
    ! [A_240,B_241] :
      ( k1_tops_1(A_240,k2_pre_topc(A_240,B_241)) = B_241
      | ~ v6_tops_1(B_241,A_240)
      | ~ m1_subset_1(B_241,k1_zfmisc_1(u1_struct_0(A_240)))
      | ~ l1_pre_topc(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4865,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')
    | ~ v6_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2839,c_4811])).

tff(c_4936,plain,(
    k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3180,c_4116,c_4865])).

tff(c_20,plain,(
    ! [B_21,A_19] :
      ( v5_tops_1(B_21,A_19)
      | k2_pre_topc(A_19,k1_tops_1(A_19,B_21)) != B_21
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4952,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) != k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4936,c_20])).

tff(c_4956,plain,(
    v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2839,c_4116,c_4952])).

tff(c_4958,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4802,c_4956])).

tff(c_4960,plain,(
    v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_4741])).

tff(c_28,plain,(
    ! [B_27,A_25] :
      ( v6_tops_1(B_27,A_25)
      | ~ v5_tops_1(k3_subset_1(u1_struct_0(A_25),B_27),A_25)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4963,plain,
    ( v6_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4960,c_28])).

tff(c_4966,plain,(
    v6_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_4963])).

tff(c_4968,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2752,c_4966])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:39:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.08/2.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.08/2.38  
% 6.08/2.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.08/2.38  %$ v6_tops_1 > v5_tops_1 > v4_pre_topc > v3_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 6.08/2.38  
% 6.08/2.38  %Foreground sorts:
% 6.08/2.38  
% 6.08/2.38  
% 6.08/2.38  %Background operators:
% 6.08/2.38  
% 6.08/2.38  
% 6.08/2.38  %Foreground operators:
% 6.08/2.38  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.08/2.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.08/2.38  tff(v6_tops_1, type, v6_tops_1: ($i * $i) > $o).
% 6.08/2.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.08/2.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.08/2.38  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.08/2.38  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.08/2.38  tff('#skF_2', type, '#skF_2': $i).
% 6.08/2.38  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 6.08/2.38  tff('#skF_1', type, '#skF_1': $i).
% 6.08/2.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.08/2.38  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.08/2.38  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 6.08/2.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.08/2.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.08/2.38  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.08/2.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.08/2.38  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.08/2.38  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.08/2.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.08/2.38  
% 6.08/2.40  tff(f_117, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v4_pre_topc(B, A)) => (v5_tops_1(B, A) <=> v6_tops_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_tops_1)).
% 6.08/2.40  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 6.08/2.40  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_tops_1(B, A) <=> (B = k1_tops_1(A, k2_pre_topc(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_tops_1)).
% 6.08/2.40  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tops_1)).
% 6.08/2.40  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 6.08/2.40  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 6.08/2.40  tff(f_33, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 6.08/2.40  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 6.08/2.40  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 6.08/2.40  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 6.08/2.40  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 6.08/2.40  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_tops_1(B, A) <=> v5_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t101_tops_1)).
% 6.08/2.40  tff(c_50, plain, (v5_tops_1('#skF_2', '#skF_1') | v6_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.08/2.40  tff(c_62, plain, (v6_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_50])).
% 6.08/2.40  tff(c_44, plain, (~v6_tops_1('#skF_2', '#skF_1') | ~v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.08/2.40  tff(c_64, plain, (~v5_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_44])).
% 6.08/2.40  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.08/2.40  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.08/2.40  tff(c_36, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.08/2.40  tff(c_238, plain, (![A_54, B_55]: (k2_pre_topc(A_54, B_55)=B_55 | ~v4_pre_topc(B_55, A_54) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.08/2.40  tff(c_262, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_238])).
% 6.08/2.40  tff(c_281, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_262])).
% 6.08/2.40  tff(c_975, plain, (![A_93, B_94]: (k1_tops_1(A_93, k2_pre_topc(A_93, B_94))=B_94 | ~v6_tops_1(B_94, A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.08/2.40  tff(c_1024, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))='#skF_2' | ~v6_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_975])).
% 6.08/2.40  tff(c_1069, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_62, c_281, c_1024])).
% 6.08/2.40  tff(c_2739, plain, (![B_142, A_143]: (v5_tops_1(B_142, A_143) | k2_pre_topc(A_143, k1_tops_1(A_143, B_142))!=B_142 | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_pre_topc(A_143))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.08/2.40  tff(c_2743, plain, (v5_tops_1('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1069, c_2739])).
% 6.08/2.40  tff(c_2748, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_281, c_2743])).
% 6.08/2.40  tff(c_2750, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_2748])).
% 6.08/2.40  tff(c_2752, plain, (~v6_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 6.08/2.40  tff(c_2755, plain, (![A_144, B_145]: (k4_xboole_0(A_144, B_145)=k3_subset_1(A_144, B_145) | ~m1_subset_1(B_145, k1_zfmisc_1(A_144)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.08/2.40  tff(c_2762, plain, (k4_xboole_0(u1_struct_0('#skF_1'), '#skF_2')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_40, c_2755])).
% 6.08/2.40  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.08/2.40  tff(c_6, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.08/2.40  tff(c_51, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6])).
% 6.08/2.40  tff(c_2805, plain, (![A_153, B_154, C_155]: (k7_subset_1(A_153, B_154, C_155)=k4_xboole_0(B_154, C_155) | ~m1_subset_1(B_154, k1_zfmisc_1(A_153)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.08/2.40  tff(c_2815, plain, (![A_156, C_157]: (k7_subset_1(A_156, A_156, C_157)=k4_xboole_0(A_156, C_157))), inference(resolution, [status(thm)], [c_51, c_2805])).
% 6.08/2.40  tff(c_8, plain, (![A_5, B_6, C_7]: (m1_subset_1(k7_subset_1(A_5, B_6, C_7), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.08/2.40  tff(c_2821, plain, (![A_156, C_157]: (m1_subset_1(k4_xboole_0(A_156, C_157), k1_zfmisc_1(A_156)) | ~m1_subset_1(A_156, k1_zfmisc_1(A_156)))), inference(superposition, [status(thm), theory('equality')], [c_2815, c_8])).
% 6.08/2.40  tff(c_2829, plain, (![A_158, C_159]: (m1_subset_1(k4_xboole_0(A_158, C_159), k1_zfmisc_1(A_158)))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_2821])).
% 6.08/2.40  tff(c_2839, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2762, c_2829])).
% 6.08/2.40  tff(c_4616, plain, (![A_236, B_237]: (k2_pre_topc(A_236, k1_tops_1(A_236, B_237))=B_237 | ~v5_tops_1(B_237, A_236) | ~m1_subset_1(B_237, k1_zfmisc_1(u1_struct_0(A_236))) | ~l1_pre_topc(A_236))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.08/2.40  tff(c_4670, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2') | ~v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2839, c_4616])).
% 6.08/2.40  tff(c_4741, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2') | ~v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_4670])).
% 6.08/2.40  tff(c_4802, plain, (~v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_4741])).
% 6.08/2.40  tff(c_2928, plain, (![A_164, B_165]: (k2_pre_topc(A_164, B_165)=B_165 | ~v4_pre_topc(B_165, A_164) | ~m1_subset_1(B_165, k1_zfmisc_1(u1_struct_0(A_164))) | ~l1_pre_topc(A_164))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.08/2.40  tff(c_2931, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2839, c_2928])).
% 6.08/2.40  tff(c_2959, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2931])).
% 6.08/2.40  tff(c_4053, plain, (~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_2959])).
% 6.08/2.40  tff(c_38, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.08/2.40  tff(c_2777, plain, (![A_147, B_148]: (k3_subset_1(A_147, k3_subset_1(A_147, B_148))=B_148 | ~m1_subset_1(B_148, k1_zfmisc_1(A_147)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.08/2.40  tff(c_2782, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_40, c_2777])).
% 6.08/2.40  tff(c_4084, plain, (![B_213, A_214]: (v4_pre_topc(B_213, A_214) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_214), B_213), A_214) | ~m1_subset_1(B_213, k1_zfmisc_1(u1_struct_0(A_214))) | ~l1_pre_topc(A_214))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.08/2.40  tff(c_4100, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v3_pre_topc('#skF_2', '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2782, c_4084])).
% 6.08/2.40  tff(c_4113, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2839, c_38, c_4100])).
% 6.08/2.40  tff(c_4115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4053, c_4113])).
% 6.08/2.40  tff(c_4116, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_2959])).
% 6.08/2.40  tff(c_2751, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 6.08/2.40  tff(c_3165, plain, (![B_175, A_176]: (v6_tops_1(B_175, A_176) | ~v5_tops_1(k3_subset_1(u1_struct_0(A_176), B_175), A_176) | ~m1_subset_1(B_175, k1_zfmisc_1(u1_struct_0(A_176))) | ~l1_pre_topc(A_176))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.08/2.40  tff(c_3172, plain, (v6_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v5_tops_1('#skF_2', '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2782, c_3165])).
% 6.08/2.40  tff(c_3180, plain, (v6_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2839, c_2751, c_3172])).
% 6.08/2.40  tff(c_4811, plain, (![A_240, B_241]: (k1_tops_1(A_240, k2_pre_topc(A_240, B_241))=B_241 | ~v6_tops_1(B_241, A_240) | ~m1_subset_1(B_241, k1_zfmisc_1(u1_struct_0(A_240))) | ~l1_pre_topc(A_240))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.08/2.40  tff(c_4865, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2') | ~v6_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2839, c_4811])).
% 6.08/2.40  tff(c_4936, plain, (k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_3180, c_4116, c_4865])).
% 6.08/2.40  tff(c_20, plain, (![B_21, A_19]: (v5_tops_1(B_21, A_19) | k2_pre_topc(A_19, k1_tops_1(A_19, B_21))!=B_21 | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.08/2.40  tff(c_4952, plain, (v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))!=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4936, c_20])).
% 6.08/2.40  tff(c_4956, plain, (v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2839, c_4116, c_4952])).
% 6.08/2.40  tff(c_4958, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4802, c_4956])).
% 6.08/2.40  tff(c_4960, plain, (v5_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_4741])).
% 6.08/2.40  tff(c_28, plain, (![B_27, A_25]: (v6_tops_1(B_27, A_25) | ~v5_tops_1(k3_subset_1(u1_struct_0(A_25), B_27), A_25) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.08/2.40  tff(c_4963, plain, (v6_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4960, c_28])).
% 6.08/2.40  tff(c_4966, plain, (v6_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_4963])).
% 6.08/2.40  tff(c_4968, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2752, c_4966])).
% 6.08/2.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.08/2.40  
% 6.08/2.40  Inference rules
% 6.08/2.40  ----------------------
% 6.08/2.40  #Ref     : 0
% 6.08/2.40  #Sup     : 1098
% 6.08/2.40  #Fact    : 0
% 6.08/2.40  #Define  : 0
% 6.08/2.40  #Split   : 12
% 6.08/2.40  #Chain   : 0
% 6.08/2.40  #Close   : 0
% 6.08/2.40  
% 6.08/2.40  Ordering : KBO
% 6.08/2.40  
% 6.08/2.40  Simplification rules
% 6.08/2.40  ----------------------
% 6.08/2.40  #Subsume      : 13
% 6.08/2.40  #Demod        : 870
% 6.08/2.40  #Tautology    : 397
% 6.08/2.40  #SimpNegUnit  : 13
% 6.08/2.40  #BackRed      : 0
% 6.08/2.40  
% 6.08/2.40  #Partial instantiations: 0
% 6.08/2.40  #Strategies tried      : 1
% 6.08/2.40  
% 6.08/2.40  Timing (in seconds)
% 6.08/2.40  ----------------------
% 6.08/2.40  Preprocessing        : 0.45
% 6.08/2.40  Parsing              : 0.24
% 6.08/2.40  CNF conversion       : 0.04
% 6.08/2.40  Main loop            : 1.11
% 6.08/2.40  Inferencing          : 0.33
% 6.08/2.40  Reduction            : 0.45
% 6.08/2.40  Demodulation         : 0.34
% 6.08/2.40  BG Simplification    : 0.06
% 6.08/2.40  Subsumption          : 0.18
% 6.08/2.40  Abstraction          : 0.08
% 6.08/2.40  MUC search           : 0.00
% 6.08/2.40  Cooper               : 0.00
% 6.08/2.40  Total                : 1.60
% 6.08/2.40  Index Insertion      : 0.00
% 6.08/2.40  Index Deletion       : 0.00
% 6.08/2.40  Index Matching       : 0.00
% 6.08/2.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
