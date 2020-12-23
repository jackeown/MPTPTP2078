%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:04 EST 2020

% Result     : Theorem 4.64s
% Output     : CNFRefutation 4.72s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 164 expanded)
%              Number of leaves         :   42 (  74 expanded)
%              Depth                    :   11
%              Number of atoms          :  153 ( 328 expanded)
%              Number of equality atoms :   43 (  87 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

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

tff(f_133,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => ( v3_tops_1(B,A)
              <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_121,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v2_tops_1(B,A)
              & v4_pre_topc(B,A) )
           => v3_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_tops_1)).

tff(f_41,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_76,axiom,(
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

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_60,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_85,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_54,plain,
    ( k2_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_91,plain,(
    ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_54])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_50,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_551,plain,(
    ! [A_94,B_95] :
      ( k1_tops_1(A_94,B_95) = k1_xboole_0
      | ~ v2_tops_1(B_95,A_94)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_566,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_551])).

tff(c_576,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_566])).

tff(c_578,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_576])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1084,plain,(
    ! [B_126,A_127] :
      ( v2_tops_1(B_126,A_127)
      | ~ r1_tarski(B_126,k2_tops_1(A_127,B_126))
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1089,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_1084])).

tff(c_1094,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_8,c_1089])).

tff(c_1096,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_578,c_1094])).

tff(c_1098,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_576])).

tff(c_48,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1948,plain,(
    ! [B_173,A_174] :
      ( v3_tops_1(B_173,A_174)
      | ~ v4_pre_topc(B_173,A_174)
      | ~ v2_tops_1(B_173,A_174)
      | ~ m1_subset_1(B_173,k1_zfmisc_1(u1_struct_0(A_174)))
      | ~ l1_pre_topc(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1966,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_1948])).

tff(c_1979,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1098,c_48,c_1966])).

tff(c_1981,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_1979])).

tff(c_1983,plain,(
    k2_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_14,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_12] : m1_subset_1(k2_subset_1(A_12),k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_61,plain,(
    ! [A_12] : m1_subset_1(A_12,k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_18])).

tff(c_2038,plain,(
    ! [A_183,B_184] :
      ( m1_subset_1(k3_subset_1(A_183,B_184),k1_zfmisc_1(A_183))
      | ~ m1_subset_1(B_184,k1_zfmisc_1(A_183)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2042,plain,(
    ! [A_183,B_184] :
      ( r1_tarski(k3_subset_1(A_183,B_184),A_183)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(A_183)) ) ),
    inference(resolution,[status(thm)],[c_2038,c_26])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2047,plain,(
    ! [A_187,B_188] :
      ( k4_xboole_0(A_187,B_188) = k3_subset_1(A_187,B_188)
      | ~ m1_subset_1(B_188,k1_zfmisc_1(A_187)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2074,plain,(
    ! [A_189] : k4_xboole_0(A_189,A_189) = k3_subset_1(A_189,A_189) ),
    inference(resolution,[status(thm)],[c_61,c_2047])).

tff(c_12,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2080,plain,(
    ! [A_189] : k4_xboole_0(A_189,k3_subset_1(A_189,A_189)) = k3_xboole_0(A_189,A_189) ),
    inference(superposition,[status(thm),theory(equality)],[c_2074,c_12])).

tff(c_2090,plain,(
    ! [A_190] : k4_xboole_0(A_190,k3_subset_1(A_190,A_190)) = A_190 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2080])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k4_xboole_0(B_6,A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2173,plain,(
    ! [A_201] :
      ( k3_subset_1(A_201,A_201) = k1_xboole_0
      | ~ r1_tarski(k3_subset_1(A_201,A_201),A_201) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2090,c_10])).

tff(c_2177,plain,(
    ! [B_184] :
      ( k3_subset_1(B_184,B_184) = k1_xboole_0
      | ~ m1_subset_1(B_184,k1_zfmisc_1(B_184)) ) ),
    inference(resolution,[status(thm)],[c_2042,c_2173])).

tff(c_2180,plain,(
    ! [B_184] : k3_subset_1(B_184,B_184) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_2177])).

tff(c_2088,plain,(
    ! [A_189] : k4_xboole_0(A_189,k3_subset_1(A_189,A_189)) = A_189 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2080])).

tff(c_2184,plain,(
    ! [A_189] : k4_xboole_0(A_189,k1_xboole_0) = A_189 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2180,c_2088])).

tff(c_2108,plain,(
    ! [A_192,B_193,C_194] :
      ( k7_subset_1(A_192,B_193,C_194) = k4_xboole_0(B_193,C_194)
      | ~ m1_subset_1(B_193,k1_zfmisc_1(A_192)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2119,plain,(
    ! [C_194] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_194) = k4_xboole_0('#skF_2',C_194) ),
    inference(resolution,[status(thm)],[c_50,c_2108])).

tff(c_1982,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_2235,plain,(
    ! [B_205,A_206] :
      ( v2_tops_1(B_205,A_206)
      | ~ v3_tops_1(B_205,A_206)
      | ~ m1_subset_1(B_205,k1_zfmisc_1(u1_struct_0(A_206)))
      | ~ l1_pre_topc(A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2246,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_2235])).

tff(c_2255,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1982,c_2246])).

tff(c_2466,plain,(
    ! [A_220,B_221] :
      ( k1_tops_1(A_220,B_221) = k1_xboole_0
      | ~ v2_tops_1(B_221,A_220)
      | ~ m1_subset_1(B_221,k1_zfmisc_1(u1_struct_0(A_220)))
      | ~ l1_pre_topc(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2481,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_2466])).

tff(c_2491,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2255,c_2481])).

tff(c_2612,plain,(
    ! [A_231,B_232] :
      ( k2_pre_topc(A_231,B_232) = B_232
      | ~ v4_pre_topc(B_232,A_231)
      | ~ m1_subset_1(B_232,k1_zfmisc_1(u1_struct_0(A_231)))
      | ~ l1_pre_topc(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2627,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_2612])).

tff(c_2637,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_2627])).

tff(c_3446,plain,(
    ! [A_276,B_277] :
      ( k7_subset_1(u1_struct_0(A_276),k2_pre_topc(A_276,B_277),k1_tops_1(A_276,B_277)) = k2_tops_1(A_276,B_277)
      | ~ m1_subset_1(B_277,k1_zfmisc_1(u1_struct_0(A_276)))
      | ~ l1_pre_topc(A_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_3458,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2637,c_3446])).

tff(c_3467,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_2184,c_2119,c_2491,c_3458])).

tff(c_3469,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1983,c_3467])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:16:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.64/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.72/1.84  
% 4.72/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.72/1.85  %$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.72/1.85  
% 4.72/1.85  %Foreground sorts:
% 4.72/1.85  
% 4.72/1.85  
% 4.72/1.85  %Background operators:
% 4.72/1.85  
% 4.72/1.85  
% 4.72/1.85  %Foreground operators:
% 4.72/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.72/1.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.72/1.85  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.72/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.72/1.85  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 4.72/1.85  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.72/1.85  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 4.72/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.72/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.72/1.85  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.72/1.85  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.72/1.85  tff('#skF_2', type, '#skF_2': $i).
% 4.72/1.85  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.72/1.85  tff('#skF_1', type, '#skF_1': $i).
% 4.72/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.72/1.85  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.72/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.72/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.72/1.85  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.72/1.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.72/1.85  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.72/1.85  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.72/1.85  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.72/1.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.72/1.85  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.72/1.85  
% 4.72/1.86  tff(f_133, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_tops_1)).
% 4.72/1.86  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 4.72/1.86  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.72/1.86  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 4.72/1.86  tff(f_121, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tops_1(B, A) & v4_pre_topc(B, A)) => v3_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_tops_1)).
% 4.72/1.86  tff(f_41, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.72/1.86  tff(f_47, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.72/1.86  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.72/1.86  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.72/1.86  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.72/1.86  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.72/1.86  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.72/1.86  tff(f_37, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 4.72/1.86  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.72/1.86  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_tops_1)).
% 4.72/1.86  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.72/1.86  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 4.72/1.86  tff(c_60, plain, (v3_tops_1('#skF_2', '#skF_1') | k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.72/1.86  tff(c_85, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(splitLeft, [status(thm)], [c_60])).
% 4.72/1.86  tff(c_54, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.72/1.86  tff(c_91, plain, (~v3_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_54])).
% 4.72/1.86  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.72/1.86  tff(c_50, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.72/1.86  tff(c_551, plain, (![A_94, B_95]: (k1_tops_1(A_94, B_95)=k1_xboole_0 | ~v2_tops_1(B_95, A_94) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.72/1.86  tff(c_566, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_551])).
% 4.72/1.86  tff(c_576, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_566])).
% 4.72/1.86  tff(c_578, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_576])).
% 4.72/1.86  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.72/1.86  tff(c_1084, plain, (![B_126, A_127]: (v2_tops_1(B_126, A_127) | ~r1_tarski(B_126, k2_tops_1(A_127, B_126)) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.72/1.86  tff(c_1089, plain, (v2_tops_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_85, c_1084])).
% 4.72/1.86  tff(c_1094, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_8, c_1089])).
% 4.72/1.86  tff(c_1096, plain, $false, inference(negUnitSimplification, [status(thm)], [c_578, c_1094])).
% 4.72/1.86  tff(c_1098, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_576])).
% 4.72/1.86  tff(c_48, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.72/1.86  tff(c_1948, plain, (![B_173, A_174]: (v3_tops_1(B_173, A_174) | ~v4_pre_topc(B_173, A_174) | ~v2_tops_1(B_173, A_174) | ~m1_subset_1(B_173, k1_zfmisc_1(u1_struct_0(A_174))) | ~l1_pre_topc(A_174))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.72/1.86  tff(c_1966, plain, (v3_tops_1('#skF_2', '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_1948])).
% 4.72/1.86  tff(c_1979, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1098, c_48, c_1966])).
% 4.72/1.86  tff(c_1981, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91, c_1979])).
% 4.72/1.86  tff(c_1983, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(splitRight, [status(thm)], [c_60])).
% 4.72/1.86  tff(c_14, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.72/1.86  tff(c_18, plain, (![A_12]: (m1_subset_1(k2_subset_1(A_12), k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.72/1.86  tff(c_61, plain, (![A_12]: (m1_subset_1(A_12, k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_18])).
% 4.72/1.86  tff(c_2038, plain, (![A_183, B_184]: (m1_subset_1(k3_subset_1(A_183, B_184), k1_zfmisc_1(A_183)) | ~m1_subset_1(B_184, k1_zfmisc_1(A_183)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.72/1.86  tff(c_26, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~m1_subset_1(A_20, k1_zfmisc_1(B_21)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.72/1.86  tff(c_2042, plain, (![A_183, B_184]: (r1_tarski(k3_subset_1(A_183, B_184), A_183) | ~m1_subset_1(B_184, k1_zfmisc_1(A_183)))), inference(resolution, [status(thm)], [c_2038, c_26])).
% 4.72/1.86  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.72/1.86  tff(c_2047, plain, (![A_187, B_188]: (k4_xboole_0(A_187, B_188)=k3_subset_1(A_187, B_188) | ~m1_subset_1(B_188, k1_zfmisc_1(A_187)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.72/1.86  tff(c_2074, plain, (![A_189]: (k4_xboole_0(A_189, A_189)=k3_subset_1(A_189, A_189))), inference(resolution, [status(thm)], [c_61, c_2047])).
% 4.72/1.86  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.72/1.86  tff(c_2080, plain, (![A_189]: (k4_xboole_0(A_189, k3_subset_1(A_189, A_189))=k3_xboole_0(A_189, A_189))), inference(superposition, [status(thm), theory('equality')], [c_2074, c_12])).
% 4.72/1.86  tff(c_2090, plain, (![A_190]: (k4_xboole_0(A_190, k3_subset_1(A_190, A_190))=A_190)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2080])).
% 4.72/1.86  tff(c_10, plain, (![A_5, B_6]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k4_xboole_0(B_6, A_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.72/1.86  tff(c_2173, plain, (![A_201]: (k3_subset_1(A_201, A_201)=k1_xboole_0 | ~r1_tarski(k3_subset_1(A_201, A_201), A_201))), inference(superposition, [status(thm), theory('equality')], [c_2090, c_10])).
% 4.72/1.86  tff(c_2177, plain, (![B_184]: (k3_subset_1(B_184, B_184)=k1_xboole_0 | ~m1_subset_1(B_184, k1_zfmisc_1(B_184)))), inference(resolution, [status(thm)], [c_2042, c_2173])).
% 4.72/1.86  tff(c_2180, plain, (![B_184]: (k3_subset_1(B_184, B_184)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_61, c_2177])).
% 4.72/1.86  tff(c_2088, plain, (![A_189]: (k4_xboole_0(A_189, k3_subset_1(A_189, A_189))=A_189)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2080])).
% 4.72/1.86  tff(c_2184, plain, (![A_189]: (k4_xboole_0(A_189, k1_xboole_0)=A_189)), inference(demodulation, [status(thm), theory('equality')], [c_2180, c_2088])).
% 4.72/1.86  tff(c_2108, plain, (![A_192, B_193, C_194]: (k7_subset_1(A_192, B_193, C_194)=k4_xboole_0(B_193, C_194) | ~m1_subset_1(B_193, k1_zfmisc_1(A_192)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.72/1.86  tff(c_2119, plain, (![C_194]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_194)=k4_xboole_0('#skF_2', C_194))), inference(resolution, [status(thm)], [c_50, c_2108])).
% 4.72/1.86  tff(c_1982, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_60])).
% 4.72/1.86  tff(c_2235, plain, (![B_205, A_206]: (v2_tops_1(B_205, A_206) | ~v3_tops_1(B_205, A_206) | ~m1_subset_1(B_205, k1_zfmisc_1(u1_struct_0(A_206))) | ~l1_pre_topc(A_206))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.72/1.86  tff(c_2246, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_2235])).
% 4.72/1.86  tff(c_2255, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1982, c_2246])).
% 4.72/1.86  tff(c_2466, plain, (![A_220, B_221]: (k1_tops_1(A_220, B_221)=k1_xboole_0 | ~v2_tops_1(B_221, A_220) | ~m1_subset_1(B_221, k1_zfmisc_1(u1_struct_0(A_220))) | ~l1_pre_topc(A_220))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.72/1.86  tff(c_2481, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_2466])).
% 4.72/1.86  tff(c_2491, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2255, c_2481])).
% 4.72/1.86  tff(c_2612, plain, (![A_231, B_232]: (k2_pre_topc(A_231, B_232)=B_232 | ~v4_pre_topc(B_232, A_231) | ~m1_subset_1(B_232, k1_zfmisc_1(u1_struct_0(A_231))) | ~l1_pre_topc(A_231))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.72/1.86  tff(c_2627, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_2612])).
% 4.72/1.86  tff(c_2637, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_2627])).
% 4.72/1.86  tff(c_3446, plain, (![A_276, B_277]: (k7_subset_1(u1_struct_0(A_276), k2_pre_topc(A_276, B_277), k1_tops_1(A_276, B_277))=k2_tops_1(A_276, B_277) | ~m1_subset_1(B_277, k1_zfmisc_1(u1_struct_0(A_276))) | ~l1_pre_topc(A_276))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.72/1.86  tff(c_3458, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2637, c_3446])).
% 4.72/1.86  tff(c_3467, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_2184, c_2119, c_2491, c_3458])).
% 4.72/1.86  tff(c_3469, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1983, c_3467])).
% 4.72/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.72/1.86  
% 4.72/1.86  Inference rules
% 4.72/1.86  ----------------------
% 4.72/1.86  #Ref     : 0
% 4.72/1.86  #Sup     : 769
% 4.72/1.86  #Fact    : 0
% 4.72/1.86  #Define  : 0
% 4.72/1.86  #Split   : 16
% 4.72/1.86  #Chain   : 0
% 4.72/1.86  #Close   : 0
% 4.72/1.86  
% 4.72/1.86  Ordering : KBO
% 4.72/1.86  
% 4.72/1.86  Simplification rules
% 4.72/1.86  ----------------------
% 4.72/1.86  #Subsume      : 78
% 4.72/1.86  #Demod        : 537
% 4.72/1.86  #Tautology    : 364
% 4.72/1.86  #SimpNegUnit  : 8
% 4.72/1.86  #BackRed      : 8
% 4.72/1.86  
% 4.72/1.86  #Partial instantiations: 0
% 4.72/1.86  #Strategies tried      : 1
% 4.72/1.86  
% 4.72/1.86  Timing (in seconds)
% 4.72/1.86  ----------------------
% 4.72/1.86  Preprocessing        : 0.34
% 4.72/1.86  Parsing              : 0.18
% 4.72/1.87  CNF conversion       : 0.02
% 4.72/1.87  Main loop            : 0.76
% 4.72/1.87  Inferencing          : 0.27
% 4.72/1.87  Reduction            : 0.26
% 4.72/1.87  Demodulation         : 0.19
% 4.72/1.87  BG Simplification    : 0.03
% 4.72/1.87  Subsumption          : 0.13
% 4.72/1.87  Abstraction          : 0.04
% 4.72/1.87  MUC search           : 0.00
% 4.72/1.87  Cooper               : 0.00
% 4.72/1.87  Total                : 1.14
% 4.72/1.87  Index Insertion      : 0.00
% 4.72/1.87  Index Deletion       : 0.00
% 4.72/1.87  Index Matching       : 0.00
% 4.72/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
