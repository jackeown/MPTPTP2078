%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:04 EST 2020

% Result     : Theorem 4.62s
% Output     : CNFRefutation 4.62s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 201 expanded)
%              Number of leaves         :   42 (  86 expanded)
%              Depth                    :   11
%              Number of atoms          :  168 ( 391 expanded)
%              Number of equality atoms :   51 ( 112 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_135,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => ( v3_tops_1(B,A)
              <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_80,axiom,(
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

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
          <=> v2_tops_1(k2_pre_topc(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_1)).

tff(f_39,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_123,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_62,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_76,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_56,plain,
    ( k2_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_82,plain,(
    ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_56])).

tff(c_54,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_52,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_583,plain,(
    ! [A_100,B_101] :
      ( k1_tops_1(A_100,B_101) = k1_xboole_0
      | ~ v2_tops_1(B_101,A_100)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_598,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_583])).

tff(c_608,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_598])).

tff(c_637,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_608])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1473,plain,(
    ! [B_164,A_165] :
      ( v2_tops_1(B_164,A_165)
      | ~ r1_tarski(B_164,k2_tops_1(A_165,B_164))
      | ~ m1_subset_1(B_164,k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ l1_pre_topc(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1482,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_1473])).

tff(c_1491,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_6,c_1482])).

tff(c_1493,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_637,c_1491])).

tff(c_1495,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_608])).

tff(c_50,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1650,plain,(
    ! [A_182,B_183] :
      ( k2_pre_topc(A_182,B_183) = B_183
      | ~ v4_pre_topc(B_183,A_182)
      | ~ m1_subset_1(B_183,k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ l1_pre_topc(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1665,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_1650])).

tff(c_1675,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_1665])).

tff(c_2188,plain,(
    ! [B_216,A_217] :
      ( v3_tops_1(B_216,A_217)
      | ~ v2_tops_1(k2_pre_topc(A_217,B_216),A_217)
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0(A_217)))
      | ~ l1_pre_topc(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2196,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1675,c_2188])).

tff(c_2205,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1495,c_2196])).

tff(c_2207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_2205])).

tff(c_2209,plain,(
    k2_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_12,plain,(
    ! [A_7] : k2_subset_1(A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_10] : m1_subset_1(k2_subset_1(A_10),k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_63,plain,(
    ! [A_10] : m1_subset_1(A_10,k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16])).

tff(c_2279,plain,(
    ! [A_233,B_234] :
      ( m1_subset_1(k3_subset_1(A_233,B_234),k1_zfmisc_1(A_233))
      | ~ m1_subset_1(B_234,k1_zfmisc_1(A_233)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ m1_subset_1(A_22,k1_zfmisc_1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2283,plain,(
    ! [A_233,B_234] :
      ( r1_tarski(k3_subset_1(A_233,B_234),A_233)
      | ~ m1_subset_1(B_234,k1_zfmisc_1(A_233)) ) ),
    inference(resolution,[status(thm)],[c_2279,c_26])).

tff(c_2408,plain,(
    ! [A_252,B_253,C_254] :
      ( k9_subset_1(A_252,B_253,C_254) = k3_xboole_0(B_253,C_254)
      | ~ m1_subset_1(C_254,k1_zfmisc_1(A_252)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2421,plain,(
    ! [A_255,B_256] : k9_subset_1(A_255,B_256,A_255) = k3_xboole_0(B_256,A_255) ),
    inference(resolution,[status(thm)],[c_63,c_2408])).

tff(c_2256,plain,(
    ! [A_228,B_229,C_230] :
      ( k9_subset_1(A_228,B_229,B_229) = B_229
      | ~ m1_subset_1(C_230,k1_zfmisc_1(A_228)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2265,plain,(
    ! [A_10,B_229] : k9_subset_1(A_10,B_229,B_229) = B_229 ),
    inference(resolution,[status(thm)],[c_63,c_2256])).

tff(c_2428,plain,(
    ! [A_255] : k3_xboole_0(A_255,A_255) = A_255 ),
    inference(superposition,[status(thm),theory(equality)],[c_2421,c_2265])).

tff(c_2288,plain,(
    ! [A_237,B_238] :
      ( k4_xboole_0(A_237,B_238) = k3_subset_1(A_237,B_238)
      | ~ m1_subset_1(B_238,k1_zfmisc_1(A_237)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2305,plain,(
    ! [A_239] : k4_xboole_0(A_239,A_239) = k3_subset_1(A_239,A_239) ),
    inference(resolution,[status(thm)],[c_63,c_2288])).

tff(c_10,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2311,plain,(
    ! [A_239] : k4_xboole_0(A_239,k3_subset_1(A_239,A_239)) = k3_xboole_0(A_239,A_239) ),
    inference(superposition,[status(thm),theory(equality)],[c_2305,c_10])).

tff(c_2472,plain,(
    ! [A_259] : k4_xboole_0(A_259,k3_subset_1(A_259,A_259)) = A_259 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2428,c_2311])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k4_xboole_0(B_4,A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2502,plain,(
    ! [A_261] :
      ( k3_subset_1(A_261,A_261) = k1_xboole_0
      | ~ r1_tarski(k3_subset_1(A_261,A_261),A_261) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2472,c_8])).

tff(c_2506,plain,(
    ! [B_234] :
      ( k3_subset_1(B_234,B_234) = k1_xboole_0
      | ~ m1_subset_1(B_234,k1_zfmisc_1(B_234)) ) ),
    inference(resolution,[status(thm)],[c_2283,c_2502])).

tff(c_2509,plain,(
    ! [B_234] : k3_subset_1(B_234,B_234) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_2506])).

tff(c_2438,plain,(
    ! [A_239] : k4_xboole_0(A_239,k3_subset_1(A_239,A_239)) = A_239 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2428,c_2311])).

tff(c_2512,plain,(
    ! [A_239] : k4_xboole_0(A_239,k1_xboole_0) = A_239 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2509,c_2438])).

tff(c_2320,plain,(
    ! [A_240,B_241,C_242] :
      ( k7_subset_1(A_240,B_241,C_242) = k4_xboole_0(B_241,C_242)
      | ~ m1_subset_1(B_241,k1_zfmisc_1(A_240)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2331,plain,(
    ! [C_242] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_242) = k4_xboole_0('#skF_2',C_242) ),
    inference(resolution,[status(thm)],[c_52,c_2320])).

tff(c_2208,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_2532,plain,(
    ! [B_263,A_264] :
      ( v2_tops_1(B_263,A_264)
      | ~ v3_tops_1(B_263,A_264)
      | ~ m1_subset_1(B_263,k1_zfmisc_1(u1_struct_0(A_264)))
      | ~ l1_pre_topc(A_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2543,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_2532])).

tff(c_2552,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2208,c_2543])).

tff(c_2694,plain,(
    ! [A_271,B_272] :
      ( k1_tops_1(A_271,B_272) = k1_xboole_0
      | ~ v2_tops_1(B_272,A_271)
      | ~ m1_subset_1(B_272,k1_zfmisc_1(u1_struct_0(A_271)))
      | ~ l1_pre_topc(A_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2709,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_2694])).

tff(c_2719,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2552,c_2709])).

tff(c_2917,plain,(
    ! [A_291,B_292] :
      ( k2_pre_topc(A_291,B_292) = B_292
      | ~ v4_pre_topc(B_292,A_291)
      | ~ m1_subset_1(B_292,k1_zfmisc_1(u1_struct_0(A_291)))
      | ~ l1_pre_topc(A_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2932,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_2917])).

tff(c_2942,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_2932])).

tff(c_3864,plain,(
    ! [A_344,B_345] :
      ( k7_subset_1(u1_struct_0(A_344),k2_pre_topc(A_344,B_345),k1_tops_1(A_344,B_345)) = k2_tops_1(A_344,B_345)
      | ~ m1_subset_1(B_345,k1_zfmisc_1(u1_struct_0(A_344)))
      | ~ l1_pre_topc(A_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_3876,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2942,c_3864])).

tff(c_3885,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2512,c_2331,c_2719,c_3876])).

tff(c_3887,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2209,c_3885])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:44:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.62/1.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.62/1.88  
% 4.62/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.62/1.88  %$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.62/1.88  
% 4.62/1.88  %Foreground sorts:
% 4.62/1.88  
% 4.62/1.88  
% 4.62/1.88  %Background operators:
% 4.62/1.88  
% 4.62/1.88  
% 4.62/1.88  %Foreground operators:
% 4.62/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.62/1.88  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.62/1.88  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.62/1.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.62/1.88  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 4.62/1.88  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.62/1.88  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 4.62/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.62/1.88  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.62/1.88  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.62/1.88  tff('#skF_2', type, '#skF_2': $i).
% 4.62/1.88  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.62/1.88  tff('#skF_1', type, '#skF_1': $i).
% 4.62/1.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.62/1.88  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.62/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.62/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.62/1.88  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.62/1.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.62/1.88  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.62/1.88  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.62/1.88  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.62/1.88  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.62/1.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.62/1.88  
% 4.62/1.90  tff(f_135, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_tops_1)).
% 4.62/1.90  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 4.62/1.90  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.62/1.90  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 4.62/1.90  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.62/1.90  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) <=> v2_tops_1(k2_pre_topc(A, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tops_1)).
% 4.62/1.90  tff(f_39, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.62/1.90  tff(f_45, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.62/1.90  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.62/1.90  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.62/1.90  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.62/1.90  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 4.62/1.90  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.62/1.90  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.62/1.90  tff(f_35, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 4.62/1.90  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.62/1.90  tff(f_123, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_tops_1)).
% 4.62/1.90  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 4.62/1.90  tff(c_62, plain, (v3_tops_1('#skF_2', '#skF_1') | k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.62/1.90  tff(c_76, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(splitLeft, [status(thm)], [c_62])).
% 4.62/1.90  tff(c_56, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.62/1.90  tff(c_82, plain, (~v3_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_56])).
% 4.62/1.90  tff(c_54, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.62/1.90  tff(c_52, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.62/1.90  tff(c_583, plain, (![A_100, B_101]: (k1_tops_1(A_100, B_101)=k1_xboole_0 | ~v2_tops_1(B_101, A_100) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.62/1.90  tff(c_598, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_583])).
% 4.62/1.90  tff(c_608, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_598])).
% 4.62/1.90  tff(c_637, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_608])).
% 4.62/1.90  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.62/1.90  tff(c_1473, plain, (![B_164, A_165]: (v2_tops_1(B_164, A_165) | ~r1_tarski(B_164, k2_tops_1(A_165, B_164)) | ~m1_subset_1(B_164, k1_zfmisc_1(u1_struct_0(A_165))) | ~l1_pre_topc(A_165))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.62/1.90  tff(c_1482, plain, (v2_tops_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_76, c_1473])).
% 4.62/1.90  tff(c_1491, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_6, c_1482])).
% 4.62/1.90  tff(c_1493, plain, $false, inference(negUnitSimplification, [status(thm)], [c_637, c_1491])).
% 4.62/1.90  tff(c_1495, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_608])).
% 4.62/1.90  tff(c_50, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.62/1.90  tff(c_1650, plain, (![A_182, B_183]: (k2_pre_topc(A_182, B_183)=B_183 | ~v4_pre_topc(B_183, A_182) | ~m1_subset_1(B_183, k1_zfmisc_1(u1_struct_0(A_182))) | ~l1_pre_topc(A_182))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.62/1.90  tff(c_1665, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_1650])).
% 4.62/1.90  tff(c_1675, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_1665])).
% 4.62/1.90  tff(c_2188, plain, (![B_216, A_217]: (v3_tops_1(B_216, A_217) | ~v2_tops_1(k2_pre_topc(A_217, B_216), A_217) | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0(A_217))) | ~l1_pre_topc(A_217))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.62/1.90  tff(c_2196, plain, (v3_tops_1('#skF_2', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1675, c_2188])).
% 4.62/1.90  tff(c_2205, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1495, c_2196])).
% 4.62/1.90  tff(c_2207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_2205])).
% 4.62/1.90  tff(c_2209, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(splitRight, [status(thm)], [c_62])).
% 4.62/1.90  tff(c_12, plain, (![A_7]: (k2_subset_1(A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.62/1.90  tff(c_16, plain, (![A_10]: (m1_subset_1(k2_subset_1(A_10), k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.62/1.90  tff(c_63, plain, (![A_10]: (m1_subset_1(A_10, k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16])).
% 4.62/1.90  tff(c_2279, plain, (![A_233, B_234]: (m1_subset_1(k3_subset_1(A_233, B_234), k1_zfmisc_1(A_233)) | ~m1_subset_1(B_234, k1_zfmisc_1(A_233)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.62/1.90  tff(c_26, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~m1_subset_1(A_22, k1_zfmisc_1(B_23)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.62/1.90  tff(c_2283, plain, (![A_233, B_234]: (r1_tarski(k3_subset_1(A_233, B_234), A_233) | ~m1_subset_1(B_234, k1_zfmisc_1(A_233)))), inference(resolution, [status(thm)], [c_2279, c_26])).
% 4.62/1.90  tff(c_2408, plain, (![A_252, B_253, C_254]: (k9_subset_1(A_252, B_253, C_254)=k3_xboole_0(B_253, C_254) | ~m1_subset_1(C_254, k1_zfmisc_1(A_252)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.62/1.90  tff(c_2421, plain, (![A_255, B_256]: (k9_subset_1(A_255, B_256, A_255)=k3_xboole_0(B_256, A_255))), inference(resolution, [status(thm)], [c_63, c_2408])).
% 4.62/1.90  tff(c_2256, plain, (![A_228, B_229, C_230]: (k9_subset_1(A_228, B_229, B_229)=B_229 | ~m1_subset_1(C_230, k1_zfmisc_1(A_228)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.62/1.90  tff(c_2265, plain, (![A_10, B_229]: (k9_subset_1(A_10, B_229, B_229)=B_229)), inference(resolution, [status(thm)], [c_63, c_2256])).
% 4.62/1.90  tff(c_2428, plain, (![A_255]: (k3_xboole_0(A_255, A_255)=A_255)), inference(superposition, [status(thm), theory('equality')], [c_2421, c_2265])).
% 4.62/1.90  tff(c_2288, plain, (![A_237, B_238]: (k4_xboole_0(A_237, B_238)=k3_subset_1(A_237, B_238) | ~m1_subset_1(B_238, k1_zfmisc_1(A_237)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.62/1.90  tff(c_2305, plain, (![A_239]: (k4_xboole_0(A_239, A_239)=k3_subset_1(A_239, A_239))), inference(resolution, [status(thm)], [c_63, c_2288])).
% 4.62/1.90  tff(c_10, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.62/1.90  tff(c_2311, plain, (![A_239]: (k4_xboole_0(A_239, k3_subset_1(A_239, A_239))=k3_xboole_0(A_239, A_239))), inference(superposition, [status(thm), theory('equality')], [c_2305, c_10])).
% 4.62/1.90  tff(c_2472, plain, (![A_259]: (k4_xboole_0(A_259, k3_subset_1(A_259, A_259))=A_259)), inference(demodulation, [status(thm), theory('equality')], [c_2428, c_2311])).
% 4.62/1.90  tff(c_8, plain, (![A_3, B_4]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k4_xboole_0(B_4, A_3)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.62/1.90  tff(c_2502, plain, (![A_261]: (k3_subset_1(A_261, A_261)=k1_xboole_0 | ~r1_tarski(k3_subset_1(A_261, A_261), A_261))), inference(superposition, [status(thm), theory('equality')], [c_2472, c_8])).
% 4.62/1.90  tff(c_2506, plain, (![B_234]: (k3_subset_1(B_234, B_234)=k1_xboole_0 | ~m1_subset_1(B_234, k1_zfmisc_1(B_234)))), inference(resolution, [status(thm)], [c_2283, c_2502])).
% 4.62/1.90  tff(c_2509, plain, (![B_234]: (k3_subset_1(B_234, B_234)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_63, c_2506])).
% 4.62/1.90  tff(c_2438, plain, (![A_239]: (k4_xboole_0(A_239, k3_subset_1(A_239, A_239))=A_239)), inference(demodulation, [status(thm), theory('equality')], [c_2428, c_2311])).
% 4.62/1.90  tff(c_2512, plain, (![A_239]: (k4_xboole_0(A_239, k1_xboole_0)=A_239)), inference(demodulation, [status(thm), theory('equality')], [c_2509, c_2438])).
% 4.62/1.90  tff(c_2320, plain, (![A_240, B_241, C_242]: (k7_subset_1(A_240, B_241, C_242)=k4_xboole_0(B_241, C_242) | ~m1_subset_1(B_241, k1_zfmisc_1(A_240)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.62/1.90  tff(c_2331, plain, (![C_242]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_242)=k4_xboole_0('#skF_2', C_242))), inference(resolution, [status(thm)], [c_52, c_2320])).
% 4.62/1.90  tff(c_2208, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_62])).
% 4.62/1.90  tff(c_2532, plain, (![B_263, A_264]: (v2_tops_1(B_263, A_264) | ~v3_tops_1(B_263, A_264) | ~m1_subset_1(B_263, k1_zfmisc_1(u1_struct_0(A_264))) | ~l1_pre_topc(A_264))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.62/1.90  tff(c_2543, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_2532])).
% 4.62/1.90  tff(c_2552, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2208, c_2543])).
% 4.62/1.90  tff(c_2694, plain, (![A_271, B_272]: (k1_tops_1(A_271, B_272)=k1_xboole_0 | ~v2_tops_1(B_272, A_271) | ~m1_subset_1(B_272, k1_zfmisc_1(u1_struct_0(A_271))) | ~l1_pre_topc(A_271))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.62/1.90  tff(c_2709, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_2694])).
% 4.62/1.90  tff(c_2719, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2552, c_2709])).
% 4.62/1.90  tff(c_2917, plain, (![A_291, B_292]: (k2_pre_topc(A_291, B_292)=B_292 | ~v4_pre_topc(B_292, A_291) | ~m1_subset_1(B_292, k1_zfmisc_1(u1_struct_0(A_291))) | ~l1_pre_topc(A_291))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.62/1.90  tff(c_2932, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_2917])).
% 4.62/1.90  tff(c_2942, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_2932])).
% 4.62/1.90  tff(c_3864, plain, (![A_344, B_345]: (k7_subset_1(u1_struct_0(A_344), k2_pre_topc(A_344, B_345), k1_tops_1(A_344, B_345))=k2_tops_1(A_344, B_345) | ~m1_subset_1(B_345, k1_zfmisc_1(u1_struct_0(A_344))) | ~l1_pre_topc(A_344))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.62/1.90  tff(c_3876, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2942, c_3864])).
% 4.62/1.90  tff(c_3885, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_2512, c_2331, c_2719, c_3876])).
% 4.62/1.90  tff(c_3887, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2209, c_3885])).
% 4.62/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.62/1.90  
% 4.62/1.90  Inference rules
% 4.62/1.90  ----------------------
% 4.62/1.90  #Ref     : 0
% 4.62/1.90  #Sup     : 867
% 4.62/1.90  #Fact    : 0
% 4.62/1.90  #Define  : 0
% 4.62/1.90  #Split   : 16
% 4.62/1.90  #Chain   : 0
% 4.62/1.90  #Close   : 0
% 4.62/1.90  
% 4.62/1.90  Ordering : KBO
% 4.62/1.90  
% 4.62/1.90  Simplification rules
% 4.62/1.90  ----------------------
% 4.62/1.90  #Subsume      : 86
% 4.62/1.90  #Demod        : 640
% 4.62/1.90  #Tautology    : 442
% 4.62/1.90  #SimpNegUnit  : 11
% 4.62/1.90  #BackRed      : 10
% 4.62/1.90  
% 4.62/1.90  #Partial instantiations: 0
% 4.62/1.90  #Strategies tried      : 1
% 4.62/1.90  
% 4.62/1.90  Timing (in seconds)
% 4.62/1.90  ----------------------
% 4.62/1.90  Preprocessing        : 0.34
% 4.62/1.90  Parsing              : 0.18
% 4.62/1.90  CNF conversion       : 0.02
% 4.62/1.90  Main loop            : 0.80
% 4.62/1.90  Inferencing          : 0.28
% 4.62/1.90  Reduction            : 0.29
% 4.62/1.90  Demodulation         : 0.20
% 4.62/1.90  BG Simplification    : 0.03
% 4.62/1.90  Subsumption          : 0.14
% 4.62/1.90  Abstraction          : 0.04
% 4.62/1.90  MUC search           : 0.00
% 4.62/1.90  Cooper               : 0.00
% 4.62/1.90  Total                : 1.17
% 4.62/1.90  Index Insertion      : 0.00
% 4.62/1.90  Index Deletion       : 0.00
% 4.62/1.90  Index Matching       : 0.00
% 4.62/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
