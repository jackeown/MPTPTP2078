%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:02 EST 2020

% Result     : Theorem 5.24s
% Output     : CNFRefutation 5.64s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 217 expanded)
%              Number of leaves         :   36 (  92 expanded)
%              Depth                    :    8
%              Number of atoms          :  165 ( 528 expanded)
%              Number of equality atoms :   47 ( 122 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_101,axiom,(
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

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

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

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
          <=> v2_tops_1(k2_pre_topc(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_1)).

tff(f_119,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_58,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_95,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_52,plain,
    ( k2_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_106,plain,(
    ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_52])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_722,plain,(
    ! [B_99,A_100] :
      ( v2_tops_1(B_99,A_100)
      | k1_tops_1(A_100,B_99) != k1_xboole_0
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_729,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_722])).

tff(c_737,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_729])).

tff(c_739,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_737])).

tff(c_895,plain,(
    ! [A_110,B_111] :
      ( k1_tops_1(A_110,B_111) = k1_xboole_0
      | ~ v2_tops_1(B_111,A_110)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_902,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_895])).

tff(c_910,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_902])).

tff(c_911,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_739,c_910])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1509,plain,(
    ! [B_124,A_125] :
      ( v2_tops_1(B_124,A_125)
      | ~ r1_tarski(B_124,k2_tops_1(A_125,B_124))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1514,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_1509])).

tff(c_1519,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_8,c_1514])).

tff(c_1521,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_911,c_1519])).

tff(c_1522,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_737])).

tff(c_46,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2171,plain,(
    ! [A_145,B_146] :
      ( k2_pre_topc(A_145,B_146) = B_146
      | ~ v4_pre_topc(B_146,A_145)
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2178,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_2171])).

tff(c_2186,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_2178])).

tff(c_2426,plain,(
    ! [B_161,A_162] :
      ( v3_tops_1(B_161,A_162)
      | ~ v2_tops_1(k2_pre_topc(A_162,B_161),A_162)
      | ~ m1_subset_1(B_161,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ l1_pre_topc(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2431,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2186,c_2426])).

tff(c_2436,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_1522,c_2431])).

tff(c_2438,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_2436])).

tff(c_2440,plain,(
    k2_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2439,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2915,plain,(
    ! [B_205,A_206] :
      ( v2_tops_1(B_205,A_206)
      | ~ v3_tops_1(B_205,A_206)
      | ~ m1_subset_1(B_205,k1_zfmisc_1(u1_struct_0(A_206)))
      | ~ l1_pre_topc(A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2922,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_2915])).

tff(c_2930,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2439,c_2922])).

tff(c_3325,plain,(
    ! [A_231,B_232] :
      ( k1_tops_1(A_231,B_232) = k1_xboole_0
      | ~ v2_tops_1(B_232,A_231)
      | ~ m1_subset_1(B_232,k1_zfmisc_1(u1_struct_0(A_231)))
      | ~ l1_pre_topc(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_3332,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_3325])).

tff(c_3340,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2930,c_3332])).

tff(c_2755,plain,(
    ! [A_189,B_190,C_191] :
      ( k7_subset_1(A_189,B_190,C_191) = k4_xboole_0(B_190,C_191)
      | ~ m1_subset_1(B_190,k1_zfmisc_1(A_189)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2763,plain,(
    ! [C_191] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_191) = k4_xboole_0('#skF_2',C_191) ),
    inference(resolution,[status(thm)],[c_48,c_2755])).

tff(c_3733,plain,(
    ! [A_239,B_240] :
      ( k2_pre_topc(A_239,B_240) = B_240
      | ~ v4_pre_topc(B_240,A_239)
      | ~ m1_subset_1(B_240,k1_zfmisc_1(u1_struct_0(A_239)))
      | ~ l1_pre_topc(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3740,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_3733])).

tff(c_3748,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_3740])).

tff(c_5460,plain,(
    ! [A_284,B_285] :
      ( k7_subset_1(u1_struct_0(A_284),k2_pre_topc(A_284,B_285),k1_tops_1(A_284,B_285)) = k2_tops_1(A_284,B_285)
      | ~ m1_subset_1(B_285,k1_zfmisc_1(u1_struct_0(A_284)))
      | ~ l1_pre_topc(A_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_5476,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3748,c_5460])).

tff(c_5491,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_3340,c_2763,c_5476])).

tff(c_4707,plain,(
    ! [B_271,A_272] :
      ( r1_tarski(B_271,k2_tops_1(A_272,B_271))
      | ~ v2_tops_1(B_271,A_272)
      | ~ m1_subset_1(B_271,k1_zfmisc_1(u1_struct_0(A_272)))
      | ~ l1_pre_topc(A_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_4712,plain,
    ( r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_4707])).

tff(c_4719,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2930,c_4712])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4745,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_4719,c_12])).

tff(c_18,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2444,plain,(
    ! [A_165,B_166] :
      ( r1_tarski(A_165,B_166)
      | ~ m1_subset_1(A_165,k1_zfmisc_1(B_166)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2456,plain,(
    ! [A_15] : r1_tarski(k1_xboole_0,A_15) ),
    inference(resolution,[status(thm)],[c_18,c_2444])).

tff(c_2458,plain,(
    ! [A_168,B_169] :
      ( k3_xboole_0(A_168,B_169) = A_168
      | ~ r1_tarski(A_168,B_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2495,plain,(
    ! [A_173] : k3_xboole_0(k1_xboole_0,A_173) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2456,c_2458])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2504,plain,(
    ! [A_173] : k3_xboole_0(A_173,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2495,c_2])).

tff(c_2480,plain,(
    ! [A_171,B_172] : k4_xboole_0(A_171,k4_xboole_0(A_171,B_172)) = k3_xboole_0(A_171,B_172) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2786,plain,(
    ! [A_201,B_202] : k4_xboole_0(A_201,k3_xboole_0(A_201,B_202)) = k3_xboole_0(A_201,k4_xboole_0(A_201,B_202)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2480,c_14])).

tff(c_2807,plain,(
    ! [A_173] : k3_xboole_0(A_173,k4_xboole_0(A_173,k1_xboole_0)) = k4_xboole_0(A_173,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2504,c_2786])).

tff(c_5505,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k4_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5491,c_2807])).

tff(c_5513,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5491,c_4745,c_5505])).

tff(c_5515,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2440,c_5513])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:59:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.24/2.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.56/2.06  
% 5.56/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.56/2.07  %$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.56/2.07  
% 5.56/2.07  %Foreground sorts:
% 5.56/2.07  
% 5.56/2.07  
% 5.56/2.07  %Background operators:
% 5.56/2.07  
% 5.56/2.07  
% 5.56/2.07  %Foreground operators:
% 5.56/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.56/2.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.56/2.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.56/2.07  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.56/2.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.56/2.07  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 5.56/2.07  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.56/2.07  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 5.56/2.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.56/2.07  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.56/2.07  tff('#skF_2', type, '#skF_2': $i).
% 5.56/2.07  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.56/2.07  tff('#skF_1', type, '#skF_1': $i).
% 5.56/2.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.56/2.07  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.56/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.56/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.56/2.07  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.56/2.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.56/2.07  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.56/2.07  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.56/2.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.56/2.07  
% 5.64/2.08  tff(f_131, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_tops_1)).
% 5.64/2.08  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 5.64/2.08  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.64/2.08  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 5.64/2.08  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.64/2.08  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) <=> v2_tops_1(k2_pre_topc(A, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tops_1)).
% 5.64/2.08  tff(f_119, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_tops_1)).
% 5.64/2.08  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.64/2.08  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 5.64/2.08  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.64/2.08  tff(f_51, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 5.64/2.08  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.64/2.08  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.64/2.08  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.64/2.08  tff(c_58, plain, (v3_tops_1('#skF_2', '#skF_1') | k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.64/2.08  tff(c_95, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(splitLeft, [status(thm)], [c_58])).
% 5.64/2.08  tff(c_52, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.64/2.08  tff(c_106, plain, (~v3_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_52])).
% 5.64/2.08  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.64/2.08  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.64/2.08  tff(c_722, plain, (![B_99, A_100]: (v2_tops_1(B_99, A_100) | k1_tops_1(A_100, B_99)!=k1_xboole_0 | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.64/2.08  tff(c_729, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_722])).
% 5.64/2.08  tff(c_737, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_729])).
% 5.64/2.08  tff(c_739, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_737])).
% 5.64/2.08  tff(c_895, plain, (![A_110, B_111]: (k1_tops_1(A_110, B_111)=k1_xboole_0 | ~v2_tops_1(B_111, A_110) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.64/2.08  tff(c_902, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_895])).
% 5.64/2.08  tff(c_910, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_902])).
% 5.64/2.08  tff(c_911, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_739, c_910])).
% 5.64/2.08  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.64/2.08  tff(c_1509, plain, (![B_124, A_125]: (v2_tops_1(B_124, A_125) | ~r1_tarski(B_124, k2_tops_1(A_125, B_124)) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.64/2.08  tff(c_1514, plain, (v2_tops_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_95, c_1509])).
% 5.64/2.08  tff(c_1519, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_8, c_1514])).
% 5.64/2.08  tff(c_1521, plain, $false, inference(negUnitSimplification, [status(thm)], [c_911, c_1519])).
% 5.64/2.08  tff(c_1522, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_737])).
% 5.64/2.08  tff(c_46, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.64/2.08  tff(c_2171, plain, (![A_145, B_146]: (k2_pre_topc(A_145, B_146)=B_146 | ~v4_pre_topc(B_146, A_145) | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(A_145))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.64/2.08  tff(c_2178, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_2171])).
% 5.64/2.08  tff(c_2186, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_2178])).
% 5.64/2.08  tff(c_2426, plain, (![B_161, A_162]: (v3_tops_1(B_161, A_162) | ~v2_tops_1(k2_pre_topc(A_162, B_161), A_162) | ~m1_subset_1(B_161, k1_zfmisc_1(u1_struct_0(A_162))) | ~l1_pre_topc(A_162))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.64/2.08  tff(c_2431, plain, (v3_tops_1('#skF_2', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2186, c_2426])).
% 5.64/2.08  tff(c_2436, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_1522, c_2431])).
% 5.64/2.08  tff(c_2438, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_2436])).
% 5.64/2.08  tff(c_2440, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(splitRight, [status(thm)], [c_58])).
% 5.64/2.08  tff(c_2439, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_58])).
% 5.64/2.08  tff(c_2915, plain, (![B_205, A_206]: (v2_tops_1(B_205, A_206) | ~v3_tops_1(B_205, A_206) | ~m1_subset_1(B_205, k1_zfmisc_1(u1_struct_0(A_206))) | ~l1_pre_topc(A_206))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.64/2.08  tff(c_2922, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_2915])).
% 5.64/2.08  tff(c_2930, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2439, c_2922])).
% 5.64/2.08  tff(c_3325, plain, (![A_231, B_232]: (k1_tops_1(A_231, B_232)=k1_xboole_0 | ~v2_tops_1(B_232, A_231) | ~m1_subset_1(B_232, k1_zfmisc_1(u1_struct_0(A_231))) | ~l1_pre_topc(A_231))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.64/2.08  tff(c_3332, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_3325])).
% 5.64/2.08  tff(c_3340, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2930, c_3332])).
% 5.64/2.08  tff(c_2755, plain, (![A_189, B_190, C_191]: (k7_subset_1(A_189, B_190, C_191)=k4_xboole_0(B_190, C_191) | ~m1_subset_1(B_190, k1_zfmisc_1(A_189)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.64/2.08  tff(c_2763, plain, (![C_191]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_191)=k4_xboole_0('#skF_2', C_191))), inference(resolution, [status(thm)], [c_48, c_2755])).
% 5.64/2.08  tff(c_3733, plain, (![A_239, B_240]: (k2_pre_topc(A_239, B_240)=B_240 | ~v4_pre_topc(B_240, A_239) | ~m1_subset_1(B_240, k1_zfmisc_1(u1_struct_0(A_239))) | ~l1_pre_topc(A_239))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.64/2.08  tff(c_3740, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_3733])).
% 5.64/2.08  tff(c_3748, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_3740])).
% 5.64/2.08  tff(c_5460, plain, (![A_284, B_285]: (k7_subset_1(u1_struct_0(A_284), k2_pre_topc(A_284, B_285), k1_tops_1(A_284, B_285))=k2_tops_1(A_284, B_285) | ~m1_subset_1(B_285, k1_zfmisc_1(u1_struct_0(A_284))) | ~l1_pre_topc(A_284))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.64/2.08  tff(c_5476, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3748, c_5460])).
% 5.64/2.08  tff(c_5491, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_3340, c_2763, c_5476])).
% 5.64/2.08  tff(c_4707, plain, (![B_271, A_272]: (r1_tarski(B_271, k2_tops_1(A_272, B_271)) | ~v2_tops_1(B_271, A_272) | ~m1_subset_1(B_271, k1_zfmisc_1(u1_struct_0(A_272))) | ~l1_pre_topc(A_272))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.64/2.08  tff(c_4712, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_4707])).
% 5.64/2.08  tff(c_4719, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2930, c_4712])).
% 5.64/2.08  tff(c_12, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.64/2.08  tff(c_4745, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_4719, c_12])).
% 5.64/2.08  tff(c_18, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.64/2.08  tff(c_2444, plain, (![A_165, B_166]: (r1_tarski(A_165, B_166) | ~m1_subset_1(A_165, k1_zfmisc_1(B_166)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.64/2.08  tff(c_2456, plain, (![A_15]: (r1_tarski(k1_xboole_0, A_15))), inference(resolution, [status(thm)], [c_18, c_2444])).
% 5.64/2.08  tff(c_2458, plain, (![A_168, B_169]: (k3_xboole_0(A_168, B_169)=A_168 | ~r1_tarski(A_168, B_169))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.64/2.08  tff(c_2495, plain, (![A_173]: (k3_xboole_0(k1_xboole_0, A_173)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2456, c_2458])).
% 5.64/2.08  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.64/2.08  tff(c_2504, plain, (![A_173]: (k3_xboole_0(A_173, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2495, c_2])).
% 5.64/2.08  tff(c_2480, plain, (![A_171, B_172]: (k4_xboole_0(A_171, k4_xboole_0(A_171, B_172))=k3_xboole_0(A_171, B_172))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.64/2.08  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.64/2.08  tff(c_2786, plain, (![A_201, B_202]: (k4_xboole_0(A_201, k3_xboole_0(A_201, B_202))=k3_xboole_0(A_201, k4_xboole_0(A_201, B_202)))), inference(superposition, [status(thm), theory('equality')], [c_2480, c_14])).
% 5.64/2.08  tff(c_2807, plain, (![A_173]: (k3_xboole_0(A_173, k4_xboole_0(A_173, k1_xboole_0))=k4_xboole_0(A_173, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2504, c_2786])).
% 5.64/2.08  tff(c_5505, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k4_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5491, c_2807])).
% 5.64/2.08  tff(c_5513, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5491, c_4745, c_5505])).
% 5.64/2.08  tff(c_5515, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2440, c_5513])).
% 5.64/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.64/2.08  
% 5.64/2.08  Inference rules
% 5.64/2.08  ----------------------
% 5.64/2.08  #Ref     : 0
% 5.64/2.08  #Sup     : 1228
% 5.64/2.08  #Fact    : 0
% 5.64/2.08  #Define  : 0
% 5.64/2.08  #Split   : 5
% 5.64/2.08  #Chain   : 0
% 5.64/2.08  #Close   : 0
% 5.64/2.08  
% 5.64/2.08  Ordering : KBO
% 5.64/2.08  
% 5.64/2.08  Simplification rules
% 5.64/2.08  ----------------------
% 5.64/2.08  #Subsume      : 296
% 5.64/2.08  #Demod        : 1129
% 5.64/2.08  #Tautology    : 574
% 5.64/2.08  #SimpNegUnit  : 5
% 5.64/2.08  #BackRed      : 0
% 5.64/2.08  
% 5.64/2.08  #Partial instantiations: 0
% 5.64/2.08  #Strategies tried      : 1
% 5.64/2.08  
% 5.64/2.08  Timing (in seconds)
% 5.64/2.08  ----------------------
% 5.64/2.09  Preprocessing        : 0.34
% 5.64/2.09  Parsing              : 0.18
% 5.64/2.09  CNF conversion       : 0.02
% 5.64/2.09  Main loop            : 0.99
% 5.64/2.09  Inferencing          : 0.33
% 5.64/2.09  Reduction            : 0.41
% 5.64/2.09  Demodulation         : 0.32
% 5.64/2.09  BG Simplification    : 0.04
% 5.64/2.09  Subsumption          : 0.15
% 5.64/2.09  Abstraction          : 0.05
% 5.64/2.09  MUC search           : 0.00
% 5.64/2.09  Cooper               : 0.00
% 5.64/2.09  Total                : 1.36
% 5.64/2.09  Index Insertion      : 0.00
% 5.64/2.09  Index Deletion       : 0.00
% 5.64/2.09  Index Matching       : 0.00
% 5.64/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
