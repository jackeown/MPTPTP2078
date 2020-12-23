%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:25 EST 2020

% Result     : Theorem 5.11s
% Output     : CNFRefutation 5.43s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 224 expanded)
%              Number of leaves         :   44 (  96 expanded)
%              Depth                    :   10
%              Number of atoms          :  176 ( 732 expanded)
%              Number of equality atoms :   32 (  76 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_28,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_48,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_44,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_162,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ~ ( ( v3_pre_topc(B,A)
                  | v4_pre_topc(B,A) )
                & v3_tex_2(B,A)
                & v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_tex_2)).

tff(f_79,axiom,(
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

tff(f_111,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tdlat_3)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_140,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v3_pre_topc(B,A)
              & v3_tex_2(B,A) )
           => v1_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ~ v1_subset_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_subset_1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(A)) )
     => ~ v1_xboole_0(k3_subset_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tex_2)).

tff(f_124,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(c_4,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_108,plain,(
    ! [B_48,A_49] : k3_xboole_0(B_48,A_49) = k3_xboole_0(A_49,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_85,plain,(
    ! [A_46] :
      ( k1_xboole_0 = A_46
      | ~ r1_tarski(A_46,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_94,plain,(
    ! [B_8] : k3_xboole_0(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_85])).

tff(c_124,plain,(
    ! [B_48] : k3_xboole_0(B_48,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_94])).

tff(c_18,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_296,plain,(
    ! [A_59,B_60] : k4_xboole_0(A_59,k4_xboole_0(A_59,B_60)) = k3_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_311,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_296])).

tff(c_314,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_311])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_66,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_2361,plain,(
    ! [A_113,B_114] :
      ( k2_pre_topc(A_113,B_114) = B_114
      | ~ v4_pre_topc(B_114,A_113)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2370,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_2361])).

tff(c_2375,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2370])).

tff(c_2376,plain,(
    ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2375])).

tff(c_70,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_68,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_62,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | v3_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_197,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_3375,plain,(
    ! [B_143,A_144] :
      ( v4_pre_topc(B_143,A_144)
      | ~ v3_pre_topc(B_143,A_144)
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ v3_tdlat_3(A_144)
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_3384,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_3375])).

tff(c_3389,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_68,c_197,c_3384])).

tff(c_3391,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2376,c_3389])).

tff(c_3392,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2375])).

tff(c_3687,plain,(
    ! [B_153,A_154] :
      ( v1_tops_1(B_153,A_154)
      | k2_pre_topc(A_154,B_153) != u1_struct_0(A_154)
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_pre_topc(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_3696,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_3687])).

tff(c_3701,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | u1_struct_0('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3392,c_3696])).

tff(c_3702,plain,(
    u1_struct_0('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3701])).

tff(c_3703,plain,(
    ! [A_155,B_156] :
      ( k2_pre_topc(A_155,B_156) = u1_struct_0(A_155)
      | ~ v1_tops_1(B_156,A_155)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ l1_pre_topc(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_3712,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_3703])).

tff(c_3717,plain,
    ( u1_struct_0('#skF_3') = '#skF_4'
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3392,c_3712])).

tff(c_3718,plain,(
    ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_3702,c_3717])).

tff(c_60,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_4349,plain,(
    ! [B_173,A_174] :
      ( v1_tops_1(B_173,A_174)
      | ~ v3_tex_2(B_173,A_174)
      | ~ v3_pre_topc(B_173,A_174)
      | ~ m1_subset_1(B_173,k1_zfmisc_1(u1_struct_0(A_174)))
      | ~ l1_pre_topc(A_174)
      | ~ v2_pre_topc(A_174)
      | v2_struct_0(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_4358,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_4349])).

tff(c_4363,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_197,c_60,c_4358])).

tff(c_4365,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3718,c_4363])).

tff(c_4367,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3701])).

tff(c_903,plain,(
    ! [A_86,B_87] :
      ( k4_xboole_0(A_86,B_87) = k3_subset_1(A_86,B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_907,plain,(
    k4_xboole_0(u1_struct_0('#skF_3'),'#skF_4') = k3_subset_1(u1_struct_0('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_903])).

tff(c_4376,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4367,c_4367,c_907])).

tff(c_4382,plain,(
    k3_subset_1('#skF_4','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_4376])).

tff(c_58,plain,(
    v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_558,plain,(
    ! [B_73,A_74] :
      ( ~ v1_subset_1(B_73,A_74)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_74))
      | ~ v1_xboole_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_561,plain,
    ( ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_64,c_558])).

tff(c_564,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_561])).

tff(c_2230,plain,(
    ! [A_111,B_112] :
      ( ~ v1_xboole_0(k3_subset_1(A_111,B_112))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(A_111))
      | ~ v1_subset_1(B_112,A_111)
      | v1_xboole_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2239,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'))
    | ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_64,c_2230])).

tff(c_2244,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2239])).

tff(c_2245,plain,(
    ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_564,c_2244])).

tff(c_4370,plain,(
    ~ v1_xboole_0(k3_subset_1('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4367,c_2245])).

tff(c_4439,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4382,c_4370])).

tff(c_4442,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4439])).

tff(c_4444,plain,(
    ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_4443,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_6967,plain,(
    ! [B_256,A_257] :
      ( v3_pre_topc(B_256,A_257)
      | ~ v4_pre_topc(B_256,A_257)
      | ~ m1_subset_1(B_256,k1_zfmisc_1(u1_struct_0(A_257)))
      | ~ v3_tdlat_3(A_257)
      | ~ l1_pre_topc(A_257)
      | ~ v2_pre_topc(A_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_6976,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_6967])).

tff(c_6981,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_68,c_4443,c_6976])).

tff(c_6983,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4444,c_6981])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:39:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.11/2.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.11/2.05  
% 5.11/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.11/2.05  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 5.11/2.05  
% 5.11/2.05  %Foreground sorts:
% 5.11/2.05  
% 5.11/2.05  
% 5.11/2.05  %Background operators:
% 5.11/2.05  
% 5.11/2.05  
% 5.11/2.05  %Foreground operators:
% 5.11/2.05  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.11/2.05  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.11/2.05  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.11/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.11/2.05  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 5.11/2.05  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.11/2.05  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.11/2.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.11/2.05  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.11/2.05  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.11/2.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.11/2.05  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.11/2.05  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.11/2.05  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 5.11/2.05  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 5.11/2.05  tff('#skF_3', type, '#skF_3': $i).
% 5.11/2.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.11/2.05  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 5.11/2.05  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.11/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.11/2.05  tff('#skF_4', type, '#skF_4': $i).
% 5.11/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.11/2.05  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.11/2.05  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.11/2.05  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.11/2.05  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.11/2.05  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.11/2.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.11/2.05  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.11/2.05  
% 5.43/2.06  tff(f_28, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.43/2.06  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.43/2.06  tff(f_38, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.43/2.06  tff(f_48, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 5.43/2.06  tff(f_44, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.43/2.06  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.43/2.06  tff(f_162, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(((v3_pre_topc(B, A) | v4_pre_topc(B, A)) & v3_tex_2(B, A)) & v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_tex_2)).
% 5.43/2.06  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.43/2.06  tff(f_111, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tdlat_3)).
% 5.43/2.06  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 5.43/2.06  tff(f_140, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_tex_2)).
% 5.43/2.06  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 5.43/2.06  tff(f_62, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~v1_subset_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_subset_1)).
% 5.43/2.06  tff(f_98, axiom, (![A, B]: (((~v1_xboole_0(A) & v1_subset_1(B, A)) & m1_subset_1(B, k1_zfmisc_1(A))) => ~v1_xboole_0(k3_subset_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tex_2)).
% 5.43/2.06  tff(f_124, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tdlat_3)).
% 5.43/2.06  tff(c_4, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 5.43/2.06  tff(c_108, plain, (![B_48, A_49]: (k3_xboole_0(B_48, A_49)=k3_xboole_0(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.43/2.06  tff(c_14, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.43/2.06  tff(c_85, plain, (![A_46]: (k1_xboole_0=A_46 | ~r1_tarski(A_46, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.43/2.06  tff(c_94, plain, (![B_8]: (k3_xboole_0(k1_xboole_0, B_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_85])).
% 5.43/2.06  tff(c_124, plain, (![B_48]: (k3_xboole_0(B_48, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_108, c_94])).
% 5.43/2.06  tff(c_18, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.43/2.06  tff(c_296, plain, (![A_59, B_60]: (k4_xboole_0(A_59, k4_xboole_0(A_59, B_60))=k3_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.43/2.06  tff(c_311, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_296])).
% 5.43/2.06  tff(c_314, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_124, c_311])).
% 5.43/2.06  tff(c_72, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.43/2.06  tff(c_66, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.43/2.06  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.43/2.06  tff(c_2361, plain, (![A_113, B_114]: (k2_pre_topc(A_113, B_114)=B_114 | ~v4_pre_topc(B_114, A_113) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.43/2.06  tff(c_2370, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_64, c_2361])).
% 5.43/2.06  tff(c_2375, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2370])).
% 5.43/2.06  tff(c_2376, plain, (~v4_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_2375])).
% 5.43/2.06  tff(c_70, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.43/2.06  tff(c_68, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.43/2.06  tff(c_62, plain, (v4_pre_topc('#skF_4', '#skF_3') | v3_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.43/2.06  tff(c_197, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_62])).
% 5.43/2.06  tff(c_3375, plain, (![B_143, A_144]: (v4_pre_topc(B_143, A_144) | ~v3_pre_topc(B_143, A_144) | ~m1_subset_1(B_143, k1_zfmisc_1(u1_struct_0(A_144))) | ~v3_tdlat_3(A_144) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.43/2.06  tff(c_3384, plain, (v4_pre_topc('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3') | ~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_64, c_3375])).
% 5.43/2.06  tff(c_3389, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_68, c_197, c_3384])).
% 5.43/2.06  tff(c_3391, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2376, c_3389])).
% 5.43/2.06  tff(c_3392, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_2375])).
% 5.43/2.06  tff(c_3687, plain, (![B_153, A_154]: (v1_tops_1(B_153, A_154) | k2_pre_topc(A_154, B_153)!=u1_struct_0(A_154) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_154))) | ~l1_pre_topc(A_154))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.43/2.06  tff(c_3696, plain, (v1_tops_1('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_64, c_3687])).
% 5.43/2.06  tff(c_3701, plain, (v1_tops_1('#skF_4', '#skF_3') | u1_struct_0('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3392, c_3696])).
% 5.43/2.06  tff(c_3702, plain, (u1_struct_0('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_3701])).
% 5.43/2.06  tff(c_3703, plain, (![A_155, B_156]: (k2_pre_topc(A_155, B_156)=u1_struct_0(A_155) | ~v1_tops_1(B_156, A_155) | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0(A_155))) | ~l1_pre_topc(A_155))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.43/2.06  tff(c_3712, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_64, c_3703])).
% 5.43/2.06  tff(c_3717, plain, (u1_struct_0('#skF_3')='#skF_4' | ~v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3392, c_3712])).
% 5.43/2.06  tff(c_3718, plain, (~v1_tops_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_3702, c_3717])).
% 5.43/2.06  tff(c_60, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.43/2.06  tff(c_4349, plain, (![B_173, A_174]: (v1_tops_1(B_173, A_174) | ~v3_tex_2(B_173, A_174) | ~v3_pre_topc(B_173, A_174) | ~m1_subset_1(B_173, k1_zfmisc_1(u1_struct_0(A_174))) | ~l1_pre_topc(A_174) | ~v2_pre_topc(A_174) | v2_struct_0(A_174))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.43/2.06  tff(c_4358, plain, (v1_tops_1('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_4349])).
% 5.43/2.06  tff(c_4363, plain, (v1_tops_1('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_197, c_60, c_4358])).
% 5.43/2.06  tff(c_4365, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_3718, c_4363])).
% 5.43/2.06  tff(c_4367, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_3701])).
% 5.43/2.06  tff(c_903, plain, (![A_86, B_87]: (k4_xboole_0(A_86, B_87)=k3_subset_1(A_86, B_87) | ~m1_subset_1(B_87, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.43/2.06  tff(c_907, plain, (k4_xboole_0(u1_struct_0('#skF_3'), '#skF_4')=k3_subset_1(u1_struct_0('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_64, c_903])).
% 5.43/2.06  tff(c_4376, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4367, c_4367, c_907])).
% 5.43/2.06  tff(c_4382, plain, (k3_subset_1('#skF_4', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_314, c_4376])).
% 5.43/2.06  tff(c_58, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.43/2.06  tff(c_558, plain, (![B_73, A_74]: (~v1_subset_1(B_73, A_74) | ~m1_subset_1(B_73, k1_zfmisc_1(A_74)) | ~v1_xboole_0(A_74))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.43/2.06  tff(c_561, plain, (~v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_64, c_558])).
% 5.43/2.06  tff(c_564, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_561])).
% 5.43/2.06  tff(c_2230, plain, (![A_111, B_112]: (~v1_xboole_0(k3_subset_1(A_111, B_112)) | ~m1_subset_1(B_112, k1_zfmisc_1(A_111)) | ~v1_subset_1(B_112, A_111) | v1_xboole_0(A_111))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.43/2.06  tff(c_2239, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4')) | ~v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_64, c_2230])).
% 5.43/2.06  tff(c_2244, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2239])).
% 5.43/2.06  tff(c_2245, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_564, c_2244])).
% 5.43/2.06  tff(c_4370, plain, (~v1_xboole_0(k3_subset_1('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4367, c_2245])).
% 5.43/2.06  tff(c_4439, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4382, c_4370])).
% 5.43/2.06  tff(c_4442, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_4439])).
% 5.43/2.06  tff(c_4444, plain, (~v3_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_62])).
% 5.43/2.06  tff(c_4443, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_62])).
% 5.43/2.06  tff(c_6967, plain, (![B_256, A_257]: (v3_pre_topc(B_256, A_257) | ~v4_pre_topc(B_256, A_257) | ~m1_subset_1(B_256, k1_zfmisc_1(u1_struct_0(A_257))) | ~v3_tdlat_3(A_257) | ~l1_pre_topc(A_257) | ~v2_pre_topc(A_257))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.43/2.06  tff(c_6976, plain, (v3_pre_topc('#skF_4', '#skF_3') | ~v4_pre_topc('#skF_4', '#skF_3') | ~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_64, c_6967])).
% 5.43/2.06  tff(c_6981, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_68, c_4443, c_6976])).
% 5.43/2.06  tff(c_6983, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4444, c_6981])).
% 5.43/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.43/2.06  
% 5.43/2.06  Inference rules
% 5.43/2.06  ----------------------
% 5.43/2.06  #Ref     : 0
% 5.43/2.06  #Sup     : 1630
% 5.43/2.06  #Fact    : 0
% 5.43/2.06  #Define  : 0
% 5.43/2.06  #Split   : 8
% 5.43/2.06  #Chain   : 0
% 5.43/2.06  #Close   : 0
% 5.43/2.06  
% 5.43/2.06  Ordering : KBO
% 5.43/2.06  
% 5.43/2.06  Simplification rules
% 5.43/2.06  ----------------------
% 5.43/2.06  #Subsume      : 177
% 5.43/2.06  #Demod        : 2210
% 5.43/2.06  #Tautology    : 1260
% 5.43/2.06  #SimpNegUnit  : 10
% 5.43/2.06  #BackRed      : 15
% 5.43/2.06  
% 5.43/2.06  #Partial instantiations: 0
% 5.43/2.06  #Strategies tried      : 1
% 5.43/2.06  
% 5.43/2.06  Timing (in seconds)
% 5.43/2.06  ----------------------
% 5.43/2.07  Preprocessing        : 0.34
% 5.43/2.07  Parsing              : 0.18
% 5.43/2.07  CNF conversion       : 0.02
% 5.43/2.07  Main loop            : 0.95
% 5.43/2.07  Inferencing          : 0.28
% 5.43/2.07  Reduction            : 0.46
% 5.43/2.07  Demodulation         : 0.38
% 5.43/2.07  BG Simplification    : 0.03
% 5.43/2.07  Subsumption          : 0.13
% 5.43/2.07  Abstraction          : 0.05
% 5.43/2.07  MUC search           : 0.00
% 5.43/2.07  Cooper               : 0.00
% 5.43/2.07  Total                : 1.33
% 5.43/2.07  Index Insertion      : 0.00
% 5.43/2.07  Index Deletion       : 0.00
% 5.43/2.07  Index Matching       : 0.00
% 5.43/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
