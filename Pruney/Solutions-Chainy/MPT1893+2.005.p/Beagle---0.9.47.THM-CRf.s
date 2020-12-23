%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:26 EST 2020

% Result     : Theorem 5.71s
% Output     : CNFRefutation 5.71s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 227 expanded)
%              Number of leaves         :   44 (  97 expanded)
%              Depth                    :   10
%              Number of atoms          :  180 ( 738 expanded)
%              Number of equality atoms :   27 (  73 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_155,negated_conjecture,(
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

tff(f_72,axiom,(
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

tff(f_104,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tdlat_3)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_133,axiom,(
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

tff(f_55,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ~ v1_subset_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_subset_1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(A)) )
     => ~ v1_xboole_0(k3_subset_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tex_2)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_117,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_56,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1332,plain,(
    ! [A_95,B_96] :
      ( k2_pre_topc(A_95,B_96) = B_96
      | ~ v4_pre_topc(B_96,A_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1341,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1332])).

tff(c_1346,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1341])).

tff(c_1347,plain,(
    ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1346])).

tff(c_60,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_58,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_52,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | v3_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_73,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_2158,plain,(
    ! [B_118,A_119] :
      ( v4_pre_topc(B_118,A_119)
      | ~ v3_pre_topc(B_118,A_119)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ v3_tdlat_3(A_119)
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2167,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_2158])).

tff(c_2172,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_58,c_73,c_2167])).

tff(c_2174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1347,c_2172])).

tff(c_2175,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1346])).

tff(c_2236,plain,(
    ! [B_122,A_123] :
      ( v1_tops_1(B_122,A_123)
      | k2_pre_topc(A_123,B_122) != u1_struct_0(A_123)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2245,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_2236])).

tff(c_2250,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | u1_struct_0('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2175,c_2245])).

tff(c_2251,plain,(
    u1_struct_0('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2250])).

tff(c_2408,plain,(
    ! [A_130,B_131] :
      ( k2_pre_topc(A_130,B_131) = u1_struct_0(A_130)
      | ~ v1_tops_1(B_131,A_130)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2417,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_2408])).

tff(c_2422,plain,
    ( u1_struct_0('#skF_3') = '#skF_4'
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2175,c_2417])).

tff(c_2423,plain,(
    ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_2251,c_2422])).

tff(c_50,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_3444,plain,(
    ! [B_154,A_155] :
      ( v1_tops_1(B_154,A_155)
      | ~ v3_tex_2(B_154,A_155)
      | ~ v3_pre_topc(B_154,A_155)
      | ~ m1_subset_1(B_154,k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ l1_pre_topc(A_155)
      | ~ v2_pre_topc(A_155)
      | v2_struct_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_3453,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_3444])).

tff(c_3458,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_73,c_50,c_3453])).

tff(c_3460,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2423,c_3458])).

tff(c_3462,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2250])).

tff(c_48,plain,(
    v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_216,plain,(
    ! [B_59,A_60] :
      ( ~ v1_subset_1(B_59,A_60)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60))
      | ~ v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_219,plain,
    ( ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_216])).

tff(c_222,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_219])).

tff(c_1165,plain,(
    ! [A_91,B_92] :
      ( ~ v1_xboole_0(k3_subset_1(A_91,B_92))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_91))
      | ~ v1_subset_1(B_92,A_91)
      | v1_xboole_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1174,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'))
    | ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_1165])).

tff(c_1179,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1174])).

tff(c_1180,plain,(
    ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_222,c_1179])).

tff(c_3464,plain,(
    ~ v1_xboole_0(k3_subset_1('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3462,c_1180])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_121,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k4_xboole_0(A_47,B_48)) = k3_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_139,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_121])).

tff(c_351,plain,(
    ! [A_67,B_68] :
      ( k4_xboole_0(A_67,B_68) = k3_subset_1(A_67,B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_355,plain,(
    k4_xboole_0(u1_struct_0('#skF_3'),'#skF_4') = k3_subset_1(u1_struct_0('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_351])).

tff(c_3468,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3462,c_3462,c_355])).

tff(c_3532,plain,(
    k3_xboole_0('#skF_4',k1_xboole_0) = k3_subset_1('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_3468])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_142,plain,(
    ! [A_49,B_50] : r1_tarski(k3_xboole_0(A_49,B_50),A_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_4])).

tff(c_145,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_142])).

tff(c_10,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_159,plain,(
    ! [B_53,A_54] :
      ( ~ r1_xboole_0(B_53,A_54)
      | ~ r1_tarski(B_53,A_54)
      | v1_xboole_0(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_164,plain,(
    ! [A_55] :
      ( ~ r1_tarski(A_55,k1_xboole_0)
      | v1_xboole_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_10,c_159])).

tff(c_181,plain,(
    ! [B_2] : v1_xboole_0(k3_xboole_0(B_2,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_145,c_164])).

tff(c_3583,plain,(
    v1_xboole_0(k3_subset_1('#skF_4','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3532,c_181])).

tff(c_3600,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3464,c_3583])).

tff(c_3602,plain,(
    ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_3601,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_5640,plain,(
    ! [B_234,A_235] :
      ( v3_pre_topc(B_234,A_235)
      | ~ v4_pre_topc(B_234,A_235)
      | ~ m1_subset_1(B_234,k1_zfmisc_1(u1_struct_0(A_235)))
      | ~ v3_tdlat_3(A_235)
      | ~ l1_pre_topc(A_235)
      | ~ v2_pre_topc(A_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_5649,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_5640])).

tff(c_5654,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_58,c_3601,c_5649])).

tff(c_5656,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3602,c_5654])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:42:55 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.71/2.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.71/2.20  
% 5.71/2.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.71/2.20  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 5.71/2.20  
% 5.71/2.20  %Foreground sorts:
% 5.71/2.20  
% 5.71/2.20  
% 5.71/2.20  %Background operators:
% 5.71/2.20  
% 5.71/2.20  
% 5.71/2.20  %Foreground operators:
% 5.71/2.20  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.71/2.20  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.71/2.20  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.71/2.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.71/2.20  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 5.71/2.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.71/2.20  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.71/2.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.71/2.20  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.71/2.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.71/2.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.71/2.20  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.71/2.20  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 5.71/2.20  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 5.71/2.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.71/2.20  tff('#skF_3', type, '#skF_3': $i).
% 5.71/2.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.71/2.20  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 5.71/2.20  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.71/2.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.71/2.20  tff('#skF_4', type, '#skF_4': $i).
% 5.71/2.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.71/2.20  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.71/2.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.71/2.20  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.71/2.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.71/2.20  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.71/2.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.71/2.20  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.71/2.20  
% 5.71/2.22  tff(f_155, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(((v3_pre_topc(B, A) | v4_pre_topc(B, A)) & v3_tex_2(B, A)) & v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_tex_2)).
% 5.71/2.22  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.71/2.22  tff(f_104, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tdlat_3)).
% 5.71/2.22  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 5.71/2.22  tff(f_133, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_tex_2)).
% 5.71/2.22  tff(f_55, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~v1_subset_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_subset_1)).
% 5.71/2.22  tff(f_91, axiom, (![A, B]: (((~v1_xboole_0(A) & v1_subset_1(B, A)) & m1_subset_1(B, k1_zfmisc_1(A))) => ~v1_xboole_0(k3_subset_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tex_2)).
% 5.71/2.22  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.71/2.22  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.71/2.22  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 5.71/2.22  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.71/2.22  tff(f_29, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.71/2.22  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.71/2.22  tff(f_43, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 5.71/2.22  tff(f_117, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tdlat_3)).
% 5.71/2.22  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.71/2.22  tff(c_56, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.71/2.22  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.71/2.22  tff(c_1332, plain, (![A_95, B_96]: (k2_pre_topc(A_95, B_96)=B_96 | ~v4_pre_topc(B_96, A_95) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.71/2.22  tff(c_1341, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_54, c_1332])).
% 5.71/2.22  tff(c_1346, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1341])).
% 5.71/2.22  tff(c_1347, plain, (~v4_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_1346])).
% 5.71/2.22  tff(c_60, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.71/2.22  tff(c_58, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.71/2.22  tff(c_52, plain, (v4_pre_topc('#skF_4', '#skF_3') | v3_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.71/2.22  tff(c_73, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_52])).
% 5.71/2.22  tff(c_2158, plain, (![B_118, A_119]: (v4_pre_topc(B_118, A_119) | ~v3_pre_topc(B_118, A_119) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_119))) | ~v3_tdlat_3(A_119) | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.71/2.22  tff(c_2167, plain, (v4_pre_topc('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3') | ~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_54, c_2158])).
% 5.71/2.22  tff(c_2172, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_58, c_73, c_2167])).
% 5.71/2.22  tff(c_2174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1347, c_2172])).
% 5.71/2.22  tff(c_2175, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_1346])).
% 5.71/2.22  tff(c_2236, plain, (![B_122, A_123]: (v1_tops_1(B_122, A_123) | k2_pre_topc(A_123, B_122)!=u1_struct_0(A_123) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.71/2.22  tff(c_2245, plain, (v1_tops_1('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_54, c_2236])).
% 5.71/2.22  tff(c_2250, plain, (v1_tops_1('#skF_4', '#skF_3') | u1_struct_0('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2175, c_2245])).
% 5.71/2.22  tff(c_2251, plain, (u1_struct_0('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_2250])).
% 5.71/2.22  tff(c_2408, plain, (![A_130, B_131]: (k2_pre_topc(A_130, B_131)=u1_struct_0(A_130) | ~v1_tops_1(B_131, A_130) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.71/2.22  tff(c_2417, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_54, c_2408])).
% 5.71/2.22  tff(c_2422, plain, (u1_struct_0('#skF_3')='#skF_4' | ~v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2175, c_2417])).
% 5.71/2.22  tff(c_2423, plain, (~v1_tops_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_2251, c_2422])).
% 5.71/2.22  tff(c_50, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.71/2.22  tff(c_3444, plain, (![B_154, A_155]: (v1_tops_1(B_154, A_155) | ~v3_tex_2(B_154, A_155) | ~v3_pre_topc(B_154, A_155) | ~m1_subset_1(B_154, k1_zfmisc_1(u1_struct_0(A_155))) | ~l1_pre_topc(A_155) | ~v2_pre_topc(A_155) | v2_struct_0(A_155))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.71/2.22  tff(c_3453, plain, (v1_tops_1('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_3444])).
% 5.71/2.22  tff(c_3458, plain, (v1_tops_1('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_73, c_50, c_3453])).
% 5.71/2.22  tff(c_3460, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_2423, c_3458])).
% 5.71/2.22  tff(c_3462, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_2250])).
% 5.71/2.22  tff(c_48, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.71/2.22  tff(c_216, plain, (![B_59, A_60]: (~v1_subset_1(B_59, A_60) | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)) | ~v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.71/2.22  tff(c_219, plain, (~v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_54, c_216])).
% 5.71/2.22  tff(c_222, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_219])).
% 5.71/2.22  tff(c_1165, plain, (![A_91, B_92]: (~v1_xboole_0(k3_subset_1(A_91, B_92)) | ~m1_subset_1(B_92, k1_zfmisc_1(A_91)) | ~v1_subset_1(B_92, A_91) | v1_xboole_0(A_91))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.71/2.22  tff(c_1174, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4')) | ~v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_54, c_1165])).
% 5.71/2.22  tff(c_1179, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1174])).
% 5.71/2.22  tff(c_1180, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_222, c_1179])).
% 5.71/2.22  tff(c_3464, plain, (~v1_xboole_0(k3_subset_1('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3462, c_1180])).
% 5.71/2.22  tff(c_6, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.71/2.22  tff(c_121, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k4_xboole_0(A_47, B_48))=k3_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.71/2.22  tff(c_139, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_121])).
% 5.71/2.22  tff(c_351, plain, (![A_67, B_68]: (k4_xboole_0(A_67, B_68)=k3_subset_1(A_67, B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.71/2.22  tff(c_355, plain, (k4_xboole_0(u1_struct_0('#skF_3'), '#skF_4')=k3_subset_1(u1_struct_0('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_54, c_351])).
% 5.71/2.22  tff(c_3468, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3462, c_3462, c_355])).
% 5.71/2.22  tff(c_3532, plain, (k3_xboole_0('#skF_4', k1_xboole_0)=k3_subset_1('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_139, c_3468])).
% 5.71/2.22  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.71/2.22  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.71/2.22  tff(c_142, plain, (![A_49, B_50]: (r1_tarski(k3_xboole_0(A_49, B_50), A_49))), inference(superposition, [status(thm), theory('equality')], [c_121, c_4])).
% 5.71/2.22  tff(c_145, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_142])).
% 5.71/2.22  tff(c_10, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.71/2.22  tff(c_159, plain, (![B_53, A_54]: (~r1_xboole_0(B_53, A_54) | ~r1_tarski(B_53, A_54) | v1_xboole_0(B_53))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.71/2.22  tff(c_164, plain, (![A_55]: (~r1_tarski(A_55, k1_xboole_0) | v1_xboole_0(A_55))), inference(resolution, [status(thm)], [c_10, c_159])).
% 5.71/2.22  tff(c_181, plain, (![B_2]: (v1_xboole_0(k3_xboole_0(B_2, k1_xboole_0)))), inference(resolution, [status(thm)], [c_145, c_164])).
% 5.71/2.22  tff(c_3583, plain, (v1_xboole_0(k3_subset_1('#skF_4', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3532, c_181])).
% 5.71/2.22  tff(c_3600, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3464, c_3583])).
% 5.71/2.22  tff(c_3602, plain, (~v3_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_52])).
% 5.71/2.22  tff(c_3601, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_52])).
% 5.71/2.22  tff(c_5640, plain, (![B_234, A_235]: (v3_pre_topc(B_234, A_235) | ~v4_pre_topc(B_234, A_235) | ~m1_subset_1(B_234, k1_zfmisc_1(u1_struct_0(A_235))) | ~v3_tdlat_3(A_235) | ~l1_pre_topc(A_235) | ~v2_pre_topc(A_235))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.71/2.22  tff(c_5649, plain, (v3_pre_topc('#skF_4', '#skF_3') | ~v4_pre_topc('#skF_4', '#skF_3') | ~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_54, c_5640])).
% 5.71/2.22  tff(c_5654, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_58, c_3601, c_5649])).
% 5.71/2.22  tff(c_5656, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3602, c_5654])).
% 5.71/2.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.71/2.22  
% 5.71/2.22  Inference rules
% 5.71/2.22  ----------------------
% 5.71/2.22  #Ref     : 0
% 5.71/2.22  #Sup     : 1337
% 5.71/2.22  #Fact    : 0
% 5.71/2.22  #Define  : 0
% 5.71/2.22  #Split   : 5
% 5.71/2.22  #Chain   : 0
% 5.71/2.22  #Close   : 0
% 5.71/2.22  
% 5.71/2.22  Ordering : KBO
% 5.71/2.22  
% 5.71/2.22  Simplification rules
% 5.71/2.22  ----------------------
% 5.71/2.22  #Subsume      : 65
% 5.71/2.22  #Demod        : 1299
% 5.71/2.22  #Tautology    : 853
% 5.71/2.22  #SimpNegUnit  : 11
% 5.71/2.22  #BackRed      : 9
% 5.71/2.22  
% 5.71/2.22  #Partial instantiations: 0
% 5.71/2.22  #Strategies tried      : 1
% 5.71/2.22  
% 5.71/2.22  Timing (in seconds)
% 5.71/2.22  ----------------------
% 5.71/2.22  Preprocessing        : 0.35
% 5.71/2.22  Parsing              : 0.20
% 5.71/2.22  CNF conversion       : 0.02
% 5.71/2.22  Main loop            : 1.06
% 5.71/2.22  Inferencing          : 0.30
% 5.71/2.22  Reduction            : 0.53
% 5.71/2.22  Demodulation         : 0.45
% 5.71/2.22  BG Simplification    : 0.04
% 5.71/2.22  Subsumption          : 0.13
% 5.71/2.22  Abstraction          : 0.05
% 5.71/2.22  MUC search           : 0.00
% 5.71/2.22  Cooper               : 0.00
% 5.71/2.22  Total                : 1.44
% 5.71/2.22  Index Insertion      : 0.00
% 5.71/2.22  Index Deletion       : 0.00
% 5.71/2.22  Index Matching       : 0.00
% 5.71/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
