%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:08 EST 2020

% Result     : Theorem 4.32s
% Output     : CNFRefutation 4.49s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 829 expanded)
%              Number of leaves         :   43 ( 296 expanded)
%              Depth                    :   14
%              Number of atoms          :  316 (2088 expanded)
%              Number of equality atoms :   39 ( 336 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_29,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_38,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_171,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tex_2(B,A)
            <=> ~ v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_107,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).

tff(f_31,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(A),k2_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_96,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_121,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_153,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v1_tops_1(B,A)
              & v2_tex_2(B,A) )
           => v3_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).

tff(f_137,axiom,(
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

tff(c_4,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_8] : ~ v1_subset_1(k2_subset_1(A_8),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_67,plain,(
    ! [A_8] : ~ v1_subset_1(A_8,A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_22,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_82,plain,(
    ! [A_45] :
      ( u1_struct_0(A_45) = k2_struct_0(A_45)
      | ~ l1_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_88,plain,(
    ! [A_47] :
      ( u1_struct_0(A_47) = k2_struct_0(A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_22,c_82])).

tff(c_92,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_88])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_93,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_50])).

tff(c_1278,plain,(
    ! [A_196,B_197] :
      ( k2_pre_topc(A_196,B_197) = B_197
      | ~ v4_pre_topc(B_197,A_196)
      | ~ m1_subset_1(B_197,k1_zfmisc_1(u1_struct_0(A_196)))
      | ~ l1_pre_topc(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1288,plain,(
    ! [B_197] :
      ( k2_pre_topc('#skF_2',B_197) = B_197
      | ~ v4_pre_topc(B_197,'#skF_2')
      | ~ m1_subset_1(B_197,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_1278])).

tff(c_1298,plain,(
    ! [B_198] :
      ( k2_pre_topc('#skF_2',B_198) = B_198
      | ~ v4_pre_topc(B_198,'#skF_2')
      | ~ m1_subset_1(B_198,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1288])).

tff(c_1311,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_93,c_1298])).

tff(c_1313,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1311])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_54,plain,(
    v1_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_1330,plain,(
    ! [B_200,A_201] :
      ( v3_pre_topc(B_200,A_201)
      | ~ m1_subset_1(B_200,k1_zfmisc_1(u1_struct_0(A_201)))
      | ~ v1_tdlat_3(A_201)
      | ~ l1_pre_topc(A_201)
      | ~ v2_pre_topc(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1340,plain,(
    ! [B_200] :
      ( v3_pre_topc(B_200,'#skF_2')
      | ~ m1_subset_1(B_200,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v1_tdlat_3('#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_1330])).

tff(c_1350,plain,(
    ! [B_202] :
      ( v3_pre_topc(B_202,'#skF_2')
      | ~ m1_subset_1(B_202,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_54,c_1340])).

tff(c_1365,plain,(
    ! [A_203] :
      ( v3_pre_topc(A_203,'#skF_2')
      | ~ r1_tarski(A_203,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_14,c_1350])).

tff(c_1381,plain,(
    ! [B_2] : v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_2'),B_2),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_1365])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_1203,plain,(
    ! [A_182,B_183,C_184] :
      ( k7_subset_1(A_182,B_183,C_184) = k4_xboole_0(B_183,C_184)
      | ~ m1_subset_1(B_183,k1_zfmisc_1(A_182)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1212,plain,(
    ! [A_4,C_184] : k7_subset_1(A_4,A_4,C_184) = k4_xboole_0(A_4,C_184) ),
    inference(resolution,[status(thm)],[c_68,c_1203])).

tff(c_1726,plain,(
    ! [B_242,A_243] :
      ( v4_pre_topc(B_242,A_243)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_243),k2_struct_0(A_243),B_242),A_243)
      | ~ m1_subset_1(B_242,k1_zfmisc_1(u1_struct_0(A_243)))
      | ~ l1_pre_topc(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1729,plain,(
    ! [B_242] :
      ( v4_pre_topc(B_242,'#skF_2')
      | ~ v3_pre_topc(k7_subset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),B_242),'#skF_2')
      | ~ m1_subset_1(B_242,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_1726])).

tff(c_1732,plain,(
    ! [B_244] :
      ( v4_pre_topc(B_244,'#skF_2')
      | ~ m1_subset_1(B_244,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_92,c_1381,c_1212,c_1729])).

tff(c_1739,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_93,c_1732])).

tff(c_1748,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1313,c_1739])).

tff(c_1749,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1311])).

tff(c_2346,plain,(
    ! [A_301,B_302] :
      ( k2_pre_topc(A_301,B_302) = u1_struct_0(A_301)
      | ~ v1_tops_1(B_302,A_301)
      | ~ m1_subset_1(B_302,k1_zfmisc_1(u1_struct_0(A_301)))
      | ~ l1_pre_topc(A_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2356,plain,(
    ! [B_302] :
      ( k2_pre_topc('#skF_2',B_302) = u1_struct_0('#skF_2')
      | ~ v1_tops_1(B_302,'#skF_2')
      | ~ m1_subset_1(B_302,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_2346])).

tff(c_2384,plain,(
    ! [B_305] :
      ( k2_pre_topc('#skF_2',B_305) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(B_305,'#skF_2')
      | ~ m1_subset_1(B_305,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_92,c_2356])).

tff(c_2391,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = k2_struct_0('#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_93,c_2384])).

tff(c_2398,plain,
    ( k2_struct_0('#skF_2') = '#skF_3'
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1749,c_2391])).

tff(c_2401,plain,(
    ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2398])).

tff(c_2311,plain,(
    ! [B_298,A_299] :
      ( v3_pre_topc(B_298,A_299)
      | ~ m1_subset_1(B_298,k1_zfmisc_1(u1_struct_0(A_299)))
      | ~ v1_tdlat_3(A_299)
      | ~ l1_pre_topc(A_299)
      | ~ v2_pre_topc(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2321,plain,(
    ! [B_298] :
      ( v3_pre_topc(B_298,'#skF_2')
      | ~ m1_subset_1(B_298,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v1_tdlat_3('#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_2311])).

tff(c_2331,plain,(
    ! [B_300] :
      ( v3_pre_topc(B_300,'#skF_2')
      | ~ m1_subset_1(B_300,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_54,c_2321])).

tff(c_2344,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_93,c_2331])).

tff(c_66,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_98,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_66])).

tff(c_99,plain,(
    ~ v1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_60,plain,
    ( v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_110,plain,
    ( v1_subset_1('#skF_3',k2_struct_0('#skF_2'))
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_60])).

tff(c_111,plain,(
    ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_110])).

tff(c_117,plain,(
    ! [B_53,A_54] :
      ( v1_subset_1(B_53,A_54)
      | B_53 = A_54
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_123,plain,
    ( v1_subset_1('#skF_3',k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_93,c_117])).

tff(c_130,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_123])).

tff(c_138,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_92])).

tff(c_218,plain,(
    ! [A_71,B_72] :
      ( k2_pre_topc(A_71,B_72) = B_72
      | ~ v4_pre_topc(B_72,A_71)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_224,plain,(
    ! [B_72] :
      ( k2_pre_topc('#skF_2',B_72) = B_72
      | ~ v4_pre_topc(B_72,'#skF_2')
      | ~ m1_subset_1(B_72,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_218])).

tff(c_238,plain,(
    ! [B_73] :
      ( k2_pre_topc('#skF_2',B_73) = B_73
      | ~ v4_pre_topc(B_73,'#skF_2')
      | ~ m1_subset_1(B_73,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_224])).

tff(c_248,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_238])).

tff(c_288,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_248])).

tff(c_249,plain,(
    ! [B_74,A_75] :
      ( v3_pre_topc(B_74,A_75)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ v1_tdlat_3(A_75)
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_361,plain,(
    ! [A_88,A_89] :
      ( v3_pre_topc(A_88,A_89)
      | ~ v1_tdlat_3(A_89)
      | ~ l1_pre_topc(A_89)
      | ~ v2_pre_topc(A_89)
      | ~ r1_tarski(A_88,u1_struct_0(A_89)) ) ),
    inference(resolution,[status(thm)],[c_14,c_249])).

tff(c_381,plain,(
    ! [A_90,B_91] :
      ( v3_pre_topc(k4_xboole_0(u1_struct_0(A_90),B_91),A_90)
      | ~ v1_tdlat_3(A_90)
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90) ) ),
    inference(resolution,[status(thm)],[c_2,c_361])).

tff(c_384,plain,(
    ! [B_91] :
      ( v3_pre_topc(k4_xboole_0('#skF_3',B_91),'#skF_2')
      | ~ v1_tdlat_3('#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_381])).

tff(c_386,plain,(
    ! [B_91] : v3_pre_topc(k4_xboole_0('#skF_3',B_91),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_54,c_384])).

tff(c_159,plain,(
    ! [A_58,B_59,C_60] :
      ( k7_subset_1(A_58,B_59,C_60) = k4_xboole_0(B_59,C_60)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_165,plain,(
    ! [A_4,C_60] : k7_subset_1(A_4,A_4,C_60) = k4_xboole_0(A_4,C_60) ),
    inference(resolution,[status(thm)],[c_68,c_159])).

tff(c_590,plain,(
    ! [B_111,A_112] :
      ( v4_pre_topc(B_111,A_112)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_112),k2_struct_0(A_112),B_111),A_112)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_597,plain,(
    ! [B_111] :
      ( v4_pre_topc(B_111,'#skF_2')
      | ~ v3_pre_topc(k7_subset_1('#skF_3',k2_struct_0('#skF_2'),B_111),'#skF_2')
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_590])).

tff(c_608,plain,(
    ! [B_113] :
      ( v4_pre_topc(B_113,'#skF_2')
      | ~ m1_subset_1(B_113,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_138,c_386,c_165,c_130,c_597])).

tff(c_616,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_608])).

tff(c_621,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_288,c_616])).

tff(c_622,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_248])).

tff(c_680,plain,(
    ! [B_121,A_122] :
      ( v1_tops_1(B_121,A_122)
      | k2_pre_topc(A_122,B_121) != u1_struct_0(A_122)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_686,plain,(
    ! [B_121] :
      ( v1_tops_1(B_121,'#skF_2')
      | k2_pre_topc('#skF_2',B_121) != u1_struct_0('#skF_2')
      | ~ m1_subset_1(B_121,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_680])).

tff(c_700,plain,(
    ! [B_123] :
      ( v1_tops_1(B_123,'#skF_2')
      | k2_pre_topc('#skF_2',B_123) != '#skF_3'
      | ~ m1_subset_1(B_123,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_138,c_686])).

tff(c_708,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | k2_pre_topc('#skF_2','#skF_3') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_68,c_700])).

tff(c_712,plain,(
    v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_708])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_754,plain,(
    ! [B_127,A_128] :
      ( v2_tex_2(B_127,A_128)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128)
      | ~ v1_tdlat_3(A_128)
      | ~ v2_pre_topc(A_128)
      | v2_struct_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_760,plain,(
    ! [B_127] :
      ( v2_tex_2(B_127,'#skF_2')
      | ~ m1_subset_1(B_127,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v1_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_754])).

tff(c_771,plain,(
    ! [B_127] :
      ( v2_tex_2(B_127,'#skF_2')
      | ~ m1_subset_1(B_127,k1_zfmisc_1('#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_760])).

tff(c_775,plain,(
    ! [B_129] :
      ( v2_tex_2(B_129,'#skF_2')
      | ~ m1_subset_1(B_129,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_771])).

tff(c_785,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_775])).

tff(c_1121,plain,(
    ! [B_169,A_170] :
      ( v3_tex_2(B_169,A_170)
      | ~ v2_tex_2(B_169,A_170)
      | ~ v1_tops_1(B_169,A_170)
      | ~ m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0(A_170)))
      | ~ l1_pre_topc(A_170)
      | ~ v2_pre_topc(A_170)
      | v2_struct_0(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_1127,plain,(
    ! [B_169] :
      ( v3_tex_2(B_169,'#skF_2')
      | ~ v2_tex_2(B_169,'#skF_2')
      | ~ v1_tops_1(B_169,'#skF_2')
      | ~ m1_subset_1(B_169,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_1121])).

tff(c_1138,plain,(
    ! [B_169] :
      ( v3_tex_2(B_169,'#skF_2')
      | ~ v2_tex_2(B_169,'#skF_2')
      | ~ v1_tops_1(B_169,'#skF_2')
      | ~ m1_subset_1(B_169,k1_zfmisc_1('#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_1127])).

tff(c_1142,plain,(
    ! [B_171] :
      ( v3_tex_2(B_171,'#skF_2')
      | ~ v2_tex_2(B_171,'#skF_2')
      | ~ v1_tops_1(B_171,'#skF_2')
      | ~ m1_subset_1(B_171,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1138])).

tff(c_1150,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_1142])).

tff(c_1154,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_712,c_785,c_1150])).

tff(c_1156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_1154])).

tff(c_1157,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_2838,plain,(
    ! [B_357,A_358] :
      ( v1_tops_1(B_357,A_358)
      | ~ v3_tex_2(B_357,A_358)
      | ~ v3_pre_topc(B_357,A_358)
      | ~ m1_subset_1(B_357,k1_zfmisc_1(u1_struct_0(A_358)))
      | ~ l1_pre_topc(A_358)
      | ~ v2_pre_topc(A_358)
      | v2_struct_0(A_358) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_2848,plain,(
    ! [B_357] :
      ( v1_tops_1(B_357,'#skF_2')
      | ~ v3_tex_2(B_357,'#skF_2')
      | ~ v3_pre_topc(B_357,'#skF_2')
      | ~ m1_subset_1(B_357,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_2838])).

tff(c_2856,plain,(
    ! [B_357] :
      ( v1_tops_1(B_357,'#skF_2')
      | ~ v3_tex_2(B_357,'#skF_2')
      | ~ v3_pre_topc(B_357,'#skF_2')
      | ~ m1_subset_1(B_357,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_2848])).

tff(c_2859,plain,(
    ! [B_359] :
      ( v1_tops_1(B_359,'#skF_2')
      | ~ v3_tex_2(B_359,'#skF_2')
      | ~ v3_pre_topc(B_359,'#skF_2')
      | ~ m1_subset_1(B_359,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2856])).

tff(c_2866,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_93,c_2859])).

tff(c_2874,plain,(
    v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2344,c_1157,c_2866])).

tff(c_2876,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2401,c_2874])).

tff(c_2877,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2398])).

tff(c_1158,plain,(
    v1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_2890,plain,(
    v1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2877,c_1158])).

tff(c_2899,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_2890])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:15:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.32/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.49/1.78  
% 4.49/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.49/1.78  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 4.49/1.78  
% 4.49/1.78  %Foreground sorts:
% 4.49/1.78  
% 4.49/1.78  
% 4.49/1.78  %Background operators:
% 4.49/1.78  
% 4.49/1.78  
% 4.49/1.78  %Foreground operators:
% 4.49/1.78  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.49/1.78  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.49/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.49/1.78  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.49/1.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.49/1.78  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.49/1.78  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.49/1.78  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 4.49/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.49/1.78  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 4.49/1.78  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.49/1.78  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.49/1.78  tff('#skF_2', type, '#skF_2': $i).
% 4.49/1.78  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.49/1.78  tff('#skF_3', type, '#skF_3': $i).
% 4.49/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.49/1.78  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.49/1.78  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.49/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.49/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.49/1.78  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.49/1.78  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.49/1.78  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.49/1.78  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.49/1.78  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.49/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.49/1.78  
% 4.49/1.81  tff(f_29, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.49/1.81  tff(f_38, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 4.49/1.81  tff(f_171, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tex_2)).
% 4.49/1.81  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.49/1.81  tff(f_46, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.49/1.81  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.49/1.81  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.49/1.81  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.49/1.81  tff(f_107, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_tdlat_3)).
% 4.49/1.81  tff(f_31, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.49/1.81  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.49/1.81  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k7_subset_1(u1_struct_0(A), k2_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_pre_topc)).
% 4.49/1.81  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 4.49/1.81  tff(f_96, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 4.49/1.81  tff(f_121, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 4.49/1.81  tff(f_153, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 4.49/1.81  tff(f_137, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_tex_2)).
% 4.49/1.81  tff(c_4, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.49/1.81  tff(c_10, plain, (![A_8]: (~v1_subset_1(k2_subset_1(A_8), A_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.49/1.81  tff(c_67, plain, (![A_8]: (~v1_subset_1(A_8, A_8))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10])).
% 4.49/1.81  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_171])).
% 4.49/1.81  tff(c_22, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.49/1.81  tff(c_82, plain, (![A_45]: (u1_struct_0(A_45)=k2_struct_0(A_45) | ~l1_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.49/1.81  tff(c_88, plain, (![A_47]: (u1_struct_0(A_47)=k2_struct_0(A_47) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_22, c_82])).
% 4.49/1.81  tff(c_92, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_88])).
% 4.49/1.81  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_171])).
% 4.49/1.81  tff(c_93, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_50])).
% 4.49/1.81  tff(c_1278, plain, (![A_196, B_197]: (k2_pre_topc(A_196, B_197)=B_197 | ~v4_pre_topc(B_197, A_196) | ~m1_subset_1(B_197, k1_zfmisc_1(u1_struct_0(A_196))) | ~l1_pre_topc(A_196))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.49/1.81  tff(c_1288, plain, (![B_197]: (k2_pre_topc('#skF_2', B_197)=B_197 | ~v4_pre_topc(B_197, '#skF_2') | ~m1_subset_1(B_197, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_1278])).
% 4.49/1.81  tff(c_1298, plain, (![B_198]: (k2_pre_topc('#skF_2', B_198)=B_198 | ~v4_pre_topc(B_198, '#skF_2') | ~m1_subset_1(B_198, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1288])).
% 4.49/1.81  tff(c_1311, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_93, c_1298])).
% 4.49/1.81  tff(c_1313, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_1311])).
% 4.49/1.81  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.49/1.81  tff(c_14, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.49/1.81  tff(c_56, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_171])).
% 4.49/1.81  tff(c_54, plain, (v1_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_171])).
% 4.49/1.81  tff(c_1330, plain, (![B_200, A_201]: (v3_pre_topc(B_200, A_201) | ~m1_subset_1(B_200, k1_zfmisc_1(u1_struct_0(A_201))) | ~v1_tdlat_3(A_201) | ~l1_pre_topc(A_201) | ~v2_pre_topc(A_201))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.49/1.81  tff(c_1340, plain, (![B_200]: (v3_pre_topc(B_200, '#skF_2') | ~m1_subset_1(B_200, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v1_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_1330])).
% 4.49/1.81  tff(c_1350, plain, (![B_202]: (v3_pre_topc(B_202, '#skF_2') | ~m1_subset_1(B_202, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_54, c_1340])).
% 4.49/1.81  tff(c_1365, plain, (![A_203]: (v3_pre_topc(A_203, '#skF_2') | ~r1_tarski(A_203, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_14, c_1350])).
% 4.49/1.81  tff(c_1381, plain, (![B_2]: (v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_2'), B_2), '#skF_2'))), inference(resolution, [status(thm)], [c_2, c_1365])).
% 4.49/1.81  tff(c_6, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.49/1.81  tff(c_68, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 4.49/1.81  tff(c_1203, plain, (![A_182, B_183, C_184]: (k7_subset_1(A_182, B_183, C_184)=k4_xboole_0(B_183, C_184) | ~m1_subset_1(B_183, k1_zfmisc_1(A_182)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.49/1.81  tff(c_1212, plain, (![A_4, C_184]: (k7_subset_1(A_4, A_4, C_184)=k4_xboole_0(A_4, C_184))), inference(resolution, [status(thm)], [c_68, c_1203])).
% 4.49/1.81  tff(c_1726, plain, (![B_242, A_243]: (v4_pre_topc(B_242, A_243) | ~v3_pre_topc(k7_subset_1(u1_struct_0(A_243), k2_struct_0(A_243), B_242), A_243) | ~m1_subset_1(B_242, k1_zfmisc_1(u1_struct_0(A_243))) | ~l1_pre_topc(A_243))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.49/1.81  tff(c_1729, plain, (![B_242]: (v4_pre_topc(B_242, '#skF_2') | ~v3_pre_topc(k7_subset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), B_242), '#skF_2') | ~m1_subset_1(B_242, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_1726])).
% 4.49/1.81  tff(c_1732, plain, (![B_244]: (v4_pre_topc(B_244, '#skF_2') | ~m1_subset_1(B_244, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_92, c_1381, c_1212, c_1729])).
% 4.49/1.81  tff(c_1739, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_93, c_1732])).
% 4.49/1.81  tff(c_1748, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1313, c_1739])).
% 4.49/1.81  tff(c_1749, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_1311])).
% 4.49/1.81  tff(c_2346, plain, (![A_301, B_302]: (k2_pre_topc(A_301, B_302)=u1_struct_0(A_301) | ~v1_tops_1(B_302, A_301) | ~m1_subset_1(B_302, k1_zfmisc_1(u1_struct_0(A_301))) | ~l1_pre_topc(A_301))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.49/1.81  tff(c_2356, plain, (![B_302]: (k2_pre_topc('#skF_2', B_302)=u1_struct_0('#skF_2') | ~v1_tops_1(B_302, '#skF_2') | ~m1_subset_1(B_302, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_2346])).
% 4.49/1.81  tff(c_2384, plain, (![B_305]: (k2_pre_topc('#skF_2', B_305)=k2_struct_0('#skF_2') | ~v1_tops_1(B_305, '#skF_2') | ~m1_subset_1(B_305, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_92, c_2356])).
% 4.49/1.81  tff(c_2391, plain, (k2_pre_topc('#skF_2', '#skF_3')=k2_struct_0('#skF_2') | ~v1_tops_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_93, c_2384])).
% 4.49/1.81  tff(c_2398, plain, (k2_struct_0('#skF_2')='#skF_3' | ~v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1749, c_2391])).
% 4.49/1.81  tff(c_2401, plain, (~v1_tops_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_2398])).
% 4.49/1.81  tff(c_2311, plain, (![B_298, A_299]: (v3_pre_topc(B_298, A_299) | ~m1_subset_1(B_298, k1_zfmisc_1(u1_struct_0(A_299))) | ~v1_tdlat_3(A_299) | ~l1_pre_topc(A_299) | ~v2_pre_topc(A_299))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.49/1.81  tff(c_2321, plain, (![B_298]: (v3_pre_topc(B_298, '#skF_2') | ~m1_subset_1(B_298, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v1_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_2311])).
% 4.49/1.81  tff(c_2331, plain, (![B_300]: (v3_pre_topc(B_300, '#skF_2') | ~m1_subset_1(B_300, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_54, c_2321])).
% 4.49/1.81  tff(c_2344, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_93, c_2331])).
% 4.49/1.81  tff(c_66, plain, (v3_tex_2('#skF_3', '#skF_2') | ~v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_171])).
% 4.49/1.81  tff(c_98, plain, (v3_tex_2('#skF_3', '#skF_2') | ~v1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_66])).
% 4.49/1.81  tff(c_99, plain, (~v1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_98])).
% 4.49/1.81  tff(c_60, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_171])).
% 4.49/1.81  tff(c_110, plain, (v1_subset_1('#skF_3', k2_struct_0('#skF_2')) | ~v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_60])).
% 4.49/1.81  tff(c_111, plain, (~v3_tex_2('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_99, c_110])).
% 4.49/1.81  tff(c_117, plain, (![B_53, A_54]: (v1_subset_1(B_53, A_54) | B_53=A_54 | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.49/1.81  tff(c_123, plain, (v1_subset_1('#skF_3', k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_93, c_117])).
% 4.49/1.81  tff(c_130, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_99, c_123])).
% 4.49/1.81  tff(c_138, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_130, c_92])).
% 4.49/1.81  tff(c_218, plain, (![A_71, B_72]: (k2_pre_topc(A_71, B_72)=B_72 | ~v4_pre_topc(B_72, A_71) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.49/1.81  tff(c_224, plain, (![B_72]: (k2_pre_topc('#skF_2', B_72)=B_72 | ~v4_pre_topc(B_72, '#skF_2') | ~m1_subset_1(B_72, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_138, c_218])).
% 4.49/1.81  tff(c_238, plain, (![B_73]: (k2_pre_topc('#skF_2', B_73)=B_73 | ~v4_pre_topc(B_73, '#skF_2') | ~m1_subset_1(B_73, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_224])).
% 4.49/1.81  tff(c_248, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_238])).
% 4.49/1.81  tff(c_288, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_248])).
% 4.49/1.81  tff(c_249, plain, (![B_74, A_75]: (v3_pre_topc(B_74, A_75) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_75))) | ~v1_tdlat_3(A_75) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.49/1.81  tff(c_361, plain, (![A_88, A_89]: (v3_pre_topc(A_88, A_89) | ~v1_tdlat_3(A_89) | ~l1_pre_topc(A_89) | ~v2_pre_topc(A_89) | ~r1_tarski(A_88, u1_struct_0(A_89)))), inference(resolution, [status(thm)], [c_14, c_249])).
% 4.49/1.81  tff(c_381, plain, (![A_90, B_91]: (v3_pre_topc(k4_xboole_0(u1_struct_0(A_90), B_91), A_90) | ~v1_tdlat_3(A_90) | ~l1_pre_topc(A_90) | ~v2_pre_topc(A_90))), inference(resolution, [status(thm)], [c_2, c_361])).
% 4.49/1.81  tff(c_384, plain, (![B_91]: (v3_pre_topc(k4_xboole_0('#skF_3', B_91), '#skF_2') | ~v1_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_138, c_381])).
% 4.49/1.81  tff(c_386, plain, (![B_91]: (v3_pre_topc(k4_xboole_0('#skF_3', B_91), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_54, c_384])).
% 4.49/1.81  tff(c_159, plain, (![A_58, B_59, C_60]: (k7_subset_1(A_58, B_59, C_60)=k4_xboole_0(B_59, C_60) | ~m1_subset_1(B_59, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.49/1.81  tff(c_165, plain, (![A_4, C_60]: (k7_subset_1(A_4, A_4, C_60)=k4_xboole_0(A_4, C_60))), inference(resolution, [status(thm)], [c_68, c_159])).
% 4.49/1.81  tff(c_590, plain, (![B_111, A_112]: (v4_pre_topc(B_111, A_112) | ~v3_pre_topc(k7_subset_1(u1_struct_0(A_112), k2_struct_0(A_112), B_111), A_112) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.49/1.81  tff(c_597, plain, (![B_111]: (v4_pre_topc(B_111, '#skF_2') | ~v3_pre_topc(k7_subset_1('#skF_3', k2_struct_0('#skF_2'), B_111), '#skF_2') | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_138, c_590])).
% 4.49/1.81  tff(c_608, plain, (![B_113]: (v4_pre_topc(B_113, '#skF_2') | ~m1_subset_1(B_113, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_138, c_386, c_165, c_130, c_597])).
% 4.49/1.81  tff(c_616, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_608])).
% 4.49/1.81  tff(c_621, plain, $false, inference(negUnitSimplification, [status(thm)], [c_288, c_616])).
% 4.49/1.81  tff(c_622, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_248])).
% 4.49/1.81  tff(c_680, plain, (![B_121, A_122]: (v1_tops_1(B_121, A_122) | k2_pre_topc(A_122, B_121)!=u1_struct_0(A_122) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.49/1.81  tff(c_686, plain, (![B_121]: (v1_tops_1(B_121, '#skF_2') | k2_pre_topc('#skF_2', B_121)!=u1_struct_0('#skF_2') | ~m1_subset_1(B_121, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_138, c_680])).
% 4.49/1.81  tff(c_700, plain, (![B_123]: (v1_tops_1(B_123, '#skF_2') | k2_pre_topc('#skF_2', B_123)!='#skF_3' | ~m1_subset_1(B_123, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_138, c_686])).
% 4.49/1.81  tff(c_708, plain, (v1_tops_1('#skF_3', '#skF_2') | k2_pre_topc('#skF_2', '#skF_3')!='#skF_3'), inference(resolution, [status(thm)], [c_68, c_700])).
% 4.49/1.81  tff(c_712, plain, (v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_622, c_708])).
% 4.49/1.81  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_171])).
% 4.49/1.81  tff(c_754, plain, (![B_127, A_128]: (v2_tex_2(B_127, A_128) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128) | ~v1_tdlat_3(A_128) | ~v2_pre_topc(A_128) | v2_struct_0(A_128))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.49/1.81  tff(c_760, plain, (![B_127]: (v2_tex_2(B_127, '#skF_2') | ~m1_subset_1(B_127, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2') | ~v1_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_138, c_754])).
% 4.49/1.81  tff(c_771, plain, (![B_127]: (v2_tex_2(B_127, '#skF_2') | ~m1_subset_1(B_127, k1_zfmisc_1('#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_760])).
% 4.49/1.81  tff(c_775, plain, (![B_129]: (v2_tex_2(B_129, '#skF_2') | ~m1_subset_1(B_129, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_58, c_771])).
% 4.49/1.81  tff(c_785, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_775])).
% 4.49/1.81  tff(c_1121, plain, (![B_169, A_170]: (v3_tex_2(B_169, A_170) | ~v2_tex_2(B_169, A_170) | ~v1_tops_1(B_169, A_170) | ~m1_subset_1(B_169, k1_zfmisc_1(u1_struct_0(A_170))) | ~l1_pre_topc(A_170) | ~v2_pre_topc(A_170) | v2_struct_0(A_170))), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.49/1.81  tff(c_1127, plain, (![B_169]: (v3_tex_2(B_169, '#skF_2') | ~v2_tex_2(B_169, '#skF_2') | ~v1_tops_1(B_169, '#skF_2') | ~m1_subset_1(B_169, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_138, c_1121])).
% 4.49/1.81  tff(c_1138, plain, (![B_169]: (v3_tex_2(B_169, '#skF_2') | ~v2_tex_2(B_169, '#skF_2') | ~v1_tops_1(B_169, '#skF_2') | ~m1_subset_1(B_169, k1_zfmisc_1('#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_1127])).
% 4.49/1.81  tff(c_1142, plain, (![B_171]: (v3_tex_2(B_171, '#skF_2') | ~v2_tex_2(B_171, '#skF_2') | ~v1_tops_1(B_171, '#skF_2') | ~m1_subset_1(B_171, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_58, c_1138])).
% 4.49/1.81  tff(c_1150, plain, (v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~v1_tops_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_1142])).
% 4.49/1.81  tff(c_1154, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_712, c_785, c_1150])).
% 4.49/1.81  tff(c_1156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111, c_1154])).
% 4.49/1.81  tff(c_1157, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_98])).
% 4.49/1.81  tff(c_2838, plain, (![B_357, A_358]: (v1_tops_1(B_357, A_358) | ~v3_tex_2(B_357, A_358) | ~v3_pre_topc(B_357, A_358) | ~m1_subset_1(B_357, k1_zfmisc_1(u1_struct_0(A_358))) | ~l1_pre_topc(A_358) | ~v2_pre_topc(A_358) | v2_struct_0(A_358))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.49/1.81  tff(c_2848, plain, (![B_357]: (v1_tops_1(B_357, '#skF_2') | ~v3_tex_2(B_357, '#skF_2') | ~v3_pre_topc(B_357, '#skF_2') | ~m1_subset_1(B_357, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_2838])).
% 4.49/1.81  tff(c_2856, plain, (![B_357]: (v1_tops_1(B_357, '#skF_2') | ~v3_tex_2(B_357, '#skF_2') | ~v3_pre_topc(B_357, '#skF_2') | ~m1_subset_1(B_357, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_2848])).
% 4.49/1.81  tff(c_2859, plain, (![B_359]: (v1_tops_1(B_359, '#skF_2') | ~v3_tex_2(B_359, '#skF_2') | ~v3_pre_topc(B_359, '#skF_2') | ~m1_subset_1(B_359, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_2856])).
% 4.49/1.81  tff(c_2866, plain, (v1_tops_1('#skF_3', '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_93, c_2859])).
% 4.49/1.81  tff(c_2874, plain, (v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2344, c_1157, c_2866])).
% 4.49/1.81  tff(c_2876, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2401, c_2874])).
% 4.49/1.81  tff(c_2877, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_2398])).
% 4.49/1.81  tff(c_1158, plain, (v1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_98])).
% 4.49/1.81  tff(c_2890, plain, (v1_subset_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2877, c_1158])).
% 4.49/1.81  tff(c_2899, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_2890])).
% 4.49/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.49/1.81  
% 4.49/1.81  Inference rules
% 4.49/1.81  ----------------------
% 4.49/1.81  #Ref     : 0
% 4.49/1.81  #Sup     : 519
% 4.49/1.81  #Fact    : 0
% 4.49/1.81  #Define  : 0
% 4.49/1.81  #Split   : 11
% 4.49/1.81  #Chain   : 0
% 4.49/1.81  #Close   : 0
% 4.49/1.81  
% 4.49/1.81  Ordering : KBO
% 4.49/1.81  
% 4.49/1.81  Simplification rules
% 4.49/1.81  ----------------------
% 4.49/1.81  #Subsume      : 101
% 4.49/1.81  #Demod        : 531
% 4.49/1.81  #Tautology    : 163
% 4.49/1.81  #SimpNegUnit  : 53
% 4.49/1.81  #BackRed      : 19
% 4.49/1.81  
% 4.49/1.81  #Partial instantiations: 0
% 4.49/1.81  #Strategies tried      : 1
% 4.49/1.81  
% 4.49/1.81  Timing (in seconds)
% 4.49/1.81  ----------------------
% 4.49/1.81  Preprocessing        : 0.35
% 4.49/1.81  Parsing              : 0.18
% 4.49/1.81  CNF conversion       : 0.02
% 4.49/1.81  Main loop            : 0.69
% 4.49/1.81  Inferencing          : 0.27
% 4.49/1.81  Reduction            : 0.22
% 4.49/1.81  Demodulation         : 0.15
% 4.49/1.81  BG Simplification    : 0.03
% 4.49/1.81  Subsumption          : 0.12
% 4.49/1.81  Abstraction          : 0.03
% 4.49/1.81  MUC search           : 0.00
% 4.49/1.81  Cooper               : 0.00
% 4.49/1.81  Total                : 1.09
% 4.49/1.81  Index Insertion      : 0.00
% 4.49/1.81  Index Deletion       : 0.00
% 4.49/1.81  Index Matching       : 0.00
% 4.49/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
