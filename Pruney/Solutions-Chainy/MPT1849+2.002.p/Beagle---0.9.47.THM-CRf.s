%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:56 EST 2020

% Result     : Theorem 12.46s
% Output     : CNFRefutation 12.81s
% Verified   : 
% Statistics : Number of formulae       :  262 (45600 expanded)
%              Number of leaves         :   39 (15561 expanded)
%              Depth                    :   23
%              Number of atoms          :  547 (115277 expanded)
%              Number of equality atoms :  100 (19741 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_163,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_tex_2(B,A)
              & m1_pre_topc(B,A) )
           => g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tex_2)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_142,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v1_subset_1(C,u1_struct_0(A)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

tff(f_121,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_117,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_149,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_128,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( ( v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_pre_topc(A,B)
              <=> k2_struct_0(C) = B ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(c_64,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_60,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_87,plain,(
    ! [B_60,A_61] :
      ( l1_pre_topc(B_60)
      | ~ m1_pre_topc(B_60,A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_93,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_87])).

tff(c_97,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_93])).

tff(c_20,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_71,plain,(
    ! [A_57] :
      ( u1_struct_0(A_57) = k2_struct_0(A_57)
      | ~ l1_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_75,plain,(
    ! [A_14] :
      ( u1_struct_0(A_14) = k2_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(resolution,[status(thm)],[c_20,c_71])).

tff(c_101,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_97,c_75])).

tff(c_16058,plain,(
    ! [B_497,A_498] :
      ( u1_struct_0(B_497) = '#skF_1'(A_498,B_497)
      | v1_tex_2(B_497,A_498)
      | ~ m1_pre_topc(B_497,A_498)
      | ~ l1_pre_topc(A_498) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_62,plain,(
    ~ v1_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_16061,plain,
    ( u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16058,c_62])).

tff(c_16064,plain,(
    k2_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_101,c_16061])).

tff(c_16103,plain,(
    u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16064,c_101])).

tff(c_42,plain,(
    ! [A_37] :
      ( m1_pre_topc(A_37,A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_985,plain,(
    ! [B_116,A_117] :
      ( m1_subset_1(u1_struct_0(B_116),k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ m1_pre_topc(B_116,A_117)
      | ~ l1_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1004,plain,(
    ! [B_116] :
      ( m1_subset_1(u1_struct_0(B_116),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_116,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_985])).

tff(c_1055,plain,(
    ! [B_120] :
      ( m1_subset_1(u1_struct_0(B_120),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_120,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_1004])).

tff(c_1064,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_1055])).

tff(c_1066,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1064])).

tff(c_1078,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_1066])).

tff(c_1082,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_1078])).

tff(c_1084,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_1064])).

tff(c_50,plain,(
    ! [B_47,A_41] :
      ( u1_struct_0(B_47) = '#skF_1'(A_41,B_47)
      | v1_tex_2(B_47,A_41)
      | ~ m1_pre_topc(B_47,A_41)
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_40,plain,(
    ! [B_36,A_34] :
      ( m1_subset_1(u1_struct_0(B_36),k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ m1_pre_topc(B_36,A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_16600,plain,(
    ! [B_523,A_524] :
      ( v1_subset_1(u1_struct_0(B_523),u1_struct_0(A_524))
      | ~ m1_subset_1(u1_struct_0(B_523),k1_zfmisc_1(u1_struct_0(A_524)))
      | ~ v1_tex_2(B_523,A_524)
      | ~ m1_pre_topc(B_523,A_524)
      | ~ l1_pre_topc(A_524) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_16890,plain,(
    ! [B_532,A_533] :
      ( v1_subset_1(u1_struct_0(B_532),u1_struct_0(A_533))
      | ~ v1_tex_2(B_532,A_533)
      | ~ m1_pre_topc(B_532,A_533)
      | ~ l1_pre_topc(A_533) ) ),
    inference(resolution,[status(thm)],[c_40,c_16600])).

tff(c_56,plain,(
    ! [B_52] :
      ( ~ v1_subset_1(B_52,B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1006,plain,(
    ! [A_117] :
      ( ~ v1_subset_1(u1_struct_0(A_117),u1_struct_0(A_117))
      | ~ m1_pre_topc(A_117,A_117)
      | ~ l1_pre_topc(A_117) ) ),
    inference(resolution,[status(thm)],[c_985,c_56])).

tff(c_16920,plain,(
    ! [A_534] :
      ( ~ v1_tex_2(A_534,A_534)
      | ~ m1_pre_topc(A_534,A_534)
      | ~ l1_pre_topc(A_534) ) ),
    inference(resolution,[status(thm)],[c_16890,c_1006])).

tff(c_16926,plain,(
    ! [A_535] :
      ( u1_struct_0(A_535) = '#skF_1'(A_535,A_535)
      | ~ m1_pre_topc(A_535,A_535)
      | ~ l1_pre_topc(A_535) ) ),
    inference(resolution,[status(thm)],[c_50,c_16920])).

tff(c_16941,plain,
    ( u1_struct_0('#skF_3') = '#skF_1'('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1084,c_16926])).

tff(c_16952,plain,(
    '#skF_1'('#skF_2','#skF_3') = '#skF_1'('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_16103,c_16941])).

tff(c_654,plain,(
    ! [B_98,A_99] :
      ( u1_struct_0(B_98) = '#skF_1'(A_99,B_98)
      | v1_tex_2(B_98,A_99)
      | ~ m1_pre_topc(B_98,A_99)
      | ~ l1_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_657,plain,
    ( u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_654,c_62])).

tff(c_660,plain,(
    k2_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_101,c_657])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_76,plain,(
    ! [A_58] :
      ( u1_struct_0(A_58) = k2_struct_0(A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(resolution,[status(thm)],[c_20,c_71])).

tff(c_80,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_76])).

tff(c_311,plain,(
    ! [B_82,A_83] :
      ( m1_subset_1(u1_struct_0(B_82),k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ m1_pre_topc(B_82,A_83)
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_330,plain,(
    ! [B_82] :
      ( m1_subset_1(u1_struct_0(B_82),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_82,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_311])).

tff(c_348,plain,(
    ! [B_85] :
      ( m1_subset_1(u1_struct_0(B_85),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_85,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_330])).

tff(c_354,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_348])).

tff(c_360,plain,(
    m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_354])).

tff(c_54,plain,(
    ! [B_52,A_51] :
      ( v1_subset_1(B_52,A_51)
      | B_52 = A_51
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_385,plain,
    ( v1_subset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_360,c_54])).

tff(c_457,plain,(
    k2_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_385])).

tff(c_168,plain,(
    ! [B_71,A_72] :
      ( r1_tarski(u1_struct_0(B_71),u1_struct_0(A_72))
      | ~ m1_pre_topc(B_71,A_72)
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_182,plain,(
    ! [B_71] :
      ( r1_tarski(u1_struct_0(B_71),k2_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_71,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_168])).

tff(c_232,plain,(
    ! [B_76] :
      ( r1_tarski(u1_struct_0(B_76),k2_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_76,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_182])).

tff(c_237,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_232])).

tff(c_243,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_237])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_247,plain,
    ( k2_struct_0('#skF_2') = k2_struct_0('#skF_3')
    | ~ r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_243,c_2])).

tff(c_287,plain,(
    ~ r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_247])).

tff(c_463,plain,(
    ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_287])).

tff(c_476,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_463])).

tff(c_477,plain,(
    v1_subset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_385])).

tff(c_664,plain,(
    v1_subset_1('#skF_1'('#skF_2','#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_660,c_477])).

tff(c_895,plain,(
    ! [A_112,B_113] :
      ( ~ v1_subset_1('#skF_1'(A_112,B_113),u1_struct_0(A_112))
      | v1_tex_2(B_113,A_112)
      | ~ m1_pre_topc(B_113,A_112)
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_901,plain,(
    ! [B_113] :
      ( ~ v1_subset_1('#skF_1'('#skF_2',B_113),k2_struct_0('#skF_2'))
      | v1_tex_2(B_113,'#skF_2')
      | ~ m1_pre_topc(B_113,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_895])).

tff(c_920,plain,(
    ! [B_115] :
      ( ~ v1_subset_1('#skF_1'('#skF_2',B_115),k2_struct_0('#skF_2'))
      | v1_tex_2(B_115,'#skF_2')
      | ~ m1_pre_topc(B_115,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_901])).

tff(c_923,plain,
    ( v1_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_664,c_920])).

tff(c_926,plain,(
    v1_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_923])).

tff(c_928,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_926])).

tff(c_929,plain,(
    k2_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_938,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_929,c_80])).

tff(c_16097,plain,(
    u1_struct_0('#skF_2') = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16064,c_938])).

tff(c_16992,plain,(
    u1_struct_0('#skF_2') = '#skF_1'('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16952,c_16097])).

tff(c_52,plain,(
    ! [A_41,B_47] :
      ( m1_subset_1('#skF_1'(A_41,B_47),k1_zfmisc_1(u1_struct_0(A_41)))
      | v1_tex_2(B_47,A_41)
      | ~ m1_pre_topc(B_47,A_41)
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_16998,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16952,c_52])).

tff(c_17005,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_16998])).

tff(c_17006,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_17005])).

tff(c_17273,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_3'),k1_zfmisc_1('#skF_1'('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16992,c_17006])).

tff(c_117,plain,(
    ! [A_70] :
      ( m1_subset_1(u1_pre_topc(A_70),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_70))))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( v1_pre_topc(g1_pre_topc(A_12,B_13))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k1_zfmisc_1(A_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_135,plain,(
    ! [A_70] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_70),u1_pre_topc(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(resolution,[status(thm)],[c_117,c_18])).

tff(c_16132,plain,
    ( v1_pre_topc(g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16103,c_135])).

tff(c_16158,plain,(
    v1_pre_topc(g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_16132])).

tff(c_16987,plain,(
    v1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16952,c_16158])).

tff(c_36,plain,(
    ! [B_33,A_31] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_33),u1_pre_topc(B_33)),A_31)
      | ~ m1_pre_topc(B_33,A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_16111,plain,(
    ! [A_31] :
      ( m1_pre_topc(g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_3')),A_31)
      | ~ m1_pre_topc('#skF_3',A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16103,c_36])).

tff(c_17876,plain,(
    ! [A_31] :
      ( m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')),A_31)
      | ~ m1_pre_topc('#skF_3',A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16952,c_16111])).

tff(c_48,plain,(
    ! [A_41,B_47] :
      ( ~ v1_subset_1('#skF_1'(A_41,B_47),u1_struct_0(A_41))
      | v1_tex_2(B_47,A_41)
      | ~ m1_pre_topc(B_47,A_41)
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_17001,plain,
    ( ~ v1_subset_1('#skF_1'('#skF_3','#skF_3'),u1_struct_0('#skF_2'))
    | v1_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16952,c_48])).

tff(c_17008,plain,
    ( ~ v1_subset_1('#skF_1'('#skF_3','#skF_3'),u1_struct_0('#skF_2'))
    | v1_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_17001])).

tff(c_17009,plain,(
    ~ v1_subset_1('#skF_1'('#skF_3','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_17008])).

tff(c_17210,plain,(
    ~ v1_subset_1('#skF_1'('#skF_3','#skF_3'),'#skF_1'('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16992,c_17009])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( l1_pre_topc(g1_pre_topc(A_12,B_13))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k1_zfmisc_1(A_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_134,plain,(
    ! [A_70] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_70),u1_pre_topc(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(resolution,[status(thm)],[c_117,c_16])).

tff(c_16135,plain,
    ( l1_pre_topc(g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16103,c_134])).

tff(c_16160,plain,(
    l1_pre_topc(g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_16135])).

tff(c_16986,plain,(
    l1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16952,c_16160])).

tff(c_16245,plain,(
    u1_struct_0(g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_3'))) = k2_struct_0(g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_16160,c_75])).

tff(c_24076,plain,(
    u1_struct_0(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3'))) = k2_struct_0(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16952,c_16952,c_16245])).

tff(c_129,plain,
    ( m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_117])).

tff(c_137,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_129])).

tff(c_16102,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'('#skF_2','#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16064,c_137])).

tff(c_16979,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'('#skF_3','#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16952,c_16102])).

tff(c_8,plain,(
    ! [A_3] :
      ( g1_pre_topc(u1_struct_0(A_3),u1_pre_topc(A_3)) = A_3
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16250,plain,(
    ! [C_500,A_501,D_502,B_503] :
      ( C_500 = A_501
      | g1_pre_topc(C_500,D_502) != g1_pre_topc(A_501,B_503)
      | ~ m1_subset_1(B_503,k1_zfmisc_1(k1_zfmisc_1(A_501))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_16252,plain,(
    ! [A_3,A_501,B_503] :
      ( u1_struct_0(A_3) = A_501
      | g1_pre_topc(A_501,B_503) != A_3
      | ~ m1_subset_1(B_503,k1_zfmisc_1(k1_zfmisc_1(A_501)))
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_16250])).

tff(c_24348,plain,(
    ! [A_669,B_670] :
      ( u1_struct_0(g1_pre_topc(A_669,B_670)) = A_669
      | ~ m1_subset_1(B_670,k1_zfmisc_1(k1_zfmisc_1(A_669)))
      | ~ v1_pre_topc(g1_pre_topc(A_669,B_670))
      | ~ l1_pre_topc(g1_pre_topc(A_669,B_670)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_16252])).

tff(c_24354,plain,
    ( u1_struct_0(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3'))) = '#skF_1'('#skF_3','#skF_3')
    | ~ v1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_16979,c_24348])).

tff(c_24366,plain,(
    k2_struct_0(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3'))) = '#skF_1'('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16986,c_16987,c_24076,c_24354])).

tff(c_24372,plain,(
    u1_struct_0(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3'))) = '#skF_1'('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24366,c_24076])).

tff(c_16622,plain,(
    ! [B_36,A_34] :
      ( v1_subset_1(u1_struct_0(B_36),u1_struct_0(A_34))
      | ~ v1_tex_2(B_36,A_34)
      | ~ m1_pre_topc(B_36,A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(resolution,[status(thm)],[c_40,c_16600])).

tff(c_17025,plain,(
    ! [B_36] :
      ( v1_subset_1(u1_struct_0(B_36),'#skF_1'('#skF_3','#skF_3'))
      | ~ v1_tex_2(B_36,'#skF_2')
      | ~ m1_pre_topc(B_36,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16992,c_16622])).

tff(c_17077,plain,(
    ! [B_36] :
      ( v1_subset_1(u1_struct_0(B_36),'#skF_1'('#skF_3','#skF_3'))
      | ~ v1_tex_2(B_36,'#skF_2')
      | ~ m1_pre_topc(B_36,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_17025])).

tff(c_24431,plain,
    ( v1_subset_1('#skF_1'('#skF_3','#skF_3'),'#skF_1'('#skF_3','#skF_3'))
    | ~ v1_tex_2(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')),'#skF_2')
    | ~ m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_24372,c_17077])).

tff(c_24570,plain,
    ( ~ v1_tex_2(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')),'#skF_2')
    | ~ m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_17210,c_24431])).

tff(c_25268,plain,(
    ~ m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_24570])).

tff(c_25271,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_17876,c_25268])).

tff(c_25275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_25271])).

tff(c_25277,plain,(
    m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_24570])).

tff(c_16521,plain,(
    ! [A_518,C_519] :
      ( k1_pre_topc(A_518,k2_struct_0(C_519)) = C_519
      | ~ m1_pre_topc(C_519,A_518)
      | ~ v1_pre_topc(C_519)
      | ~ m1_subset_1(k2_struct_0(C_519),k1_zfmisc_1(u1_struct_0(A_518)))
      | ~ l1_pre_topc(A_518) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16527,plain,(
    ! [C_519] :
      ( k1_pre_topc('#skF_2',k2_struct_0(C_519)) = C_519
      | ~ m1_pre_topc(C_519,'#skF_2')
      | ~ v1_pre_topc(C_519)
      | ~ m1_subset_1(k2_struct_0(C_519),k1_zfmisc_1('#skF_1'('#skF_2','#skF_3')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16097,c_16521])).

tff(c_16536,plain,(
    ! [C_519] :
      ( k1_pre_topc('#skF_2',k2_struct_0(C_519)) = C_519
      | ~ m1_pre_topc(C_519,'#skF_2')
      | ~ v1_pre_topc(C_519)
      | ~ m1_subset_1(k2_struct_0(C_519),k1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_16527])).

tff(c_27711,plain,(
    ! [C_716] :
      ( k1_pre_topc('#skF_2',k2_struct_0(C_716)) = C_716
      | ~ m1_pre_topc(C_716,'#skF_2')
      | ~ v1_pre_topc(C_716)
      | ~ m1_subset_1(k2_struct_0(C_716),k1_zfmisc_1('#skF_1'('#skF_3','#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16952,c_16536])).

tff(c_27717,plain,
    ( k1_pre_topc('#skF_2',k2_struct_0(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')))) = g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3'))
    | ~ m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')),'#skF_2')
    | ~ v1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')))
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_3'),k1_zfmisc_1('#skF_1'('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_24366,c_27711])).

tff(c_27728,plain,(
    g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')) = k1_pre_topc('#skF_2','#skF_1'('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17273,c_16987,c_25277,c_24366,c_27717])).

tff(c_27756,plain,(
    v1_pre_topc(k1_pre_topc('#skF_2','#skF_1'('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27728,c_16987])).

tff(c_150,plain,(
    l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_137,c_16])).

tff(c_15558,plain,(
    ! [B_479,A_480] :
      ( m1_pre_topc(B_479,A_480)
      | ~ m1_pre_topc(B_479,g1_pre_topc(u1_struct_0(A_480),u1_pre_topc(A_480)))
      | ~ l1_pre_topc(A_480) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_15567,plain,(
    ! [B_479] :
      ( m1_pre_topc(B_479,'#skF_3')
      | ~ m1_pre_topc(B_479,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_15558])).

tff(c_15577,plain,(
    ! [B_481] :
      ( m1_pre_topc(B_481,'#skF_3')
      | ~ m1_pre_topc(B_481,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_15567])).

tff(c_15581,plain,
    ( m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_42,c_15577])).

tff(c_15584,plain,(
    m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_15581])).

tff(c_16078,plain,(
    m1_pre_topc(g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16064,c_15584])).

tff(c_16978,plain,(
    m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16952,c_16078])).

tff(c_27754,plain,(
    m1_pre_topc(k1_pre_topc('#skF_2','#skF_1'('#skF_3','#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27728,c_16978])).

tff(c_27748,plain,(
    k2_struct_0(k1_pre_topc('#skF_2','#skF_1'('#skF_3','#skF_3'))) = '#skF_1'('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27728,c_24366])).

tff(c_16530,plain,(
    ! [C_519] :
      ( k1_pre_topc('#skF_3',k2_struct_0(C_519)) = C_519
      | ~ m1_pre_topc(C_519,'#skF_3')
      | ~ v1_pre_topc(C_519)
      | ~ m1_subset_1(k2_struct_0(C_519),k1_zfmisc_1('#skF_1'('#skF_2','#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16103,c_16521])).

tff(c_16538,plain,(
    ! [C_519] :
      ( k1_pre_topc('#skF_3',k2_struct_0(C_519)) = C_519
      | ~ m1_pre_topc(C_519,'#skF_3')
      | ~ v1_pre_topc(C_519)
      | ~ m1_subset_1(k2_struct_0(C_519),k1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_16530])).

tff(c_28809,plain,(
    ! [C_722] :
      ( k1_pre_topc('#skF_3',k2_struct_0(C_722)) = C_722
      | ~ m1_pre_topc(C_722,'#skF_3')
      | ~ v1_pre_topc(C_722)
      | ~ m1_subset_1(k2_struct_0(C_722),k1_zfmisc_1('#skF_1'('#skF_3','#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16952,c_16538])).

tff(c_28812,plain,
    ( k1_pre_topc('#skF_3',k2_struct_0(k1_pre_topc('#skF_2','#skF_1'('#skF_3','#skF_3')))) = k1_pre_topc('#skF_2','#skF_1'('#skF_3','#skF_3'))
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_1'('#skF_3','#skF_3')),'#skF_3')
    | ~ v1_pre_topc(k1_pre_topc('#skF_2','#skF_1'('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_3'),k1_zfmisc_1('#skF_1'('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_27748,c_28809])).

tff(c_28826,plain,(
    k1_pre_topc('#skF_2','#skF_1'('#skF_3','#skF_3')) = k1_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17273,c_27756,c_27754,c_27748,c_28812])).

tff(c_58,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_81,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_58])).

tff(c_116,plain,(
    g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_81])).

tff(c_937,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_2')) != g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_929,c_116])).

tff(c_16089,plain,(
    g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_2')) != g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16064,c_16064,c_937])).

tff(c_16980,plain,(
    g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')) != g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16952,c_16952,c_16089])).

tff(c_27752,plain,(
    g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')) != k1_pre_topc('#skF_2','#skF_1'('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27728,c_16980])).

tff(c_30785,plain,(
    g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')) != k1_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28826,c_27752])).

tff(c_132,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_2'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_117])).

tff(c_139,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_132])).

tff(c_167,plain,(
    v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_139,c_18])).

tff(c_934,plain,(
    v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_929,c_167])).

tff(c_16096,plain,(
    v1_pre_topc(g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16064,c_934])).

tff(c_16983,plain,(
    v1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16952,c_16096])).

tff(c_19439,plain,(
    ! [A_607,B_608] :
      ( u1_struct_0(g1_pre_topc(A_607,B_608)) = A_607
      | ~ m1_subset_1(B_608,k1_zfmisc_1(k1_zfmisc_1(A_607)))
      | ~ v1_pre_topc(g1_pre_topc(A_607,B_608))
      | ~ l1_pre_topc(g1_pre_topc(A_607,B_608)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_16252])).

tff(c_19445,plain,
    ( u1_struct_0(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3'))) = '#skF_1'('#skF_3','#skF_3')
    | ~ v1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_16979,c_19439])).

tff(c_19457,plain,(
    u1_struct_0(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3'))) = '#skF_1'('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16986,c_16987,c_19445])).

tff(c_19510,plain,
    ( v1_subset_1('#skF_1'('#skF_3','#skF_3'),'#skF_1'('#skF_3','#skF_3'))
    | ~ v1_tex_2(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')),'#skF_2')
    | ~ m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_19457,c_17077])).

tff(c_19649,plain,
    ( ~ v1_tex_2(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')),'#skF_2')
    | ~ m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_17210,c_19510])).

tff(c_19940,plain,(
    ~ m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_19649])).

tff(c_19943,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_17876,c_19940])).

tff(c_19947,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_19943])).

tff(c_19949,plain,(
    m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_19649])).

tff(c_15735,plain,(
    ! [D_489,B_490,C_491,A_492] :
      ( D_489 = B_490
      | g1_pre_topc(C_491,D_489) != g1_pre_topc(A_492,B_490)
      | ~ m1_subset_1(B_490,k1_zfmisc_1(k1_zfmisc_1(A_492))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_15737,plain,(
    ! [A_3,B_490,A_492] :
      ( u1_pre_topc(A_3) = B_490
      | g1_pre_topc(A_492,B_490) != A_3
      | ~ m1_subset_1(B_490,k1_zfmisc_1(k1_zfmisc_1(A_492)))
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_15735])).

tff(c_19164,plain,(
    ! [A_605,B_606] :
      ( u1_pre_topc(g1_pre_topc(A_605,B_606)) = B_606
      | ~ m1_subset_1(B_606,k1_zfmisc_1(k1_zfmisc_1(A_605)))
      | ~ v1_pre_topc(g1_pre_topc(A_605,B_606))
      | ~ l1_pre_topc(g1_pre_topc(A_605,B_606)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_15737])).

tff(c_19170,plain,
    ( u1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3'))) = u1_pre_topc('#skF_3')
    | ~ v1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_16979,c_19164])).

tff(c_19182,plain,(
    u1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3'))) = u1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16986,c_16987,c_19170])).

tff(c_192,plain,(
    ! [A_73] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_73),u1_pre_topc(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(resolution,[status(thm)],[c_117,c_16])).

tff(c_18580,plain,(
    ! [A_593] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_593),u1_pre_topc(A_593))) = k2_struct_0(g1_pre_topc(u1_struct_0(A_593),u1_pre_topc(A_593)))
      | ~ l1_pre_topc(A_593) ) ),
    inference(resolution,[status(thm)],[c_192,c_75])).

tff(c_18723,plain,(
    ! [A_3] :
      ( k2_struct_0(g1_pre_topc(u1_struct_0(A_3),u1_pre_topc(A_3))) = u1_struct_0(A_3)
      | ~ l1_pre_topc(A_3)
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_18580])).

tff(c_19492,plain,
    ( k2_struct_0(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3'))))) = u1_struct_0(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_19457,c_18723])).

tff(c_19634,plain,(
    k2_struct_0(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3'))) = '#skF_1'('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16986,c_16987,c_16986,c_19457,c_19182,c_19492])).

tff(c_22288,plain,(
    ! [C_649] :
      ( k1_pre_topc('#skF_2',k2_struct_0(C_649)) = C_649
      | ~ m1_pre_topc(C_649,'#skF_2')
      | ~ v1_pre_topc(C_649)
      | ~ m1_subset_1(k2_struct_0(C_649),k1_zfmisc_1('#skF_1'('#skF_3','#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16952,c_16536])).

tff(c_22294,plain,
    ( k1_pre_topc('#skF_2',k2_struct_0(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')))) = g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3'))
    | ~ m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')),'#skF_2')
    | ~ v1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')))
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_3'),k1_zfmisc_1('#skF_1'('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_19634,c_22288])).

tff(c_22305,plain,(
    g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_3')) = k1_pre_topc('#skF_2','#skF_1'('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17273,c_16987,c_19949,c_19634,c_22294])).

tff(c_22332,plain,(
    m1_pre_topc(k1_pre_topc('#skF_2','#skF_1'('#skF_3','#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22305,c_16978])).

tff(c_166,plain,(
    l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_139,c_16])).

tff(c_935,plain,(
    l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_929,c_166])).

tff(c_16095,plain,(
    l1_pre_topc(g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16064,c_935])).

tff(c_16982,plain,(
    l1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16952,c_16095])).

tff(c_17391,plain,(
    ! [A_543] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(A_543),u1_pre_topc(A_543)),A_543)
      | ~ l1_pre_topc(A_543)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_543),u1_pre_topc(A_543))) ) ),
    inference(resolution,[status(thm)],[c_42,c_15558])).

tff(c_17408,plain,
    ( m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_16992,c_17391])).

tff(c_17419,plain,(
    m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16982,c_16992,c_64,c_17408])).

tff(c_16903,plain,(
    ! [A_533] :
      ( v1_subset_1('#skF_1'('#skF_2','#skF_3'),u1_struct_0(A_533))
      | ~ v1_tex_2('#skF_2',A_533)
      | ~ m1_pre_topc('#skF_2',A_533)
      | ~ l1_pre_topc(A_533) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16097,c_16890])).

tff(c_17323,plain,(
    ! [A_542] :
      ( v1_subset_1('#skF_1'('#skF_3','#skF_3'),u1_struct_0(A_542))
      | ~ v1_tex_2('#skF_2',A_542)
      | ~ m1_pre_topc('#skF_2',A_542)
      | ~ l1_pre_topc(A_542) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16952,c_16903])).

tff(c_17333,plain,
    ( v1_subset_1('#skF_1'('#skF_3','#skF_3'),'#skF_1'('#skF_3','#skF_3'))
    | ~ v1_tex_2('#skF_2','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16992,c_17323])).

tff(c_17341,plain,
    ( v1_subset_1('#skF_1'('#skF_3','#skF_3'),'#skF_1'('#skF_3','#skF_3'))
    | ~ v1_tex_2('#skF_2','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_17333])).

tff(c_17342,plain,
    ( ~ v1_tex_2('#skF_2','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_17210,c_17341])).

tff(c_17343,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_17342])).

tff(c_17346,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_17343])).

tff(c_17350,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_17346])).

tff(c_17352,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_17342])).

tff(c_16261,plain,(
    ! [A_504,B_505] :
      ( m1_pre_topc(A_504,g1_pre_topc(u1_struct_0(B_505),u1_pre_topc(B_505)))
      | ~ m1_pre_topc(A_504,B_505)
      | ~ l1_pre_topc(B_505)
      | ~ l1_pre_topc(A_504) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_16274,plain,(
    ! [A_504] :
      ( m1_pre_topc(A_504,g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_2')))
      | ~ m1_pre_topc(A_504,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_504) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16097,c_16261])).

tff(c_16286,plain,(
    ! [A_504] :
      ( m1_pre_topc(A_504,g1_pre_topc('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_2')))
      | ~ m1_pre_topc(A_504,'#skF_2')
      | ~ l1_pre_topc(A_504) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_16274])).

tff(c_18112,plain,(
    ! [A_504] :
      ( m1_pre_topc(A_504,g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')))
      | ~ m1_pre_topc(A_504,'#skF_2')
      | ~ l1_pre_topc(A_504) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16952,c_16286])).

tff(c_187,plain,(
    ! [B_71] :
      ( r1_tarski(u1_struct_0(B_71),k2_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_71,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_182])).

tff(c_932,plain,(
    ! [B_71] :
      ( r1_tarski(u1_struct_0(B_71),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_71,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_929,c_187])).

tff(c_207,plain,(
    ! [A_74] :
      ( r1_tarski(k2_struct_0('#skF_2'),u1_struct_0(A_74))
      | ~ m1_pre_topc('#skF_2',A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_168])).

tff(c_216,plain,(
    ! [A_74] :
      ( u1_struct_0(A_74) = k2_struct_0('#skF_2')
      | ~ r1_tarski(u1_struct_0(A_74),k2_struct_0('#skF_2'))
      | ~ m1_pre_topc('#skF_2',A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(resolution,[status(thm)],[c_207,c_2])).

tff(c_15605,plain,(
    ! [A_483] :
      ( u1_struct_0(A_483) = k2_struct_0('#skF_3')
      | ~ r1_tarski(u1_struct_0(A_483),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc('#skF_2',A_483)
      | ~ l1_pre_topc(A_483) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_929,c_929,c_216])).

tff(c_15618,plain,(
    ! [B_71] :
      ( u1_struct_0(B_71) = k2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',B_71)
      | ~ l1_pre_topc(B_71)
      | ~ m1_pre_topc(B_71,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_932,c_15605])).

tff(c_16623,plain,(
    ! [B_71] :
      ( u1_struct_0(B_71) = '#skF_1'('#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_2',B_71)
      | ~ l1_pre_topc(B_71)
      | ~ m1_pre_topc(B_71,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16064,c_15618])).

tff(c_18145,plain,(
    ! [B_587] :
      ( u1_struct_0(B_587) = '#skF_1'('#skF_3','#skF_3')
      | ~ m1_pre_topc('#skF_2',B_587)
      | ~ l1_pre_topc(B_587)
      | ~ m1_pre_topc(B_587,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16952,c_16623])).

tff(c_18148,plain,
    ( u1_struct_0(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2'))) = '#skF_1'('#skF_3','#skF_3')
    | ~ l1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')))
    | ~ m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')),'#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_18112,c_18145])).

tff(c_18162,plain,(
    u1_struct_0(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2'))) = '#skF_1'('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_17352,c_17419,c_16982,c_18148])).

tff(c_18720,plain,
    ( u1_struct_0(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2'))) = k2_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16992,c_18580])).

tff(c_18731,plain,(
    k2_struct_0(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2'))) = '#skF_1'('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_16992,c_18162,c_18720])).

tff(c_22297,plain,
    ( k1_pre_topc('#skF_2',k2_struct_0(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')))) = g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2'))
    | ~ m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')),'#skF_2')
    | ~ v1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')))
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_3'),k1_zfmisc_1('#skF_1'('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_18731,c_22288])).

tff(c_22307,plain,(
    g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')) = k1_pre_topc('#skF_2','#skF_1'('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17273,c_16983,c_17419,c_18731,c_22297])).

tff(c_16912,plain,(
    ! [B_532] :
      ( v1_subset_1(u1_struct_0(B_532),'#skF_1'('#skF_2','#skF_3'))
      | ~ v1_tex_2(B_532,'#skF_3')
      | ~ m1_pre_topc(B_532,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16103,c_16890])).

tff(c_16919,plain,(
    ! [B_532] :
      ( v1_subset_1(u1_struct_0(B_532),'#skF_1'('#skF_2','#skF_3'))
      | ~ v1_tex_2(B_532,'#skF_3')
      | ~ m1_pre_topc(B_532,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_16912])).

tff(c_17700,plain,(
    ! [B_532] :
      ( v1_subset_1(u1_struct_0(B_532),'#skF_1'('#skF_3','#skF_3'))
      | ~ v1_tex_2(B_532,'#skF_3')
      | ~ m1_pre_topc(B_532,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16952,c_16919])).

tff(c_18189,plain,
    ( v1_subset_1('#skF_1'('#skF_3','#skF_3'),'#skF_1'('#skF_3','#skF_3'))
    | ~ v1_tex_2(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18162,c_17700])).

tff(c_18300,plain,
    ( ~ v1_tex_2(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_17210,c_18189])).

tff(c_18525,plain,(
    ~ m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_18300])).

tff(c_23375,plain,(
    ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_1'('#skF_3','#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22307,c_18525])).

tff(c_23393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22332,c_23375])).

tff(c_23395,plain,(
    m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_18300])).

tff(c_23396,plain,(
    ! [A_655] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_655),u1_pre_topc(A_655))) = k2_struct_0(g1_pre_topc(u1_struct_0(A_655),u1_pre_topc(A_655)))
      | ~ l1_pre_topc(A_655) ) ),
    inference(resolution,[status(thm)],[c_192,c_75])).

tff(c_23536,plain,
    ( u1_struct_0(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2'))) = k2_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16992,c_23396])).

tff(c_23547,plain,(
    k2_struct_0(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2'))) = '#skF_1'('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_16992,c_18162,c_23536])).

tff(c_28818,plain,
    ( k1_pre_topc('#skF_3',k2_struct_0(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')))) = g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2'))
    | ~ m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v1_pre_topc(g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')))
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_3'),k1_zfmisc_1('#skF_1'('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_23547,c_28809])).

tff(c_28828,plain,(
    g1_pre_topc('#skF_1'('#skF_3','#skF_3'),u1_pre_topc('#skF_2')) = k1_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17273,c_16983,c_23395,c_23547,c_28818])).

tff(c_30830,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30785,c_28828])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:34:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.46/5.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.55/5.41  
% 12.55/5.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.55/5.42  %$ v1_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 12.55/5.42  
% 12.55/5.42  %Foreground sorts:
% 12.55/5.42  
% 12.55/5.42  
% 12.55/5.42  %Background operators:
% 12.55/5.42  
% 12.55/5.42  
% 12.55/5.42  %Foreground operators:
% 12.55/5.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 12.55/5.42  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 12.55/5.42  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 12.55/5.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.55/5.42  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 12.55/5.42  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 12.55/5.42  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 12.55/5.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.55/5.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.55/5.42  tff('#skF_2', type, '#skF_2': $i).
% 12.55/5.42  tff('#skF_3', type, '#skF_3': $i).
% 12.55/5.42  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 12.55/5.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.55/5.42  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 12.55/5.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.55/5.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.55/5.42  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 12.55/5.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.55/5.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.55/5.42  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 12.55/5.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.55/5.42  
% 12.79/5.45  tff(f_163, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_tex_2(B, A) & m1_pre_topc(B, A)) => (g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tex_2)).
% 12.79/5.45  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 12.79/5.45  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 12.79/5.45  tff(f_55, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 12.79/5.45  tff(f_142, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 12.79/5.45  tff(f_121, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 12.79/5.45  tff(f_117, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 12.79/5.45  tff(f_149, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 12.79/5.45  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.79/5.45  tff(f_128, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_borsuk_1)).
% 12.79/5.45  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 12.79/5.45  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 12.79/5.45  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 12.79/5.45  tff(f_37, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 12.79/5.45  tff(f_85, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 12.79/5.45  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((v1_pre_topc(C) & m1_pre_topc(C, A)) => ((C = k1_pre_topc(A, B)) <=> (k2_struct_0(C) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_pre_topc)).
% 12.79/5.45  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 12.79/5.45  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 12.79/5.45  tff(c_64, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 12.79/5.45  tff(c_60, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 12.79/5.45  tff(c_87, plain, (![B_60, A_61]: (l1_pre_topc(B_60) | ~m1_pre_topc(B_60, A_61) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_72])).
% 12.79/5.45  tff(c_93, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_87])).
% 12.79/5.45  tff(c_97, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_93])).
% 12.79/5.45  tff(c_20, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.79/5.45  tff(c_71, plain, (![A_57]: (u1_struct_0(A_57)=k2_struct_0(A_57) | ~l1_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.79/5.45  tff(c_75, plain, (![A_14]: (u1_struct_0(A_14)=k2_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(resolution, [status(thm)], [c_20, c_71])).
% 12.79/5.45  tff(c_101, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_97, c_75])).
% 12.79/5.45  tff(c_16058, plain, (![B_497, A_498]: (u1_struct_0(B_497)='#skF_1'(A_498, B_497) | v1_tex_2(B_497, A_498) | ~m1_pre_topc(B_497, A_498) | ~l1_pre_topc(A_498))), inference(cnfTransformation, [status(thm)], [f_142])).
% 12.79/5.45  tff(c_62, plain, (~v1_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 12.79/5.45  tff(c_16061, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16058, c_62])).
% 12.79/5.45  tff(c_16064, plain, (k2_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_101, c_16061])).
% 12.79/5.45  tff(c_16103, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16064, c_101])).
% 12.79/5.45  tff(c_42, plain, (![A_37]: (m1_pre_topc(A_37, A_37) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_121])).
% 12.79/5.45  tff(c_985, plain, (![B_116, A_117]: (m1_subset_1(u1_struct_0(B_116), k1_zfmisc_1(u1_struct_0(A_117))) | ~m1_pre_topc(B_116, A_117) | ~l1_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_117])).
% 12.79/5.45  tff(c_1004, plain, (![B_116]: (m1_subset_1(u1_struct_0(B_116), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_116, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_985])).
% 12.79/5.45  tff(c_1055, plain, (![B_120]: (m1_subset_1(u1_struct_0(B_120), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_120, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_1004])).
% 12.79/5.45  tff(c_1064, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_101, c_1055])).
% 12.79/5.45  tff(c_1066, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_1064])).
% 12.79/5.45  tff(c_1078, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_1066])).
% 12.79/5.45  tff(c_1082, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_97, c_1078])).
% 12.79/5.45  tff(c_1084, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_1064])).
% 12.79/5.45  tff(c_50, plain, (![B_47, A_41]: (u1_struct_0(B_47)='#skF_1'(A_41, B_47) | v1_tex_2(B_47, A_41) | ~m1_pre_topc(B_47, A_41) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_142])).
% 12.79/5.45  tff(c_40, plain, (![B_36, A_34]: (m1_subset_1(u1_struct_0(B_36), k1_zfmisc_1(u1_struct_0(A_34))) | ~m1_pre_topc(B_36, A_34) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_117])).
% 12.79/5.45  tff(c_16600, plain, (![B_523, A_524]: (v1_subset_1(u1_struct_0(B_523), u1_struct_0(A_524)) | ~m1_subset_1(u1_struct_0(B_523), k1_zfmisc_1(u1_struct_0(A_524))) | ~v1_tex_2(B_523, A_524) | ~m1_pre_topc(B_523, A_524) | ~l1_pre_topc(A_524))), inference(cnfTransformation, [status(thm)], [f_142])).
% 12.79/5.45  tff(c_16890, plain, (![B_532, A_533]: (v1_subset_1(u1_struct_0(B_532), u1_struct_0(A_533)) | ~v1_tex_2(B_532, A_533) | ~m1_pre_topc(B_532, A_533) | ~l1_pre_topc(A_533))), inference(resolution, [status(thm)], [c_40, c_16600])).
% 12.79/5.45  tff(c_56, plain, (![B_52]: (~v1_subset_1(B_52, B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(B_52)))), inference(cnfTransformation, [status(thm)], [f_149])).
% 12.79/5.45  tff(c_1006, plain, (![A_117]: (~v1_subset_1(u1_struct_0(A_117), u1_struct_0(A_117)) | ~m1_pre_topc(A_117, A_117) | ~l1_pre_topc(A_117))), inference(resolution, [status(thm)], [c_985, c_56])).
% 12.79/5.45  tff(c_16920, plain, (![A_534]: (~v1_tex_2(A_534, A_534) | ~m1_pre_topc(A_534, A_534) | ~l1_pre_topc(A_534))), inference(resolution, [status(thm)], [c_16890, c_1006])).
% 12.79/5.45  tff(c_16926, plain, (![A_535]: (u1_struct_0(A_535)='#skF_1'(A_535, A_535) | ~m1_pre_topc(A_535, A_535) | ~l1_pre_topc(A_535))), inference(resolution, [status(thm)], [c_50, c_16920])).
% 12.79/5.45  tff(c_16941, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1084, c_16926])).
% 12.79/5.45  tff(c_16952, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_1'('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_16103, c_16941])).
% 12.79/5.45  tff(c_654, plain, (![B_98, A_99]: (u1_struct_0(B_98)='#skF_1'(A_99, B_98) | v1_tex_2(B_98, A_99) | ~m1_pre_topc(B_98, A_99) | ~l1_pre_topc(A_99))), inference(cnfTransformation, [status(thm)], [f_142])).
% 12.79/5.45  tff(c_657, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_654, c_62])).
% 12.79/5.45  tff(c_660, plain, (k2_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_101, c_657])).
% 12.79/5.45  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.79/5.45  tff(c_76, plain, (![A_58]: (u1_struct_0(A_58)=k2_struct_0(A_58) | ~l1_pre_topc(A_58))), inference(resolution, [status(thm)], [c_20, c_71])).
% 12.79/5.45  tff(c_80, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_76])).
% 12.79/5.45  tff(c_311, plain, (![B_82, A_83]: (m1_subset_1(u1_struct_0(B_82), k1_zfmisc_1(u1_struct_0(A_83))) | ~m1_pre_topc(B_82, A_83) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_117])).
% 12.79/5.45  tff(c_330, plain, (![B_82]: (m1_subset_1(u1_struct_0(B_82), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_82, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_80, c_311])).
% 12.79/5.45  tff(c_348, plain, (![B_85]: (m1_subset_1(u1_struct_0(B_85), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_85, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_330])).
% 12.79/5.45  tff(c_354, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_101, c_348])).
% 12.79/5.45  tff(c_360, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_354])).
% 12.79/5.45  tff(c_54, plain, (![B_52, A_51]: (v1_subset_1(B_52, A_51) | B_52=A_51 | ~m1_subset_1(B_52, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_149])).
% 12.79/5.45  tff(c_385, plain, (v1_subset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_360, c_54])).
% 12.79/5.45  tff(c_457, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_385])).
% 12.79/5.45  tff(c_168, plain, (![B_71, A_72]: (r1_tarski(u1_struct_0(B_71), u1_struct_0(A_72)) | ~m1_pre_topc(B_71, A_72) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_128])).
% 12.79/5.45  tff(c_182, plain, (![B_71]: (r1_tarski(u1_struct_0(B_71), k2_struct_0('#skF_2')) | ~m1_pre_topc(B_71, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_80, c_168])).
% 12.79/5.45  tff(c_232, plain, (![B_76]: (r1_tarski(u1_struct_0(B_76), k2_struct_0('#skF_2')) | ~m1_pre_topc(B_76, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_182])).
% 12.79/5.45  tff(c_237, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_101, c_232])).
% 12.79/5.45  tff(c_243, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_237])).
% 12.79/5.45  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.79/5.45  tff(c_247, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3') | ~r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_243, c_2])).
% 12.79/5.45  tff(c_287, plain, (~r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_247])).
% 12.79/5.45  tff(c_463, plain, (~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_457, c_287])).
% 12.79/5.45  tff(c_476, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_463])).
% 12.79/5.45  tff(c_477, plain, (v1_subset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_385])).
% 12.79/5.45  tff(c_664, plain, (v1_subset_1('#skF_1'('#skF_2', '#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_660, c_477])).
% 12.79/5.45  tff(c_895, plain, (![A_112, B_113]: (~v1_subset_1('#skF_1'(A_112, B_113), u1_struct_0(A_112)) | v1_tex_2(B_113, A_112) | ~m1_pre_topc(B_113, A_112) | ~l1_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_142])).
% 12.79/5.45  tff(c_901, plain, (![B_113]: (~v1_subset_1('#skF_1'('#skF_2', B_113), k2_struct_0('#skF_2')) | v1_tex_2(B_113, '#skF_2') | ~m1_pre_topc(B_113, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_80, c_895])).
% 12.79/5.45  tff(c_920, plain, (![B_115]: (~v1_subset_1('#skF_1'('#skF_2', B_115), k2_struct_0('#skF_2')) | v1_tex_2(B_115, '#skF_2') | ~m1_pre_topc(B_115, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_901])).
% 12.79/5.45  tff(c_923, plain, (v1_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_664, c_920])).
% 12.79/5.45  tff(c_926, plain, (v1_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_923])).
% 12.79/5.45  tff(c_928, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_926])).
% 12.79/5.45  tff(c_929, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_247])).
% 12.79/5.45  tff(c_938, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_929, c_80])).
% 12.79/5.45  tff(c_16097, plain, (u1_struct_0('#skF_2')='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16064, c_938])).
% 12.79/5.45  tff(c_16992, plain, (u1_struct_0('#skF_2')='#skF_1'('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16952, c_16097])).
% 12.79/5.45  tff(c_52, plain, (![A_41, B_47]: (m1_subset_1('#skF_1'(A_41, B_47), k1_zfmisc_1(u1_struct_0(A_41))) | v1_tex_2(B_47, A_41) | ~m1_pre_topc(B_47, A_41) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_142])).
% 12.79/5.45  tff(c_16998, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16952, c_52])).
% 12.79/5.45  tff(c_17005, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_16998])).
% 12.79/5.45  tff(c_17006, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_62, c_17005])).
% 12.79/5.45  tff(c_17273, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_3'), k1_zfmisc_1('#skF_1'('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_16992, c_17006])).
% 12.79/5.45  tff(c_117, plain, (![A_70]: (m1_subset_1(u1_pre_topc(A_70), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_70)))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.79/5.45  tff(c_18, plain, (![A_12, B_13]: (v1_pre_topc(g1_pre_topc(A_12, B_13)) | ~m1_subset_1(B_13, k1_zfmisc_1(k1_zfmisc_1(A_12))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 12.79/5.45  tff(c_135, plain, (![A_70]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_70), u1_pre_topc(A_70))) | ~l1_pre_topc(A_70))), inference(resolution, [status(thm)], [c_117, c_18])).
% 12.79/5.45  tff(c_16132, plain, (v1_pre_topc(g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16103, c_135])).
% 12.79/5.45  tff(c_16158, plain, (v1_pre_topc(g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_16132])).
% 12.79/5.45  tff(c_16987, plain, (v1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_16952, c_16158])).
% 12.79/5.45  tff(c_36, plain, (![B_33, A_31]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_33), u1_pre_topc(B_33)), A_31) | ~m1_pre_topc(B_33, A_31) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_110])).
% 12.79/5.45  tff(c_16111, plain, (![A_31]: (m1_pre_topc(g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_3')), A_31) | ~m1_pre_topc('#skF_3', A_31) | ~l1_pre_topc(A_31))), inference(superposition, [status(thm), theory('equality')], [c_16103, c_36])).
% 12.79/5.45  tff(c_17876, plain, (![A_31]: (m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')), A_31) | ~m1_pre_topc('#skF_3', A_31) | ~l1_pre_topc(A_31))), inference(demodulation, [status(thm), theory('equality')], [c_16952, c_16111])).
% 12.79/5.45  tff(c_48, plain, (![A_41, B_47]: (~v1_subset_1('#skF_1'(A_41, B_47), u1_struct_0(A_41)) | v1_tex_2(B_47, A_41) | ~m1_pre_topc(B_47, A_41) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_142])).
% 12.79/5.45  tff(c_17001, plain, (~v1_subset_1('#skF_1'('#skF_3', '#skF_3'), u1_struct_0('#skF_2')) | v1_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16952, c_48])).
% 12.79/5.45  tff(c_17008, plain, (~v1_subset_1('#skF_1'('#skF_3', '#skF_3'), u1_struct_0('#skF_2')) | v1_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_17001])).
% 12.79/5.45  tff(c_17009, plain, (~v1_subset_1('#skF_1'('#skF_3', '#skF_3'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_62, c_17008])).
% 12.79/5.45  tff(c_17210, plain, (~v1_subset_1('#skF_1'('#skF_3', '#skF_3'), '#skF_1'('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_16992, c_17009])).
% 12.79/5.45  tff(c_16, plain, (![A_12, B_13]: (l1_pre_topc(g1_pre_topc(A_12, B_13)) | ~m1_subset_1(B_13, k1_zfmisc_1(k1_zfmisc_1(A_12))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 12.79/5.45  tff(c_134, plain, (![A_70]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_70), u1_pre_topc(A_70))) | ~l1_pre_topc(A_70))), inference(resolution, [status(thm)], [c_117, c_16])).
% 12.79/5.45  tff(c_16135, plain, (l1_pre_topc(g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16103, c_134])).
% 12.79/5.45  tff(c_16160, plain, (l1_pre_topc(g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_16135])).
% 12.79/5.45  tff(c_16986, plain, (l1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_16952, c_16160])).
% 12.79/5.45  tff(c_16245, plain, (u1_struct_0(g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_3')))=k2_struct_0(g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_3')))), inference(resolution, [status(thm)], [c_16160, c_75])).
% 12.79/5.45  tff(c_24076, plain, (u1_struct_0(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')))=k2_struct_0(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_16952, c_16952, c_16245])).
% 12.79/5.45  tff(c_129, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_101, c_117])).
% 12.79/5.45  tff(c_137, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_129])).
% 12.79/5.45  tff(c_16102, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_16064, c_137])).
% 12.79/5.45  tff(c_16979, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_1'('#skF_3', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_16952, c_16102])).
% 12.79/5.45  tff(c_8, plain, (![A_3]: (g1_pre_topc(u1_struct_0(A_3), u1_pre_topc(A_3))=A_3 | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.79/5.45  tff(c_16250, plain, (![C_500, A_501, D_502, B_503]: (C_500=A_501 | g1_pre_topc(C_500, D_502)!=g1_pre_topc(A_501, B_503) | ~m1_subset_1(B_503, k1_zfmisc_1(k1_zfmisc_1(A_501))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.79/5.45  tff(c_16252, plain, (![A_3, A_501, B_503]: (u1_struct_0(A_3)=A_501 | g1_pre_topc(A_501, B_503)!=A_3 | ~m1_subset_1(B_503, k1_zfmisc_1(k1_zfmisc_1(A_501))) | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(superposition, [status(thm), theory('equality')], [c_8, c_16250])).
% 12.79/5.45  tff(c_24348, plain, (![A_669, B_670]: (u1_struct_0(g1_pre_topc(A_669, B_670))=A_669 | ~m1_subset_1(B_670, k1_zfmisc_1(k1_zfmisc_1(A_669))) | ~v1_pre_topc(g1_pre_topc(A_669, B_670)) | ~l1_pre_topc(g1_pre_topc(A_669, B_670)))), inference(reflexivity, [status(thm), theory('equality')], [c_16252])).
% 12.79/5.45  tff(c_24354, plain, (u1_struct_0(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')))='#skF_1'('#skF_3', '#skF_3') | ~v1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')))), inference(resolution, [status(thm)], [c_16979, c_24348])).
% 12.79/5.45  tff(c_24366, plain, (k2_struct_0(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')))='#skF_1'('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16986, c_16987, c_24076, c_24354])).
% 12.79/5.45  tff(c_24372, plain, (u1_struct_0(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')))='#skF_1'('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24366, c_24076])).
% 12.79/5.45  tff(c_16622, plain, (![B_36, A_34]: (v1_subset_1(u1_struct_0(B_36), u1_struct_0(A_34)) | ~v1_tex_2(B_36, A_34) | ~m1_pre_topc(B_36, A_34) | ~l1_pre_topc(A_34))), inference(resolution, [status(thm)], [c_40, c_16600])).
% 12.79/5.45  tff(c_17025, plain, (![B_36]: (v1_subset_1(u1_struct_0(B_36), '#skF_1'('#skF_3', '#skF_3')) | ~v1_tex_2(B_36, '#skF_2') | ~m1_pre_topc(B_36, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_16992, c_16622])).
% 12.79/5.45  tff(c_17077, plain, (![B_36]: (v1_subset_1(u1_struct_0(B_36), '#skF_1'('#skF_3', '#skF_3')) | ~v1_tex_2(B_36, '#skF_2') | ~m1_pre_topc(B_36, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_17025])).
% 12.79/5.45  tff(c_24431, plain, (v1_subset_1('#skF_1'('#skF_3', '#skF_3'), '#skF_1'('#skF_3', '#skF_3')) | ~v1_tex_2(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')), '#skF_2') | ~m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_24372, c_17077])).
% 12.79/5.45  tff(c_24570, plain, (~v1_tex_2(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')), '#skF_2') | ~m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_17210, c_24431])).
% 12.79/5.45  tff(c_25268, plain, (~m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')), '#skF_2')), inference(splitLeft, [status(thm)], [c_24570])).
% 12.79/5.45  tff(c_25271, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_17876, c_25268])).
% 12.79/5.45  tff(c_25275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_25271])).
% 12.79/5.45  tff(c_25277, plain, (m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')), '#skF_2')), inference(splitRight, [status(thm)], [c_24570])).
% 12.79/5.45  tff(c_16521, plain, (![A_518, C_519]: (k1_pre_topc(A_518, k2_struct_0(C_519))=C_519 | ~m1_pre_topc(C_519, A_518) | ~v1_pre_topc(C_519) | ~m1_subset_1(k2_struct_0(C_519), k1_zfmisc_1(u1_struct_0(A_518))) | ~l1_pre_topc(A_518))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.79/5.45  tff(c_16527, plain, (![C_519]: (k1_pre_topc('#skF_2', k2_struct_0(C_519))=C_519 | ~m1_pre_topc(C_519, '#skF_2') | ~v1_pre_topc(C_519) | ~m1_subset_1(k2_struct_0(C_519), k1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_16097, c_16521])).
% 12.79/5.45  tff(c_16536, plain, (![C_519]: (k1_pre_topc('#skF_2', k2_struct_0(C_519))=C_519 | ~m1_pre_topc(C_519, '#skF_2') | ~v1_pre_topc(C_519) | ~m1_subset_1(k2_struct_0(C_519), k1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_16527])).
% 12.79/5.45  tff(c_27711, plain, (![C_716]: (k1_pre_topc('#skF_2', k2_struct_0(C_716))=C_716 | ~m1_pre_topc(C_716, '#skF_2') | ~v1_pre_topc(C_716) | ~m1_subset_1(k2_struct_0(C_716), k1_zfmisc_1('#skF_1'('#skF_3', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_16952, c_16536])).
% 12.79/5.45  tff(c_27717, plain, (k1_pre_topc('#skF_2', k2_struct_0(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3'))))=g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')) | ~m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')), '#skF_2') | ~v1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_3'), k1_zfmisc_1('#skF_1'('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_24366, c_27711])).
% 12.79/5.45  tff(c_27728, plain, (g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3'))=k1_pre_topc('#skF_2', '#skF_1'('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_17273, c_16987, c_25277, c_24366, c_27717])).
% 12.79/5.45  tff(c_27756, plain, (v1_pre_topc(k1_pre_topc('#skF_2', '#skF_1'('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_27728, c_16987])).
% 12.79/5.45  tff(c_150, plain, (l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(resolution, [status(thm)], [c_137, c_16])).
% 12.79/5.45  tff(c_15558, plain, (![B_479, A_480]: (m1_pre_topc(B_479, A_480) | ~m1_pre_topc(B_479, g1_pre_topc(u1_struct_0(A_480), u1_pre_topc(A_480))) | ~l1_pre_topc(A_480))), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.79/5.45  tff(c_15567, plain, (![B_479]: (m1_pre_topc(B_479, '#skF_3') | ~m1_pre_topc(B_479, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_15558])).
% 12.79/5.45  tff(c_15577, plain, (![B_481]: (m1_pre_topc(B_481, '#skF_3') | ~m1_pre_topc(B_481, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_15567])).
% 12.79/5.45  tff(c_15581, plain, (m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_3') | ~l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(resolution, [status(thm)], [c_42, c_15577])).
% 12.79/5.45  tff(c_15584, plain, (m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_150, c_15581])).
% 12.79/5.45  tff(c_16078, plain, (m1_pre_topc(g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16064, c_15584])).
% 12.79/5.45  tff(c_16978, plain, (m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16952, c_16078])).
% 12.79/5.45  tff(c_27754, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_1'('#skF_3', '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_27728, c_16978])).
% 12.79/5.45  tff(c_27748, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_1'('#skF_3', '#skF_3')))='#skF_1'('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_27728, c_24366])).
% 12.79/5.45  tff(c_16530, plain, (![C_519]: (k1_pre_topc('#skF_3', k2_struct_0(C_519))=C_519 | ~m1_pre_topc(C_519, '#skF_3') | ~v1_pre_topc(C_519) | ~m1_subset_1(k2_struct_0(C_519), k1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_16103, c_16521])).
% 12.79/5.45  tff(c_16538, plain, (![C_519]: (k1_pre_topc('#skF_3', k2_struct_0(C_519))=C_519 | ~m1_pre_topc(C_519, '#skF_3') | ~v1_pre_topc(C_519) | ~m1_subset_1(k2_struct_0(C_519), k1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_16530])).
% 12.79/5.45  tff(c_28809, plain, (![C_722]: (k1_pre_topc('#skF_3', k2_struct_0(C_722))=C_722 | ~m1_pre_topc(C_722, '#skF_3') | ~v1_pre_topc(C_722) | ~m1_subset_1(k2_struct_0(C_722), k1_zfmisc_1('#skF_1'('#skF_3', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_16952, c_16538])).
% 12.79/5.45  tff(c_28812, plain, (k1_pre_topc('#skF_3', k2_struct_0(k1_pre_topc('#skF_2', '#skF_1'('#skF_3', '#skF_3'))))=k1_pre_topc('#skF_2', '#skF_1'('#skF_3', '#skF_3')) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_1'('#skF_3', '#skF_3')), '#skF_3') | ~v1_pre_topc(k1_pre_topc('#skF_2', '#skF_1'('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_3'), k1_zfmisc_1('#skF_1'('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_27748, c_28809])).
% 12.79/5.45  tff(c_28826, plain, (k1_pre_topc('#skF_2', '#skF_1'('#skF_3', '#skF_3'))=k1_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_17273, c_27756, c_27754, c_27748, c_28812])).
% 12.79/5.45  tff(c_58, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 12.79/5.45  tff(c_81, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_58])).
% 12.79/5.45  tff(c_116, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_81])).
% 12.79/5.45  tff(c_937, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_2'))!=g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_929, c_116])).
% 12.79/5.45  tff(c_16089, plain, (g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_2'))!=g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_16064, c_16064, c_937])).
% 12.79/5.45  tff(c_16980, plain, (g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2'))!=g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_16952, c_16952, c_16089])).
% 12.79/5.45  tff(c_27752, plain, (g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2'))!=k1_pre_topc('#skF_2', '#skF_1'('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_27728, c_16980])).
% 12.79/5.45  tff(c_30785, plain, (g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2'))!=k1_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28826, c_27752])).
% 12.79/5.45  tff(c_132, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_80, c_117])).
% 12.79/5.45  tff(c_139, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_132])).
% 12.79/5.45  tff(c_167, plain, (v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_139, c_18])).
% 12.79/5.45  tff(c_934, plain, (v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_929, c_167])).
% 12.79/5.45  tff(c_16096, plain, (v1_pre_topc(g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_16064, c_934])).
% 12.79/5.45  tff(c_16983, plain, (v1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_16952, c_16096])).
% 12.79/5.45  tff(c_19439, plain, (![A_607, B_608]: (u1_struct_0(g1_pre_topc(A_607, B_608))=A_607 | ~m1_subset_1(B_608, k1_zfmisc_1(k1_zfmisc_1(A_607))) | ~v1_pre_topc(g1_pre_topc(A_607, B_608)) | ~l1_pre_topc(g1_pre_topc(A_607, B_608)))), inference(reflexivity, [status(thm), theory('equality')], [c_16252])).
% 12.79/5.45  tff(c_19445, plain, (u1_struct_0(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')))='#skF_1'('#skF_3', '#skF_3') | ~v1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')))), inference(resolution, [status(thm)], [c_16979, c_19439])).
% 12.79/5.45  tff(c_19457, plain, (u1_struct_0(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')))='#skF_1'('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16986, c_16987, c_19445])).
% 12.79/5.45  tff(c_19510, plain, (v1_subset_1('#skF_1'('#skF_3', '#skF_3'), '#skF_1'('#skF_3', '#skF_3')) | ~v1_tex_2(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')), '#skF_2') | ~m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_19457, c_17077])).
% 12.79/5.45  tff(c_19649, plain, (~v1_tex_2(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')), '#skF_2') | ~m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_17210, c_19510])).
% 12.79/5.45  tff(c_19940, plain, (~m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')), '#skF_2')), inference(splitLeft, [status(thm)], [c_19649])).
% 12.79/5.45  tff(c_19943, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_17876, c_19940])).
% 12.79/5.45  tff(c_19947, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_19943])).
% 12.79/5.45  tff(c_19949, plain, (m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')), '#skF_2')), inference(splitRight, [status(thm)], [c_19649])).
% 12.79/5.45  tff(c_15735, plain, (![D_489, B_490, C_491, A_492]: (D_489=B_490 | g1_pre_topc(C_491, D_489)!=g1_pre_topc(A_492, B_490) | ~m1_subset_1(B_490, k1_zfmisc_1(k1_zfmisc_1(A_492))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.79/5.45  tff(c_15737, plain, (![A_3, B_490, A_492]: (u1_pre_topc(A_3)=B_490 | g1_pre_topc(A_492, B_490)!=A_3 | ~m1_subset_1(B_490, k1_zfmisc_1(k1_zfmisc_1(A_492))) | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(superposition, [status(thm), theory('equality')], [c_8, c_15735])).
% 12.79/5.45  tff(c_19164, plain, (![A_605, B_606]: (u1_pre_topc(g1_pre_topc(A_605, B_606))=B_606 | ~m1_subset_1(B_606, k1_zfmisc_1(k1_zfmisc_1(A_605))) | ~v1_pre_topc(g1_pre_topc(A_605, B_606)) | ~l1_pre_topc(g1_pre_topc(A_605, B_606)))), inference(reflexivity, [status(thm), theory('equality')], [c_15737])).
% 12.79/5.45  tff(c_19170, plain, (u1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')))=u1_pre_topc('#skF_3') | ~v1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')))), inference(resolution, [status(thm)], [c_16979, c_19164])).
% 12.79/5.45  tff(c_19182, plain, (u1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')))=u1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16986, c_16987, c_19170])).
% 12.79/5.45  tff(c_192, plain, (![A_73]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_73), u1_pre_topc(A_73))) | ~l1_pre_topc(A_73))), inference(resolution, [status(thm)], [c_117, c_16])).
% 12.79/5.45  tff(c_18580, plain, (![A_593]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_593), u1_pre_topc(A_593)))=k2_struct_0(g1_pre_topc(u1_struct_0(A_593), u1_pre_topc(A_593))) | ~l1_pre_topc(A_593))), inference(resolution, [status(thm)], [c_192, c_75])).
% 12.79/5.45  tff(c_18723, plain, (![A_3]: (k2_struct_0(g1_pre_topc(u1_struct_0(A_3), u1_pre_topc(A_3)))=u1_struct_0(A_3) | ~l1_pre_topc(A_3) | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(superposition, [status(thm), theory('equality')], [c_8, c_18580])).
% 12.79/5.45  tff(c_19492, plain, (k2_struct_0(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')))))=u1_struct_0(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3'))) | ~v1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_19457, c_18723])).
% 12.79/5.45  tff(c_19634, plain, (k2_struct_0(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')))='#skF_1'('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16986, c_16987, c_16986, c_19457, c_19182, c_19492])).
% 12.79/5.45  tff(c_22288, plain, (![C_649]: (k1_pre_topc('#skF_2', k2_struct_0(C_649))=C_649 | ~m1_pre_topc(C_649, '#skF_2') | ~v1_pre_topc(C_649) | ~m1_subset_1(k2_struct_0(C_649), k1_zfmisc_1('#skF_1'('#skF_3', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_16952, c_16536])).
% 12.79/5.45  tff(c_22294, plain, (k1_pre_topc('#skF_2', k2_struct_0(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3'))))=g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')) | ~m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3')), '#skF_2') | ~v1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_3'), k1_zfmisc_1('#skF_1'('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_19634, c_22288])).
% 12.79/5.45  tff(c_22305, plain, (g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_3'))=k1_pre_topc('#skF_2', '#skF_1'('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_17273, c_16987, c_19949, c_19634, c_22294])).
% 12.79/5.45  tff(c_22332, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_1'('#skF_3', '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22305, c_16978])).
% 12.79/5.45  tff(c_166, plain, (l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_139, c_16])).
% 12.79/5.45  tff(c_935, plain, (l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_929, c_166])).
% 12.79/5.45  tff(c_16095, plain, (l1_pre_topc(g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_16064, c_935])).
% 12.79/5.45  tff(c_16982, plain, (l1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_16952, c_16095])).
% 12.79/5.45  tff(c_17391, plain, (![A_543]: (m1_pre_topc(g1_pre_topc(u1_struct_0(A_543), u1_pre_topc(A_543)), A_543) | ~l1_pre_topc(A_543) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_543), u1_pre_topc(A_543))))), inference(resolution, [status(thm)], [c_42, c_15558])).
% 12.79/5.45  tff(c_17408, plain, (m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')), '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_16992, c_17391])).
% 12.79/5.45  tff(c_17419, plain, (m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16982, c_16992, c_64, c_17408])).
% 12.79/5.45  tff(c_16903, plain, (![A_533]: (v1_subset_1('#skF_1'('#skF_2', '#skF_3'), u1_struct_0(A_533)) | ~v1_tex_2('#skF_2', A_533) | ~m1_pre_topc('#skF_2', A_533) | ~l1_pre_topc(A_533))), inference(superposition, [status(thm), theory('equality')], [c_16097, c_16890])).
% 12.79/5.45  tff(c_17323, plain, (![A_542]: (v1_subset_1('#skF_1'('#skF_3', '#skF_3'), u1_struct_0(A_542)) | ~v1_tex_2('#skF_2', A_542) | ~m1_pre_topc('#skF_2', A_542) | ~l1_pre_topc(A_542))), inference(demodulation, [status(thm), theory('equality')], [c_16952, c_16903])).
% 12.79/5.45  tff(c_17333, plain, (v1_subset_1('#skF_1'('#skF_3', '#skF_3'), '#skF_1'('#skF_3', '#skF_3')) | ~v1_tex_2('#skF_2', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16992, c_17323])).
% 12.79/5.45  tff(c_17341, plain, (v1_subset_1('#skF_1'('#skF_3', '#skF_3'), '#skF_1'('#skF_3', '#skF_3')) | ~v1_tex_2('#skF_2', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_17333])).
% 12.79/5.45  tff(c_17342, plain, (~v1_tex_2('#skF_2', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_17210, c_17341])).
% 12.79/5.45  tff(c_17343, plain, (~m1_pre_topc('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_17342])).
% 12.79/5.45  tff(c_17346, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_17343])).
% 12.79/5.45  tff(c_17350, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_17346])).
% 12.79/5.45  tff(c_17352, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(splitRight, [status(thm)], [c_17342])).
% 12.79/5.45  tff(c_16261, plain, (![A_504, B_505]: (m1_pre_topc(A_504, g1_pre_topc(u1_struct_0(B_505), u1_pre_topc(B_505))) | ~m1_pre_topc(A_504, B_505) | ~l1_pre_topc(B_505) | ~l1_pre_topc(A_504))), inference(cnfTransformation, [status(thm)], [f_101])).
% 12.79/5.45  tff(c_16274, plain, (![A_504]: (m1_pre_topc(A_504, g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_2'))) | ~m1_pre_topc(A_504, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_504))), inference(superposition, [status(thm), theory('equality')], [c_16097, c_16261])).
% 12.79/5.45  tff(c_16286, plain, (![A_504]: (m1_pre_topc(A_504, g1_pre_topc('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_2'))) | ~m1_pre_topc(A_504, '#skF_2') | ~l1_pre_topc(A_504))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_16274])).
% 12.79/5.45  tff(c_18112, plain, (![A_504]: (m1_pre_topc(A_504, g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2'))) | ~m1_pre_topc(A_504, '#skF_2') | ~l1_pre_topc(A_504))), inference(demodulation, [status(thm), theory('equality')], [c_16952, c_16286])).
% 12.79/5.45  tff(c_187, plain, (![B_71]: (r1_tarski(u1_struct_0(B_71), k2_struct_0('#skF_2')) | ~m1_pre_topc(B_71, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_182])).
% 12.79/5.45  tff(c_932, plain, (![B_71]: (r1_tarski(u1_struct_0(B_71), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_71, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_929, c_187])).
% 12.79/5.45  tff(c_207, plain, (![A_74]: (r1_tarski(k2_struct_0('#skF_2'), u1_struct_0(A_74)) | ~m1_pre_topc('#skF_2', A_74) | ~l1_pre_topc(A_74))), inference(superposition, [status(thm), theory('equality')], [c_80, c_168])).
% 12.79/5.45  tff(c_216, plain, (![A_74]: (u1_struct_0(A_74)=k2_struct_0('#skF_2') | ~r1_tarski(u1_struct_0(A_74), k2_struct_0('#skF_2')) | ~m1_pre_topc('#skF_2', A_74) | ~l1_pre_topc(A_74))), inference(resolution, [status(thm)], [c_207, c_2])).
% 12.79/5.45  tff(c_15605, plain, (![A_483]: (u1_struct_0(A_483)=k2_struct_0('#skF_3') | ~r1_tarski(u1_struct_0(A_483), k2_struct_0('#skF_3')) | ~m1_pre_topc('#skF_2', A_483) | ~l1_pre_topc(A_483))), inference(demodulation, [status(thm), theory('equality')], [c_929, c_929, c_216])).
% 12.79/5.45  tff(c_15618, plain, (![B_71]: (u1_struct_0(B_71)=k2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', B_71) | ~l1_pre_topc(B_71) | ~m1_pre_topc(B_71, '#skF_2'))), inference(resolution, [status(thm)], [c_932, c_15605])).
% 12.79/5.45  tff(c_16623, plain, (![B_71]: (u1_struct_0(B_71)='#skF_1'('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', B_71) | ~l1_pre_topc(B_71) | ~m1_pre_topc(B_71, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16064, c_15618])).
% 12.79/5.45  tff(c_18145, plain, (![B_587]: (u1_struct_0(B_587)='#skF_1'('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_2', B_587) | ~l1_pre_topc(B_587) | ~m1_pre_topc(B_587, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16952, c_16623])).
% 12.79/5.45  tff(c_18148, plain, (u1_struct_0(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')))='#skF_1'('#skF_3', '#skF_3') | ~l1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2'))) | ~m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')), '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_18112, c_18145])).
% 12.79/5.45  tff(c_18162, plain, (u1_struct_0(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')))='#skF_1'('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_17352, c_17419, c_16982, c_18148])).
% 12.79/5.45  tff(c_18720, plain, (u1_struct_0(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')))=k2_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16992, c_18580])).
% 12.79/5.45  tff(c_18731, plain, (k2_struct_0(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')))='#skF_1'('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_16992, c_18162, c_18720])).
% 12.79/5.45  tff(c_22297, plain, (k1_pre_topc('#skF_2', k2_struct_0(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2'))))=g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')) | ~m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')), '#skF_2') | ~v1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_3'), k1_zfmisc_1('#skF_1'('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_18731, c_22288])).
% 12.79/5.45  tff(c_22307, plain, (g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2'))=k1_pre_topc('#skF_2', '#skF_1'('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_17273, c_16983, c_17419, c_18731, c_22297])).
% 12.79/5.45  tff(c_16912, plain, (![B_532]: (v1_subset_1(u1_struct_0(B_532), '#skF_1'('#skF_2', '#skF_3')) | ~v1_tex_2(B_532, '#skF_3') | ~m1_pre_topc(B_532, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_16103, c_16890])).
% 12.79/5.45  tff(c_16919, plain, (![B_532]: (v1_subset_1(u1_struct_0(B_532), '#skF_1'('#skF_2', '#skF_3')) | ~v1_tex_2(B_532, '#skF_3') | ~m1_pre_topc(B_532, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_16912])).
% 12.79/5.45  tff(c_17700, plain, (![B_532]: (v1_subset_1(u1_struct_0(B_532), '#skF_1'('#skF_3', '#skF_3')) | ~v1_tex_2(B_532, '#skF_3') | ~m1_pre_topc(B_532, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_16952, c_16919])).
% 12.79/5.45  tff(c_18189, plain, (v1_subset_1('#skF_1'('#skF_3', '#skF_3'), '#skF_1'('#skF_3', '#skF_3')) | ~v1_tex_2(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')), '#skF_3') | ~m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18162, c_17700])).
% 12.79/5.45  tff(c_18300, plain, (~v1_tex_2(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')), '#skF_3') | ~m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_17210, c_18189])).
% 12.79/5.45  tff(c_18525, plain, (~m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')), '#skF_3')), inference(splitLeft, [status(thm)], [c_18300])).
% 12.79/5.45  tff(c_23375, plain, (~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_1'('#skF_3', '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22307, c_18525])).
% 12.79/5.45  tff(c_23393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22332, c_23375])).
% 12.79/5.45  tff(c_23395, plain, (m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_18300])).
% 12.79/5.45  tff(c_23396, plain, (![A_655]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_655), u1_pre_topc(A_655)))=k2_struct_0(g1_pre_topc(u1_struct_0(A_655), u1_pre_topc(A_655))) | ~l1_pre_topc(A_655))), inference(resolution, [status(thm)], [c_192, c_75])).
% 12.79/5.45  tff(c_23536, plain, (u1_struct_0(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')))=k2_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16992, c_23396])).
% 12.79/5.45  tff(c_23547, plain, (k2_struct_0(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')))='#skF_1'('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_16992, c_18162, c_23536])).
% 12.79/5.45  tff(c_28818, plain, (k1_pre_topc('#skF_3', k2_struct_0(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2'))))=g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')) | ~m1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2')), '#skF_3') | ~v1_pre_topc(g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_3'), k1_zfmisc_1('#skF_1'('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_23547, c_28809])).
% 12.81/5.45  tff(c_28828, plain, (g1_pre_topc('#skF_1'('#skF_3', '#skF_3'), u1_pre_topc('#skF_2'))=k1_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_17273, c_16983, c_23395, c_23547, c_28818])).
% 12.81/5.45  tff(c_30830, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30785, c_28828])).
% 12.81/5.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.81/5.45  
% 12.81/5.45  Inference rules
% 12.81/5.45  ----------------------
% 12.81/5.45  #Ref     : 20
% 12.81/5.45  #Sup     : 6534
% 12.81/5.45  #Fact    : 0
% 12.81/5.45  #Define  : 0
% 12.81/5.45  #Split   : 47
% 12.81/5.45  #Chain   : 0
% 12.81/5.45  #Close   : 0
% 12.81/5.45  
% 12.81/5.45  Ordering : KBO
% 12.81/5.45  
% 12.81/5.45  Simplification rules
% 12.81/5.45  ----------------------
% 12.81/5.45  #Subsume      : 995
% 12.81/5.45  #Demod        : 17491
% 12.81/5.45  #Tautology    : 2071
% 12.81/5.45  #SimpNegUnit  : 342
% 12.81/5.45  #BackRed      : 456
% 12.81/5.45  
% 12.81/5.45  #Partial instantiations: 0
% 12.81/5.45  #Strategies tried      : 1
% 12.81/5.45  
% 12.81/5.45  Timing (in seconds)
% 12.81/5.45  ----------------------
% 12.81/5.45  Preprocessing        : 0.34
% 12.81/5.45  Parsing              : 0.18
% 12.81/5.45  CNF conversion       : 0.02
% 12.81/5.46  Main loop            : 4.30
% 12.81/5.46  Inferencing          : 0.97
% 12.81/5.46  Reduction            : 2.05
% 12.81/5.46  Demodulation         : 1.61
% 12.81/5.46  BG Simplification    : 0.12
% 12.81/5.46  Subsumption          : 0.88
% 12.81/5.46  Abstraction          : 0.19
% 12.81/5.46  MUC search           : 0.00
% 12.81/5.46  Cooper               : 0.00
% 12.81/5.46  Total                : 4.73
% 12.81/5.46  Index Insertion      : 0.00
% 12.81/5.46  Index Deletion       : 0.00
% 12.81/5.46  Index Matching       : 0.00
% 12.81/5.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
