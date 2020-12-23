%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:17 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 272 expanded)
%              Number of leaves         :   27 ( 105 expanded)
%              Depth                    :   11
%              Number of atoms          :  210 (1016 expanded)
%              Number of equality atoms :    9 (  45 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v2_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v3_tex_2(B,A)
            <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_98,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( v2_tex_2(B,A)
          <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_34,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_44,plain,
    ( ~ v1_zfmisc_1('#skF_4')
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_51,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_36,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_132,plain,(
    ! [A_52,B_53] :
      ( '#skF_2'(A_52,B_53) != B_53
      | v3_tex_2(B_53,A_52)
      | ~ v2_tex_2(B_53,A_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_139,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_132])).

tff(c_143,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_139])).

tff(c_144,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_143])).

tff(c_145,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_40,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_38,plain,(
    v2_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_50,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_52,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_50])).

tff(c_301,plain,(
    ! [B_105,A_106] :
      ( v2_tex_2(B_105,A_106)
      | ~ v1_zfmisc_1(B_105)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_106)))
      | v1_xboole_0(B_105)
      | ~ l1_pre_topc(A_106)
      | ~ v2_tdlat_3(A_106)
      | ~ v2_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_308,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_301])).

tff(c_312,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_52,c_308])).

tff(c_314,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_34,c_145,c_312])).

tff(c_316,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_330,plain,(
    ! [B_109,A_110] :
      ( r1_tarski(B_109,'#skF_2'(A_110,B_109))
      | v3_tex_2(B_109,A_110)
      | ~ v2_tex_2(B_109,A_110)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_335,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_330])).

tff(c_339,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_316,c_335])).

tff(c_340,plain,(
    r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_339])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_76,plain,(
    ! [C_37,A_38,B_39] :
      ( r2_hidden(C_37,A_38)
      | ~ r2_hidden(C_37,B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_80,plain,(
    ! [A_40,A_41] :
      ( r2_hidden('#skF_1'(A_40),A_41)
      | ~ m1_subset_1(A_40,k1_zfmisc_1(A_41))
      | v1_xboole_0(A_40) ) ),
    inference(resolution,[status(thm)],[c_4,c_76])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_88,plain,(
    ! [A_42,A_43] :
      ( ~ v1_xboole_0(A_42)
      | ~ m1_subset_1(A_43,k1_zfmisc_1(A_42))
      | v1_xboole_0(A_43) ) ),
    inference(resolution,[status(thm)],[c_80,c_2])).

tff(c_95,plain,(
    ! [B_10,A_9] :
      ( ~ v1_xboole_0(B_10)
      | v1_xboole_0(A_9)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(resolution,[status(thm)],[c_10,c_88])).

tff(c_343,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_340,c_95])).

tff(c_349,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_343])).

tff(c_315,plain,(
    '#skF_2'('#skF_3','#skF_4') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_26,plain,(
    ! [B_24,A_22] :
      ( B_24 = A_22
      | ~ r1_tarski(A_22,B_24)
      | ~ v1_zfmisc_1(B_24)
      | v1_xboole_0(B_24)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_346,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_340,c_26])).

tff(c_352,plain,
    ( ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_315,c_346])).

tff(c_353,plain,(
    ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_349,c_352])).

tff(c_317,plain,(
    ! [A_107,B_108] :
      ( v2_tex_2('#skF_2'(A_107,B_108),A_107)
      | v3_tex_2(B_108,A_107)
      | ~ v2_tex_2(B_108,A_107)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_322,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_317])).

tff(c_326,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_322])).

tff(c_327,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_326])).

tff(c_329,plain,(
    v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_327])).

tff(c_20,plain,(
    ! [A_12,B_18] :
      ( m1_subset_1('#skF_2'(A_12,B_18),k1_zfmisc_1(u1_struct_0(A_12)))
      | v3_tex_2(B_18,A_12)
      | ~ v2_tex_2(B_18,A_12)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_443,plain,(
    ! [B_130,A_131] :
      ( v1_zfmisc_1(B_130)
      | ~ v2_tex_2(B_130,A_131)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_131)))
      | v1_xboole_0(B_130)
      | ~ l1_pre_topc(A_131)
      | ~ v2_tdlat_3(A_131)
      | ~ v2_pre_topc(A_131)
      | v2_struct_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_798,plain,(
    ! [A_223,B_224] :
      ( v1_zfmisc_1('#skF_2'(A_223,B_224))
      | ~ v2_tex_2('#skF_2'(A_223,B_224),A_223)
      | v1_xboole_0('#skF_2'(A_223,B_224))
      | ~ v2_tdlat_3(A_223)
      | ~ v2_pre_topc(A_223)
      | v2_struct_0(A_223)
      | v3_tex_2(B_224,A_223)
      | ~ v2_tex_2(B_224,A_223)
      | ~ m1_subset_1(B_224,k1_zfmisc_1(u1_struct_0(A_223)))
      | ~ l1_pre_topc(A_223) ) ),
    inference(resolution,[status(thm)],[c_20,c_443])).

tff(c_804,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_329,c_798])).

tff(c_809,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_316,c_40,c_38,c_804])).

tff(c_811,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_42,c_349,c_353,c_809])).

tff(c_812,plain,(
    ~ v1_zfmisc_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_813,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_876,plain,(
    ! [B_244,A_245] :
      ( v2_tex_2(B_244,A_245)
      | ~ v3_tex_2(B_244,A_245)
      | ~ m1_subset_1(B_244,k1_zfmisc_1(u1_struct_0(A_245)))
      | ~ l1_pre_topc(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_883,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_876])).

tff(c_887,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_813,c_883])).

tff(c_1058,plain,(
    ! [B_301,A_302] :
      ( v1_zfmisc_1(B_301)
      | ~ v2_tex_2(B_301,A_302)
      | ~ m1_subset_1(B_301,k1_zfmisc_1(u1_struct_0(A_302)))
      | v1_xboole_0(B_301)
      | ~ l1_pre_topc(A_302)
      | ~ v2_tdlat_3(A_302)
      | ~ v2_pre_topc(A_302)
      | v2_struct_0(A_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1065,plain,
    ( v1_zfmisc_1('#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_1058])).

tff(c_1069,plain,
    ( v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_887,c_1065])).

tff(c_1071,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_34,c_812,c_1069])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:25:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.84/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.84/1.68  
% 3.84/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.84/1.68  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.84/1.68  
% 3.84/1.68  %Foreground sorts:
% 3.84/1.68  
% 3.84/1.68  
% 3.84/1.68  %Background operators:
% 3.84/1.68  
% 3.84/1.68  
% 3.84/1.68  %Foreground operators:
% 3.84/1.68  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.84/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.84/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.84/1.68  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.84/1.68  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.84/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.84/1.68  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.84/1.68  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.84/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.84/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.84/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.84/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.84/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.84/1.68  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.84/1.68  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.84/1.68  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.84/1.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.84/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.84/1.68  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 3.84/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.84/1.68  
% 3.97/1.70  tff(f_118, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tex_2)).
% 3.97/1.70  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 3.97/1.70  tff(f_98, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 3.97/1.70  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.97/1.70  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.97/1.70  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.97/1.70  tff(f_79, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 3.97/1.70  tff(c_42, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.97/1.70  tff(c_34, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.97/1.70  tff(c_44, plain, (~v1_zfmisc_1('#skF_4') | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.97/1.70  tff(c_51, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 3.97/1.70  tff(c_36, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.97/1.70  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.97/1.70  tff(c_132, plain, (![A_52, B_53]: ('#skF_2'(A_52, B_53)!=B_53 | v3_tex_2(B_53, A_52) | ~v2_tex_2(B_53, A_52) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.97/1.70  tff(c_139, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_32, c_132])).
% 3.97/1.70  tff(c_143, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_139])).
% 3.97/1.70  tff(c_144, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~v2_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_51, c_143])).
% 3.97/1.70  tff(c_145, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_144])).
% 3.97/1.70  tff(c_40, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.97/1.70  tff(c_38, plain, (v2_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.97/1.70  tff(c_50, plain, (v3_tex_2('#skF_4', '#skF_3') | v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.97/1.70  tff(c_52, plain, (v1_zfmisc_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_51, c_50])).
% 3.97/1.70  tff(c_301, plain, (![B_105, A_106]: (v2_tex_2(B_105, A_106) | ~v1_zfmisc_1(B_105) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_106))) | v1_xboole_0(B_105) | ~l1_pre_topc(A_106) | ~v2_tdlat_3(A_106) | ~v2_pre_topc(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.97/1.70  tff(c_308, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_301])).
% 3.97/1.70  tff(c_312, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_52, c_308])).
% 3.97/1.70  tff(c_314, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_34, c_145, c_312])).
% 3.97/1.70  tff(c_316, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_144])).
% 3.97/1.70  tff(c_330, plain, (![B_109, A_110]: (r1_tarski(B_109, '#skF_2'(A_110, B_109)) | v3_tex_2(B_109, A_110) | ~v2_tex_2(B_109, A_110) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.97/1.70  tff(c_335, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_32, c_330])).
% 3.97/1.70  tff(c_339, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_316, c_335])).
% 3.97/1.70  tff(c_340, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_51, c_339])).
% 3.97/1.70  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.97/1.70  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.97/1.70  tff(c_76, plain, (![C_37, A_38, B_39]: (r2_hidden(C_37, A_38) | ~r2_hidden(C_37, B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.97/1.70  tff(c_80, plain, (![A_40, A_41]: (r2_hidden('#skF_1'(A_40), A_41) | ~m1_subset_1(A_40, k1_zfmisc_1(A_41)) | v1_xboole_0(A_40))), inference(resolution, [status(thm)], [c_4, c_76])).
% 3.97/1.70  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.97/1.70  tff(c_88, plain, (![A_42, A_43]: (~v1_xboole_0(A_42) | ~m1_subset_1(A_43, k1_zfmisc_1(A_42)) | v1_xboole_0(A_43))), inference(resolution, [status(thm)], [c_80, c_2])).
% 3.97/1.70  tff(c_95, plain, (![B_10, A_9]: (~v1_xboole_0(B_10) | v1_xboole_0(A_9) | ~r1_tarski(A_9, B_10))), inference(resolution, [status(thm)], [c_10, c_88])).
% 3.97/1.70  tff(c_343, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_340, c_95])).
% 3.97/1.70  tff(c_349, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_34, c_343])).
% 3.97/1.70  tff(c_315, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4'), inference(splitRight, [status(thm)], [c_144])).
% 3.97/1.70  tff(c_26, plain, (![B_24, A_22]: (B_24=A_22 | ~r1_tarski(A_22, B_24) | ~v1_zfmisc_1(B_24) | v1_xboole_0(B_24) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.97/1.70  tff(c_346, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_340, c_26])).
% 3.97/1.70  tff(c_352, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_34, c_315, c_346])).
% 3.97/1.70  tff(c_353, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_349, c_352])).
% 3.97/1.70  tff(c_317, plain, (![A_107, B_108]: (v2_tex_2('#skF_2'(A_107, B_108), A_107) | v3_tex_2(B_108, A_107) | ~v2_tex_2(B_108, A_107) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.97/1.70  tff(c_322, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_32, c_317])).
% 3.97/1.70  tff(c_326, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_322])).
% 3.97/1.70  tff(c_327, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_51, c_326])).
% 3.97/1.70  tff(c_329, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_316, c_327])).
% 3.97/1.70  tff(c_20, plain, (![A_12, B_18]: (m1_subset_1('#skF_2'(A_12, B_18), k1_zfmisc_1(u1_struct_0(A_12))) | v3_tex_2(B_18, A_12) | ~v2_tex_2(B_18, A_12) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.97/1.70  tff(c_443, plain, (![B_130, A_131]: (v1_zfmisc_1(B_130) | ~v2_tex_2(B_130, A_131) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_131))) | v1_xboole_0(B_130) | ~l1_pre_topc(A_131) | ~v2_tdlat_3(A_131) | ~v2_pre_topc(A_131) | v2_struct_0(A_131))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.97/1.70  tff(c_798, plain, (![A_223, B_224]: (v1_zfmisc_1('#skF_2'(A_223, B_224)) | ~v2_tex_2('#skF_2'(A_223, B_224), A_223) | v1_xboole_0('#skF_2'(A_223, B_224)) | ~v2_tdlat_3(A_223) | ~v2_pre_topc(A_223) | v2_struct_0(A_223) | v3_tex_2(B_224, A_223) | ~v2_tex_2(B_224, A_223) | ~m1_subset_1(B_224, k1_zfmisc_1(u1_struct_0(A_223))) | ~l1_pre_topc(A_223))), inference(resolution, [status(thm)], [c_20, c_443])).
% 3.97/1.70  tff(c_804, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_329, c_798])).
% 3.97/1.70  tff(c_809, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_316, c_40, c_38, c_804])).
% 3.97/1.70  tff(c_811, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_42, c_349, c_353, c_809])).
% 3.97/1.70  tff(c_812, plain, (~v1_zfmisc_1('#skF_4')), inference(splitRight, [status(thm)], [c_44])).
% 3.97/1.70  tff(c_813, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 3.97/1.70  tff(c_876, plain, (![B_244, A_245]: (v2_tex_2(B_244, A_245) | ~v3_tex_2(B_244, A_245) | ~m1_subset_1(B_244, k1_zfmisc_1(u1_struct_0(A_245))) | ~l1_pre_topc(A_245))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.97/1.70  tff(c_883, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_32, c_876])).
% 3.97/1.70  tff(c_887, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_813, c_883])).
% 3.97/1.70  tff(c_1058, plain, (![B_301, A_302]: (v1_zfmisc_1(B_301) | ~v2_tex_2(B_301, A_302) | ~m1_subset_1(B_301, k1_zfmisc_1(u1_struct_0(A_302))) | v1_xboole_0(B_301) | ~l1_pre_topc(A_302) | ~v2_tdlat_3(A_302) | ~v2_pre_topc(A_302) | v2_struct_0(A_302))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.97/1.70  tff(c_1065, plain, (v1_zfmisc_1('#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_1058])).
% 3.97/1.70  tff(c_1069, plain, (v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_887, c_1065])).
% 3.97/1.70  tff(c_1071, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_34, c_812, c_1069])).
% 3.97/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.97/1.70  
% 3.97/1.70  Inference rules
% 3.97/1.70  ----------------------
% 3.97/1.70  #Ref     : 0
% 3.97/1.70  #Sup     : 200
% 3.97/1.70  #Fact    : 0
% 3.97/1.70  #Define  : 0
% 3.97/1.70  #Split   : 10
% 3.97/1.70  #Chain   : 0
% 3.97/1.70  #Close   : 0
% 3.97/1.70  
% 3.97/1.70  Ordering : KBO
% 3.97/1.70  
% 3.97/1.70  Simplification rules
% 3.97/1.70  ----------------------
% 3.97/1.70  #Subsume      : 51
% 3.97/1.70  #Demod        : 120
% 3.97/1.70  #Tautology    : 20
% 3.97/1.70  #SimpNegUnit  : 46
% 3.97/1.70  #BackRed      : 0
% 3.97/1.70  
% 3.97/1.70  #Partial instantiations: 0
% 3.97/1.70  #Strategies tried      : 1
% 3.97/1.70  
% 3.97/1.70  Timing (in seconds)
% 3.97/1.70  ----------------------
% 3.97/1.70  Preprocessing        : 0.30
% 3.97/1.70  Parsing              : 0.16
% 3.97/1.70  CNF conversion       : 0.02
% 3.97/1.70  Main loop            : 0.62
% 3.97/1.70  Inferencing          : 0.22
% 3.97/1.70  Reduction            : 0.16
% 3.97/1.70  Demodulation         : 0.09
% 3.97/1.70  BG Simplification    : 0.02
% 3.97/1.70  Subsumption          : 0.17
% 3.97/1.71  Abstraction          : 0.02
% 3.97/1.71  MUC search           : 0.00
% 3.97/1.71  Cooper               : 0.00
% 3.97/1.71  Total                : 0.96
% 3.97/1.71  Index Insertion      : 0.00
% 3.97/1.71  Index Deletion       : 0.00
% 3.97/1.71  Index Matching       : 0.00
% 3.97/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
