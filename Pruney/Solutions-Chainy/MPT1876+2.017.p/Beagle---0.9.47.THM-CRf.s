%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:52 EST 2020

% Result     : Theorem 10.10s
% Output     : CNFRefutation 10.34s
% Verified   : 
% Statistics : Number of formulae       :  174 (1122 expanded)
%              Number of leaves         :   46 ( 401 expanded)
%              Depth                    :   23
%              Number of atoms          :  440 (3289 expanded)
%              Number of equality atoms :   19 (  99 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_207,negated_conjecture,(
    ~ ! [A] :
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_146,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_187,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_175,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ ( v2_tex_2(B,A)
              & ! [C] :
                  ( ( ~ v2_struct_0(C)
                    & v1_pre_topc(C)
                    & v1_tdlat_3(C)
                    & m1_pre_topc(C,A) )
                 => B != u1_struct_0(C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_133,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_tdlat_3(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_tdlat_3(A)
       => v2_pre_topc(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).

tff(f_119,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & v2_tdlat_3(A) )
       => ( ~ v2_struct_0(A)
          & v7_struct_0(A)
          & v2_pre_topc(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(c_68,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_72,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_76,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_93,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_82,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_94,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_82])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_162,plain,(
    ! [A_77,B_78] :
      ( ~ r2_hidden('#skF_2'(A_77,B_78),B_78)
      | r1_tarski(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_168,plain,(
    ! [A_79] : r1_tarski(A_79,A_79) ),
    inference(resolution,[status(thm)],[c_10,c_162])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | ~ r1_tarski(k1_tarski(A_13),B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_174,plain,(
    ! [A_80] : r2_hidden(A_80,k1_tarski(A_80)) ),
    inference(resolution,[status(thm)],[c_168,c_18])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_182,plain,(
    ! [A_80] : ~ v1_xboole_0(k1_tarski(A_80)) ),
    inference(resolution,[status(thm)],[c_174,c_2])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(k1_tarski(A_13),B_14)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8077,plain,(
    ! [B_342,A_343] :
      ( B_342 = A_343
      | ~ r1_tarski(A_343,B_342)
      | ~ v1_zfmisc_1(B_342)
      | v1_xboole_0(B_342)
      | v1_xboole_0(A_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_8092,plain,(
    ! [A_13,B_14] :
      ( k1_tarski(A_13) = B_14
      | ~ v1_zfmisc_1(B_14)
      | v1_xboole_0(B_14)
      | v1_xboole_0(k1_tarski(A_13))
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(resolution,[status(thm)],[c_20,c_8077])).

tff(c_8148,plain,(
    ! [A_346,B_347] :
      ( k1_tarski(A_346) = B_347
      | ~ v1_zfmisc_1(B_347)
      | v1_xboole_0(B_347)
      | ~ r2_hidden(A_346,B_347) ) ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_8092])).

tff(c_8167,plain,(
    ! [A_1] :
      ( k1_tarski('#skF_1'(A_1)) = A_1
      | ~ v1_zfmisc_1(A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_8148])).

tff(c_237,plain,(
    ! [C_91,B_92,A_93] :
      ( r2_hidden(C_91,B_92)
      | ~ r2_hidden(C_91,A_93)
      | ~ r1_tarski(A_93,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_246,plain,(
    ! [A_1,B_92] :
      ( r2_hidden('#skF_1'(A_1),B_92)
      | ~ r1_tarski(A_1,B_92)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_237])).

tff(c_10781,plain,(
    ! [A_468,B_469] :
      ( k1_tarski('#skF_1'(A_468)) = B_469
      | ~ v1_zfmisc_1(B_469)
      | v1_xboole_0(B_469)
      | ~ r1_tarski(A_468,B_469)
      | v1_xboole_0(A_468) ) ),
    inference(resolution,[status(thm)],[c_246,c_8148])).

tff(c_10813,plain,(
    ! [A_13,B_14] :
      ( k1_tarski('#skF_1'(k1_tarski(A_13))) = B_14
      | ~ v1_zfmisc_1(B_14)
      | v1_xboole_0(B_14)
      | v1_xboole_0(k1_tarski(A_13))
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(resolution,[status(thm)],[c_20,c_10781])).

tff(c_10867,plain,(
    ! [A_473,B_474] :
      ( k1_tarski('#skF_1'(k1_tarski(A_473))) = B_474
      | ~ v1_zfmisc_1(B_474)
      | v1_xboole_0(B_474)
      | ~ r2_hidden(A_473,B_474) ) ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_10813])).

tff(c_11078,plain,(
    ! [A_479] :
      ( k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_479)))) = A_479
      | ~ v1_zfmisc_1(A_479)
      | v1_xboole_0(A_479) ) ),
    inference(resolution,[status(thm)],[c_4,c_10867])).

tff(c_173,plain,(
    ! [A_13] : r2_hidden(A_13,k1_tarski(A_13)) ),
    inference(resolution,[status(thm)],[c_168,c_18])).

tff(c_11142,plain,(
    ! [A_479] :
      ( r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_479))),A_479)
      | ~ v1_zfmisc_1(A_479)
      | v1_xboole_0(A_479) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11078,c_173])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_139,plain,(
    ! [A_73,B_74] :
      ( r1_tarski(A_73,B_74)
      | ~ m1_subset_1(A_73,k1_zfmisc_1(B_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_152,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_64,c_139])).

tff(c_167,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_162])).

tff(c_252,plain,(
    ! [A_95,B_96] :
      ( r2_hidden('#skF_1'(A_95),B_96)
      | ~ r1_tarski(A_95,B_96)
      | v1_xboole_0(A_95) ) ),
    inference(resolution,[status(thm)],[c_4,c_237])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10042,plain,(
    ! [A_440,B_441,B_442] :
      ( r2_hidden('#skF_1'(A_440),B_441)
      | ~ r1_tarski(B_442,B_441)
      | ~ r1_tarski(A_440,B_442)
      | v1_xboole_0(A_440) ) ),
    inference(resolution,[status(thm)],[c_252,c_6])).

tff(c_13895,plain,(
    ! [A_560,B_561,A_562] :
      ( r2_hidden('#skF_1'(A_560),B_561)
      | ~ r1_tarski(A_560,k1_tarski(A_562))
      | v1_xboole_0(A_560)
      | ~ r2_hidden(A_562,B_561) ) ),
    inference(resolution,[status(thm)],[c_20,c_10042])).

tff(c_13950,plain,(
    ! [A_562,B_561] :
      ( r2_hidden('#skF_1'(k1_tarski(A_562)),B_561)
      | v1_xboole_0(k1_tarski(A_562))
      | ~ r2_hidden(A_562,B_561) ) ),
    inference(resolution,[status(thm)],[c_167,c_13895])).

tff(c_13977,plain,(
    ! [A_563,B_564] :
      ( r2_hidden('#skF_1'(k1_tarski(A_563)),B_564)
      | ~ r2_hidden(A_563,B_564) ) ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_13950])).

tff(c_14218,plain,(
    ! [A_570,B_571,B_572] :
      ( r2_hidden('#skF_1'(k1_tarski(A_570)),B_571)
      | ~ r1_tarski(B_572,B_571)
      | ~ r2_hidden(A_570,B_572) ) ),
    inference(resolution,[status(thm)],[c_13977,c_6])).

tff(c_14274,plain,(
    ! [A_570] :
      ( r2_hidden('#skF_1'(k1_tarski(A_570)),u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_570,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_152,c_14218])).

tff(c_17881,plain,(
    ! [A_656,B_657] :
      ( r1_tarski(A_656,B_657)
      | ~ r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_656))),B_657)
      | ~ v1_zfmisc_1(A_656)
      | v1_xboole_0(A_656) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11078,c_20])).

tff(c_18469,plain,(
    ! [A_664] :
      ( r1_tarski(A_664,u1_struct_0('#skF_4'))
      | ~ v1_zfmisc_1(A_664)
      | v1_xboole_0(A_664)
      | ~ r2_hidden('#skF_1'(A_664),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_14274,c_17881])).

tff(c_18500,plain,
    ( r1_tarski(k1_tarski('#skF_1'('#skF_5')),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))
    | v1_xboole_0(k1_tarski('#skF_1'('#skF_5')))
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_11142,c_18469])).

tff(c_18529,plain,
    ( r1_tarski(k1_tarski('#skF_1'('#skF_5')),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))
    | v1_xboole_0(k1_tarski('#skF_1'('#skF_5')))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_18500])).

tff(c_18530,plain,
    ( r1_tarski(k1_tarski('#skF_1'('#skF_5')),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_182,c_18529])).

tff(c_18537,plain,(
    ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_18530])).

tff(c_18540,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_8167,c_18537])).

tff(c_18542,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_94,c_18540])).

tff(c_18544,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_18542])).

tff(c_18545,plain,(
    r1_tarski(k1_tarski('#skF_1'('#skF_5')),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_18530])).

tff(c_18662,plain,(
    r2_hidden('#skF_1'('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_18545,c_18])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,B_21)
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18700,plain,(
    m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_18662,c_26])).

tff(c_191,plain,(
    ! [B_85,A_86] :
      ( v1_xboole_0(B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_86))
      | ~ v1_xboole_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_201,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_64,c_191])).

tff(c_206,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_201])).

tff(c_10079,plain,(
    ! [A_443] :
      ( r2_hidden('#skF_1'(A_443),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_443,'#skF_5')
      | v1_xboole_0(A_443) ) ),
    inference(resolution,[status(thm)],[c_152,c_10042])).

tff(c_10104,plain,(
    ! [A_444] :
      ( m1_subset_1('#skF_1'(A_444),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_444,'#skF_5')
      | v1_xboole_0(A_444) ) ),
    inference(resolution,[status(thm)],[c_10079,c_26])).

tff(c_38,plain,(
    ! [A_29,B_30] :
      ( k6_domain_1(A_29,B_30) = k1_tarski(B_30)
      | ~ m1_subset_1(B_30,A_29)
      | v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_10107,plain,(
    ! [A_444] :
      ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'(A_444)) = k1_tarski('#skF_1'(A_444))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_444,'#skF_5')
      | v1_xboole_0(A_444) ) ),
    inference(resolution,[status(thm)],[c_10104,c_38])).

tff(c_17446,plain,(
    ! [A_644] :
      ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'(A_644)) = k1_tarski('#skF_1'(A_644))
      | ~ r1_tarski(A_644,'#skF_5')
      | v1_xboole_0(A_644) ) ),
    inference(negUnitSimplification,[status(thm)],[c_206,c_10107])).

tff(c_62,plain,(
    ! [A_45,B_47] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_45),B_47),A_45)
      | ~ m1_subset_1(B_47,u1_struct_0(A_45))
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_17455,plain,(
    ! [A_644] :
      ( v2_tex_2(k1_tarski('#skF_1'(A_644)),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_644),u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_644,'#skF_5')
      | v1_xboole_0(A_644) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17446,c_62])).

tff(c_17479,plain,(
    ! [A_644] :
      ( v2_tex_2(k1_tarski('#skF_1'(A_644)),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_644),u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_644,'#skF_5')
      | v1_xboole_0(A_644) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_17455])).

tff(c_17480,plain,(
    ! [A_644] :
      ( v2_tex_2(k1_tarski('#skF_1'(A_644)),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_644),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_644,'#skF_5')
      | v1_xboole_0(A_644) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_17479])).

tff(c_30,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(A_22,k1_zfmisc_1(B_23))
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8414,plain,(
    ! [A_379,B_380] :
      ( v1_tdlat_3('#skF_3'(A_379,B_380))
      | ~ v2_tex_2(B_380,A_379)
      | ~ m1_subset_1(B_380,k1_zfmisc_1(u1_struct_0(A_379)))
      | v1_xboole_0(B_380)
      | ~ l1_pre_topc(A_379)
      | ~ v2_pre_topc(A_379)
      | v2_struct_0(A_379) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_8441,plain,(
    ! [A_379,A_22] :
      ( v1_tdlat_3('#skF_3'(A_379,A_22))
      | ~ v2_tex_2(A_22,A_379)
      | v1_xboole_0(A_22)
      | ~ l1_pre_topc(A_379)
      | ~ v2_pre_topc(A_379)
      | v2_struct_0(A_379)
      | ~ r1_tarski(A_22,u1_struct_0(A_379)) ) ),
    inference(resolution,[status(thm)],[c_30,c_8414])).

tff(c_18598,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4',k1_tarski('#skF_1'('#skF_5'))))
    | ~ v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4')
    | v1_xboole_0(k1_tarski('#skF_1'('#skF_5')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_18545,c_8441])).

tff(c_18647,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4',k1_tarski('#skF_1'('#skF_5'))))
    | ~ v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4')
    | v1_xboole_0(k1_tarski('#skF_1'('#skF_5')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_18598])).

tff(c_18648,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4',k1_tarski('#skF_1'('#skF_5'))))
    | ~ v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_182,c_18647])).

tff(c_18702,plain,(
    ~ v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_18648])).

tff(c_18705,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_17480,c_18702])).

tff(c_18714,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_18705])).

tff(c_18715,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_18714])).

tff(c_18727,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18700,c_18715])).

tff(c_18729,plain,(
    v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_18648])).

tff(c_18732,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_8167,c_18729])).

tff(c_18734,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_18732])).

tff(c_18736,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_93,c_18734])).

tff(c_18738,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_18775,plain,(
    ! [A_678,B_679] :
      ( r1_tarski(A_678,B_679)
      | ~ m1_subset_1(A_678,k1_zfmisc_1(B_679)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_18779,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_64,c_18775])).

tff(c_20794,plain,(
    ! [A_816,B_817] :
      ( m1_pre_topc('#skF_3'(A_816,B_817),A_816)
      | ~ v2_tex_2(B_817,A_816)
      | ~ m1_subset_1(B_817,k1_zfmisc_1(u1_struct_0(A_816)))
      | v1_xboole_0(B_817)
      | ~ l1_pre_topc(A_816)
      | ~ v2_pre_topc(A_816)
      | v2_struct_0(A_816) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_21541,plain,(
    ! [A_832,A_833] :
      ( m1_pre_topc('#skF_3'(A_832,A_833),A_832)
      | ~ v2_tex_2(A_833,A_832)
      | v1_xboole_0(A_833)
      | ~ l1_pre_topc(A_832)
      | ~ v2_pre_topc(A_832)
      | v2_struct_0(A_832)
      | ~ r1_tarski(A_833,u1_struct_0(A_832)) ) ),
    inference(resolution,[status(thm)],[c_30,c_20794])).

tff(c_21574,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_18779,c_21541])).

tff(c_21593,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_18738,c_21574])).

tff(c_21594,plain,(
    m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_66,c_21593])).

tff(c_34,plain,(
    ! [B_27,A_25] :
      ( l1_pre_topc(B_27)
      | ~ m1_pre_topc(B_27,A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_21600,plain,
    ( l1_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_21594,c_34])).

tff(c_21607,plain,(
    l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_21600])).

tff(c_32,plain,(
    ! [A_24] :
      ( l1_struct_0(A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_20203,plain,(
    ! [A_796,B_797] :
      ( ~ v2_struct_0('#skF_3'(A_796,B_797))
      | ~ v2_tex_2(B_797,A_796)
      | ~ m1_subset_1(B_797,k1_zfmisc_1(u1_struct_0(A_796)))
      | v1_xboole_0(B_797)
      | ~ l1_pre_topc(A_796)
      | ~ v2_pre_topc(A_796)
      | v2_struct_0(A_796) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_21336,plain,(
    ! [A_828,A_829] :
      ( ~ v2_struct_0('#skF_3'(A_828,A_829))
      | ~ v2_tex_2(A_829,A_828)
      | v1_xboole_0(A_829)
      | ~ l1_pre_topc(A_828)
      | ~ v2_pre_topc(A_828)
      | v2_struct_0(A_828)
      | ~ r1_tarski(A_829,u1_struct_0(A_828)) ) ),
    inference(resolution,[status(thm)],[c_30,c_20203])).

tff(c_21381,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_18779,c_21336])).

tff(c_21400,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_18738,c_21381])).

tff(c_21401,plain,(
    ~ v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_66,c_21400])).

tff(c_70,plain,(
    v2_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_48,plain,(
    ! [B_35,A_33] :
      ( v2_tdlat_3(B_35)
      | ~ m1_pre_topc(B_35,A_33)
      | ~ l1_pre_topc(A_33)
      | ~ v2_tdlat_3(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_21597,plain,
    ( v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_21594,c_48])).

tff(c_21603,plain,
    ( v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_21597])).

tff(c_21604,plain,(
    v2_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_21603])).

tff(c_40,plain,(
    ! [A_31] :
      ( v2_pre_topc(A_31)
      | ~ v2_tdlat_3(A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_21611,plain,
    ( v2_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_21604,c_40])).

tff(c_21613,plain,(
    v2_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21607,c_21611])).

tff(c_19728,plain,(
    ! [A_775,B_776] :
      ( v1_tdlat_3('#skF_3'(A_775,B_776))
      | ~ v2_tex_2(B_776,A_775)
      | ~ m1_subset_1(B_776,k1_zfmisc_1(u1_struct_0(A_775)))
      | v1_xboole_0(B_776)
      | ~ l1_pre_topc(A_775)
      | ~ v2_pre_topc(A_775)
      | v2_struct_0(A_775) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_21063,plain,(
    ! [A_819,A_820] :
      ( v1_tdlat_3('#skF_3'(A_819,A_820))
      | ~ v2_tex_2(A_820,A_819)
      | v1_xboole_0(A_820)
      | ~ l1_pre_topc(A_819)
      | ~ v2_pre_topc(A_819)
      | v2_struct_0(A_819)
      | ~ r1_tarski(A_820,u1_struct_0(A_819)) ) ),
    inference(resolution,[status(thm)],[c_30,c_19728])).

tff(c_21105,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_18779,c_21063])).

tff(c_21124,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_18738,c_21105])).

tff(c_21125,plain,(
    v1_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_66,c_21124])).

tff(c_44,plain,(
    ! [A_32] :
      ( v7_struct_0(A_32)
      | ~ v2_tdlat_3(A_32)
      | ~ v1_tdlat_3(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_18737,plain,(
    ~ v1_zfmisc_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_20490,plain,(
    ! [A_809,B_810] :
      ( u1_struct_0('#skF_3'(A_809,B_810)) = B_810
      | ~ v2_tex_2(B_810,A_809)
      | ~ m1_subset_1(B_810,k1_zfmisc_1(u1_struct_0(A_809)))
      | v1_xboole_0(B_810)
      | ~ l1_pre_topc(A_809)
      | ~ v2_pre_topc(A_809)
      | v2_struct_0(A_809) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_21731,plain,(
    ! [A_836,A_837] :
      ( u1_struct_0('#skF_3'(A_836,A_837)) = A_837
      | ~ v2_tex_2(A_837,A_836)
      | v1_xboole_0(A_837)
      | ~ l1_pre_topc(A_836)
      | ~ v2_pre_topc(A_836)
      | v2_struct_0(A_836)
      | ~ r1_tarski(A_837,u1_struct_0(A_836)) ) ),
    inference(resolution,[status(thm)],[c_30,c_20490])).

tff(c_21776,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_18779,c_21731])).

tff(c_21795,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_18738,c_21776])).

tff(c_21796,plain,(
    u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_66,c_21795])).

tff(c_36,plain,(
    ! [A_28] :
      ( v1_zfmisc_1(u1_struct_0(A_28))
      | ~ l1_struct_0(A_28)
      | ~ v7_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_21837,plain,
    ( v1_zfmisc_1('#skF_5')
    | ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_21796,c_36])).

tff(c_21882,plain,
    ( ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_18737,c_21837])).

tff(c_21888,plain,(
    ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_21882])).

tff(c_21891,plain,
    ( ~ v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_44,c_21888])).

tff(c_21894,plain,(
    v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21607,c_21613,c_21125,c_21604,c_21891])).

tff(c_21896,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21401,c_21894])).

tff(c_21897,plain,(
    ~ l1_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_21882])).

tff(c_21902,plain,(
    ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_32,c_21897])).

tff(c_21906,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21607,c_21902])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:59:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.10/4.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.10/4.18  
% 10.10/4.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.10/4.19  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 10.10/4.19  
% 10.10/4.19  %Foreground sorts:
% 10.10/4.19  
% 10.10/4.19  
% 10.10/4.19  %Background operators:
% 10.10/4.19  
% 10.10/4.19  
% 10.10/4.19  %Foreground operators:
% 10.10/4.19  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.10/4.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.10/4.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.10/4.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.10/4.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.10/4.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.10/4.19  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 10.10/4.19  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.10/4.19  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 10.10/4.19  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.10/4.19  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 10.10/4.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.10/4.19  tff('#skF_5', type, '#skF_5': $i).
% 10.10/4.19  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 10.10/4.19  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 10.10/4.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.10/4.19  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 10.10/4.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.10/4.19  tff('#skF_4', type, '#skF_4': $i).
% 10.10/4.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.10/4.19  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.10/4.19  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 10.10/4.19  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 10.10/4.19  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.10/4.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.10/4.19  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.10/4.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.10/4.19  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 10.10/4.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.10/4.19  
% 10.34/4.21  tff(f_207, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 10.34/4.21  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 10.34/4.21  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 10.34/4.21  tff(f_53, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 10.34/4.21  tff(f_146, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 10.34/4.21  tff(f_71, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.34/4.21  tff(f_67, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 10.34/4.21  tff(f_63, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 10.34/4.21  tff(f_95, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 10.34/4.21  tff(f_187, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 10.34/4.21  tff(f_175, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tex_2)).
% 10.34/4.21  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 10.34/4.21  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 10.34/4.21  tff(f_133, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_tdlat_3(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_tdlat_3)).
% 10.34/4.21  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (v2_tdlat_3(A) => v2_pre_topc(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tdlat_3)).
% 10.34/4.21  tff(f_119, axiom, (![A]: (l1_pre_topc(A) => ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & v2_tdlat_3(A)) => ((~v2_struct_0(A) & v7_struct_0(A)) & v2_pre_topc(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_1)).
% 10.34/4.21  tff(f_88, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 10.34/4.21  tff(c_68, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 10.34/4.21  tff(c_74, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 10.34/4.21  tff(c_66, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_207])).
% 10.34/4.21  tff(c_72, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 10.34/4.21  tff(c_76, plain, (~v1_zfmisc_1('#skF_5') | ~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 10.34/4.21  tff(c_93, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_76])).
% 10.34/4.21  tff(c_82, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_207])).
% 10.34/4.21  tff(c_94, plain, (v1_zfmisc_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_93, c_82])).
% 10.34/4.21  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.34/4.21  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.34/4.21  tff(c_162, plain, (![A_77, B_78]: (~r2_hidden('#skF_2'(A_77, B_78), B_78) | r1_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.34/4.21  tff(c_168, plain, (![A_79]: (r1_tarski(A_79, A_79))), inference(resolution, [status(thm)], [c_10, c_162])).
% 10.34/4.21  tff(c_18, plain, (![A_13, B_14]: (r2_hidden(A_13, B_14) | ~r1_tarski(k1_tarski(A_13), B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.34/4.21  tff(c_174, plain, (![A_80]: (r2_hidden(A_80, k1_tarski(A_80)))), inference(resolution, [status(thm)], [c_168, c_18])).
% 10.34/4.21  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.34/4.21  tff(c_182, plain, (![A_80]: (~v1_xboole_0(k1_tarski(A_80)))), inference(resolution, [status(thm)], [c_174, c_2])).
% 10.34/4.21  tff(c_20, plain, (![A_13, B_14]: (r1_tarski(k1_tarski(A_13), B_14) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.34/4.21  tff(c_8077, plain, (![B_342, A_343]: (B_342=A_343 | ~r1_tarski(A_343, B_342) | ~v1_zfmisc_1(B_342) | v1_xboole_0(B_342) | v1_xboole_0(A_343))), inference(cnfTransformation, [status(thm)], [f_146])).
% 10.34/4.21  tff(c_8092, plain, (![A_13, B_14]: (k1_tarski(A_13)=B_14 | ~v1_zfmisc_1(B_14) | v1_xboole_0(B_14) | v1_xboole_0(k1_tarski(A_13)) | ~r2_hidden(A_13, B_14))), inference(resolution, [status(thm)], [c_20, c_8077])).
% 10.34/4.21  tff(c_8148, plain, (![A_346, B_347]: (k1_tarski(A_346)=B_347 | ~v1_zfmisc_1(B_347) | v1_xboole_0(B_347) | ~r2_hidden(A_346, B_347))), inference(negUnitSimplification, [status(thm)], [c_182, c_8092])).
% 10.34/4.21  tff(c_8167, plain, (![A_1]: (k1_tarski('#skF_1'(A_1))=A_1 | ~v1_zfmisc_1(A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_8148])).
% 10.34/4.21  tff(c_237, plain, (![C_91, B_92, A_93]: (r2_hidden(C_91, B_92) | ~r2_hidden(C_91, A_93) | ~r1_tarski(A_93, B_92))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.34/4.21  tff(c_246, plain, (![A_1, B_92]: (r2_hidden('#skF_1'(A_1), B_92) | ~r1_tarski(A_1, B_92) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_237])).
% 10.34/4.21  tff(c_10781, plain, (![A_468, B_469]: (k1_tarski('#skF_1'(A_468))=B_469 | ~v1_zfmisc_1(B_469) | v1_xboole_0(B_469) | ~r1_tarski(A_468, B_469) | v1_xboole_0(A_468))), inference(resolution, [status(thm)], [c_246, c_8148])).
% 10.34/4.21  tff(c_10813, plain, (![A_13, B_14]: (k1_tarski('#skF_1'(k1_tarski(A_13)))=B_14 | ~v1_zfmisc_1(B_14) | v1_xboole_0(B_14) | v1_xboole_0(k1_tarski(A_13)) | ~r2_hidden(A_13, B_14))), inference(resolution, [status(thm)], [c_20, c_10781])).
% 10.34/4.21  tff(c_10867, plain, (![A_473, B_474]: (k1_tarski('#skF_1'(k1_tarski(A_473)))=B_474 | ~v1_zfmisc_1(B_474) | v1_xboole_0(B_474) | ~r2_hidden(A_473, B_474))), inference(negUnitSimplification, [status(thm)], [c_182, c_10813])).
% 10.34/4.21  tff(c_11078, plain, (![A_479]: (k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_479))))=A_479 | ~v1_zfmisc_1(A_479) | v1_xboole_0(A_479))), inference(resolution, [status(thm)], [c_4, c_10867])).
% 10.34/4.21  tff(c_173, plain, (![A_13]: (r2_hidden(A_13, k1_tarski(A_13)))), inference(resolution, [status(thm)], [c_168, c_18])).
% 10.34/4.21  tff(c_11142, plain, (![A_479]: (r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_479))), A_479) | ~v1_zfmisc_1(A_479) | v1_xboole_0(A_479))), inference(superposition, [status(thm), theory('equality')], [c_11078, c_173])).
% 10.34/4.21  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_207])).
% 10.34/4.21  tff(c_139, plain, (![A_73, B_74]: (r1_tarski(A_73, B_74) | ~m1_subset_1(A_73, k1_zfmisc_1(B_74)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.34/4.21  tff(c_152, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_64, c_139])).
% 10.34/4.21  tff(c_167, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_162])).
% 10.34/4.21  tff(c_252, plain, (![A_95, B_96]: (r2_hidden('#skF_1'(A_95), B_96) | ~r1_tarski(A_95, B_96) | v1_xboole_0(A_95))), inference(resolution, [status(thm)], [c_4, c_237])).
% 10.34/4.21  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.34/4.21  tff(c_10042, plain, (![A_440, B_441, B_442]: (r2_hidden('#skF_1'(A_440), B_441) | ~r1_tarski(B_442, B_441) | ~r1_tarski(A_440, B_442) | v1_xboole_0(A_440))), inference(resolution, [status(thm)], [c_252, c_6])).
% 10.34/4.21  tff(c_13895, plain, (![A_560, B_561, A_562]: (r2_hidden('#skF_1'(A_560), B_561) | ~r1_tarski(A_560, k1_tarski(A_562)) | v1_xboole_0(A_560) | ~r2_hidden(A_562, B_561))), inference(resolution, [status(thm)], [c_20, c_10042])).
% 10.34/4.21  tff(c_13950, plain, (![A_562, B_561]: (r2_hidden('#skF_1'(k1_tarski(A_562)), B_561) | v1_xboole_0(k1_tarski(A_562)) | ~r2_hidden(A_562, B_561))), inference(resolution, [status(thm)], [c_167, c_13895])).
% 10.34/4.21  tff(c_13977, plain, (![A_563, B_564]: (r2_hidden('#skF_1'(k1_tarski(A_563)), B_564) | ~r2_hidden(A_563, B_564))), inference(negUnitSimplification, [status(thm)], [c_182, c_13950])).
% 10.34/4.21  tff(c_14218, plain, (![A_570, B_571, B_572]: (r2_hidden('#skF_1'(k1_tarski(A_570)), B_571) | ~r1_tarski(B_572, B_571) | ~r2_hidden(A_570, B_572))), inference(resolution, [status(thm)], [c_13977, c_6])).
% 10.34/4.21  tff(c_14274, plain, (![A_570]: (r2_hidden('#skF_1'(k1_tarski(A_570)), u1_struct_0('#skF_4')) | ~r2_hidden(A_570, '#skF_5'))), inference(resolution, [status(thm)], [c_152, c_14218])).
% 10.34/4.21  tff(c_17881, plain, (![A_656, B_657]: (r1_tarski(A_656, B_657) | ~r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_656))), B_657) | ~v1_zfmisc_1(A_656) | v1_xboole_0(A_656))), inference(superposition, [status(thm), theory('equality')], [c_11078, c_20])).
% 10.34/4.21  tff(c_18469, plain, (![A_664]: (r1_tarski(A_664, u1_struct_0('#skF_4')) | ~v1_zfmisc_1(A_664) | v1_xboole_0(A_664) | ~r2_hidden('#skF_1'(A_664), '#skF_5'))), inference(resolution, [status(thm)], [c_14274, c_17881])).
% 10.34/4.21  tff(c_18500, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) | v1_xboole_0(k1_tarski('#skF_1'('#skF_5'))) | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_11142, c_18469])).
% 10.34/4.21  tff(c_18529, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) | v1_xboole_0(k1_tarski('#skF_1'('#skF_5'))) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_18500])).
% 10.34/4.21  tff(c_18530, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_66, c_182, c_18529])).
% 10.34/4.21  tff(c_18537, plain, (~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))), inference(splitLeft, [status(thm)], [c_18530])).
% 10.34/4.21  tff(c_18540, plain, (~v1_zfmisc_1('#skF_5') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_8167, c_18537])).
% 10.34/4.21  tff(c_18542, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_94, c_18540])).
% 10.34/4.21  tff(c_18544, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_18542])).
% 10.34/4.21  tff(c_18545, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_18530])).
% 10.34/4.21  tff(c_18662, plain, (r2_hidden('#skF_1'('#skF_5'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_18545, c_18])).
% 10.34/4.21  tff(c_26, plain, (![A_20, B_21]: (m1_subset_1(A_20, B_21) | ~r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.34/4.21  tff(c_18700, plain, (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_18662, c_26])).
% 10.34/4.21  tff(c_191, plain, (![B_85, A_86]: (v1_xboole_0(B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(A_86)) | ~v1_xboole_0(A_86))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.34/4.21  tff(c_201, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_64, c_191])).
% 10.34/4.21  tff(c_206, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_66, c_201])).
% 10.34/4.21  tff(c_10079, plain, (![A_443]: (r2_hidden('#skF_1'(A_443), u1_struct_0('#skF_4')) | ~r1_tarski(A_443, '#skF_5') | v1_xboole_0(A_443))), inference(resolution, [status(thm)], [c_152, c_10042])).
% 10.34/4.21  tff(c_10104, plain, (![A_444]: (m1_subset_1('#skF_1'(A_444), u1_struct_0('#skF_4')) | ~r1_tarski(A_444, '#skF_5') | v1_xboole_0(A_444))), inference(resolution, [status(thm)], [c_10079, c_26])).
% 10.34/4.21  tff(c_38, plain, (![A_29, B_30]: (k6_domain_1(A_29, B_30)=k1_tarski(B_30) | ~m1_subset_1(B_30, A_29) | v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.34/4.21  tff(c_10107, plain, (![A_444]: (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'(A_444))=k1_tarski('#skF_1'(A_444)) | v1_xboole_0(u1_struct_0('#skF_4')) | ~r1_tarski(A_444, '#skF_5') | v1_xboole_0(A_444))), inference(resolution, [status(thm)], [c_10104, c_38])).
% 10.34/4.21  tff(c_17446, plain, (![A_644]: (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'(A_644))=k1_tarski('#skF_1'(A_644)) | ~r1_tarski(A_644, '#skF_5') | v1_xboole_0(A_644))), inference(negUnitSimplification, [status(thm)], [c_206, c_10107])).
% 10.34/4.21  tff(c_62, plain, (![A_45, B_47]: (v2_tex_2(k6_domain_1(u1_struct_0(A_45), B_47), A_45) | ~m1_subset_1(B_47, u1_struct_0(A_45)) | ~l1_pre_topc(A_45) | ~v2_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_187])).
% 10.34/4.21  tff(c_17455, plain, (![A_644]: (v2_tex_2(k1_tarski('#skF_1'(A_644)), '#skF_4') | ~m1_subset_1('#skF_1'(A_644), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(A_644, '#skF_5') | v1_xboole_0(A_644))), inference(superposition, [status(thm), theory('equality')], [c_17446, c_62])).
% 10.34/4.21  tff(c_17479, plain, (![A_644]: (v2_tex_2(k1_tarski('#skF_1'(A_644)), '#skF_4') | ~m1_subset_1('#skF_1'(A_644), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | ~r1_tarski(A_644, '#skF_5') | v1_xboole_0(A_644))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_17455])).
% 10.34/4.21  tff(c_17480, plain, (![A_644]: (v2_tex_2(k1_tarski('#skF_1'(A_644)), '#skF_4') | ~m1_subset_1('#skF_1'(A_644), u1_struct_0('#skF_4')) | ~r1_tarski(A_644, '#skF_5') | v1_xboole_0(A_644))), inference(negUnitSimplification, [status(thm)], [c_74, c_17479])).
% 10.34/4.21  tff(c_30, plain, (![A_22, B_23]: (m1_subset_1(A_22, k1_zfmisc_1(B_23)) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.34/4.21  tff(c_8414, plain, (![A_379, B_380]: (v1_tdlat_3('#skF_3'(A_379, B_380)) | ~v2_tex_2(B_380, A_379) | ~m1_subset_1(B_380, k1_zfmisc_1(u1_struct_0(A_379))) | v1_xboole_0(B_380) | ~l1_pre_topc(A_379) | ~v2_pre_topc(A_379) | v2_struct_0(A_379))), inference(cnfTransformation, [status(thm)], [f_175])).
% 10.34/4.21  tff(c_8441, plain, (![A_379, A_22]: (v1_tdlat_3('#skF_3'(A_379, A_22)) | ~v2_tex_2(A_22, A_379) | v1_xboole_0(A_22) | ~l1_pre_topc(A_379) | ~v2_pre_topc(A_379) | v2_struct_0(A_379) | ~r1_tarski(A_22, u1_struct_0(A_379)))), inference(resolution, [status(thm)], [c_30, c_8414])).
% 10.34/4.21  tff(c_18598, plain, (v1_tdlat_3('#skF_3'('#skF_4', k1_tarski('#skF_1'('#skF_5')))) | ~v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4') | v1_xboole_0(k1_tarski('#skF_1'('#skF_5'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_18545, c_8441])).
% 10.34/4.21  tff(c_18647, plain, (v1_tdlat_3('#skF_3'('#skF_4', k1_tarski('#skF_1'('#skF_5')))) | ~v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4') | v1_xboole_0(k1_tarski('#skF_1'('#skF_5'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_18598])).
% 10.34/4.21  tff(c_18648, plain, (v1_tdlat_3('#skF_3'('#skF_4', k1_tarski('#skF_1'('#skF_5')))) | ~v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_74, c_182, c_18647])).
% 10.34/4.21  tff(c_18702, plain, (~v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_18648])).
% 10.34/4.21  tff(c_18705, plain, (~m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | ~r1_tarski('#skF_5', '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_17480, c_18702])).
% 10.34/4.21  tff(c_18714, plain, (~m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_167, c_18705])).
% 10.34/4.21  tff(c_18715, plain, (~m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_66, c_18714])).
% 10.34/4.21  tff(c_18727, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18700, c_18715])).
% 10.34/4.21  tff(c_18729, plain, (v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4')), inference(splitRight, [status(thm)], [c_18648])).
% 10.34/4.21  tff(c_18732, plain, (v2_tex_2('#skF_5', '#skF_4') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_8167, c_18729])).
% 10.34/4.21  tff(c_18734, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_18732])).
% 10.34/4.21  tff(c_18736, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_93, c_18734])).
% 10.34/4.21  tff(c_18738, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_76])).
% 10.34/4.21  tff(c_18775, plain, (![A_678, B_679]: (r1_tarski(A_678, B_679) | ~m1_subset_1(A_678, k1_zfmisc_1(B_679)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.34/4.21  tff(c_18779, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_64, c_18775])).
% 10.34/4.21  tff(c_20794, plain, (![A_816, B_817]: (m1_pre_topc('#skF_3'(A_816, B_817), A_816) | ~v2_tex_2(B_817, A_816) | ~m1_subset_1(B_817, k1_zfmisc_1(u1_struct_0(A_816))) | v1_xboole_0(B_817) | ~l1_pre_topc(A_816) | ~v2_pre_topc(A_816) | v2_struct_0(A_816))), inference(cnfTransformation, [status(thm)], [f_175])).
% 10.34/4.21  tff(c_21541, plain, (![A_832, A_833]: (m1_pre_topc('#skF_3'(A_832, A_833), A_832) | ~v2_tex_2(A_833, A_832) | v1_xboole_0(A_833) | ~l1_pre_topc(A_832) | ~v2_pre_topc(A_832) | v2_struct_0(A_832) | ~r1_tarski(A_833, u1_struct_0(A_832)))), inference(resolution, [status(thm)], [c_30, c_20794])).
% 10.34/4.21  tff(c_21574, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_18779, c_21541])).
% 10.34/4.21  tff(c_21593, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_18738, c_21574])).
% 10.34/4.21  tff(c_21594, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_74, c_66, c_21593])).
% 10.34/4.21  tff(c_34, plain, (![B_27, A_25]: (l1_pre_topc(B_27) | ~m1_pre_topc(B_27, A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.34/4.21  tff(c_21600, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_21594, c_34])).
% 10.34/4.21  tff(c_21607, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_21600])).
% 10.34/4.21  tff(c_32, plain, (![A_24]: (l1_struct_0(A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.34/4.21  tff(c_20203, plain, (![A_796, B_797]: (~v2_struct_0('#skF_3'(A_796, B_797)) | ~v2_tex_2(B_797, A_796) | ~m1_subset_1(B_797, k1_zfmisc_1(u1_struct_0(A_796))) | v1_xboole_0(B_797) | ~l1_pre_topc(A_796) | ~v2_pre_topc(A_796) | v2_struct_0(A_796))), inference(cnfTransformation, [status(thm)], [f_175])).
% 10.34/4.21  tff(c_21336, plain, (![A_828, A_829]: (~v2_struct_0('#skF_3'(A_828, A_829)) | ~v2_tex_2(A_829, A_828) | v1_xboole_0(A_829) | ~l1_pre_topc(A_828) | ~v2_pre_topc(A_828) | v2_struct_0(A_828) | ~r1_tarski(A_829, u1_struct_0(A_828)))), inference(resolution, [status(thm)], [c_30, c_20203])).
% 10.34/4.21  tff(c_21381, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_18779, c_21336])).
% 10.34/4.21  tff(c_21400, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_18738, c_21381])).
% 10.34/4.21  tff(c_21401, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_74, c_66, c_21400])).
% 10.34/4.21  tff(c_70, plain, (v2_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 10.34/4.21  tff(c_48, plain, (![B_35, A_33]: (v2_tdlat_3(B_35) | ~m1_pre_topc(B_35, A_33) | ~l1_pre_topc(A_33) | ~v2_tdlat_3(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_133])).
% 10.34/4.21  tff(c_21597, plain, (v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_21594, c_48])).
% 10.34/4.21  tff(c_21603, plain, (v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_21597])).
% 10.34/4.21  tff(c_21604, plain, (v2_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_74, c_21603])).
% 10.34/4.21  tff(c_40, plain, (![A_31]: (v2_pre_topc(A_31) | ~v2_tdlat_3(A_31) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.34/4.21  tff(c_21611, plain, (v2_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_21604, c_40])).
% 10.34/4.21  tff(c_21613, plain, (v2_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_21607, c_21611])).
% 10.34/4.21  tff(c_19728, plain, (![A_775, B_776]: (v1_tdlat_3('#skF_3'(A_775, B_776)) | ~v2_tex_2(B_776, A_775) | ~m1_subset_1(B_776, k1_zfmisc_1(u1_struct_0(A_775))) | v1_xboole_0(B_776) | ~l1_pre_topc(A_775) | ~v2_pre_topc(A_775) | v2_struct_0(A_775))), inference(cnfTransformation, [status(thm)], [f_175])).
% 10.34/4.21  tff(c_21063, plain, (![A_819, A_820]: (v1_tdlat_3('#skF_3'(A_819, A_820)) | ~v2_tex_2(A_820, A_819) | v1_xboole_0(A_820) | ~l1_pre_topc(A_819) | ~v2_pre_topc(A_819) | v2_struct_0(A_819) | ~r1_tarski(A_820, u1_struct_0(A_819)))), inference(resolution, [status(thm)], [c_30, c_19728])).
% 10.34/4.21  tff(c_21105, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_18779, c_21063])).
% 10.34/4.21  tff(c_21124, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_18738, c_21105])).
% 10.34/4.21  tff(c_21125, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_74, c_66, c_21124])).
% 10.34/4.21  tff(c_44, plain, (![A_32]: (v7_struct_0(A_32) | ~v2_tdlat_3(A_32) | ~v1_tdlat_3(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.34/4.21  tff(c_18737, plain, (~v1_zfmisc_1('#skF_5')), inference(splitRight, [status(thm)], [c_76])).
% 10.34/4.21  tff(c_20490, plain, (![A_809, B_810]: (u1_struct_0('#skF_3'(A_809, B_810))=B_810 | ~v2_tex_2(B_810, A_809) | ~m1_subset_1(B_810, k1_zfmisc_1(u1_struct_0(A_809))) | v1_xboole_0(B_810) | ~l1_pre_topc(A_809) | ~v2_pre_topc(A_809) | v2_struct_0(A_809))), inference(cnfTransformation, [status(thm)], [f_175])).
% 10.34/4.21  tff(c_21731, plain, (![A_836, A_837]: (u1_struct_0('#skF_3'(A_836, A_837))=A_837 | ~v2_tex_2(A_837, A_836) | v1_xboole_0(A_837) | ~l1_pre_topc(A_836) | ~v2_pre_topc(A_836) | v2_struct_0(A_836) | ~r1_tarski(A_837, u1_struct_0(A_836)))), inference(resolution, [status(thm)], [c_30, c_20490])).
% 10.34/4.21  tff(c_21776, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_18779, c_21731])).
% 10.34/4.21  tff(c_21795, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_18738, c_21776])).
% 10.34/4.21  tff(c_21796, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_74, c_66, c_21795])).
% 10.34/4.21  tff(c_36, plain, (![A_28]: (v1_zfmisc_1(u1_struct_0(A_28)) | ~l1_struct_0(A_28) | ~v7_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.34/4.21  tff(c_21837, plain, (v1_zfmisc_1('#skF_5') | ~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_21796, c_36])).
% 10.34/4.21  tff(c_21882, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_18737, c_21837])).
% 10.34/4.21  tff(c_21888, plain, (~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_21882])).
% 10.34/4.21  tff(c_21891, plain, (~v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_21888])).
% 10.34/4.21  tff(c_21894, plain, (v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_21607, c_21613, c_21125, c_21604, c_21891])).
% 10.34/4.21  tff(c_21896, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21401, c_21894])).
% 10.34/4.21  tff(c_21897, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_21882])).
% 10.34/4.21  tff(c_21902, plain, (~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_32, c_21897])).
% 10.34/4.21  tff(c_21906, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21607, c_21902])).
% 10.34/4.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.34/4.21  
% 10.34/4.21  Inference rules
% 10.34/4.21  ----------------------
% 10.34/4.21  #Ref     : 0
% 10.34/4.21  #Sup     : 5134
% 10.34/4.21  #Fact    : 0
% 10.34/4.21  #Define  : 0
% 10.34/4.21  #Split   : 38
% 10.34/4.21  #Chain   : 0
% 10.34/4.21  #Close   : 0
% 10.34/4.21  
% 10.34/4.21  Ordering : KBO
% 10.34/4.21  
% 10.34/4.21  Simplification rules
% 10.34/4.21  ----------------------
% 10.34/4.21  #Subsume      : 1513
% 10.34/4.21  #Demod        : 1722
% 10.34/4.21  #Tautology    : 1233
% 10.34/4.21  #SimpNegUnit  : 1111
% 10.34/4.21  #BackRed      : 97
% 10.34/4.21  
% 10.34/4.21  #Partial instantiations: 0
% 10.34/4.21  #Strategies tried      : 1
% 10.34/4.21  
% 10.34/4.21  Timing (in seconds)
% 10.34/4.21  ----------------------
% 10.34/4.21  Preprocessing        : 0.34
% 10.34/4.21  Parsing              : 0.18
% 10.34/4.21  CNF conversion       : 0.03
% 10.34/4.21  Main loop            : 3.10
% 10.34/4.21  Inferencing          : 0.85
% 10.34/4.22  Reduction            : 0.96
% 10.34/4.22  Demodulation         : 0.59
% 10.34/4.22  BG Simplification    : 0.09
% 10.34/4.22  Subsumption          : 0.98
% 10.34/4.22  Abstraction          : 0.13
% 10.34/4.22  MUC search           : 0.00
% 10.34/4.22  Cooper               : 0.00
% 10.34/4.22  Total                : 3.49
% 10.34/4.22  Index Insertion      : 0.00
% 10.34/4.22  Index Deletion       : 0.00
% 10.34/4.22  Index Matching       : 0.00
% 10.34/4.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
