%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:53 EST 2020

% Result     : Theorem 5.28s
% Output     : CNFRefutation 5.57s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 306 expanded)
%              Number of leaves         :   46 ( 127 expanded)
%              Depth                    :   13
%              Number of atoms          :  283 ( 995 expanded)
%              Number of equality atoms :   21 (  47 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_194,negated_conjecture,(
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

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_47,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_133,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_174,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_162,axiom,(
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

tff(f_83,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_120,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ( ~ v2_struct_0(B)
              & ~ v7_struct_0(B) )
           => ( ~ v2_struct_0(B)
              & ~ v1_tdlat_3(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc32_tex_2)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(c_40,plain,(
    ! [A_23] :
      ( l1_struct_0(A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_76,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_72,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_86,plain,
    ( v2_tex_2('#skF_6','#skF_5')
    | v1_zfmisc_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_89,plain,(
    v1_zfmisc_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_80,plain,
    ( ~ v1_zfmisc_1('#skF_6')
    | ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_92,plain,(
    ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_80])).

tff(c_68,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_117,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(A_60,B_61)
      | ~ m1_subset_1(A_60,k1_zfmisc_1(B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_126,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_68,c_117])).

tff(c_133,plain,(
    ! [A_66,B_67] :
      ( k3_xboole_0(A_66,B_67) = A_66
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_140,plain,(
    k3_xboole_0('#skF_6',u1_struct_0('#skF_5')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_126,c_133])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_174,plain,(
    ! [D_73,B_74,A_75] :
      ( r2_hidden(D_73,B_74)
      | ~ r2_hidden(D_73,k3_xboole_0(A_75,B_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_277,plain,(
    ! [A_89,B_90] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_89,B_90)),B_90)
      | v1_xboole_0(k3_xboole_0(A_89,B_90)) ) ),
    inference(resolution,[status(thm)],[c_4,c_174])).

tff(c_297,plain,
    ( r2_hidden('#skF_1'('#skF_6'),u1_struct_0('#skF_5'))
    | v1_xboole_0(k3_xboole_0('#skF_6',u1_struct_0('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_277])).

tff(c_302,plain,
    ( r2_hidden('#skF_1'('#skF_6'),u1_struct_0('#skF_5'))
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_297])).

tff(c_303,plain,(
    r2_hidden('#skF_1'('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_302])).

tff(c_34,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,B_20)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_310,plain,(
    m1_subset_1('#skF_1'('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_303,c_34])).

tff(c_193,plain,(
    ! [D_78,A_79,B_80] :
      ( r2_hidden(D_78,A_79)
      | ~ r2_hidden(D_78,k3_xboole_0(A_79,B_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_401,plain,(
    ! [A_98,B_99] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_98,B_99)),A_98)
      | v1_xboole_0(k3_xboole_0(A_98,B_99)) ) ),
    inference(resolution,[status(thm)],[c_4,c_193])).

tff(c_424,plain,
    ( r2_hidden('#skF_1'('#skF_6'),'#skF_6')
    | v1_xboole_0(k3_xboole_0('#skF_6',u1_struct_0('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_401])).

tff(c_430,plain,
    ( r2_hidden('#skF_1'('#skF_6'),'#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_424])).

tff(c_431,plain,(
    r2_hidden('#skF_1'('#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_430])).

tff(c_26,plain,(
    ! [A_13] : ~ v1_xboole_0(k1_tarski(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_30,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(k1_tarski(A_14),B_15)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_327,plain,(
    ! [B_93,A_94] :
      ( B_93 = A_94
      | ~ r1_tarski(A_94,B_93)
      | ~ v1_zfmisc_1(B_93)
      | v1_xboole_0(B_93)
      | v1_xboole_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_336,plain,(
    ! [A_14,B_15] :
      ( k1_tarski(A_14) = B_15
      | ~ v1_zfmisc_1(B_15)
      | v1_xboole_0(B_15)
      | v1_xboole_0(k1_tarski(A_14))
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(resolution,[status(thm)],[c_30,c_327])).

tff(c_343,plain,(
    ! [A_14,B_15] :
      ( k1_tarski(A_14) = B_15
      | ~ v1_zfmisc_1(B_15)
      | v1_xboole_0(B_15)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_336])).

tff(c_434,plain,
    ( k1_tarski('#skF_1'('#skF_6')) = '#skF_6'
    | ~ v1_zfmisc_1('#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_431,c_343])).

tff(c_443,plain,
    ( k1_tarski('#skF_1'('#skF_6')) = '#skF_6'
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_434])).

tff(c_444,plain,(
    k1_tarski('#skF_1'('#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_443])).

tff(c_147,plain,(
    ! [B_69,A_70] :
      ( v1_xboole_0(B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_70))
      | ~ v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_157,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_68,c_147])).

tff(c_162,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_157])).

tff(c_46,plain,(
    ! [A_28,B_29] :
      ( k6_domain_1(A_28,B_29) = k1_tarski(B_29)
      | ~ m1_subset_1(B_29,A_28)
      | v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_314,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_1'('#skF_6')) = k1_tarski('#skF_1'('#skF_6'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_310,c_46])).

tff(c_317,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_1'('#skF_6')) = k1_tarski('#skF_1'('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_314])).

tff(c_480,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_1'('#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_317])).

tff(c_1171,plain,(
    ! [A_134,B_135] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_134),B_135),A_134)
      | ~ m1_subset_1(B_135,u1_struct_0(A_134))
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134)
      | v2_struct_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_1174,plain,
    ( v2_tex_2('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_1'('#skF_6'),u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_1171])).

tff(c_1183,plain,
    ( v2_tex_2('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_310,c_1174])).

tff(c_1185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_92,c_1183])).

tff(c_1186,plain,(
    v2_tex_2('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_3502,plain,(
    ! [A_296,B_297] :
      ( ~ v2_struct_0('#skF_4'(A_296,B_297))
      | ~ v2_tex_2(B_297,A_296)
      | ~ m1_subset_1(B_297,k1_zfmisc_1(u1_struct_0(A_296)))
      | v1_xboole_0(B_297)
      | ~ l1_pre_topc(A_296)
      | ~ v2_pre_topc(A_296)
      | v2_struct_0(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_3533,plain,
    ( ~ v2_struct_0('#skF_4'('#skF_5','#skF_6'))
    | ~ v2_tex_2('#skF_6','#skF_5')
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_3502])).

tff(c_3543,plain,
    ( ~ v2_struct_0('#skF_4'('#skF_5','#skF_6'))
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_1186,c_3533])).

tff(c_3544,plain,(
    ~ v2_struct_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_70,c_3543])).

tff(c_1187,plain,(
    ~ v1_zfmisc_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_4222,plain,(
    ! [A_327,B_328] :
      ( u1_struct_0('#skF_4'(A_327,B_328)) = B_328
      | ~ v2_tex_2(B_328,A_327)
      | ~ m1_subset_1(B_328,k1_zfmisc_1(u1_struct_0(A_327)))
      | v1_xboole_0(B_328)
      | ~ l1_pre_topc(A_327)
      | ~ v2_pre_topc(A_327)
      | v2_struct_0(A_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_4253,plain,
    ( u1_struct_0('#skF_4'('#skF_5','#skF_6')) = '#skF_6'
    | ~ v2_tex_2('#skF_6','#skF_5')
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_4222])).

tff(c_4263,plain,
    ( u1_struct_0('#skF_4'('#skF_5','#skF_6')) = '#skF_6'
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_1186,c_4253])).

tff(c_4264,plain,(
    u1_struct_0('#skF_4'('#skF_5','#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_70,c_4263])).

tff(c_44,plain,(
    ! [A_27] :
      ( v1_zfmisc_1(u1_struct_0(A_27))
      | ~ l1_struct_0(A_27)
      | ~ v7_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4283,plain,
    ( v1_zfmisc_1('#skF_6')
    | ~ l1_struct_0('#skF_4'('#skF_5','#skF_6'))
    | ~ v7_struct_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4264,c_44])).

tff(c_4292,plain,
    ( ~ l1_struct_0('#skF_4'('#skF_5','#skF_6'))
    | ~ v7_struct_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_1187,c_4283])).

tff(c_4294,plain,(
    ~ v7_struct_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_4292])).

tff(c_74,plain,(
    v2_tdlat_3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_3691,plain,(
    ! [A_315,B_316] :
      ( v1_tdlat_3('#skF_4'(A_315,B_316))
      | ~ v2_tex_2(B_316,A_315)
      | ~ m1_subset_1(B_316,k1_zfmisc_1(u1_struct_0(A_315)))
      | v1_xboole_0(B_316)
      | ~ l1_pre_topc(A_315)
      | ~ v2_pre_topc(A_315)
      | v2_struct_0(A_315) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_3722,plain,
    ( v1_tdlat_3('#skF_4'('#skF_5','#skF_6'))
    | ~ v2_tex_2('#skF_6','#skF_5')
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_3691])).

tff(c_3732,plain,
    ( v1_tdlat_3('#skF_4'('#skF_5','#skF_6'))
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_1186,c_3722])).

tff(c_3733,plain,(
    v1_tdlat_3('#skF_4'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_70,c_3732])).

tff(c_4552,plain,(
    ! [A_336,B_337] :
      ( m1_pre_topc('#skF_4'(A_336,B_337),A_336)
      | ~ v2_tex_2(B_337,A_336)
      | ~ m1_subset_1(B_337,k1_zfmisc_1(u1_struct_0(A_336)))
      | v1_xboole_0(B_337)
      | ~ l1_pre_topc(A_336)
      | ~ v2_pre_topc(A_336)
      | v2_struct_0(A_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_4577,plain,
    ( m1_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5')
    | ~ v2_tex_2('#skF_6','#skF_5')
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_4552])).

tff(c_4588,plain,
    ( m1_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5')
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_1186,c_4577])).

tff(c_4589,plain,(
    m1_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_70,c_4588])).

tff(c_50,plain,(
    ! [B_33,A_31] :
      ( ~ v1_tdlat_3(B_33)
      | v7_struct_0(B_33)
      | v2_struct_0(B_33)
      | ~ m1_pre_topc(B_33,A_31)
      | ~ l1_pre_topc(A_31)
      | ~ v2_tdlat_3(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_4592,plain,
    ( ~ v1_tdlat_3('#skF_4'('#skF_5','#skF_6'))
    | v7_struct_0('#skF_4'('#skF_5','#skF_6'))
    | v2_struct_0('#skF_4'('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_tdlat_3('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4589,c_50])).

tff(c_4598,plain,
    ( v7_struct_0('#skF_4'('#skF_5','#skF_6'))
    | v2_struct_0('#skF_4'('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_3733,c_4592])).

tff(c_4600,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3544,c_4294,c_4598])).

tff(c_4601,plain,(
    ~ l1_struct_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_4292])).

tff(c_4606,plain,(
    ~ l1_pre_topc('#skF_4'('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_40,c_4601])).

tff(c_4812,plain,(
    ! [A_341,B_342] :
      ( m1_pre_topc('#skF_4'(A_341,B_342),A_341)
      | ~ v2_tex_2(B_342,A_341)
      | ~ m1_subset_1(B_342,k1_zfmisc_1(u1_struct_0(A_341)))
      | v1_xboole_0(B_342)
      | ~ l1_pre_topc(A_341)
      | ~ v2_pre_topc(A_341)
      | v2_struct_0(A_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_4837,plain,
    ( m1_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5')
    | ~ v2_tex_2('#skF_6','#skF_5')
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_4812])).

tff(c_4848,plain,
    ( m1_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5')
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_1186,c_4837])).

tff(c_4849,plain,(
    m1_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_70,c_4848])).

tff(c_42,plain,(
    ! [B_26,A_24] :
      ( l1_pre_topc(B_26)
      | ~ m1_pre_topc(B_26,A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4855,plain,
    ( l1_pre_topc('#skF_4'('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_4849,c_42])).

tff(c_4862,plain,(
    l1_pre_topc('#skF_4'('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4855])).

tff(c_4864,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4606,c_4862])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:49:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.28/2.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.28/2.04  
% 5.28/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.28/2.04  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 5.28/2.04  
% 5.28/2.04  %Foreground sorts:
% 5.28/2.04  
% 5.28/2.04  
% 5.28/2.04  %Background operators:
% 5.28/2.04  
% 5.28/2.04  
% 5.28/2.04  %Foreground operators:
% 5.28/2.04  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.28/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.28/2.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.28/2.04  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.28/2.04  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.28/2.04  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 5.28/2.04  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.28/2.04  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 5.28/2.04  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 5.28/2.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.28/2.04  tff('#skF_5', type, '#skF_5': $i).
% 5.28/2.04  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 5.28/2.04  tff('#skF_6', type, '#skF_6': $i).
% 5.28/2.04  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.28/2.04  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 5.28/2.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.28/2.04  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.28/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.28/2.04  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.28/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.28/2.04  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 5.28/2.04  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.28/2.04  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.28/2.04  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.28/2.04  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.28/2.04  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.28/2.04  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.28/2.04  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 5.28/2.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.28/2.04  
% 5.57/2.06  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.57/2.06  tff(f_194, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 5.57/2.06  tff(f_66, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.57/2.06  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.57/2.06  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.57/2.06  tff(f_40, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 5.57/2.06  tff(f_62, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 5.57/2.06  tff(f_47, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 5.57/2.06  tff(f_51, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 5.57/2.06  tff(f_133, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 5.57/2.06  tff(f_58, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 5.57/2.06  tff(f_90, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 5.57/2.06  tff(f_174, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 5.57/2.06  tff(f_162, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tex_2)).
% 5.57/2.06  tff(f_83, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 5.57/2.06  tff(f_120, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((~v2_struct_0(B) & ~v7_struct_0(B)) => (~v2_struct_0(B) & ~v1_tdlat_3(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc32_tex_2)).
% 5.57/2.06  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.57/2.06  tff(c_40, plain, (![A_23]: (l1_struct_0(A_23) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.57/2.06  tff(c_78, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_194])).
% 5.57/2.06  tff(c_70, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_194])).
% 5.57/2.06  tff(c_76, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_194])).
% 5.57/2.06  tff(c_72, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_194])).
% 5.57/2.06  tff(c_86, plain, (v2_tex_2('#skF_6', '#skF_5') | v1_zfmisc_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_194])).
% 5.57/2.06  tff(c_89, plain, (v1_zfmisc_1('#skF_6')), inference(splitLeft, [status(thm)], [c_86])).
% 5.57/2.06  tff(c_80, plain, (~v1_zfmisc_1('#skF_6') | ~v2_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_194])).
% 5.57/2.06  tff(c_92, plain, (~v2_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_80])).
% 5.57/2.06  tff(c_68, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_194])).
% 5.57/2.06  tff(c_117, plain, (![A_60, B_61]: (r1_tarski(A_60, B_61) | ~m1_subset_1(A_60, k1_zfmisc_1(B_61)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.57/2.06  tff(c_126, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_68, c_117])).
% 5.57/2.06  tff(c_133, plain, (![A_66, B_67]: (k3_xboole_0(A_66, B_67)=A_66 | ~r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.57/2.06  tff(c_140, plain, (k3_xboole_0('#skF_6', u1_struct_0('#skF_5'))='#skF_6'), inference(resolution, [status(thm)], [c_126, c_133])).
% 5.57/2.06  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.57/2.06  tff(c_174, plain, (![D_73, B_74, A_75]: (r2_hidden(D_73, B_74) | ~r2_hidden(D_73, k3_xboole_0(A_75, B_74)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.57/2.06  tff(c_277, plain, (![A_89, B_90]: (r2_hidden('#skF_1'(k3_xboole_0(A_89, B_90)), B_90) | v1_xboole_0(k3_xboole_0(A_89, B_90)))), inference(resolution, [status(thm)], [c_4, c_174])).
% 5.57/2.06  tff(c_297, plain, (r2_hidden('#skF_1'('#skF_6'), u1_struct_0('#skF_5')) | v1_xboole_0(k3_xboole_0('#skF_6', u1_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_140, c_277])).
% 5.57/2.06  tff(c_302, plain, (r2_hidden('#skF_1'('#skF_6'), u1_struct_0('#skF_5')) | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_297])).
% 5.57/2.06  tff(c_303, plain, (r2_hidden('#skF_1'('#skF_6'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_70, c_302])).
% 5.57/2.06  tff(c_34, plain, (![A_19, B_20]: (m1_subset_1(A_19, B_20) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.57/2.06  tff(c_310, plain, (m1_subset_1('#skF_1'('#skF_6'), u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_303, c_34])).
% 5.57/2.06  tff(c_193, plain, (![D_78, A_79, B_80]: (r2_hidden(D_78, A_79) | ~r2_hidden(D_78, k3_xboole_0(A_79, B_80)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.57/2.06  tff(c_401, plain, (![A_98, B_99]: (r2_hidden('#skF_1'(k3_xboole_0(A_98, B_99)), A_98) | v1_xboole_0(k3_xboole_0(A_98, B_99)))), inference(resolution, [status(thm)], [c_4, c_193])).
% 5.57/2.06  tff(c_424, plain, (r2_hidden('#skF_1'('#skF_6'), '#skF_6') | v1_xboole_0(k3_xboole_0('#skF_6', u1_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_140, c_401])).
% 5.57/2.06  tff(c_430, plain, (r2_hidden('#skF_1'('#skF_6'), '#skF_6') | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_424])).
% 5.57/2.06  tff(c_431, plain, (r2_hidden('#skF_1'('#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_70, c_430])).
% 5.57/2.06  tff(c_26, plain, (![A_13]: (~v1_xboole_0(k1_tarski(A_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.57/2.06  tff(c_30, plain, (![A_14, B_15]: (r1_tarski(k1_tarski(A_14), B_15) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.57/2.06  tff(c_327, plain, (![B_93, A_94]: (B_93=A_94 | ~r1_tarski(A_94, B_93) | ~v1_zfmisc_1(B_93) | v1_xboole_0(B_93) | v1_xboole_0(A_94))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.57/2.06  tff(c_336, plain, (![A_14, B_15]: (k1_tarski(A_14)=B_15 | ~v1_zfmisc_1(B_15) | v1_xboole_0(B_15) | v1_xboole_0(k1_tarski(A_14)) | ~r2_hidden(A_14, B_15))), inference(resolution, [status(thm)], [c_30, c_327])).
% 5.57/2.06  tff(c_343, plain, (![A_14, B_15]: (k1_tarski(A_14)=B_15 | ~v1_zfmisc_1(B_15) | v1_xboole_0(B_15) | ~r2_hidden(A_14, B_15))), inference(negUnitSimplification, [status(thm)], [c_26, c_336])).
% 5.57/2.06  tff(c_434, plain, (k1_tarski('#skF_1'('#skF_6'))='#skF_6' | ~v1_zfmisc_1('#skF_6') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_431, c_343])).
% 5.57/2.06  tff(c_443, plain, (k1_tarski('#skF_1'('#skF_6'))='#skF_6' | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_434])).
% 5.57/2.06  tff(c_444, plain, (k1_tarski('#skF_1'('#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_70, c_443])).
% 5.57/2.06  tff(c_147, plain, (![B_69, A_70]: (v1_xboole_0(B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(A_70)) | ~v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.57/2.06  tff(c_157, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_68, c_147])).
% 5.57/2.06  tff(c_162, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_70, c_157])).
% 5.57/2.06  tff(c_46, plain, (![A_28, B_29]: (k6_domain_1(A_28, B_29)=k1_tarski(B_29) | ~m1_subset_1(B_29, A_28) | v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.57/2.06  tff(c_314, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_1'('#skF_6'))=k1_tarski('#skF_1'('#skF_6')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_310, c_46])).
% 5.57/2.06  tff(c_317, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_1'('#skF_6'))=k1_tarski('#skF_1'('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_162, c_314])).
% 5.57/2.06  tff(c_480, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_1'('#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_444, c_317])).
% 5.57/2.06  tff(c_1171, plain, (![A_134, B_135]: (v2_tex_2(k6_domain_1(u1_struct_0(A_134), B_135), A_134) | ~m1_subset_1(B_135, u1_struct_0(A_134)) | ~l1_pre_topc(A_134) | ~v2_pre_topc(A_134) | v2_struct_0(A_134))), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.57/2.06  tff(c_1174, plain, (v2_tex_2('#skF_6', '#skF_5') | ~m1_subset_1('#skF_1'('#skF_6'), u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_480, c_1171])).
% 5.57/2.06  tff(c_1183, plain, (v2_tex_2('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_310, c_1174])).
% 5.57/2.06  tff(c_1185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_92, c_1183])).
% 5.57/2.06  tff(c_1186, plain, (v2_tex_2('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_86])).
% 5.57/2.06  tff(c_3502, plain, (![A_296, B_297]: (~v2_struct_0('#skF_4'(A_296, B_297)) | ~v2_tex_2(B_297, A_296) | ~m1_subset_1(B_297, k1_zfmisc_1(u1_struct_0(A_296))) | v1_xboole_0(B_297) | ~l1_pre_topc(A_296) | ~v2_pre_topc(A_296) | v2_struct_0(A_296))), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.57/2.06  tff(c_3533, plain, (~v2_struct_0('#skF_4'('#skF_5', '#skF_6')) | ~v2_tex_2('#skF_6', '#skF_5') | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_68, c_3502])).
% 5.57/2.06  tff(c_3543, plain, (~v2_struct_0('#skF_4'('#skF_5', '#skF_6')) | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_1186, c_3533])).
% 5.57/2.06  tff(c_3544, plain, (~v2_struct_0('#skF_4'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_78, c_70, c_3543])).
% 5.57/2.06  tff(c_1187, plain, (~v1_zfmisc_1('#skF_6')), inference(splitRight, [status(thm)], [c_86])).
% 5.57/2.06  tff(c_4222, plain, (![A_327, B_328]: (u1_struct_0('#skF_4'(A_327, B_328))=B_328 | ~v2_tex_2(B_328, A_327) | ~m1_subset_1(B_328, k1_zfmisc_1(u1_struct_0(A_327))) | v1_xboole_0(B_328) | ~l1_pre_topc(A_327) | ~v2_pre_topc(A_327) | v2_struct_0(A_327))), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.57/2.06  tff(c_4253, plain, (u1_struct_0('#skF_4'('#skF_5', '#skF_6'))='#skF_6' | ~v2_tex_2('#skF_6', '#skF_5') | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_68, c_4222])).
% 5.57/2.06  tff(c_4263, plain, (u1_struct_0('#skF_4'('#skF_5', '#skF_6'))='#skF_6' | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_1186, c_4253])).
% 5.57/2.06  tff(c_4264, plain, (u1_struct_0('#skF_4'('#skF_5', '#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_78, c_70, c_4263])).
% 5.57/2.06  tff(c_44, plain, (![A_27]: (v1_zfmisc_1(u1_struct_0(A_27)) | ~l1_struct_0(A_27) | ~v7_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.57/2.06  tff(c_4283, plain, (v1_zfmisc_1('#skF_6') | ~l1_struct_0('#skF_4'('#skF_5', '#skF_6')) | ~v7_struct_0('#skF_4'('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4264, c_44])).
% 5.57/2.06  tff(c_4292, plain, (~l1_struct_0('#skF_4'('#skF_5', '#skF_6')) | ~v7_struct_0('#skF_4'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_1187, c_4283])).
% 5.57/2.06  tff(c_4294, plain, (~v7_struct_0('#skF_4'('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_4292])).
% 5.57/2.06  tff(c_74, plain, (v2_tdlat_3('#skF_5')), inference(cnfTransformation, [status(thm)], [f_194])).
% 5.57/2.06  tff(c_3691, plain, (![A_315, B_316]: (v1_tdlat_3('#skF_4'(A_315, B_316)) | ~v2_tex_2(B_316, A_315) | ~m1_subset_1(B_316, k1_zfmisc_1(u1_struct_0(A_315))) | v1_xboole_0(B_316) | ~l1_pre_topc(A_315) | ~v2_pre_topc(A_315) | v2_struct_0(A_315))), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.57/2.06  tff(c_3722, plain, (v1_tdlat_3('#skF_4'('#skF_5', '#skF_6')) | ~v2_tex_2('#skF_6', '#skF_5') | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_68, c_3691])).
% 5.57/2.06  tff(c_3732, plain, (v1_tdlat_3('#skF_4'('#skF_5', '#skF_6')) | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_1186, c_3722])).
% 5.57/2.06  tff(c_3733, plain, (v1_tdlat_3('#skF_4'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_78, c_70, c_3732])).
% 5.57/2.06  tff(c_4552, plain, (![A_336, B_337]: (m1_pre_topc('#skF_4'(A_336, B_337), A_336) | ~v2_tex_2(B_337, A_336) | ~m1_subset_1(B_337, k1_zfmisc_1(u1_struct_0(A_336))) | v1_xboole_0(B_337) | ~l1_pre_topc(A_336) | ~v2_pre_topc(A_336) | v2_struct_0(A_336))), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.57/2.06  tff(c_4577, plain, (m1_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5') | ~v2_tex_2('#skF_6', '#skF_5') | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_68, c_4552])).
% 5.57/2.06  tff(c_4588, plain, (m1_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5') | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_1186, c_4577])).
% 5.57/2.06  tff(c_4589, plain, (m1_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_78, c_70, c_4588])).
% 5.57/2.06  tff(c_50, plain, (![B_33, A_31]: (~v1_tdlat_3(B_33) | v7_struct_0(B_33) | v2_struct_0(B_33) | ~m1_pre_topc(B_33, A_31) | ~l1_pre_topc(A_31) | ~v2_tdlat_3(A_31) | ~v2_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.57/2.06  tff(c_4592, plain, (~v1_tdlat_3('#skF_4'('#skF_5', '#skF_6')) | v7_struct_0('#skF_4'('#skF_5', '#skF_6')) | v2_struct_0('#skF_4'('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | ~v2_tdlat_3('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_4589, c_50])).
% 5.57/2.06  tff(c_4598, plain, (v7_struct_0('#skF_4'('#skF_5', '#skF_6')) | v2_struct_0('#skF_4'('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_3733, c_4592])).
% 5.57/2.06  tff(c_4600, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_3544, c_4294, c_4598])).
% 5.57/2.06  tff(c_4601, plain, (~l1_struct_0('#skF_4'('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_4292])).
% 5.57/2.06  tff(c_4606, plain, (~l1_pre_topc('#skF_4'('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_40, c_4601])).
% 5.57/2.06  tff(c_4812, plain, (![A_341, B_342]: (m1_pre_topc('#skF_4'(A_341, B_342), A_341) | ~v2_tex_2(B_342, A_341) | ~m1_subset_1(B_342, k1_zfmisc_1(u1_struct_0(A_341))) | v1_xboole_0(B_342) | ~l1_pre_topc(A_341) | ~v2_pre_topc(A_341) | v2_struct_0(A_341))), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.57/2.06  tff(c_4837, plain, (m1_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5') | ~v2_tex_2('#skF_6', '#skF_5') | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_68, c_4812])).
% 5.57/2.06  tff(c_4848, plain, (m1_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5') | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_1186, c_4837])).
% 5.57/2.06  tff(c_4849, plain, (m1_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_78, c_70, c_4848])).
% 5.57/2.06  tff(c_42, plain, (![B_26, A_24]: (l1_pre_topc(B_26) | ~m1_pre_topc(B_26, A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.57/2.06  tff(c_4855, plain, (l1_pre_topc('#skF_4'('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_4849, c_42])).
% 5.57/2.06  tff(c_4862, plain, (l1_pre_topc('#skF_4'('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4855])).
% 5.57/2.06  tff(c_4864, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4606, c_4862])).
% 5.57/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.57/2.06  
% 5.57/2.06  Inference rules
% 5.57/2.06  ----------------------
% 5.57/2.06  #Ref     : 0
% 5.57/2.06  #Sup     : 1183
% 5.57/2.06  #Fact    : 0
% 5.57/2.06  #Define  : 0
% 5.57/2.06  #Split   : 11
% 5.57/2.06  #Chain   : 0
% 5.57/2.06  #Close   : 0
% 5.57/2.06  
% 5.57/2.06  Ordering : KBO
% 5.57/2.06  
% 5.57/2.06  Simplification rules
% 5.57/2.06  ----------------------
% 5.57/2.06  #Subsume      : 313
% 5.57/2.06  #Demod        : 285
% 5.57/2.06  #Tautology    : 286
% 5.57/2.06  #SimpNegUnit  : 123
% 5.57/2.06  #BackRed      : 2
% 5.57/2.06  
% 5.57/2.06  #Partial instantiations: 0
% 5.57/2.06  #Strategies tried      : 1
% 5.57/2.06  
% 5.57/2.06  Timing (in seconds)
% 5.57/2.06  ----------------------
% 5.57/2.07  Preprocessing        : 0.36
% 5.57/2.07  Parsing              : 0.19
% 5.57/2.07  CNF conversion       : 0.03
% 5.57/2.07  Main loop            : 0.94
% 5.57/2.07  Inferencing          : 0.32
% 5.57/2.07  Reduction            : 0.28
% 5.57/2.07  Demodulation         : 0.19
% 5.57/2.07  BG Simplification    : 0.04
% 5.57/2.07  Subsumption          : 0.21
% 5.57/2.07  Abstraction          : 0.05
% 5.57/2.07  MUC search           : 0.00
% 5.57/2.07  Cooper               : 0.00
% 5.57/2.07  Total                : 1.34
% 5.57/2.07  Index Insertion      : 0.00
% 5.57/2.07  Index Deletion       : 0.00
% 5.70/2.07  Index Matching       : 0.00
% 5.70/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
