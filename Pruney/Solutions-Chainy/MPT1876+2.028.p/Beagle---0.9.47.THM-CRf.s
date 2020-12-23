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
% DateTime   : Thu Dec  3 10:29:54 EST 2020

% Result     : Theorem 4.68s
% Output     : CNFRefutation 5.06s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 430 expanded)
%              Number of leaves         :   44 ( 168 expanded)
%              Depth                    :   16
%              Number of atoms          :  329 (1499 expanded)
%              Number of equality atoms :   19 (  48 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

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

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
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

tff(f_89,axiom,(
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

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_69,axiom,(
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

tff(f_82,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(c_72,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_76,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_86,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_90,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_80,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_92,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_80])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_226,plain,(
    ! [B_82,A_83] :
      ( m1_subset_1(B_82,A_83)
      | ~ r2_hidden(B_82,A_83)
      | v1_xboole_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_244,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_226])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_143,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(A_66,B_67)
      | ~ m1_subset_1(A_66,k1_zfmisc_1(B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_156,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_68,c_143])).

tff(c_157,plain,(
    ! [A_68,B_69] :
      ( r2_hidden('#skF_2'(A_68,B_69),A_68)
      | r1_tarski(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_161,plain,(
    ! [A_68,B_69] :
      ( ~ v1_xboole_0(A_68)
      | r1_tarski(A_68,B_69) ) ),
    inference(resolution,[status(thm)],[c_157,c_2])).

tff(c_168,plain,(
    ! [B_72,A_73] :
      ( B_72 = A_73
      | ~ r1_tarski(B_72,A_73)
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_184,plain,(
    ! [B_74,A_75] :
      ( B_74 = A_75
      | ~ r1_tarski(B_74,A_75)
      | ~ v1_xboole_0(A_75) ) ),
    inference(resolution,[status(thm)],[c_161,c_168])).

tff(c_198,plain,
    ( u1_struct_0('#skF_4') = '#skF_5'
    | ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_156,c_184])).

tff(c_203,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_198])).

tff(c_24,plain,(
    ! [B_15,A_14] :
      ( r2_hidden(B_15,A_14)
      | ~ m1_subset_1(B_15,A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_245,plain,(
    ! [C_84,B_85,A_86] :
      ( r2_hidden(C_84,B_85)
      | ~ r2_hidden(C_84,A_86)
      | ~ r1_tarski(A_86,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_625,plain,(
    ! [B_128,B_129,A_130] :
      ( r2_hidden(B_128,B_129)
      | ~ r1_tarski(A_130,B_129)
      | ~ m1_subset_1(B_128,A_130)
      | v1_xboole_0(A_130) ) ),
    inference(resolution,[status(thm)],[c_24,c_245])).

tff(c_633,plain,(
    ! [B_128] :
      ( r2_hidden(B_128,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_128,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_156,c_625])).

tff(c_648,plain,(
    ! [B_131] :
      ( r2_hidden(B_131,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_131,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_633])).

tff(c_22,plain,(
    ! [B_15,A_14] :
      ( m1_subset_1(B_15,A_14)
      | ~ r2_hidden(B_15,A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_656,plain,(
    ! [B_131] :
      ( m1_subset_1(B_131,u1_struct_0('#skF_4'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_131,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_648,c_22])).

tff(c_669,plain,(
    ! [B_131] :
      ( m1_subset_1(B_131,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_131,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_203,c_656])).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_107,plain,(
    ! [A_51,B_52] :
      ( r2_hidden(A_51,B_52)
      | ~ r1_tarski(k1_tarski(A_51),B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_113,plain,(
    ! [A_53] : r2_hidden(A_53,k1_tarski(A_53)) ),
    inference(resolution,[status(thm)],[c_16,c_107])).

tff(c_117,plain,(
    ! [A_53] : ~ v1_xboole_0(k1_tarski(A_53)) ),
    inference(resolution,[status(thm)],[c_113,c_2])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(k1_tarski(A_12),B_13)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_332,plain,(
    ! [B_97,A_98] :
      ( B_97 = A_98
      | ~ r1_tarski(A_98,B_97)
      | ~ v1_zfmisc_1(B_97)
      | v1_xboole_0(B_97)
      | v1_xboole_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_344,plain,(
    ! [A_12,B_13] :
      ( k1_tarski(A_12) = B_13
      | ~ v1_zfmisc_1(B_13)
      | v1_xboole_0(B_13)
      | v1_xboole_0(k1_tarski(A_12))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_20,c_332])).

tff(c_420,plain,(
    ! [A_107,B_108] :
      ( k1_tarski(A_107) = B_108
      | ~ v1_zfmisc_1(B_108)
      | v1_xboole_0(B_108)
      | ~ r2_hidden(A_107,B_108) ) ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_344])).

tff(c_443,plain,(
    ! [A_1] :
      ( k1_tarski('#skF_1'(A_1)) = A_1
      | ~ v1_zfmisc_1(A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_420])).

tff(c_700,plain,(
    ! [B_134] :
      ( m1_subset_1(B_134,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_134,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_203,c_656])).

tff(c_40,plain,(
    ! [A_23,B_24] :
      ( k6_domain_1(A_23,B_24) = k1_tarski(B_24)
      | ~ m1_subset_1(B_24,A_23)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_710,plain,(
    ! [B_134] :
      ( k6_domain_1(u1_struct_0('#skF_4'),B_134) = k1_tarski(B_134)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_134,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_700,c_40])).

tff(c_723,plain,(
    ! [B_135] :
      ( k6_domain_1(u1_struct_0('#skF_4'),B_135) = k1_tarski(B_135)
      | ~ m1_subset_1(B_135,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_203,c_710])).

tff(c_66,plain,(
    ! [A_40,B_42] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_40),B_42),A_40)
      | ~ m1_subset_1(B_42,u1_struct_0(A_40))
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_729,plain,(
    ! [B_135] :
      ( v2_tex_2(k1_tarski(B_135),'#skF_4')
      | ~ m1_subset_1(B_135,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(B_135,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_723,c_66])).

tff(c_743,plain,(
    ! [B_135] :
      ( v2_tex_2(k1_tarski(B_135),'#skF_4')
      | ~ m1_subset_1(B_135,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(B_135,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_729])).

tff(c_772,plain,(
    ! [B_139] :
      ( v2_tex_2(k1_tarski(B_139),'#skF_4')
      | ~ m1_subset_1(B_139,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_139,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_743])).

tff(c_1210,plain,(
    ! [A_168] :
      ( v2_tex_2(A_168,'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_168),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(A_168),'#skF_5')
      | ~ v1_zfmisc_1(A_168)
      | v1_xboole_0(A_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_443,c_772])).

tff(c_1443,plain,(
    ! [A_177] :
      ( v2_tex_2(A_177,'#skF_4')
      | ~ v1_zfmisc_1(A_177)
      | v1_xboole_0(A_177)
      | ~ m1_subset_1('#skF_1'(A_177),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_669,c_1210])).

tff(c_1455,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_244,c_1443])).

tff(c_1467,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_1455])).

tff(c_1469,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_92,c_1467])).

tff(c_1470,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_1471,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_1484,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1470,c_1471])).

tff(c_1485,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1484])).

tff(c_1486,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_2899,plain,(
    ! [A_313,B_314] :
      ( m1_pre_topc('#skF_3'(A_313,B_314),A_313)
      | ~ v2_tex_2(B_314,A_313)
      | ~ m1_subset_1(B_314,k1_zfmisc_1(u1_struct_0(A_313)))
      | v1_xboole_0(B_314)
      | ~ l1_pre_topc(A_313)
      | ~ v2_pre_topc(A_313)
      | v2_struct_0(A_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_2919,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_2899])).

tff(c_2928,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_1486,c_2919])).

tff(c_2929,plain,(
    m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_70,c_2928])).

tff(c_36,plain,(
    ! [B_21,A_19] :
      ( l1_pre_topc(B_21)
      | ~ m1_pre_topc(B_21,A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2935,plain,
    ( l1_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_2929,c_36])).

tff(c_2942,plain,(
    l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2935])).

tff(c_34,plain,(
    ! [A_18] :
      ( l1_struct_0(A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2451,plain,(
    ! [A_289,B_290] :
      ( ~ v2_struct_0('#skF_3'(A_289,B_290))
      | ~ v2_tex_2(B_290,A_289)
      | ~ m1_subset_1(B_290,k1_zfmisc_1(u1_struct_0(A_289)))
      | v1_xboole_0(B_290)
      | ~ l1_pre_topc(A_289)
      | ~ v2_pre_topc(A_289)
      | v2_struct_0(A_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_2478,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_2451])).

tff(c_2487,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_1486,c_2478])).

tff(c_2488,plain,(
    ~ v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_70,c_2487])).

tff(c_74,plain,(
    v2_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_52,plain,(
    ! [B_30,A_28] :
      ( v2_tdlat_3(B_30)
      | ~ m1_pre_topc(B_30,A_28)
      | ~ l1_pre_topc(A_28)
      | ~ v2_tdlat_3(A_28)
      | ~ v2_pre_topc(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2932,plain,
    ( v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_2929,c_52])).

tff(c_2938,plain,
    ( v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_2932])).

tff(c_2939,plain,(
    v2_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2938])).

tff(c_44,plain,(
    ! [A_26] :
      ( v2_pre_topc(A_26)
      | ~ v2_tdlat_3(A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2946,plain,
    ( v2_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_2939,c_44])).

tff(c_2948,plain,(
    v2_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2942,c_2946])).

tff(c_2211,plain,(
    ! [A_277,B_278] :
      ( v1_tdlat_3('#skF_3'(A_277,B_278))
      | ~ v2_tex_2(B_278,A_277)
      | ~ m1_subset_1(B_278,k1_zfmisc_1(u1_struct_0(A_277)))
      | v1_xboole_0(B_278)
      | ~ l1_pre_topc(A_277)
      | ~ v2_pre_topc(A_277)
      | v2_struct_0(A_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_2234,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_2211])).

tff(c_2242,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_1486,c_2234])).

tff(c_2243,plain,(
    v1_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_70,c_2242])).

tff(c_48,plain,(
    ! [A_27] :
      ( v7_struct_0(A_27)
      | ~ v2_tdlat_3(A_27)
      | ~ v1_tdlat_3(A_27)
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1487,plain,(
    ~ v1_zfmisc_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_3127,plain,(
    ! [A_324,B_325] :
      ( u1_struct_0('#skF_3'(A_324,B_325)) = B_325
      | ~ v2_tex_2(B_325,A_324)
      | ~ m1_subset_1(B_325,k1_zfmisc_1(u1_struct_0(A_324)))
      | v1_xboole_0(B_325)
      | ~ l1_pre_topc(A_324)
      | ~ v2_pre_topc(A_324)
      | v2_struct_0(A_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_3154,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_3127])).

tff(c_3163,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_1486,c_3154])).

tff(c_3164,plain,(
    u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_70,c_3163])).

tff(c_38,plain,(
    ! [A_22] :
      ( v1_zfmisc_1(u1_struct_0(A_22))
      | ~ l1_struct_0(A_22)
      | ~ v7_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3185,plain,
    ( v1_zfmisc_1('#skF_5')
    | ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3164,c_38])).

tff(c_3206,plain,
    ( ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_1487,c_3185])).

tff(c_3208,plain,(
    ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_3206])).

tff(c_3211,plain,
    ( ~ v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_48,c_3208])).

tff(c_3214,plain,(
    v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2942,c_2948,c_2243,c_2939,c_3211])).

tff(c_3216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2488,c_3214])).

tff(c_3217,plain,(
    ~ l1_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_3206])).

tff(c_3227,plain,(
    ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_34,c_3217])).

tff(c_3231,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2942,c_3227])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:36:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.68/1.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.91  
% 4.68/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.91  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 4.68/1.91  
% 4.68/1.91  %Foreground sorts:
% 4.68/1.91  
% 4.68/1.91  
% 4.68/1.91  %Background operators:
% 4.68/1.91  
% 4.68/1.91  
% 4.68/1.91  %Foreground operators:
% 4.68/1.91  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.68/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.68/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.68/1.91  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.68/1.91  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.68/1.91  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 4.68/1.91  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.68/1.91  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 4.68/1.91  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.68/1.91  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.68/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.68/1.91  tff('#skF_5', type, '#skF_5': $i).
% 4.68/1.91  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.68/1.91  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.68/1.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.68/1.91  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.68/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.68/1.91  tff('#skF_4', type, '#skF_4': $i).
% 4.68/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.68/1.91  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.68/1.91  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 4.68/1.91  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.68/1.91  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.68/1.91  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.68/1.91  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.68/1.91  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 4.68/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.68/1.91  
% 5.06/1.93  tff(f_207, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 5.06/1.93  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.06/1.93  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 5.06/1.93  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.06/1.93  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.06/1.93  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.06/1.93  tff(f_48, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 5.06/1.93  tff(f_146, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 5.06/1.93  tff(f_89, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 5.06/1.93  tff(f_187, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 5.06/1.93  tff(f_175, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tex_2)).
% 5.06/1.93  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.06/1.93  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.06/1.93  tff(f_133, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_tdlat_3(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_tdlat_3)).
% 5.06/1.93  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (v2_tdlat_3(A) => v2_pre_topc(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tdlat_3)).
% 5.06/1.93  tff(f_119, axiom, (![A]: (l1_pre_topc(A) => ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & v2_tdlat_3(A)) => ((~v2_struct_0(A) & v7_struct_0(A)) & v2_pre_topc(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_1)).
% 5.06/1.93  tff(f_82, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 5.06/1.93  tff(c_72, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 5.06/1.93  tff(c_78, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 5.06/1.93  tff(c_70, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_207])).
% 5.06/1.93  tff(c_76, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 5.06/1.93  tff(c_86, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_207])).
% 5.06/1.93  tff(c_90, plain, (v1_zfmisc_1('#skF_5')), inference(splitLeft, [status(thm)], [c_86])).
% 5.06/1.93  tff(c_80, plain, (~v1_zfmisc_1('#skF_5') | ~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 5.06/1.93  tff(c_92, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_80])).
% 5.06/1.93  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.06/1.93  tff(c_226, plain, (![B_82, A_83]: (m1_subset_1(B_82, A_83) | ~r2_hidden(B_82, A_83) | v1_xboole_0(A_83))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.06/1.93  tff(c_244, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_226])).
% 5.06/1.93  tff(c_68, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_207])).
% 5.06/1.93  tff(c_143, plain, (![A_66, B_67]: (r1_tarski(A_66, B_67) | ~m1_subset_1(A_66, k1_zfmisc_1(B_67)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.06/1.93  tff(c_156, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_143])).
% 5.06/1.93  tff(c_157, plain, (![A_68, B_69]: (r2_hidden('#skF_2'(A_68, B_69), A_68) | r1_tarski(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.06/1.93  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.06/1.93  tff(c_161, plain, (![A_68, B_69]: (~v1_xboole_0(A_68) | r1_tarski(A_68, B_69))), inference(resolution, [status(thm)], [c_157, c_2])).
% 5.06/1.93  tff(c_168, plain, (![B_72, A_73]: (B_72=A_73 | ~r1_tarski(B_72, A_73) | ~r1_tarski(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.06/1.93  tff(c_184, plain, (![B_74, A_75]: (B_74=A_75 | ~r1_tarski(B_74, A_75) | ~v1_xboole_0(A_75))), inference(resolution, [status(thm)], [c_161, c_168])).
% 5.06/1.93  tff(c_198, plain, (u1_struct_0('#skF_4')='#skF_5' | ~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_156, c_184])).
% 5.06/1.93  tff(c_203, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_198])).
% 5.06/1.93  tff(c_24, plain, (![B_15, A_14]: (r2_hidden(B_15, A_14) | ~m1_subset_1(B_15, A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.06/1.93  tff(c_245, plain, (![C_84, B_85, A_86]: (r2_hidden(C_84, B_85) | ~r2_hidden(C_84, A_86) | ~r1_tarski(A_86, B_85))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.06/1.93  tff(c_625, plain, (![B_128, B_129, A_130]: (r2_hidden(B_128, B_129) | ~r1_tarski(A_130, B_129) | ~m1_subset_1(B_128, A_130) | v1_xboole_0(A_130))), inference(resolution, [status(thm)], [c_24, c_245])).
% 5.06/1.93  tff(c_633, plain, (![B_128]: (r2_hidden(B_128, u1_struct_0('#skF_4')) | ~m1_subset_1(B_128, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_156, c_625])).
% 5.06/1.93  tff(c_648, plain, (![B_131]: (r2_hidden(B_131, u1_struct_0('#skF_4')) | ~m1_subset_1(B_131, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_70, c_633])).
% 5.06/1.93  tff(c_22, plain, (![B_15, A_14]: (m1_subset_1(B_15, A_14) | ~r2_hidden(B_15, A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.06/1.93  tff(c_656, plain, (![B_131]: (m1_subset_1(B_131, u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(B_131, '#skF_5'))), inference(resolution, [status(thm)], [c_648, c_22])).
% 5.06/1.93  tff(c_669, plain, (![B_131]: (m1_subset_1(B_131, u1_struct_0('#skF_4')) | ~m1_subset_1(B_131, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_203, c_656])).
% 5.06/1.93  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.06/1.93  tff(c_107, plain, (![A_51, B_52]: (r2_hidden(A_51, B_52) | ~r1_tarski(k1_tarski(A_51), B_52))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.06/1.93  tff(c_113, plain, (![A_53]: (r2_hidden(A_53, k1_tarski(A_53)))), inference(resolution, [status(thm)], [c_16, c_107])).
% 5.06/1.93  tff(c_117, plain, (![A_53]: (~v1_xboole_0(k1_tarski(A_53)))), inference(resolution, [status(thm)], [c_113, c_2])).
% 5.06/1.93  tff(c_20, plain, (![A_12, B_13]: (r1_tarski(k1_tarski(A_12), B_13) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.06/1.93  tff(c_332, plain, (![B_97, A_98]: (B_97=A_98 | ~r1_tarski(A_98, B_97) | ~v1_zfmisc_1(B_97) | v1_xboole_0(B_97) | v1_xboole_0(A_98))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.06/1.93  tff(c_344, plain, (![A_12, B_13]: (k1_tarski(A_12)=B_13 | ~v1_zfmisc_1(B_13) | v1_xboole_0(B_13) | v1_xboole_0(k1_tarski(A_12)) | ~r2_hidden(A_12, B_13))), inference(resolution, [status(thm)], [c_20, c_332])).
% 5.06/1.93  tff(c_420, plain, (![A_107, B_108]: (k1_tarski(A_107)=B_108 | ~v1_zfmisc_1(B_108) | v1_xboole_0(B_108) | ~r2_hidden(A_107, B_108))), inference(negUnitSimplification, [status(thm)], [c_117, c_344])).
% 5.06/1.93  tff(c_443, plain, (![A_1]: (k1_tarski('#skF_1'(A_1))=A_1 | ~v1_zfmisc_1(A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_420])).
% 5.06/1.93  tff(c_700, plain, (![B_134]: (m1_subset_1(B_134, u1_struct_0('#skF_4')) | ~m1_subset_1(B_134, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_203, c_656])).
% 5.06/1.93  tff(c_40, plain, (![A_23, B_24]: (k6_domain_1(A_23, B_24)=k1_tarski(B_24) | ~m1_subset_1(B_24, A_23) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.06/1.93  tff(c_710, plain, (![B_134]: (k6_domain_1(u1_struct_0('#skF_4'), B_134)=k1_tarski(B_134) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(B_134, '#skF_5'))), inference(resolution, [status(thm)], [c_700, c_40])).
% 5.06/1.93  tff(c_723, plain, (![B_135]: (k6_domain_1(u1_struct_0('#skF_4'), B_135)=k1_tarski(B_135) | ~m1_subset_1(B_135, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_203, c_710])).
% 5.06/1.93  tff(c_66, plain, (![A_40, B_42]: (v2_tex_2(k6_domain_1(u1_struct_0(A_40), B_42), A_40) | ~m1_subset_1(B_42, u1_struct_0(A_40)) | ~l1_pre_topc(A_40) | ~v2_pre_topc(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.06/1.93  tff(c_729, plain, (![B_135]: (v2_tex_2(k1_tarski(B_135), '#skF_4') | ~m1_subset_1(B_135, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_subset_1(B_135, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_723, c_66])).
% 5.06/1.93  tff(c_743, plain, (![B_135]: (v2_tex_2(k1_tarski(B_135), '#skF_4') | ~m1_subset_1(B_135, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | ~m1_subset_1(B_135, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_729])).
% 5.06/1.93  tff(c_772, plain, (![B_139]: (v2_tex_2(k1_tarski(B_139), '#skF_4') | ~m1_subset_1(B_139, u1_struct_0('#skF_4')) | ~m1_subset_1(B_139, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_78, c_743])).
% 5.06/1.93  tff(c_1210, plain, (![A_168]: (v2_tex_2(A_168, '#skF_4') | ~m1_subset_1('#skF_1'(A_168), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(A_168), '#skF_5') | ~v1_zfmisc_1(A_168) | v1_xboole_0(A_168))), inference(superposition, [status(thm), theory('equality')], [c_443, c_772])).
% 5.06/1.93  tff(c_1443, plain, (![A_177]: (v2_tex_2(A_177, '#skF_4') | ~v1_zfmisc_1(A_177) | v1_xboole_0(A_177) | ~m1_subset_1('#skF_1'(A_177), '#skF_5'))), inference(resolution, [status(thm)], [c_669, c_1210])).
% 5.06/1.93  tff(c_1455, plain, (v2_tex_2('#skF_5', '#skF_4') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_244, c_1443])).
% 5.06/1.93  tff(c_1467, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_1455])).
% 5.06/1.93  tff(c_1469, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_92, c_1467])).
% 5.06/1.93  tff(c_1470, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_198])).
% 5.06/1.93  tff(c_1471, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_198])).
% 5.06/1.93  tff(c_1484, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1470, c_1471])).
% 5.06/1.93  tff(c_1485, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_1484])).
% 5.06/1.93  tff(c_1486, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_86])).
% 5.06/1.93  tff(c_2899, plain, (![A_313, B_314]: (m1_pre_topc('#skF_3'(A_313, B_314), A_313) | ~v2_tex_2(B_314, A_313) | ~m1_subset_1(B_314, k1_zfmisc_1(u1_struct_0(A_313))) | v1_xboole_0(B_314) | ~l1_pre_topc(A_313) | ~v2_pre_topc(A_313) | v2_struct_0(A_313))), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.06/1.94  tff(c_2919, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_68, c_2899])).
% 5.06/1.94  tff(c_2928, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_1486, c_2919])).
% 5.06/1.94  tff(c_2929, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_78, c_70, c_2928])).
% 5.06/1.94  tff(c_36, plain, (![B_21, A_19]: (l1_pre_topc(B_21) | ~m1_pre_topc(B_21, A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.06/1.94  tff(c_2935, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_2929, c_36])).
% 5.06/1.94  tff(c_2942, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2935])).
% 5.06/1.94  tff(c_34, plain, (![A_18]: (l1_struct_0(A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.06/1.94  tff(c_2451, plain, (![A_289, B_290]: (~v2_struct_0('#skF_3'(A_289, B_290)) | ~v2_tex_2(B_290, A_289) | ~m1_subset_1(B_290, k1_zfmisc_1(u1_struct_0(A_289))) | v1_xboole_0(B_290) | ~l1_pre_topc(A_289) | ~v2_pre_topc(A_289) | v2_struct_0(A_289))), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.06/1.94  tff(c_2478, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_68, c_2451])).
% 5.06/1.94  tff(c_2487, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_1486, c_2478])).
% 5.06/1.94  tff(c_2488, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_78, c_70, c_2487])).
% 5.06/1.94  tff(c_74, plain, (v2_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 5.06/1.94  tff(c_52, plain, (![B_30, A_28]: (v2_tdlat_3(B_30) | ~m1_pre_topc(B_30, A_28) | ~l1_pre_topc(A_28) | ~v2_tdlat_3(A_28) | ~v2_pre_topc(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.06/1.94  tff(c_2932, plain, (v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_2929, c_52])).
% 5.06/1.94  tff(c_2938, plain, (v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_2932])).
% 5.06/1.94  tff(c_2939, plain, (v2_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_78, c_2938])).
% 5.06/1.94  tff(c_44, plain, (![A_26]: (v2_pre_topc(A_26) | ~v2_tdlat_3(A_26) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.06/1.94  tff(c_2946, plain, (v2_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_2939, c_44])).
% 5.06/1.94  tff(c_2948, plain, (v2_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2942, c_2946])).
% 5.06/1.94  tff(c_2211, plain, (![A_277, B_278]: (v1_tdlat_3('#skF_3'(A_277, B_278)) | ~v2_tex_2(B_278, A_277) | ~m1_subset_1(B_278, k1_zfmisc_1(u1_struct_0(A_277))) | v1_xboole_0(B_278) | ~l1_pre_topc(A_277) | ~v2_pre_topc(A_277) | v2_struct_0(A_277))), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.06/1.94  tff(c_2234, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_68, c_2211])).
% 5.06/1.94  tff(c_2242, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_1486, c_2234])).
% 5.06/1.94  tff(c_2243, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_78, c_70, c_2242])).
% 5.06/1.94  tff(c_48, plain, (![A_27]: (v7_struct_0(A_27) | ~v2_tdlat_3(A_27) | ~v1_tdlat_3(A_27) | ~v2_pre_topc(A_27) | v2_struct_0(A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.06/1.94  tff(c_1487, plain, (~v1_zfmisc_1('#skF_5')), inference(splitRight, [status(thm)], [c_86])).
% 5.06/1.94  tff(c_3127, plain, (![A_324, B_325]: (u1_struct_0('#skF_3'(A_324, B_325))=B_325 | ~v2_tex_2(B_325, A_324) | ~m1_subset_1(B_325, k1_zfmisc_1(u1_struct_0(A_324))) | v1_xboole_0(B_325) | ~l1_pre_topc(A_324) | ~v2_pre_topc(A_324) | v2_struct_0(A_324))), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.06/1.94  tff(c_3154, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_68, c_3127])).
% 5.06/1.94  tff(c_3163, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_1486, c_3154])).
% 5.06/1.94  tff(c_3164, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_78, c_70, c_3163])).
% 5.06/1.94  tff(c_38, plain, (![A_22]: (v1_zfmisc_1(u1_struct_0(A_22)) | ~l1_struct_0(A_22) | ~v7_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.06/1.94  tff(c_3185, plain, (v1_zfmisc_1('#skF_5') | ~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3164, c_38])).
% 5.06/1.94  tff(c_3206, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_1487, c_3185])).
% 5.06/1.94  tff(c_3208, plain, (~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_3206])).
% 5.06/1.94  tff(c_3211, plain, (~v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_48, c_3208])).
% 5.06/1.94  tff(c_3214, plain, (v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2942, c_2948, c_2243, c_2939, c_3211])).
% 5.06/1.94  tff(c_3216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2488, c_3214])).
% 5.06/1.94  tff(c_3217, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_3206])).
% 5.06/1.94  tff(c_3227, plain, (~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_34, c_3217])).
% 5.06/1.94  tff(c_3231, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2942, c_3227])).
% 5.06/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.06/1.94  
% 5.06/1.94  Inference rules
% 5.06/1.94  ----------------------
% 5.06/1.94  #Ref     : 0
% 5.06/1.94  #Sup     : 665
% 5.06/1.94  #Fact    : 0
% 5.06/1.94  #Define  : 0
% 5.06/1.94  #Split   : 11
% 5.06/1.94  #Chain   : 0
% 5.06/1.94  #Close   : 0
% 5.06/1.94  
% 5.06/1.94  Ordering : KBO
% 5.06/1.94  
% 5.06/1.94  Simplification rules
% 5.06/1.94  ----------------------
% 5.06/1.94  #Subsume      : 169
% 5.06/1.94  #Demod        : 102
% 5.06/1.94  #Tautology    : 141
% 5.06/1.94  #SimpNegUnit  : 159
% 5.06/1.94  #BackRed      : 3
% 5.06/1.94  
% 5.06/1.94  #Partial instantiations: 0
% 5.06/1.94  #Strategies tried      : 1
% 5.06/1.94  
% 5.06/1.94  Timing (in seconds)
% 5.06/1.94  ----------------------
% 5.06/1.94  Preprocessing        : 0.36
% 5.06/1.94  Parsing              : 0.19
% 5.06/1.94  CNF conversion       : 0.03
% 5.06/1.94  Main loop            : 0.78
% 5.06/1.94  Inferencing          : 0.28
% 5.06/1.94  Reduction            : 0.21
% 5.06/1.94  Demodulation         : 0.13
% 5.06/1.94  BG Simplification    : 0.04
% 5.06/1.94  Subsumption          : 0.19
% 5.06/1.94  Abstraction          : 0.04
% 5.06/1.94  MUC search           : 0.00
% 5.06/1.94  Cooper               : 0.00
% 5.06/1.94  Total                : 1.19
% 5.06/1.94  Index Insertion      : 0.00
% 5.06/1.94  Index Deletion       : 0.00
% 5.06/1.94  Index Matching       : 0.00
% 5.06/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
