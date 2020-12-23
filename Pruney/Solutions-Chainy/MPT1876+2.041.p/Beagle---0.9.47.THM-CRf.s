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
% DateTime   : Thu Dec  3 10:29:56 EST 2020

% Result     : Theorem 5.37s
% Output     : CNFRefutation 5.37s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 649 expanded)
%              Number of leaves         :   42 ( 238 expanded)
%              Depth                    :   26
%              Number of atoms          :  373 (1974 expanded)
%              Number of equality atoms :   18 (  61 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

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

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_190,negated_conjecture,(
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

tff(f_41,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_129,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_62,axiom,(
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

tff(f_58,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_170,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_158,axiom,(
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

tff(f_79,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_116,axiom,(
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

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(c_30,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_66,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_62,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_76,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_79,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_70,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_81,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_70])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_10] : ~ v1_xboole_0(k1_tarski(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(k1_tarski(A_11),B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_305,plain,(
    ! [B_91,A_92] :
      ( B_91 = A_92
      | ~ r1_tarski(A_92,B_91)
      | ~ v1_zfmisc_1(B_91)
      | v1_xboole_0(B_91)
      | v1_xboole_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_317,plain,(
    ! [A_11,B_12] :
      ( k1_tarski(A_11) = B_12
      | ~ v1_zfmisc_1(B_12)
      | v1_xboole_0(B_12)
      | v1_xboole_0(k1_tarski(A_11))
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(resolution,[status(thm)],[c_16,c_305])).

tff(c_368,plain,(
    ! [A_97,B_98] :
      ( k1_tarski(A_97) = B_98
      | ~ v1_zfmisc_1(B_98)
      | v1_xboole_0(B_98)
      | ~ r2_hidden(A_97,B_98) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_317])).

tff(c_391,plain,(
    ! [A_1] :
      ( k1_tarski('#skF_1'(A_1)) = A_1
      | ~ v1_zfmisc_1(A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_368])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_95,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,B_48)
      | ~ m1_subset_1(A_47,k1_zfmisc_1(B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_99,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_58,c_95])).

tff(c_207,plain,(
    ! [C_78,B_79,A_80] :
      ( r2_hidden(C_78,B_79)
      | ~ r2_hidden(C_78,A_80)
      | ~ r1_tarski(A_80,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_221,plain,(
    ! [A_82,B_83] :
      ( r2_hidden('#skF_1'(A_82),B_83)
      | ~ r1_tarski(A_82,B_83)
      | v1_xboole_0(A_82) ) ),
    inference(resolution,[status(thm)],[c_4,c_207])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_233,plain,(
    ! [B_84,A_85] :
      ( ~ v1_xboole_0(B_84)
      | ~ r1_tarski(A_85,B_84)
      | v1_xboole_0(A_85) ) ),
    inference(resolution,[status(thm)],[c_221,c_2])).

tff(c_248,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_99,c_233])).

tff(c_256,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_248])).

tff(c_139,plain,(
    ! [B_64,A_65] :
      ( m1_subset_1(B_64,A_65)
      | ~ r2_hidden(B_64,A_65)
      | v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_147,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_139])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( r2_hidden(B_14,A_13)
      | ~ m1_subset_1(B_14,A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_454,plain,(
    ! [B_104,B_105,A_106] :
      ( r2_hidden(B_104,B_105)
      | ~ r1_tarski(A_106,B_105)
      | ~ m1_subset_1(B_104,A_106)
      | v1_xboole_0(A_106) ) ),
    inference(resolution,[status(thm)],[c_20,c_207])).

tff(c_462,plain,(
    ! [B_104,B_12,A_11] :
      ( r2_hidden(B_104,B_12)
      | ~ m1_subset_1(B_104,k1_tarski(A_11))
      | v1_xboole_0(k1_tarski(A_11))
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(resolution,[status(thm)],[c_16,c_454])).

tff(c_548,plain,(
    ! [B_110,B_111,A_112] :
      ( r2_hidden(B_110,B_111)
      | ~ m1_subset_1(B_110,k1_tarski(A_112))
      | ~ r2_hidden(A_112,B_111) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_462])).

tff(c_558,plain,(
    ! [A_112,B_111] :
      ( r2_hidden('#skF_1'(k1_tarski(A_112)),B_111)
      | ~ r2_hidden(A_112,B_111)
      | v1_xboole_0(k1_tarski(A_112)) ) ),
    inference(resolution,[status(thm)],[c_147,c_548])).

tff(c_570,plain,(
    ! [A_113,B_114] :
      ( r2_hidden('#skF_1'(k1_tarski(A_113)),B_114)
      | ~ r2_hidden(A_113,B_114) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_558])).

tff(c_327,plain,(
    ! [A_11,B_12] :
      ( k1_tarski(A_11) = B_12
      | ~ v1_zfmisc_1(B_12)
      | v1_xboole_0(B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_317])).

tff(c_1522,plain,(
    ! [A_171,B_172] :
      ( k1_tarski('#skF_1'(k1_tarski(A_171))) = B_172
      | ~ v1_zfmisc_1(B_172)
      | v1_xboole_0(B_172)
      | ~ r2_hidden(A_171,B_172) ) ),
    inference(resolution,[status(thm)],[c_570,c_327])).

tff(c_1808,plain,(
    ! [A_178] :
      ( k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_178)))) = A_178
      | ~ v1_zfmisc_1(A_178)
      | v1_xboole_0(A_178) ) ),
    inference(resolution,[status(thm)],[c_4,c_1522])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_173,plain,(
    ! [A_71,B_72] :
      ( ~ r2_hidden('#skF_2'(A_71,B_72),B_72)
      | r1_tarski(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_184,plain,(
    ! [A_73] : r1_tarski(A_73,A_73) ),
    inference(resolution,[status(thm)],[c_10,c_173])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | ~ r1_tarski(k1_tarski(A_11),B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_190,plain,(
    ! [A_74] : r2_hidden(A_74,k1_tarski(A_74)) ),
    inference(resolution,[status(thm)],[c_184,c_14])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( m1_subset_1(B_14,A_13)
      | ~ r2_hidden(B_14,A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_193,plain,(
    ! [A_74] :
      ( m1_subset_1(A_74,k1_tarski(A_74))
      | v1_xboole_0(k1_tarski(A_74)) ) ),
    inference(resolution,[status(thm)],[c_190,c_18])).

tff(c_199,plain,(
    ! [A_74] : m1_subset_1(A_74,k1_tarski(A_74)) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_193])).

tff(c_1934,plain,(
    ! [A_179] :
      ( m1_subset_1('#skF_1'(k1_tarski('#skF_1'(A_179))),A_179)
      | ~ v1_zfmisc_1(A_179)
      | v1_xboole_0(A_179) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1808,c_199])).

tff(c_464,plain,(
    ! [B_104] :
      ( r2_hidden(B_104,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_104,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_99,c_454])).

tff(c_473,plain,(
    ! [B_104] :
      ( r2_hidden(B_104,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_104,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_464])).

tff(c_189,plain,(
    ! [A_11] : r2_hidden(A_11,k1_tarski(A_11)) ),
    inference(resolution,[status(thm)],[c_184,c_14])).

tff(c_392,plain,(
    ! [A_99] :
      ( k1_tarski('#skF_1'(A_99)) = A_99
      | ~ v1_zfmisc_1(A_99)
      | v1_xboole_0(A_99) ) ),
    inference(resolution,[status(thm)],[c_4,c_368])).

tff(c_718,plain,(
    ! [A_133,B_134] :
      ( r1_tarski(A_133,B_134)
      | ~ r2_hidden('#skF_1'(A_133),B_134)
      | ~ v1_zfmisc_1(A_133)
      | v1_xboole_0(A_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_392,c_16])).

tff(c_786,plain,(
    ! [A_137] :
      ( r1_tarski(A_137,k1_tarski('#skF_1'(A_137)))
      | ~ v1_zfmisc_1(A_137)
      | v1_xboole_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_189,c_718])).

tff(c_803,plain,(
    ! [A_11] :
      ( r2_hidden(A_11,k1_tarski('#skF_1'(k1_tarski(A_11))))
      | ~ v1_zfmisc_1(k1_tarski(A_11))
      | v1_xboole_0(k1_tarski(A_11)) ) ),
    inference(resolution,[status(thm)],[c_786,c_14])).

tff(c_818,plain,(
    ! [A_138] :
      ( r2_hidden(A_138,k1_tarski('#skF_1'(k1_tarski(A_138))))
      | ~ v1_zfmisc_1(k1_tarski(A_138)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_803])).

tff(c_830,plain,(
    ! [A_138] :
      ( m1_subset_1(A_138,k1_tarski('#skF_1'(k1_tarski(A_138))))
      | v1_xboole_0(k1_tarski('#skF_1'(k1_tarski(A_138))))
      | ~ v1_zfmisc_1(k1_tarski(A_138)) ) ),
    inference(resolution,[status(thm)],[c_818,c_18])).

tff(c_852,plain,(
    ! [A_139] :
      ( m1_subset_1(A_139,k1_tarski('#skF_1'(k1_tarski(A_139))))
      | ~ v1_zfmisc_1(k1_tarski(A_139)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_830])).

tff(c_470,plain,(
    ! [B_104,B_12,A_11] :
      ( r2_hidden(B_104,B_12)
      | ~ m1_subset_1(B_104,k1_tarski(A_11))
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_462])).

tff(c_1100,plain,(
    ! [A_151,B_152] :
      ( r2_hidden(A_151,B_152)
      | ~ r2_hidden('#skF_1'(k1_tarski(A_151)),B_152)
      | ~ v1_zfmisc_1(k1_tarski(A_151)) ) ),
    inference(resolution,[status(thm)],[c_852,c_470])).

tff(c_1142,plain,(
    ! [A_151] :
      ( r2_hidden(A_151,u1_struct_0('#skF_4'))
      | ~ v1_zfmisc_1(k1_tarski(A_151))
      | ~ m1_subset_1('#skF_1'(k1_tarski(A_151)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_473,c_1100])).

tff(c_1945,plain,
    ( r2_hidden('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1934,c_1142])).

tff(c_1983,plain,
    ( r2_hidden('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_1945])).

tff(c_1984,plain,
    ( r2_hidden('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1983])).

tff(c_1997,plain,(
    ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_1984])).

tff(c_2000,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_1997])).

tff(c_2002,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_79,c_2000])).

tff(c_2004,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2002])).

tff(c_2005,plain,(
    r2_hidden('#skF_1'('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1984])).

tff(c_2029,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2005,c_18])).

tff(c_2044,plain,(
    m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_256,c_2029])).

tff(c_36,plain,(
    ! [A_22,B_23] :
      ( k6_domain_1(A_22,B_23) = k1_tarski(B_23)
      | ~ m1_subset_1(B_23,A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2051,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')) = k1_tarski('#skF_1'('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2044,c_36])).

tff(c_2059,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')) = k1_tarski('#skF_1'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_256,c_2051])).

tff(c_56,plain,(
    ! [A_37,B_39] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_37),B_39),A_37)
      | ~ m1_subset_1(B_39,u1_struct_0(A_37))
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_2197,plain,
    ( v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2059,c_56])).

tff(c_2205,plain,
    ( v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_2044,c_2197])).

tff(c_2206,plain,(
    v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2205])).

tff(c_2211,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_2206])).

tff(c_2213,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_2211])).

tff(c_2215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_81,c_2213])).

tff(c_2216,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_3071,plain,(
    ! [A_286,B_287] :
      ( ~ v2_struct_0('#skF_3'(A_286,B_287))
      | ~ v2_tex_2(B_287,A_286)
      | ~ m1_subset_1(B_287,k1_zfmisc_1(u1_struct_0(A_286)))
      | v1_xboole_0(B_287)
      | ~ l1_pre_topc(A_286)
      | ~ v2_pre_topc(A_286)
      | v2_struct_0(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_3098,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_3071])).

tff(c_3107,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_2216,c_3098])).

tff(c_3108,plain,(
    ~ v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_60,c_3107])).

tff(c_2217,plain,(
    ~ v1_zfmisc_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_3583,plain,(
    ! [A_311,B_312] :
      ( u1_struct_0('#skF_3'(A_311,B_312)) = B_312
      | ~ v2_tex_2(B_312,A_311)
      | ~ m1_subset_1(B_312,k1_zfmisc_1(u1_struct_0(A_311)))
      | v1_xboole_0(B_312)
      | ~ l1_pre_topc(A_311)
      | ~ v2_pre_topc(A_311)
      | v2_struct_0(A_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_3610,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_3583])).

tff(c_3619,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_2216,c_3610])).

tff(c_3620,plain,(
    u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_60,c_3619])).

tff(c_34,plain,(
    ! [A_21] :
      ( v1_zfmisc_1(u1_struct_0(A_21))
      | ~ l1_struct_0(A_21)
      | ~ v7_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3639,plain,
    ( v1_zfmisc_1('#skF_5')
    | ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3620,c_34])).

tff(c_3648,plain,
    ( ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_2217,c_3639])).

tff(c_3650,plain,(
    ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_3648])).

tff(c_64,plain,(
    v2_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_2806,plain,(
    ! [A_271,B_272] :
      ( v1_tdlat_3('#skF_3'(A_271,B_272))
      | ~ v2_tex_2(B_272,A_271)
      | ~ m1_subset_1(B_272,k1_zfmisc_1(u1_struct_0(A_271)))
      | v1_xboole_0(B_272)
      | ~ l1_pre_topc(A_271)
      | ~ v2_pre_topc(A_271)
      | v2_struct_0(A_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_2825,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_2806])).

tff(c_2832,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_2216,c_2825])).

tff(c_2833,plain,(
    v1_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_60,c_2832])).

tff(c_3781,plain,(
    ! [A_318,B_319] :
      ( m1_pre_topc('#skF_3'(A_318,B_319),A_318)
      | ~ v2_tex_2(B_319,A_318)
      | ~ m1_subset_1(B_319,k1_zfmisc_1(u1_struct_0(A_318)))
      | v1_xboole_0(B_319)
      | ~ l1_pre_topc(A_318)
      | ~ v2_pre_topc(A_318)
      | v2_struct_0(A_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_3803,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_3781])).

tff(c_3813,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_2216,c_3803])).

tff(c_3814,plain,(
    m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_60,c_3813])).

tff(c_40,plain,(
    ! [B_27,A_25] :
      ( ~ v1_tdlat_3(B_27)
      | v7_struct_0(B_27)
      | v2_struct_0(B_27)
      | ~ m1_pre_topc(B_27,A_25)
      | ~ l1_pre_topc(A_25)
      | ~ v2_tdlat_3(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_3817,plain,
    ( ~ v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v7_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_3814,c_40])).

tff(c_3823,plain,
    ( v7_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_2833,c_3817])).

tff(c_3825,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3108,c_3650,c_3823])).

tff(c_3826,plain,(
    ~ l1_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_3648])).

tff(c_3831,plain,(
    ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_30,c_3826])).

tff(c_3962,plain,(
    ! [A_325,B_326] :
      ( m1_pre_topc('#skF_3'(A_325,B_326),A_325)
      | ~ v2_tex_2(B_326,A_325)
      | ~ m1_subset_1(B_326,k1_zfmisc_1(u1_struct_0(A_325)))
      | v1_xboole_0(B_326)
      | ~ l1_pre_topc(A_325)
      | ~ v2_pre_topc(A_325)
      | v2_struct_0(A_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_3984,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_3962])).

tff(c_3994,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_2216,c_3984])).

tff(c_3995,plain,(
    m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_60,c_3994])).

tff(c_32,plain,(
    ! [B_20,A_18] :
      ( l1_pre_topc(B_20)
      | ~ m1_pre_topc(B_20,A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4001,plain,
    ( l1_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_3995,c_32])).

tff(c_4008,plain,(
    l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4001])).

tff(c_4010,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3831,c_4008])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:19:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.37/2.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.37/2.02  
% 5.37/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.37/2.02  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 5.37/2.02  
% 5.37/2.02  %Foreground sorts:
% 5.37/2.02  
% 5.37/2.02  
% 5.37/2.02  %Background operators:
% 5.37/2.02  
% 5.37/2.02  
% 5.37/2.02  %Foreground operators:
% 5.37/2.02  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.37/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.37/2.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.37/2.02  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.37/2.02  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.37/2.02  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 5.37/2.02  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.37/2.02  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 5.37/2.02  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.37/2.02  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 5.37/2.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.37/2.02  tff('#skF_5', type, '#skF_5': $i).
% 5.37/2.02  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 5.37/2.02  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 5.37/2.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.37/2.02  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.37/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.37/2.02  tff('#skF_4', type, '#skF_4': $i).
% 5.37/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.37/2.02  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.37/2.02  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 5.37/2.02  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.37/2.02  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.37/2.02  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.37/2.02  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.37/2.02  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 5.37/2.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.37/2.02  
% 5.37/2.05  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.37/2.05  tff(f_190, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 5.37/2.05  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.37/2.05  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 5.37/2.05  tff(f_45, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 5.37/2.05  tff(f_129, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 5.37/2.05  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.37/2.05  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.37/2.05  tff(f_58, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 5.37/2.05  tff(f_86, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 5.37/2.05  tff(f_170, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 5.37/2.05  tff(f_158, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tex_2)).
% 5.37/2.05  tff(f_79, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 5.37/2.05  tff(f_116, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((~v2_struct_0(B) & ~v7_struct_0(B)) => (~v2_struct_0(B) & ~v1_tdlat_3(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc32_tex_2)).
% 5.37/2.05  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.37/2.05  tff(c_30, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.37/2.05  tff(c_68, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_190])).
% 5.37/2.05  tff(c_60, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_190])).
% 5.37/2.05  tff(c_66, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_190])).
% 5.37/2.05  tff(c_62, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_190])).
% 5.37/2.05  tff(c_76, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_190])).
% 5.37/2.05  tff(c_79, plain, (v1_zfmisc_1('#skF_5')), inference(splitLeft, [status(thm)], [c_76])).
% 5.37/2.05  tff(c_70, plain, (~v1_zfmisc_1('#skF_5') | ~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_190])).
% 5.37/2.05  tff(c_81, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_70])).
% 5.37/2.05  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.37/2.05  tff(c_12, plain, (![A_10]: (~v1_xboole_0(k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.37/2.05  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(k1_tarski(A_11), B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.37/2.05  tff(c_305, plain, (![B_91, A_92]: (B_91=A_92 | ~r1_tarski(A_92, B_91) | ~v1_zfmisc_1(B_91) | v1_xboole_0(B_91) | v1_xboole_0(A_92))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.37/2.05  tff(c_317, plain, (![A_11, B_12]: (k1_tarski(A_11)=B_12 | ~v1_zfmisc_1(B_12) | v1_xboole_0(B_12) | v1_xboole_0(k1_tarski(A_11)) | ~r2_hidden(A_11, B_12))), inference(resolution, [status(thm)], [c_16, c_305])).
% 5.37/2.05  tff(c_368, plain, (![A_97, B_98]: (k1_tarski(A_97)=B_98 | ~v1_zfmisc_1(B_98) | v1_xboole_0(B_98) | ~r2_hidden(A_97, B_98))), inference(negUnitSimplification, [status(thm)], [c_12, c_317])).
% 5.37/2.05  tff(c_391, plain, (![A_1]: (k1_tarski('#skF_1'(A_1))=A_1 | ~v1_zfmisc_1(A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_368])).
% 5.37/2.05  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_190])).
% 5.37/2.05  tff(c_95, plain, (![A_47, B_48]: (r1_tarski(A_47, B_48) | ~m1_subset_1(A_47, k1_zfmisc_1(B_48)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.37/2.05  tff(c_99, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_95])).
% 5.37/2.05  tff(c_207, plain, (![C_78, B_79, A_80]: (r2_hidden(C_78, B_79) | ~r2_hidden(C_78, A_80) | ~r1_tarski(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.37/2.05  tff(c_221, plain, (![A_82, B_83]: (r2_hidden('#skF_1'(A_82), B_83) | ~r1_tarski(A_82, B_83) | v1_xboole_0(A_82))), inference(resolution, [status(thm)], [c_4, c_207])).
% 5.37/2.05  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.37/2.05  tff(c_233, plain, (![B_84, A_85]: (~v1_xboole_0(B_84) | ~r1_tarski(A_85, B_84) | v1_xboole_0(A_85))), inference(resolution, [status(thm)], [c_221, c_2])).
% 5.37/2.05  tff(c_248, plain, (~v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_99, c_233])).
% 5.37/2.05  tff(c_256, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_60, c_248])).
% 5.37/2.05  tff(c_139, plain, (![B_64, A_65]: (m1_subset_1(B_64, A_65) | ~r2_hidden(B_64, A_65) | v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.37/2.05  tff(c_147, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_139])).
% 5.37/2.05  tff(c_20, plain, (![B_14, A_13]: (r2_hidden(B_14, A_13) | ~m1_subset_1(B_14, A_13) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.37/2.05  tff(c_454, plain, (![B_104, B_105, A_106]: (r2_hidden(B_104, B_105) | ~r1_tarski(A_106, B_105) | ~m1_subset_1(B_104, A_106) | v1_xboole_0(A_106))), inference(resolution, [status(thm)], [c_20, c_207])).
% 5.37/2.05  tff(c_462, plain, (![B_104, B_12, A_11]: (r2_hidden(B_104, B_12) | ~m1_subset_1(B_104, k1_tarski(A_11)) | v1_xboole_0(k1_tarski(A_11)) | ~r2_hidden(A_11, B_12))), inference(resolution, [status(thm)], [c_16, c_454])).
% 5.37/2.05  tff(c_548, plain, (![B_110, B_111, A_112]: (r2_hidden(B_110, B_111) | ~m1_subset_1(B_110, k1_tarski(A_112)) | ~r2_hidden(A_112, B_111))), inference(negUnitSimplification, [status(thm)], [c_12, c_462])).
% 5.37/2.05  tff(c_558, plain, (![A_112, B_111]: (r2_hidden('#skF_1'(k1_tarski(A_112)), B_111) | ~r2_hidden(A_112, B_111) | v1_xboole_0(k1_tarski(A_112)))), inference(resolution, [status(thm)], [c_147, c_548])).
% 5.37/2.05  tff(c_570, plain, (![A_113, B_114]: (r2_hidden('#skF_1'(k1_tarski(A_113)), B_114) | ~r2_hidden(A_113, B_114))), inference(negUnitSimplification, [status(thm)], [c_12, c_558])).
% 5.37/2.05  tff(c_327, plain, (![A_11, B_12]: (k1_tarski(A_11)=B_12 | ~v1_zfmisc_1(B_12) | v1_xboole_0(B_12) | ~r2_hidden(A_11, B_12))), inference(negUnitSimplification, [status(thm)], [c_12, c_317])).
% 5.37/2.05  tff(c_1522, plain, (![A_171, B_172]: (k1_tarski('#skF_1'(k1_tarski(A_171)))=B_172 | ~v1_zfmisc_1(B_172) | v1_xboole_0(B_172) | ~r2_hidden(A_171, B_172))), inference(resolution, [status(thm)], [c_570, c_327])).
% 5.37/2.05  tff(c_1808, plain, (![A_178]: (k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_178))))=A_178 | ~v1_zfmisc_1(A_178) | v1_xboole_0(A_178))), inference(resolution, [status(thm)], [c_4, c_1522])).
% 5.37/2.05  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.37/2.05  tff(c_173, plain, (![A_71, B_72]: (~r2_hidden('#skF_2'(A_71, B_72), B_72) | r1_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.37/2.05  tff(c_184, plain, (![A_73]: (r1_tarski(A_73, A_73))), inference(resolution, [status(thm)], [c_10, c_173])).
% 5.37/2.05  tff(c_14, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | ~r1_tarski(k1_tarski(A_11), B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.37/2.05  tff(c_190, plain, (![A_74]: (r2_hidden(A_74, k1_tarski(A_74)))), inference(resolution, [status(thm)], [c_184, c_14])).
% 5.37/2.05  tff(c_18, plain, (![B_14, A_13]: (m1_subset_1(B_14, A_13) | ~r2_hidden(B_14, A_13) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.37/2.05  tff(c_193, plain, (![A_74]: (m1_subset_1(A_74, k1_tarski(A_74)) | v1_xboole_0(k1_tarski(A_74)))), inference(resolution, [status(thm)], [c_190, c_18])).
% 5.37/2.05  tff(c_199, plain, (![A_74]: (m1_subset_1(A_74, k1_tarski(A_74)))), inference(negUnitSimplification, [status(thm)], [c_12, c_193])).
% 5.37/2.05  tff(c_1934, plain, (![A_179]: (m1_subset_1('#skF_1'(k1_tarski('#skF_1'(A_179))), A_179) | ~v1_zfmisc_1(A_179) | v1_xboole_0(A_179))), inference(superposition, [status(thm), theory('equality')], [c_1808, c_199])).
% 5.37/2.05  tff(c_464, plain, (![B_104]: (r2_hidden(B_104, u1_struct_0('#skF_4')) | ~m1_subset_1(B_104, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_99, c_454])).
% 5.37/2.05  tff(c_473, plain, (![B_104]: (r2_hidden(B_104, u1_struct_0('#skF_4')) | ~m1_subset_1(B_104, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_60, c_464])).
% 5.37/2.05  tff(c_189, plain, (![A_11]: (r2_hidden(A_11, k1_tarski(A_11)))), inference(resolution, [status(thm)], [c_184, c_14])).
% 5.37/2.05  tff(c_392, plain, (![A_99]: (k1_tarski('#skF_1'(A_99))=A_99 | ~v1_zfmisc_1(A_99) | v1_xboole_0(A_99))), inference(resolution, [status(thm)], [c_4, c_368])).
% 5.37/2.05  tff(c_718, plain, (![A_133, B_134]: (r1_tarski(A_133, B_134) | ~r2_hidden('#skF_1'(A_133), B_134) | ~v1_zfmisc_1(A_133) | v1_xboole_0(A_133))), inference(superposition, [status(thm), theory('equality')], [c_392, c_16])).
% 5.37/2.05  tff(c_786, plain, (![A_137]: (r1_tarski(A_137, k1_tarski('#skF_1'(A_137))) | ~v1_zfmisc_1(A_137) | v1_xboole_0(A_137))), inference(resolution, [status(thm)], [c_189, c_718])).
% 5.37/2.05  tff(c_803, plain, (![A_11]: (r2_hidden(A_11, k1_tarski('#skF_1'(k1_tarski(A_11)))) | ~v1_zfmisc_1(k1_tarski(A_11)) | v1_xboole_0(k1_tarski(A_11)))), inference(resolution, [status(thm)], [c_786, c_14])).
% 5.37/2.05  tff(c_818, plain, (![A_138]: (r2_hidden(A_138, k1_tarski('#skF_1'(k1_tarski(A_138)))) | ~v1_zfmisc_1(k1_tarski(A_138)))), inference(negUnitSimplification, [status(thm)], [c_12, c_803])).
% 5.37/2.05  tff(c_830, plain, (![A_138]: (m1_subset_1(A_138, k1_tarski('#skF_1'(k1_tarski(A_138)))) | v1_xboole_0(k1_tarski('#skF_1'(k1_tarski(A_138)))) | ~v1_zfmisc_1(k1_tarski(A_138)))), inference(resolution, [status(thm)], [c_818, c_18])).
% 5.37/2.05  tff(c_852, plain, (![A_139]: (m1_subset_1(A_139, k1_tarski('#skF_1'(k1_tarski(A_139)))) | ~v1_zfmisc_1(k1_tarski(A_139)))), inference(negUnitSimplification, [status(thm)], [c_12, c_830])).
% 5.37/2.05  tff(c_470, plain, (![B_104, B_12, A_11]: (r2_hidden(B_104, B_12) | ~m1_subset_1(B_104, k1_tarski(A_11)) | ~r2_hidden(A_11, B_12))), inference(negUnitSimplification, [status(thm)], [c_12, c_462])).
% 5.37/2.05  tff(c_1100, plain, (![A_151, B_152]: (r2_hidden(A_151, B_152) | ~r2_hidden('#skF_1'(k1_tarski(A_151)), B_152) | ~v1_zfmisc_1(k1_tarski(A_151)))), inference(resolution, [status(thm)], [c_852, c_470])).
% 5.37/2.05  tff(c_1142, plain, (![A_151]: (r2_hidden(A_151, u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski(A_151)) | ~m1_subset_1('#skF_1'(k1_tarski(A_151)), '#skF_5'))), inference(resolution, [status(thm)], [c_473, c_1100])).
% 5.37/2.05  tff(c_1945, plain, (r2_hidden('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_1934, c_1142])).
% 5.37/2.05  tff(c_1983, plain, (r2_hidden('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_1945])).
% 5.37/2.05  tff(c_1984, plain, (r2_hidden('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_1983])).
% 5.37/2.05  tff(c_1997, plain, (~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))), inference(splitLeft, [status(thm)], [c_1984])).
% 5.37/2.05  tff(c_2000, plain, (~v1_zfmisc_1('#skF_5') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_391, c_1997])).
% 5.37/2.05  tff(c_2002, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_79, c_2000])).
% 5.37/2.05  tff(c_2004, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_2002])).
% 5.37/2.05  tff(c_2005, plain, (r2_hidden('#skF_1'('#skF_5'), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_1984])).
% 5.37/2.05  tff(c_2029, plain, (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_2005, c_18])).
% 5.37/2.05  tff(c_2044, plain, (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_256, c_2029])).
% 5.37/2.05  tff(c_36, plain, (![A_22, B_23]: (k6_domain_1(A_22, B_23)=k1_tarski(B_23) | ~m1_subset_1(B_23, A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.37/2.05  tff(c_2051, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'('#skF_5'))=k1_tarski('#skF_1'('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_2044, c_36])).
% 5.37/2.05  tff(c_2059, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'('#skF_5'))=k1_tarski('#skF_1'('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_256, c_2051])).
% 5.37/2.05  tff(c_56, plain, (![A_37, B_39]: (v2_tex_2(k6_domain_1(u1_struct_0(A_37), B_39), A_37) | ~m1_subset_1(B_39, u1_struct_0(A_37)) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.37/2.05  tff(c_2197, plain, (v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2059, c_56])).
% 5.37/2.05  tff(c_2205, plain, (v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_2044, c_2197])).
% 5.37/2.05  tff(c_2206, plain, (v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_68, c_2205])).
% 5.37/2.05  tff(c_2211, plain, (v2_tex_2('#skF_5', '#skF_4') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_391, c_2206])).
% 5.37/2.05  tff(c_2213, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_2211])).
% 5.37/2.05  tff(c_2215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_81, c_2213])).
% 5.37/2.05  tff(c_2216, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_76])).
% 5.37/2.05  tff(c_3071, plain, (![A_286, B_287]: (~v2_struct_0('#skF_3'(A_286, B_287)) | ~v2_tex_2(B_287, A_286) | ~m1_subset_1(B_287, k1_zfmisc_1(u1_struct_0(A_286))) | v1_xboole_0(B_287) | ~l1_pre_topc(A_286) | ~v2_pre_topc(A_286) | v2_struct_0(A_286))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.37/2.05  tff(c_3098, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_58, c_3071])).
% 5.37/2.05  tff(c_3107, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_2216, c_3098])).
% 5.37/2.05  tff(c_3108, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_68, c_60, c_3107])).
% 5.37/2.05  tff(c_2217, plain, (~v1_zfmisc_1('#skF_5')), inference(splitRight, [status(thm)], [c_76])).
% 5.37/2.05  tff(c_3583, plain, (![A_311, B_312]: (u1_struct_0('#skF_3'(A_311, B_312))=B_312 | ~v2_tex_2(B_312, A_311) | ~m1_subset_1(B_312, k1_zfmisc_1(u1_struct_0(A_311))) | v1_xboole_0(B_312) | ~l1_pre_topc(A_311) | ~v2_pre_topc(A_311) | v2_struct_0(A_311))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.37/2.05  tff(c_3610, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_58, c_3583])).
% 5.37/2.05  tff(c_3619, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_2216, c_3610])).
% 5.37/2.05  tff(c_3620, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_68, c_60, c_3619])).
% 5.37/2.05  tff(c_34, plain, (![A_21]: (v1_zfmisc_1(u1_struct_0(A_21)) | ~l1_struct_0(A_21) | ~v7_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.37/2.05  tff(c_3639, plain, (v1_zfmisc_1('#skF_5') | ~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3620, c_34])).
% 5.37/2.05  tff(c_3648, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_2217, c_3639])).
% 5.37/2.05  tff(c_3650, plain, (~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_3648])).
% 5.37/2.05  tff(c_64, plain, (v2_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_190])).
% 5.37/2.05  tff(c_2806, plain, (![A_271, B_272]: (v1_tdlat_3('#skF_3'(A_271, B_272)) | ~v2_tex_2(B_272, A_271) | ~m1_subset_1(B_272, k1_zfmisc_1(u1_struct_0(A_271))) | v1_xboole_0(B_272) | ~l1_pre_topc(A_271) | ~v2_pre_topc(A_271) | v2_struct_0(A_271))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.37/2.05  tff(c_2825, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_58, c_2806])).
% 5.37/2.05  tff(c_2832, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_2216, c_2825])).
% 5.37/2.05  tff(c_2833, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_68, c_60, c_2832])).
% 5.37/2.05  tff(c_3781, plain, (![A_318, B_319]: (m1_pre_topc('#skF_3'(A_318, B_319), A_318) | ~v2_tex_2(B_319, A_318) | ~m1_subset_1(B_319, k1_zfmisc_1(u1_struct_0(A_318))) | v1_xboole_0(B_319) | ~l1_pre_topc(A_318) | ~v2_pre_topc(A_318) | v2_struct_0(A_318))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.37/2.05  tff(c_3803, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_58, c_3781])).
% 5.37/2.05  tff(c_3813, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_2216, c_3803])).
% 5.37/2.05  tff(c_3814, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_68, c_60, c_3813])).
% 5.37/2.05  tff(c_40, plain, (![B_27, A_25]: (~v1_tdlat_3(B_27) | v7_struct_0(B_27) | v2_struct_0(B_27) | ~m1_pre_topc(B_27, A_25) | ~l1_pre_topc(A_25) | ~v2_tdlat_3(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.37/2.05  tff(c_3817, plain, (~v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v7_struct_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_3814, c_40])).
% 5.37/2.05  tff(c_3823, plain, (v7_struct_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_2833, c_3817])).
% 5.37/2.05  tff(c_3825, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_3108, c_3650, c_3823])).
% 5.37/2.05  tff(c_3826, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_3648])).
% 5.37/2.05  tff(c_3831, plain, (~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_30, c_3826])).
% 5.37/2.05  tff(c_3962, plain, (![A_325, B_326]: (m1_pre_topc('#skF_3'(A_325, B_326), A_325) | ~v2_tex_2(B_326, A_325) | ~m1_subset_1(B_326, k1_zfmisc_1(u1_struct_0(A_325))) | v1_xboole_0(B_326) | ~l1_pre_topc(A_325) | ~v2_pre_topc(A_325) | v2_struct_0(A_325))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.37/2.05  tff(c_3984, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_58, c_3962])).
% 5.37/2.05  tff(c_3994, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_2216, c_3984])).
% 5.37/2.05  tff(c_3995, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_68, c_60, c_3994])).
% 5.37/2.05  tff(c_32, plain, (![B_20, A_18]: (l1_pre_topc(B_20) | ~m1_pre_topc(B_20, A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.37/2.05  tff(c_4001, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_3995, c_32])).
% 5.37/2.05  tff(c_4008, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4001])).
% 5.37/2.05  tff(c_4010, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3831, c_4008])).
% 5.37/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.37/2.05  
% 5.37/2.05  Inference rules
% 5.37/2.05  ----------------------
% 5.37/2.05  #Ref     : 0
% 5.37/2.05  #Sup     : 873
% 5.37/2.05  #Fact    : 0
% 5.37/2.05  #Define  : 0
% 5.37/2.05  #Split   : 9
% 5.37/2.05  #Chain   : 0
% 5.37/2.05  #Close   : 0
% 5.37/2.05  
% 5.37/2.05  Ordering : KBO
% 5.37/2.05  
% 5.37/2.05  Simplification rules
% 5.37/2.05  ----------------------
% 5.37/2.05  #Subsume      : 232
% 5.37/2.05  #Demod        : 105
% 5.37/2.05  #Tautology    : 182
% 5.37/2.05  #SimpNegUnit  : 223
% 5.37/2.05  #BackRed      : 0
% 5.37/2.05  
% 5.37/2.05  #Partial instantiations: 0
% 5.37/2.05  #Strategies tried      : 1
% 5.37/2.05  
% 5.37/2.05  Timing (in seconds)
% 5.37/2.05  ----------------------
% 5.37/2.05  Preprocessing        : 0.33
% 5.37/2.05  Parsing              : 0.18
% 5.37/2.05  CNF conversion       : 0.03
% 5.37/2.05  Main loop            : 0.94
% 5.37/2.05  Inferencing          : 0.34
% 5.37/2.05  Reduction            : 0.27
% 5.37/2.05  Demodulation         : 0.16
% 5.37/2.05  BG Simplification    : 0.04
% 5.37/2.05  Subsumption          : 0.21
% 5.37/2.05  Abstraction          : 0.05
% 5.37/2.05  MUC search           : 0.00
% 5.37/2.05  Cooper               : 0.00
% 5.37/2.05  Total                : 1.33
% 5.37/2.05  Index Insertion      : 0.00
% 5.37/2.05  Index Deletion       : 0.00
% 5.37/2.05  Index Matching       : 0.00
% 5.37/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
