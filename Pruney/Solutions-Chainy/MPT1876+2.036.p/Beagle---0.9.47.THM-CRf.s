%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:55 EST 2020

% Result     : Theorem 7.11s
% Output     : CNFRefutation 7.11s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 665 expanded)
%              Number of leaves         :   44 ( 247 expanded)
%              Depth                    :   23
%              Number of atoms          :  351 (2134 expanded)
%              Number of equality atoms :   18 (  79 expanded)
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

tff(f_189,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_41,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_128,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_169,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_157,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_115,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_tdlat_3(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_tdlat_3)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_tdlat_3(A)
       => v2_pre_topc(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & v2_tdlat_3(A) )
       => ( ~ v2_struct_0(A)
          & v7_struct_0(A)
          & v2_pre_topc(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

tff(c_60,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_64,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_68,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_77,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_74,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_78,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_74])).

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

tff(c_219,plain,(
    ! [B_82,A_83] :
      ( B_82 = A_83
      | ~ r1_tarski(A_83,B_82)
      | ~ v1_zfmisc_1(B_82)
      | v1_xboole_0(B_82)
      | v1_xboole_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_234,plain,(
    ! [A_11,B_12] :
      ( k1_tarski(A_11) = B_12
      | ~ v1_zfmisc_1(B_12)
      | v1_xboole_0(B_12)
      | v1_xboole_0(k1_tarski(A_11))
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(resolution,[status(thm)],[c_16,c_219])).

tff(c_304,plain,(
    ! [A_91,B_92] :
      ( k1_tarski(A_91) = B_92
      | ~ v1_zfmisc_1(B_92)
      | v1_xboole_0(B_92)
      | ~ r2_hidden(A_91,B_92) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_234])).

tff(c_323,plain,(
    ! [A_1] :
      ( k1_tarski('#skF_1'(A_1)) = A_1
      | ~ v1_zfmisc_1(A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_304])).

tff(c_136,plain,(
    ! [C_66,B_67,A_68] :
      ( r2_hidden(C_66,B_67)
      | ~ r2_hidden(C_66,A_68)
      | ~ r1_tarski(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_142,plain,(
    ! [A_1,B_67] :
      ( r2_hidden('#skF_1'(A_1),B_67)
      | ~ r1_tarski(A_1,B_67)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_136])).

tff(c_1158,plain,(
    ! [A_167,B_168] :
      ( k1_tarski('#skF_1'(A_167)) = B_168
      | ~ v1_zfmisc_1(B_168)
      | v1_xboole_0(B_168)
      | ~ r1_tarski(A_167,B_168)
      | v1_xboole_0(A_167) ) ),
    inference(resolution,[status(thm)],[c_142,c_304])).

tff(c_1184,plain,(
    ! [A_11,B_12] :
      ( k1_tarski('#skF_1'(k1_tarski(A_11))) = B_12
      | ~ v1_zfmisc_1(B_12)
      | v1_xboole_0(B_12)
      | v1_xboole_0(k1_tarski(A_11))
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(resolution,[status(thm)],[c_16,c_1158])).

tff(c_1205,plain,(
    ! [A_169,B_170] :
      ( k1_tarski('#skF_1'(k1_tarski(A_169))) = B_170
      | ~ v1_zfmisc_1(B_170)
      | v1_xboole_0(B_170)
      | ~ r2_hidden(A_169,B_170) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_1184])).

tff(c_1439,plain,(
    ! [A_176] :
      ( k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_176)))) = A_176
      | ~ v1_zfmisc_1(A_176)
      | v1_xboole_0(A_176) ) ),
    inference(resolution,[status(thm)],[c_4,c_1205])).

tff(c_122,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_2'(A_64,B_65),A_64)
      | r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_143,plain,(
    ! [A_69] : r1_tarski(A_69,A_69) ),
    inference(resolution,[status(thm)],[c_122,c_8])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | ~ r1_tarski(k1_tarski(A_11),B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_148,plain,(
    ! [A_11] : r2_hidden(A_11,k1_tarski(A_11)) ),
    inference(resolution,[status(thm)],[c_143,c_14])).

tff(c_1511,plain,(
    ! [A_176] :
      ( r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_176))),A_176)
      | ~ v1_zfmisc_1(A_176)
      | v1_xboole_0(A_176) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1439,c_148])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_106,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(A_59,B_60)
      | ~ m1_subset_1(A_59,k1_zfmisc_1(B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_119,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_106])).

tff(c_133,plain,(
    ! [A_64] : r1_tarski(A_64,A_64) ),
    inference(resolution,[status(thm)],[c_122,c_8])).

tff(c_207,plain,(
    ! [A_80,B_81] :
      ( r2_hidden('#skF_1'(A_80),B_81)
      | ~ r1_tarski(A_80,B_81)
      | v1_xboole_0(A_80) ) ),
    inference(resolution,[status(thm)],[c_4,c_136])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_690,plain,(
    ! [A_132,B_133,B_134] :
      ( r2_hidden('#skF_1'(A_132),B_133)
      | ~ r1_tarski(B_134,B_133)
      | ~ r1_tarski(A_132,B_134)
      | v1_xboole_0(A_132) ) ),
    inference(resolution,[status(thm)],[c_207,c_6])).

tff(c_2814,plain,(
    ! [A_201,B_202,A_203] :
      ( r2_hidden('#skF_1'(A_201),B_202)
      | ~ r1_tarski(A_201,k1_tarski(A_203))
      | v1_xboole_0(A_201)
      | ~ r2_hidden(A_203,B_202) ) ),
    inference(resolution,[status(thm)],[c_16,c_690])).

tff(c_2857,plain,(
    ! [A_203,B_202] :
      ( r2_hidden('#skF_1'(k1_tarski(A_203)),B_202)
      | v1_xboole_0(k1_tarski(A_203))
      | ~ r2_hidden(A_203,B_202) ) ),
    inference(resolution,[status(thm)],[c_133,c_2814])).

tff(c_2879,plain,(
    ! [A_204,B_205] :
      ( r2_hidden('#skF_1'(k1_tarski(A_204)),B_205)
      | ~ r2_hidden(A_204,B_205) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_2857])).

tff(c_3049,plain,(
    ! [A_211,B_212,B_213] :
      ( r2_hidden('#skF_1'(k1_tarski(A_211)),B_212)
      | ~ r1_tarski(B_213,B_212)
      | ~ r2_hidden(A_211,B_213) ) ),
    inference(resolution,[status(thm)],[c_2879,c_6])).

tff(c_3096,plain,(
    ! [A_211] :
      ( r2_hidden('#skF_1'(k1_tarski(A_211)),u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_211,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_119,c_3049])).

tff(c_4544,plain,(
    ! [A_254,B_255] :
      ( r1_tarski(A_254,B_255)
      | ~ r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_254))),B_255)
      | ~ v1_zfmisc_1(A_254)
      | v1_xboole_0(A_254) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1439,c_16])).

tff(c_5022,plain,(
    ! [A_264] :
      ( r1_tarski(A_264,u1_struct_0('#skF_4'))
      | ~ v1_zfmisc_1(A_264)
      | v1_xboole_0(A_264)
      | ~ r2_hidden('#skF_1'(A_264),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3096,c_4544])).

tff(c_5050,plain,
    ( r1_tarski(k1_tarski('#skF_1'('#skF_5')),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))
    | v1_xboole_0(k1_tarski('#skF_1'('#skF_5')))
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1511,c_5022])).

tff(c_5075,plain,
    ( r1_tarski(k1_tarski('#skF_1'('#skF_5')),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))
    | v1_xboole_0(k1_tarski('#skF_1'('#skF_5')))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_5050])).

tff(c_5076,plain,
    ( r1_tarski(k1_tarski('#skF_1'('#skF_5')),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_12,c_5075])).

tff(c_5082,plain,(
    ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_5076])).

tff(c_5085,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_5082])).

tff(c_5087,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_78,c_5085])).

tff(c_5089,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_5087])).

tff(c_5090,plain,(
    r1_tarski(k1_tarski('#skF_1'('#skF_5')),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_5076])).

tff(c_5178,plain,(
    r2_hidden('#skF_1'('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_5090,c_14])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,B_14)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_5274,plain,(
    m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_5178,c_18])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_245,plain,(
    ! [B_84,A_85] :
      ( ~ v1_xboole_0(B_84)
      | ~ r1_tarski(A_85,B_84)
      | v1_xboole_0(A_85) ) ),
    inference(resolution,[status(thm)],[c_207,c_2])).

tff(c_257,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_119,c_245])).

tff(c_266,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_257])).

tff(c_30,plain,(
    ! [A_22,B_23] :
      ( k6_domain_1(A_22,B_23) = k1_tarski(B_23)
      | ~ m1_subset_1(B_23,A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_5278,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')) = k1_tarski('#skF_1'('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_5274,c_30])).

tff(c_5281,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')) = k1_tarski('#skF_1'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_266,c_5278])).

tff(c_54,plain,(
    ! [A_38,B_40] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_38),B_40),A_38)
      | ~ m1_subset_1(B_40,u1_struct_0(A_38))
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_5404,plain,
    ( v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5281,c_54])).

tff(c_5415,plain,
    ( v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_5274,c_5404])).

tff(c_5416,plain,(
    v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_5415])).

tff(c_5424,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_5416])).

tff(c_5426,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_5424])).

tff(c_5428,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_77,c_5426])).

tff(c_5430,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_6167,plain,(
    ! [A_369,B_370] :
      ( m1_pre_topc('#skF_3'(A_369,B_370),A_369)
      | ~ v2_tex_2(B_370,A_369)
      | ~ m1_subset_1(B_370,k1_zfmisc_1(u1_struct_0(A_369)))
      | v1_xboole_0(B_370)
      | ~ l1_pre_topc(A_369)
      | ~ v2_pre_topc(A_369)
      | v2_struct_0(A_369) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_6184,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_6167])).

tff(c_6192,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_5430,c_6184])).

tff(c_6193,plain,(
    m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_6192])).

tff(c_26,plain,(
    ! [B_20,A_18] :
      ( l1_pre_topc(B_20)
      | ~ m1_pre_topc(B_20,A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6199,plain,
    ( l1_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6193,c_26])).

tff(c_6206,plain,(
    l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6199])).

tff(c_24,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_5865,plain,(
    ! [A_347,B_348] :
      ( ~ v2_struct_0('#skF_3'(A_347,B_348))
      | ~ v2_tex_2(B_348,A_347)
      | ~ m1_subset_1(B_348,k1_zfmisc_1(u1_struct_0(A_347)))
      | v1_xboole_0(B_348)
      | ~ l1_pre_topc(A_347)
      | ~ v2_pre_topc(A_347)
      | v2_struct_0(A_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_5888,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_5865])).

tff(c_5896,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_5430,c_5888])).

tff(c_5897,plain,(
    ~ v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_5896])).

tff(c_62,plain,(
    v2_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_40,plain,(
    ! [B_28,A_26] :
      ( v2_tdlat_3(B_28)
      | ~ m1_pre_topc(B_28,A_26)
      | ~ l1_pre_topc(A_26)
      | ~ v2_tdlat_3(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_6196,plain,
    ( v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_6193,c_40])).

tff(c_6202,plain,
    ( v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_6196])).

tff(c_6203,plain,(
    v2_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_6202])).

tff(c_32,plain,(
    ! [A_24] :
      ( v2_pre_topc(A_24)
      | ~ v2_tdlat_3(A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6210,plain,
    ( v2_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_6203,c_32])).

tff(c_6212,plain,(
    v2_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6206,c_6210])).

tff(c_5973,plain,(
    ! [A_355,B_356] :
      ( v1_tdlat_3('#skF_3'(A_355,B_356))
      | ~ v2_tex_2(B_356,A_355)
      | ~ m1_subset_1(B_356,k1_zfmisc_1(u1_struct_0(A_355)))
      | v1_xboole_0(B_356)
      | ~ l1_pre_topc(A_355)
      | ~ v2_pre_topc(A_355)
      | v2_struct_0(A_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_5996,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_5973])).

tff(c_6004,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_5430,c_5996])).

tff(c_6005,plain,(
    v1_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_6004])).

tff(c_36,plain,(
    ! [A_25] :
      ( v7_struct_0(A_25)
      | ~ v2_tdlat_3(A_25)
      | ~ v1_tdlat_3(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_5429,plain,(
    ~ v1_zfmisc_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_6306,plain,(
    ! [A_378,B_379] :
      ( u1_struct_0('#skF_3'(A_378,B_379)) = B_379
      | ~ v2_tex_2(B_379,A_378)
      | ~ m1_subset_1(B_379,k1_zfmisc_1(u1_struct_0(A_378)))
      | v1_xboole_0(B_379)
      | ~ l1_pre_topc(A_378)
      | ~ v2_pre_topc(A_378)
      | v2_struct_0(A_378) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_6329,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_6306])).

tff(c_6337,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_5430,c_6329])).

tff(c_6338,plain,(
    u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_6337])).

tff(c_28,plain,(
    ! [A_21] :
      ( v1_zfmisc_1(u1_struct_0(A_21))
      | ~ l1_struct_0(A_21)
      | ~ v7_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6359,plain,
    ( v1_zfmisc_1('#skF_5')
    | ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6338,c_28])).

tff(c_6380,plain,
    ( ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_5429,c_6359])).

tff(c_6382,plain,(
    ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_6380])).

tff(c_6385,plain,
    ( ~ v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_36,c_6382])).

tff(c_6388,plain,(
    v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6206,c_6212,c_6005,c_6203,c_6385])).

tff(c_6390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5897,c_6388])).

tff(c_6391,plain,(
    ~ l1_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_6380])).

tff(c_6401,plain,(
    ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_24,c_6391])).

tff(c_6405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6206,c_6401])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n015.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 10:52:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.11/2.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.11/2.46  
% 7.11/2.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.11/2.47  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 7.11/2.47  
% 7.11/2.47  %Foreground sorts:
% 7.11/2.47  
% 7.11/2.47  
% 7.11/2.47  %Background operators:
% 7.11/2.47  
% 7.11/2.47  
% 7.11/2.47  %Foreground operators:
% 7.11/2.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.11/2.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.11/2.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.11/2.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.11/2.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.11/2.47  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 7.11/2.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.11/2.47  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 7.11/2.47  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.11/2.47  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 7.11/2.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.11/2.47  tff('#skF_5', type, '#skF_5': $i).
% 7.11/2.47  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 7.11/2.47  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 7.11/2.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.11/2.47  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.11/2.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.11/2.47  tff('#skF_4', type, '#skF_4': $i).
% 7.11/2.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.11/2.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.11/2.47  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 7.11/2.47  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.11/2.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.11/2.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.11/2.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.11/2.47  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 7.11/2.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.11/2.47  
% 7.11/2.49  tff(f_189, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 7.11/2.49  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.11/2.49  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 7.11/2.49  tff(f_45, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 7.11/2.49  tff(f_128, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 7.11/2.49  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.11/2.49  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.11/2.49  tff(f_49, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 7.11/2.49  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 7.11/2.49  tff(f_169, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 7.11/2.49  tff(f_157, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tex_2)).
% 7.11/2.49  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 7.11/2.49  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.11/2.49  tff(f_115, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_tdlat_3(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_tdlat_3)).
% 7.11/2.49  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (v2_tdlat_3(A) => v2_pre_topc(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tdlat_3)).
% 7.11/2.49  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & v2_tdlat_3(A)) => ((~v2_struct_0(A) & v7_struct_0(A)) & v2_pre_topc(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_1)).
% 7.11/2.49  tff(f_70, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 7.11/2.49  tff(c_60, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.11/2.49  tff(c_66, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.11/2.49  tff(c_58, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.11/2.49  tff(c_64, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.11/2.49  tff(c_68, plain, (~v1_zfmisc_1('#skF_5') | ~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.11/2.49  tff(c_77, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_68])).
% 7.11/2.49  tff(c_74, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.11/2.49  tff(c_78, plain, (v1_zfmisc_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_77, c_74])).
% 7.11/2.49  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.11/2.49  tff(c_12, plain, (![A_10]: (~v1_xboole_0(k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.11/2.49  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(k1_tarski(A_11), B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.11/2.49  tff(c_219, plain, (![B_82, A_83]: (B_82=A_83 | ~r1_tarski(A_83, B_82) | ~v1_zfmisc_1(B_82) | v1_xboole_0(B_82) | v1_xboole_0(A_83))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.11/2.49  tff(c_234, plain, (![A_11, B_12]: (k1_tarski(A_11)=B_12 | ~v1_zfmisc_1(B_12) | v1_xboole_0(B_12) | v1_xboole_0(k1_tarski(A_11)) | ~r2_hidden(A_11, B_12))), inference(resolution, [status(thm)], [c_16, c_219])).
% 7.11/2.49  tff(c_304, plain, (![A_91, B_92]: (k1_tarski(A_91)=B_92 | ~v1_zfmisc_1(B_92) | v1_xboole_0(B_92) | ~r2_hidden(A_91, B_92))), inference(negUnitSimplification, [status(thm)], [c_12, c_234])).
% 7.11/2.49  tff(c_323, plain, (![A_1]: (k1_tarski('#skF_1'(A_1))=A_1 | ~v1_zfmisc_1(A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_304])).
% 7.11/2.49  tff(c_136, plain, (![C_66, B_67, A_68]: (r2_hidden(C_66, B_67) | ~r2_hidden(C_66, A_68) | ~r1_tarski(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.11/2.49  tff(c_142, plain, (![A_1, B_67]: (r2_hidden('#skF_1'(A_1), B_67) | ~r1_tarski(A_1, B_67) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_136])).
% 7.11/2.49  tff(c_1158, plain, (![A_167, B_168]: (k1_tarski('#skF_1'(A_167))=B_168 | ~v1_zfmisc_1(B_168) | v1_xboole_0(B_168) | ~r1_tarski(A_167, B_168) | v1_xboole_0(A_167))), inference(resolution, [status(thm)], [c_142, c_304])).
% 7.11/2.49  tff(c_1184, plain, (![A_11, B_12]: (k1_tarski('#skF_1'(k1_tarski(A_11)))=B_12 | ~v1_zfmisc_1(B_12) | v1_xboole_0(B_12) | v1_xboole_0(k1_tarski(A_11)) | ~r2_hidden(A_11, B_12))), inference(resolution, [status(thm)], [c_16, c_1158])).
% 7.11/2.49  tff(c_1205, plain, (![A_169, B_170]: (k1_tarski('#skF_1'(k1_tarski(A_169)))=B_170 | ~v1_zfmisc_1(B_170) | v1_xboole_0(B_170) | ~r2_hidden(A_169, B_170))), inference(negUnitSimplification, [status(thm)], [c_12, c_1184])).
% 7.11/2.49  tff(c_1439, plain, (![A_176]: (k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_176))))=A_176 | ~v1_zfmisc_1(A_176) | v1_xboole_0(A_176))), inference(resolution, [status(thm)], [c_4, c_1205])).
% 7.11/2.49  tff(c_122, plain, (![A_64, B_65]: (r2_hidden('#skF_2'(A_64, B_65), A_64) | r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.11/2.49  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.11/2.49  tff(c_143, plain, (![A_69]: (r1_tarski(A_69, A_69))), inference(resolution, [status(thm)], [c_122, c_8])).
% 7.11/2.49  tff(c_14, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | ~r1_tarski(k1_tarski(A_11), B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.11/2.49  tff(c_148, plain, (![A_11]: (r2_hidden(A_11, k1_tarski(A_11)))), inference(resolution, [status(thm)], [c_143, c_14])).
% 7.11/2.49  tff(c_1511, plain, (![A_176]: (r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_176))), A_176) | ~v1_zfmisc_1(A_176) | v1_xboole_0(A_176))), inference(superposition, [status(thm), theory('equality')], [c_1439, c_148])).
% 7.11/2.49  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.11/2.49  tff(c_106, plain, (![A_59, B_60]: (r1_tarski(A_59, B_60) | ~m1_subset_1(A_59, k1_zfmisc_1(B_60)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.11/2.49  tff(c_119, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_106])).
% 7.11/2.49  tff(c_133, plain, (![A_64]: (r1_tarski(A_64, A_64))), inference(resolution, [status(thm)], [c_122, c_8])).
% 7.11/2.49  tff(c_207, plain, (![A_80, B_81]: (r2_hidden('#skF_1'(A_80), B_81) | ~r1_tarski(A_80, B_81) | v1_xboole_0(A_80))), inference(resolution, [status(thm)], [c_4, c_136])).
% 7.11/2.49  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.11/2.49  tff(c_690, plain, (![A_132, B_133, B_134]: (r2_hidden('#skF_1'(A_132), B_133) | ~r1_tarski(B_134, B_133) | ~r1_tarski(A_132, B_134) | v1_xboole_0(A_132))), inference(resolution, [status(thm)], [c_207, c_6])).
% 7.11/2.49  tff(c_2814, plain, (![A_201, B_202, A_203]: (r2_hidden('#skF_1'(A_201), B_202) | ~r1_tarski(A_201, k1_tarski(A_203)) | v1_xboole_0(A_201) | ~r2_hidden(A_203, B_202))), inference(resolution, [status(thm)], [c_16, c_690])).
% 7.11/2.49  tff(c_2857, plain, (![A_203, B_202]: (r2_hidden('#skF_1'(k1_tarski(A_203)), B_202) | v1_xboole_0(k1_tarski(A_203)) | ~r2_hidden(A_203, B_202))), inference(resolution, [status(thm)], [c_133, c_2814])).
% 7.11/2.49  tff(c_2879, plain, (![A_204, B_205]: (r2_hidden('#skF_1'(k1_tarski(A_204)), B_205) | ~r2_hidden(A_204, B_205))), inference(negUnitSimplification, [status(thm)], [c_12, c_2857])).
% 7.11/2.49  tff(c_3049, plain, (![A_211, B_212, B_213]: (r2_hidden('#skF_1'(k1_tarski(A_211)), B_212) | ~r1_tarski(B_213, B_212) | ~r2_hidden(A_211, B_213))), inference(resolution, [status(thm)], [c_2879, c_6])).
% 7.11/2.49  tff(c_3096, plain, (![A_211]: (r2_hidden('#skF_1'(k1_tarski(A_211)), u1_struct_0('#skF_4')) | ~r2_hidden(A_211, '#skF_5'))), inference(resolution, [status(thm)], [c_119, c_3049])).
% 7.11/2.49  tff(c_4544, plain, (![A_254, B_255]: (r1_tarski(A_254, B_255) | ~r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_254))), B_255) | ~v1_zfmisc_1(A_254) | v1_xboole_0(A_254))), inference(superposition, [status(thm), theory('equality')], [c_1439, c_16])).
% 7.11/2.49  tff(c_5022, plain, (![A_264]: (r1_tarski(A_264, u1_struct_0('#skF_4')) | ~v1_zfmisc_1(A_264) | v1_xboole_0(A_264) | ~r2_hidden('#skF_1'(A_264), '#skF_5'))), inference(resolution, [status(thm)], [c_3096, c_4544])).
% 7.11/2.49  tff(c_5050, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) | v1_xboole_0(k1_tarski('#skF_1'('#skF_5'))) | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_1511, c_5022])).
% 7.11/2.49  tff(c_5075, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) | v1_xboole_0(k1_tarski('#skF_1'('#skF_5'))) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_5050])).
% 7.11/2.49  tff(c_5076, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_12, c_5075])).
% 7.11/2.49  tff(c_5082, plain, (~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))), inference(splitLeft, [status(thm)], [c_5076])).
% 7.11/2.49  tff(c_5085, plain, (~v1_zfmisc_1('#skF_5') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_323, c_5082])).
% 7.11/2.49  tff(c_5087, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_78, c_5085])).
% 7.11/2.49  tff(c_5089, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_5087])).
% 7.11/2.49  tff(c_5090, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_5076])).
% 7.11/2.49  tff(c_5178, plain, (r2_hidden('#skF_1'('#skF_5'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_5090, c_14])).
% 7.11/2.49  tff(c_18, plain, (![A_13, B_14]: (m1_subset_1(A_13, B_14) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.11/2.49  tff(c_5274, plain, (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_5178, c_18])).
% 7.11/2.49  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.11/2.49  tff(c_245, plain, (![B_84, A_85]: (~v1_xboole_0(B_84) | ~r1_tarski(A_85, B_84) | v1_xboole_0(A_85))), inference(resolution, [status(thm)], [c_207, c_2])).
% 7.11/2.49  tff(c_257, plain, (~v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_119, c_245])).
% 7.11/2.49  tff(c_266, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_257])).
% 7.11/2.49  tff(c_30, plain, (![A_22, B_23]: (k6_domain_1(A_22, B_23)=k1_tarski(B_23) | ~m1_subset_1(B_23, A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.11/2.49  tff(c_5278, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'('#skF_5'))=k1_tarski('#skF_1'('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_5274, c_30])).
% 7.11/2.49  tff(c_5281, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'('#skF_5'))=k1_tarski('#skF_1'('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_266, c_5278])).
% 7.11/2.49  tff(c_54, plain, (![A_38, B_40]: (v2_tex_2(k6_domain_1(u1_struct_0(A_38), B_40), A_38) | ~m1_subset_1(B_40, u1_struct_0(A_38)) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_169])).
% 7.11/2.49  tff(c_5404, plain, (v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5281, c_54])).
% 7.11/2.49  tff(c_5415, plain, (v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_5274, c_5404])).
% 7.11/2.49  tff(c_5416, plain, (v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_66, c_5415])).
% 7.11/2.49  tff(c_5424, plain, (v2_tex_2('#skF_5', '#skF_4') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_323, c_5416])).
% 7.11/2.49  tff(c_5426, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_5424])).
% 7.11/2.49  tff(c_5428, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_77, c_5426])).
% 7.11/2.49  tff(c_5430, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_68])).
% 7.11/2.49  tff(c_6167, plain, (![A_369, B_370]: (m1_pre_topc('#skF_3'(A_369, B_370), A_369) | ~v2_tex_2(B_370, A_369) | ~m1_subset_1(B_370, k1_zfmisc_1(u1_struct_0(A_369))) | v1_xboole_0(B_370) | ~l1_pre_topc(A_369) | ~v2_pre_topc(A_369) | v2_struct_0(A_369))), inference(cnfTransformation, [status(thm)], [f_157])).
% 7.11/2.49  tff(c_6184, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_6167])).
% 7.11/2.49  tff(c_6192, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_5430, c_6184])).
% 7.11/2.49  tff(c_6193, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_6192])).
% 7.11/2.49  tff(c_26, plain, (![B_20, A_18]: (l1_pre_topc(B_20) | ~m1_pre_topc(B_20, A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.11/2.49  tff(c_6199, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6193, c_26])).
% 7.11/2.49  tff(c_6206, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_6199])).
% 7.11/2.49  tff(c_24, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.11/2.49  tff(c_5865, plain, (![A_347, B_348]: (~v2_struct_0('#skF_3'(A_347, B_348)) | ~v2_tex_2(B_348, A_347) | ~m1_subset_1(B_348, k1_zfmisc_1(u1_struct_0(A_347))) | v1_xboole_0(B_348) | ~l1_pre_topc(A_347) | ~v2_pre_topc(A_347) | v2_struct_0(A_347))), inference(cnfTransformation, [status(thm)], [f_157])).
% 7.11/2.49  tff(c_5888, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_5865])).
% 7.11/2.49  tff(c_5896, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_5430, c_5888])).
% 7.11/2.49  tff(c_5897, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_5896])).
% 7.11/2.49  tff(c_62, plain, (v2_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.11/2.49  tff(c_40, plain, (![B_28, A_26]: (v2_tdlat_3(B_28) | ~m1_pre_topc(B_28, A_26) | ~l1_pre_topc(A_26) | ~v2_tdlat_3(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.11/2.49  tff(c_6196, plain, (v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_6193, c_40])).
% 7.11/2.49  tff(c_6202, plain, (v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_6196])).
% 7.11/2.49  tff(c_6203, plain, (v2_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_6202])).
% 7.11/2.49  tff(c_32, plain, (![A_24]: (v2_pre_topc(A_24) | ~v2_tdlat_3(A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.11/2.49  tff(c_6210, plain, (v2_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_6203, c_32])).
% 7.11/2.49  tff(c_6212, plain, (v2_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_6206, c_6210])).
% 7.11/2.49  tff(c_5973, plain, (![A_355, B_356]: (v1_tdlat_3('#skF_3'(A_355, B_356)) | ~v2_tex_2(B_356, A_355) | ~m1_subset_1(B_356, k1_zfmisc_1(u1_struct_0(A_355))) | v1_xboole_0(B_356) | ~l1_pre_topc(A_355) | ~v2_pre_topc(A_355) | v2_struct_0(A_355))), inference(cnfTransformation, [status(thm)], [f_157])).
% 7.11/2.49  tff(c_5996, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_5973])).
% 7.11/2.49  tff(c_6004, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_5430, c_5996])).
% 7.11/2.49  tff(c_6005, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_6004])).
% 7.11/2.49  tff(c_36, plain, (![A_25]: (v7_struct_0(A_25) | ~v2_tdlat_3(A_25) | ~v1_tdlat_3(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.11/2.49  tff(c_5429, plain, (~v1_zfmisc_1('#skF_5')), inference(splitRight, [status(thm)], [c_68])).
% 7.11/2.49  tff(c_6306, plain, (![A_378, B_379]: (u1_struct_0('#skF_3'(A_378, B_379))=B_379 | ~v2_tex_2(B_379, A_378) | ~m1_subset_1(B_379, k1_zfmisc_1(u1_struct_0(A_378))) | v1_xboole_0(B_379) | ~l1_pre_topc(A_378) | ~v2_pre_topc(A_378) | v2_struct_0(A_378))), inference(cnfTransformation, [status(thm)], [f_157])).
% 7.11/2.49  tff(c_6329, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_6306])).
% 7.11/2.49  tff(c_6337, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_5430, c_6329])).
% 7.11/2.49  tff(c_6338, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_6337])).
% 7.11/2.49  tff(c_28, plain, (![A_21]: (v1_zfmisc_1(u1_struct_0(A_21)) | ~l1_struct_0(A_21) | ~v7_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.11/2.49  tff(c_6359, plain, (v1_zfmisc_1('#skF_5') | ~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_6338, c_28])).
% 7.11/2.49  tff(c_6380, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_5429, c_6359])).
% 7.11/2.49  tff(c_6382, plain, (~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_6380])).
% 7.11/2.49  tff(c_6385, plain, (~v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_36, c_6382])).
% 7.11/2.49  tff(c_6388, plain, (v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_6206, c_6212, c_6005, c_6203, c_6385])).
% 7.11/2.49  tff(c_6390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5897, c_6388])).
% 7.11/2.49  tff(c_6391, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_6380])).
% 7.11/2.49  tff(c_6401, plain, (~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_24, c_6391])).
% 7.11/2.49  tff(c_6405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6206, c_6401])).
% 7.11/2.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.11/2.49  
% 7.11/2.49  Inference rules
% 7.11/2.49  ----------------------
% 7.11/2.49  #Ref     : 0
% 7.11/2.49  #Sup     : 1479
% 7.11/2.49  #Fact    : 0
% 7.11/2.49  #Define  : 0
% 7.11/2.49  #Split   : 10
% 7.11/2.49  #Chain   : 0
% 7.11/2.49  #Close   : 0
% 7.11/2.49  
% 7.11/2.49  Ordering : KBO
% 7.11/2.49  
% 7.11/2.49  Simplification rules
% 7.11/2.49  ----------------------
% 7.11/2.49  #Subsume      : 379
% 7.11/2.49  #Demod        : 227
% 7.11/2.49  #Tautology    : 225
% 7.11/2.49  #SimpNegUnit  : 327
% 7.11/2.49  #BackRed      : 0
% 7.11/2.49  
% 7.11/2.49  #Partial instantiations: 0
% 7.11/2.49  #Strategies tried      : 1
% 7.11/2.49  
% 7.11/2.49  Timing (in seconds)
% 7.11/2.49  ----------------------
% 7.11/2.49  Preprocessing        : 0.35
% 7.11/2.49  Parsing              : 0.19
% 7.11/2.49  CNF conversion       : 0.02
% 7.11/2.49  Main loop            : 1.36
% 7.11/2.49  Inferencing          : 0.46
% 7.11/2.49  Reduction            : 0.38
% 7.11/2.49  Demodulation         : 0.22
% 7.11/2.49  BG Simplification    : 0.05
% 7.11/2.49  Subsumption          : 0.34
% 7.11/2.49  Abstraction          : 0.07
% 7.11/2.49  MUC search           : 0.00
% 7.11/2.49  Cooper               : 0.00
% 7.11/2.49  Total                : 1.76
% 7.11/2.49  Index Insertion      : 0.00
% 7.11/2.49  Index Deletion       : 0.00
% 7.11/2.49  Index Matching       : 0.00
% 7.11/2.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
