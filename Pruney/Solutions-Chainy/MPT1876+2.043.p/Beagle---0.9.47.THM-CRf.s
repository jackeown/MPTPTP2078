%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:56 EST 2020

% Result     : Theorem 6.67s
% Output     : CNFRefutation 6.95s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 690 expanded)
%              Number of leaves         :   42 ( 253 expanded)
%              Depth                    :   20
%              Number of atoms          :  381 (2091 expanded)
%              Number of equality atoms :   18 (  89 expanded)
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

tff(f_181,negated_conjecture,(
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

tff(f_120,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_161,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_149,axiom,(
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

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_107,axiom,(
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

tff(f_70,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(c_56,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_60,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_70,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_74,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_64,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_76,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_64])).

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

tff(c_271,plain,(
    ! [B_91,A_92] :
      ( B_91 = A_92
      | ~ r1_tarski(A_92,B_91)
      | ~ v1_zfmisc_1(B_91)
      | v1_xboole_0(B_91)
      | v1_xboole_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_289,plain,(
    ! [A_11,B_12] :
      ( k1_tarski(A_11) = B_12
      | ~ v1_zfmisc_1(B_12)
      | v1_xboole_0(B_12)
      | v1_xboole_0(k1_tarski(A_11))
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(resolution,[status(thm)],[c_16,c_271])).

tff(c_316,plain,(
    ! [A_95,B_96] :
      ( k1_tarski(A_95) = B_96
      | ~ v1_zfmisc_1(B_96)
      | v1_xboole_0(B_96)
      | ~ r2_hidden(A_95,B_96) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_289])).

tff(c_335,plain,(
    ! [A_1] :
      ( k1_tarski('#skF_1'(A_1)) = A_1
      | ~ v1_zfmisc_1(A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_316])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_133,plain,(
    ! [A_65,B_66] :
      ( ~ r2_hidden('#skF_2'(A_65,B_66),B_66)
      | r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_138,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_133])).

tff(c_155,plain,(
    ! [C_70,B_71,A_72] :
      ( r2_hidden(C_70,B_71)
      | ~ r2_hidden(C_70,A_72)
      | ~ r1_tarski(A_72,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_164,plain,(
    ! [A_1,B_71] :
      ( r2_hidden('#skF_1'(A_1),B_71)
      | ~ r1_tarski(A_1,B_71)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_155])).

tff(c_1146,plain,(
    ! [A_166,B_167] :
      ( k1_tarski('#skF_1'(A_166)) = B_167
      | ~ v1_zfmisc_1(B_167)
      | v1_xboole_0(B_167)
      | ~ r1_tarski(A_166,B_167)
      | v1_xboole_0(A_166) ) ),
    inference(resolution,[status(thm)],[c_164,c_316])).

tff(c_1170,plain,(
    ! [A_11,B_12] :
      ( k1_tarski('#skF_1'(k1_tarski(A_11))) = B_12
      | ~ v1_zfmisc_1(B_12)
      | v1_xboole_0(B_12)
      | v1_xboole_0(k1_tarski(A_11))
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(resolution,[status(thm)],[c_16,c_1146])).

tff(c_1220,plain,(
    ! [A_169,B_170] :
      ( k1_tarski('#skF_1'(k1_tarski(A_169))) = B_170
      | ~ v1_zfmisc_1(B_170)
      | v1_xboole_0(B_170)
      | ~ r2_hidden(A_169,B_170) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_1170])).

tff(c_1427,plain,(
    ! [A_174] :
      ( k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_174)))) = A_174
      | ~ v1_zfmisc_1(A_174)
      | v1_xboole_0(A_174) ) ),
    inference(resolution,[status(thm)],[c_4,c_1220])).

tff(c_139,plain,(
    ! [A_67] : r1_tarski(A_67,A_67) ),
    inference(resolution,[status(thm)],[c_10,c_133])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | ~ r1_tarski(k1_tarski(A_11),B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_144,plain,(
    ! [A_11] : r2_hidden(A_11,k1_tarski(A_11)) ),
    inference(resolution,[status(thm)],[c_139,c_14])).

tff(c_1499,plain,(
    ! [A_174] :
      ( r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_174))),A_174)
      | ~ v1_zfmisc_1(A_174)
      | v1_xboole_0(A_174) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1427,c_144])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_99,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,B_58)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_112,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_99])).

tff(c_172,plain,(
    ! [A_76,B_77] :
      ( r2_hidden('#skF_1'(A_76),B_77)
      | ~ r1_tarski(A_76,B_77)
      | v1_xboole_0(A_76) ) ),
    inference(resolution,[status(thm)],[c_4,c_155])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_711,plain,(
    ! [A_132,B_133,B_134] :
      ( r2_hidden('#skF_1'(A_132),B_133)
      | ~ r1_tarski(B_134,B_133)
      | ~ r1_tarski(A_132,B_134)
      | v1_xboole_0(A_132) ) ),
    inference(resolution,[status(thm)],[c_172,c_6])).

tff(c_2857,plain,(
    ! [A_201,B_202,A_203] :
      ( r2_hidden('#skF_1'(A_201),B_202)
      | ~ r1_tarski(A_201,k1_tarski(A_203))
      | v1_xboole_0(A_201)
      | ~ r2_hidden(A_203,B_202) ) ),
    inference(resolution,[status(thm)],[c_16,c_711])).

tff(c_2897,plain,(
    ! [A_203,B_202] :
      ( r2_hidden('#skF_1'(k1_tarski(A_203)),B_202)
      | v1_xboole_0(k1_tarski(A_203))
      | ~ r2_hidden(A_203,B_202) ) ),
    inference(resolution,[status(thm)],[c_138,c_2857])).

tff(c_2922,plain,(
    ! [A_204,B_205] :
      ( r2_hidden('#skF_1'(k1_tarski(A_204)),B_205)
      | ~ r2_hidden(A_204,B_205) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_2897])).

tff(c_3097,plain,(
    ! [A_211,B_212,B_213] :
      ( r2_hidden('#skF_1'(k1_tarski(A_211)),B_212)
      | ~ r1_tarski(B_213,B_212)
      | ~ r2_hidden(A_211,B_213) ) ),
    inference(resolution,[status(thm)],[c_2922,c_6])).

tff(c_3145,plain,(
    ! [A_211] :
      ( r2_hidden('#skF_1'(k1_tarski(A_211)),u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_211,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_112,c_3097])).

tff(c_4589,plain,(
    ! [A_257,B_258] :
      ( r1_tarski(A_257,B_258)
      | ~ r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_257))),B_258)
      | ~ v1_zfmisc_1(A_257)
      | v1_xboole_0(A_257) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1427,c_16])).

tff(c_5683,plain,(
    ! [A_296] :
      ( r1_tarski(A_296,u1_struct_0('#skF_4'))
      | ~ v1_zfmisc_1(A_296)
      | v1_xboole_0(A_296)
      | ~ r2_hidden('#skF_1'(A_296),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3145,c_4589])).

tff(c_5715,plain,
    ( r1_tarski(k1_tarski('#skF_1'('#skF_5')),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))
    | v1_xboole_0(k1_tarski('#skF_1'('#skF_5')))
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1499,c_5683])).

tff(c_5743,plain,
    ( r1_tarski(k1_tarski('#skF_1'('#skF_5')),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))
    | v1_xboole_0(k1_tarski('#skF_1'('#skF_5')))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_5715])).

tff(c_5744,plain,
    ( r1_tarski(k1_tarski('#skF_1'('#skF_5')),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_12,c_5743])).

tff(c_5750,plain,(
    ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_5744])).

tff(c_5753,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_5750])).

tff(c_5755,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_74,c_5753])).

tff(c_5757,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_5755])).

tff(c_5758,plain,(
    r1_tarski(k1_tarski('#skF_1'('#skF_5')),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_5744])).

tff(c_5853,plain,(
    r2_hidden('#skF_1'('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_5758,c_14])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,B_14)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_5888,plain,(
    m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_5853,c_18])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_184,plain,(
    ! [B_78,A_79] :
      ( ~ v1_xboole_0(B_78)
      | ~ r1_tarski(A_79,B_78)
      | v1_xboole_0(A_79) ) ),
    inference(resolution,[status(thm)],[c_172,c_2])).

tff(c_199,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_112,c_184])).

tff(c_207,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_199])).

tff(c_739,plain,(
    ! [A_135] :
      ( r2_hidden('#skF_1'(A_135),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_135,'#skF_5')
      | v1_xboole_0(A_135) ) ),
    inference(resolution,[status(thm)],[c_112,c_711])).

tff(c_760,plain,(
    ! [A_136] :
      ( m1_subset_1('#skF_1'(A_136),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_136,'#skF_5')
      | v1_xboole_0(A_136) ) ),
    inference(resolution,[status(thm)],[c_739,c_18])).

tff(c_30,plain,(
    ! [A_22,B_23] :
      ( k6_domain_1(A_22,B_23) = k1_tarski(B_23)
      | ~ m1_subset_1(B_23,A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_763,plain,(
    ! [A_136] :
      ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'(A_136)) = k1_tarski('#skF_1'(A_136))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_136,'#skF_5')
      | v1_xboole_0(A_136) ) ),
    inference(resolution,[status(thm)],[c_760,c_30])).

tff(c_1193,plain,(
    ! [A_168] :
      ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'(A_168)) = k1_tarski('#skF_1'(A_168))
      | ~ r1_tarski(A_168,'#skF_5')
      | v1_xboole_0(A_168) ) ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_763])).

tff(c_50,plain,(
    ! [A_37,B_39] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_37),B_39),A_37)
      | ~ m1_subset_1(B_39,u1_struct_0(A_37))
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1199,plain,(
    ! [A_168] :
      ( v2_tex_2(k1_tarski('#skF_1'(A_168)),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_168),u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_168,'#skF_5')
      | v1_xboole_0(A_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1193,c_50])).

tff(c_1213,plain,(
    ! [A_168] :
      ( v2_tex_2(k1_tarski('#skF_1'(A_168)),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_168),u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_168,'#skF_5')
      | v1_xboole_0(A_168) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_1199])).

tff(c_1214,plain,(
    ! [A_168] :
      ( v2_tex_2(k1_tarski('#skF_1'(A_168)),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_168),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_168,'#skF_5')
      | v1_xboole_0(A_168) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1213])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_604,plain,(
    ! [A_124,B_125] :
      ( v1_pre_topc('#skF_3'(A_124,B_125))
      | ~ v2_tex_2(B_125,A_124)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_124)))
      | v1_xboole_0(B_125)
      | ~ l1_pre_topc(A_124)
      | ~ v2_pre_topc(A_124)
      | v2_struct_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_631,plain,(
    ! [A_124,A_15] :
      ( v1_pre_topc('#skF_3'(A_124,A_15))
      | ~ v2_tex_2(A_15,A_124)
      | v1_xboole_0(A_15)
      | ~ l1_pre_topc(A_124)
      | ~ v2_pre_topc(A_124)
      | v2_struct_0(A_124)
      | ~ r1_tarski(A_15,u1_struct_0(A_124)) ) ),
    inference(resolution,[status(thm)],[c_22,c_604])).

tff(c_5786,plain,
    ( v1_pre_topc('#skF_3'('#skF_4',k1_tarski('#skF_1'('#skF_5'))))
    | ~ v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4')
    | v1_xboole_0(k1_tarski('#skF_1'('#skF_5')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_5758,c_631])).

tff(c_5832,plain,
    ( v1_pre_topc('#skF_3'('#skF_4',k1_tarski('#skF_1'('#skF_5'))))
    | ~ v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4')
    | v1_xboole_0(k1_tarski('#skF_1'('#skF_5')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_5786])).

tff(c_5833,plain,
    ( v1_pre_topc('#skF_3'('#skF_4',k1_tarski('#skF_1'('#skF_5'))))
    | ~ v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_12,c_5832])).

tff(c_5896,plain,(
    ~ v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5833])).

tff(c_5902,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1214,c_5896])).

tff(c_5911,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_5888,c_5902])).

tff(c_5913,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_5911])).

tff(c_5915,plain,(
    v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_5833])).

tff(c_5918,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_5915])).

tff(c_5920,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_5918])).

tff(c_5922,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_76,c_5920])).

tff(c_5923,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_6725,plain,(
    ! [A_396,B_397] :
      ( m1_pre_topc('#skF_3'(A_396,B_397),A_396)
      | ~ v2_tex_2(B_397,A_396)
      | ~ m1_subset_1(B_397,k1_zfmisc_1(u1_struct_0(A_396)))
      | v1_xboole_0(B_397)
      | ~ l1_pre_topc(A_396)
      | ~ v2_pre_topc(A_396)
      | v2_struct_0(A_396) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_6742,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_6725])).

tff(c_6750,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_5923,c_6742])).

tff(c_6751,plain,(
    m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_54,c_6750])).

tff(c_26,plain,(
    ! [B_20,A_18] :
      ( l1_pre_topc(B_20)
      | ~ m1_pre_topc(B_20,A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6757,plain,
    ( l1_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6751,c_26])).

tff(c_6764,plain,(
    l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_6757])).

tff(c_24,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_5924,plain,(
    ~ v1_zfmisc_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_6528,plain,(
    ! [A_383,B_384] :
      ( ~ v2_struct_0('#skF_3'(A_383,B_384))
      | ~ v2_tex_2(B_384,A_383)
      | ~ m1_subset_1(B_384,k1_zfmisc_1(u1_struct_0(A_383)))
      | v1_xboole_0(B_384)
      | ~ l1_pre_topc(A_383)
      | ~ v2_pre_topc(A_383)
      | v2_struct_0(A_383) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_6551,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_6528])).

tff(c_6559,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_5923,c_6551])).

tff(c_6560,plain,(
    ~ v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_54,c_6559])).

tff(c_58,plain,(
    v2_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_6437,plain,(
    ! [A_375,B_376] :
      ( v1_tdlat_3('#skF_3'(A_375,B_376))
      | ~ v2_tex_2(B_376,A_375)
      | ~ m1_subset_1(B_376,k1_zfmisc_1(u1_struct_0(A_375)))
      | v1_xboole_0(B_376)
      | ~ l1_pre_topc(A_375)
      | ~ v2_pre_topc(A_375)
      | v2_struct_0(A_375) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_6460,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_6437])).

tff(c_6468,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_5923,c_6460])).

tff(c_6469,plain,(
    v1_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_54,c_6468])).

tff(c_34,plain,(
    ! [B_27,A_25] :
      ( ~ v1_tdlat_3(B_27)
      | v7_struct_0(B_27)
      | v2_struct_0(B_27)
      | ~ m1_pre_topc(B_27,A_25)
      | ~ l1_pre_topc(A_25)
      | ~ v2_tdlat_3(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_6754,plain,
    ( ~ v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v7_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_6751,c_34])).

tff(c_6760,plain,
    ( v7_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_6469,c_6754])).

tff(c_6761,plain,(
    v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_6560,c_6760])).

tff(c_6908,plain,(
    ! [A_413,B_414] :
      ( u1_struct_0('#skF_3'(A_413,B_414)) = B_414
      | ~ v2_tex_2(B_414,A_413)
      | ~ m1_subset_1(B_414,k1_zfmisc_1(u1_struct_0(A_413)))
      | v1_xboole_0(B_414)
      | ~ l1_pre_topc(A_413)
      | ~ v2_pre_topc(A_413)
      | v2_struct_0(A_413) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_6931,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_6908])).

tff(c_6939,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_5923,c_6931])).

tff(c_6940,plain,(
    u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_54,c_6939])).

tff(c_28,plain,(
    ! [A_21] :
      ( v1_zfmisc_1(u1_struct_0(A_21))
      | ~ l1_struct_0(A_21)
      | ~ v7_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6961,plain,
    ( v1_zfmisc_1('#skF_5')
    | ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6940,c_28])).

tff(c_6983,plain,
    ( v1_zfmisc_1('#skF_5')
    | ~ l1_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6761,c_6961])).

tff(c_6984,plain,(
    ~ l1_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_5924,c_6983])).

tff(c_6988,plain,(
    ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_24,c_6984])).

tff(c_6992,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6764,c_6988])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:43:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.67/2.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.67/2.36  
% 6.67/2.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.67/2.36  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 6.67/2.36  
% 6.67/2.36  %Foreground sorts:
% 6.67/2.36  
% 6.67/2.36  
% 6.67/2.36  %Background operators:
% 6.67/2.36  
% 6.67/2.36  
% 6.67/2.36  %Foreground operators:
% 6.67/2.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.67/2.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.67/2.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.67/2.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.67/2.36  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.67/2.36  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 6.67/2.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.67/2.36  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 6.67/2.36  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.67/2.36  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 6.67/2.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.67/2.36  tff('#skF_5', type, '#skF_5': $i).
% 6.67/2.36  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 6.67/2.36  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 6.67/2.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.67/2.36  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.67/2.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.67/2.36  tff('#skF_4', type, '#skF_4': $i).
% 6.67/2.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.67/2.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.67/2.36  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 6.67/2.36  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.67/2.36  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.67/2.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.67/2.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.67/2.36  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 6.67/2.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.67/2.36  
% 6.95/2.38  tff(f_181, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 6.95/2.38  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.95/2.38  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 6.95/2.38  tff(f_45, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 6.95/2.38  tff(f_120, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 6.95/2.38  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.95/2.38  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.95/2.38  tff(f_49, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 6.95/2.38  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 6.95/2.38  tff(f_161, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 6.95/2.38  tff(f_149, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tex_2)).
% 6.95/2.38  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 6.95/2.38  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.95/2.38  tff(f_107, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((~v2_struct_0(B) & ~v7_struct_0(B)) => (~v2_struct_0(B) & ~v1_tdlat_3(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc32_tex_2)).
% 6.95/2.38  tff(f_70, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 6.95/2.38  tff(c_56, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_181])).
% 6.95/2.38  tff(c_62, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_181])).
% 6.95/2.38  tff(c_54, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_181])).
% 6.95/2.38  tff(c_60, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_181])).
% 6.95/2.38  tff(c_70, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_181])).
% 6.95/2.38  tff(c_74, plain, (v1_zfmisc_1('#skF_5')), inference(splitLeft, [status(thm)], [c_70])).
% 6.95/2.38  tff(c_64, plain, (~v1_zfmisc_1('#skF_5') | ~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_181])).
% 6.95/2.38  tff(c_76, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_64])).
% 6.95/2.38  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.95/2.38  tff(c_12, plain, (![A_10]: (~v1_xboole_0(k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.95/2.38  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(k1_tarski(A_11), B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.95/2.38  tff(c_271, plain, (![B_91, A_92]: (B_91=A_92 | ~r1_tarski(A_92, B_91) | ~v1_zfmisc_1(B_91) | v1_xboole_0(B_91) | v1_xboole_0(A_92))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.95/2.38  tff(c_289, plain, (![A_11, B_12]: (k1_tarski(A_11)=B_12 | ~v1_zfmisc_1(B_12) | v1_xboole_0(B_12) | v1_xboole_0(k1_tarski(A_11)) | ~r2_hidden(A_11, B_12))), inference(resolution, [status(thm)], [c_16, c_271])).
% 6.95/2.38  tff(c_316, plain, (![A_95, B_96]: (k1_tarski(A_95)=B_96 | ~v1_zfmisc_1(B_96) | v1_xboole_0(B_96) | ~r2_hidden(A_95, B_96))), inference(negUnitSimplification, [status(thm)], [c_12, c_289])).
% 6.95/2.38  tff(c_335, plain, (![A_1]: (k1_tarski('#skF_1'(A_1))=A_1 | ~v1_zfmisc_1(A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_316])).
% 6.95/2.38  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.95/2.38  tff(c_133, plain, (![A_65, B_66]: (~r2_hidden('#skF_2'(A_65, B_66), B_66) | r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.95/2.38  tff(c_138, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_133])).
% 6.95/2.38  tff(c_155, plain, (![C_70, B_71, A_72]: (r2_hidden(C_70, B_71) | ~r2_hidden(C_70, A_72) | ~r1_tarski(A_72, B_71))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.95/2.38  tff(c_164, plain, (![A_1, B_71]: (r2_hidden('#skF_1'(A_1), B_71) | ~r1_tarski(A_1, B_71) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_155])).
% 6.95/2.38  tff(c_1146, plain, (![A_166, B_167]: (k1_tarski('#skF_1'(A_166))=B_167 | ~v1_zfmisc_1(B_167) | v1_xboole_0(B_167) | ~r1_tarski(A_166, B_167) | v1_xboole_0(A_166))), inference(resolution, [status(thm)], [c_164, c_316])).
% 6.95/2.38  tff(c_1170, plain, (![A_11, B_12]: (k1_tarski('#skF_1'(k1_tarski(A_11)))=B_12 | ~v1_zfmisc_1(B_12) | v1_xboole_0(B_12) | v1_xboole_0(k1_tarski(A_11)) | ~r2_hidden(A_11, B_12))), inference(resolution, [status(thm)], [c_16, c_1146])).
% 6.95/2.38  tff(c_1220, plain, (![A_169, B_170]: (k1_tarski('#skF_1'(k1_tarski(A_169)))=B_170 | ~v1_zfmisc_1(B_170) | v1_xboole_0(B_170) | ~r2_hidden(A_169, B_170))), inference(negUnitSimplification, [status(thm)], [c_12, c_1170])).
% 6.95/2.38  tff(c_1427, plain, (![A_174]: (k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_174))))=A_174 | ~v1_zfmisc_1(A_174) | v1_xboole_0(A_174))), inference(resolution, [status(thm)], [c_4, c_1220])).
% 6.95/2.38  tff(c_139, plain, (![A_67]: (r1_tarski(A_67, A_67))), inference(resolution, [status(thm)], [c_10, c_133])).
% 6.95/2.38  tff(c_14, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | ~r1_tarski(k1_tarski(A_11), B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.95/2.38  tff(c_144, plain, (![A_11]: (r2_hidden(A_11, k1_tarski(A_11)))), inference(resolution, [status(thm)], [c_139, c_14])).
% 6.95/2.38  tff(c_1499, plain, (![A_174]: (r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_174))), A_174) | ~v1_zfmisc_1(A_174) | v1_xboole_0(A_174))), inference(superposition, [status(thm), theory('equality')], [c_1427, c_144])).
% 6.95/2.38  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_181])).
% 6.95/2.38  tff(c_99, plain, (![A_57, B_58]: (r1_tarski(A_57, B_58) | ~m1_subset_1(A_57, k1_zfmisc_1(B_58)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.95/2.38  tff(c_112, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_52, c_99])).
% 6.95/2.38  tff(c_172, plain, (![A_76, B_77]: (r2_hidden('#skF_1'(A_76), B_77) | ~r1_tarski(A_76, B_77) | v1_xboole_0(A_76))), inference(resolution, [status(thm)], [c_4, c_155])).
% 6.95/2.38  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.95/2.38  tff(c_711, plain, (![A_132, B_133, B_134]: (r2_hidden('#skF_1'(A_132), B_133) | ~r1_tarski(B_134, B_133) | ~r1_tarski(A_132, B_134) | v1_xboole_0(A_132))), inference(resolution, [status(thm)], [c_172, c_6])).
% 6.95/2.38  tff(c_2857, plain, (![A_201, B_202, A_203]: (r2_hidden('#skF_1'(A_201), B_202) | ~r1_tarski(A_201, k1_tarski(A_203)) | v1_xboole_0(A_201) | ~r2_hidden(A_203, B_202))), inference(resolution, [status(thm)], [c_16, c_711])).
% 6.95/2.38  tff(c_2897, plain, (![A_203, B_202]: (r2_hidden('#skF_1'(k1_tarski(A_203)), B_202) | v1_xboole_0(k1_tarski(A_203)) | ~r2_hidden(A_203, B_202))), inference(resolution, [status(thm)], [c_138, c_2857])).
% 6.95/2.38  tff(c_2922, plain, (![A_204, B_205]: (r2_hidden('#skF_1'(k1_tarski(A_204)), B_205) | ~r2_hidden(A_204, B_205))), inference(negUnitSimplification, [status(thm)], [c_12, c_2897])).
% 6.95/2.38  tff(c_3097, plain, (![A_211, B_212, B_213]: (r2_hidden('#skF_1'(k1_tarski(A_211)), B_212) | ~r1_tarski(B_213, B_212) | ~r2_hidden(A_211, B_213))), inference(resolution, [status(thm)], [c_2922, c_6])).
% 6.95/2.38  tff(c_3145, plain, (![A_211]: (r2_hidden('#skF_1'(k1_tarski(A_211)), u1_struct_0('#skF_4')) | ~r2_hidden(A_211, '#skF_5'))), inference(resolution, [status(thm)], [c_112, c_3097])).
% 6.95/2.38  tff(c_4589, plain, (![A_257, B_258]: (r1_tarski(A_257, B_258) | ~r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_257))), B_258) | ~v1_zfmisc_1(A_257) | v1_xboole_0(A_257))), inference(superposition, [status(thm), theory('equality')], [c_1427, c_16])).
% 6.95/2.38  tff(c_5683, plain, (![A_296]: (r1_tarski(A_296, u1_struct_0('#skF_4')) | ~v1_zfmisc_1(A_296) | v1_xboole_0(A_296) | ~r2_hidden('#skF_1'(A_296), '#skF_5'))), inference(resolution, [status(thm)], [c_3145, c_4589])).
% 6.95/2.38  tff(c_5715, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) | v1_xboole_0(k1_tarski('#skF_1'('#skF_5'))) | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_1499, c_5683])).
% 6.95/2.38  tff(c_5743, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) | v1_xboole_0(k1_tarski('#skF_1'('#skF_5'))) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_5715])).
% 6.95/2.38  tff(c_5744, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_54, c_12, c_5743])).
% 6.95/2.38  tff(c_5750, plain, (~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))), inference(splitLeft, [status(thm)], [c_5744])).
% 6.95/2.38  tff(c_5753, plain, (~v1_zfmisc_1('#skF_5') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_335, c_5750])).
% 6.95/2.38  tff(c_5755, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_74, c_5753])).
% 6.95/2.38  tff(c_5757, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_5755])).
% 6.95/2.38  tff(c_5758, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_5744])).
% 6.95/2.38  tff(c_5853, plain, (r2_hidden('#skF_1'('#skF_5'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_5758, c_14])).
% 6.95/2.38  tff(c_18, plain, (![A_13, B_14]: (m1_subset_1(A_13, B_14) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.95/2.38  tff(c_5888, plain, (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_5853, c_18])).
% 6.95/2.38  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.95/2.38  tff(c_184, plain, (![B_78, A_79]: (~v1_xboole_0(B_78) | ~r1_tarski(A_79, B_78) | v1_xboole_0(A_79))), inference(resolution, [status(thm)], [c_172, c_2])).
% 6.95/2.38  tff(c_199, plain, (~v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_112, c_184])).
% 6.95/2.38  tff(c_207, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_199])).
% 6.95/2.38  tff(c_739, plain, (![A_135]: (r2_hidden('#skF_1'(A_135), u1_struct_0('#skF_4')) | ~r1_tarski(A_135, '#skF_5') | v1_xboole_0(A_135))), inference(resolution, [status(thm)], [c_112, c_711])).
% 6.95/2.38  tff(c_760, plain, (![A_136]: (m1_subset_1('#skF_1'(A_136), u1_struct_0('#skF_4')) | ~r1_tarski(A_136, '#skF_5') | v1_xboole_0(A_136))), inference(resolution, [status(thm)], [c_739, c_18])).
% 6.95/2.38  tff(c_30, plain, (![A_22, B_23]: (k6_domain_1(A_22, B_23)=k1_tarski(B_23) | ~m1_subset_1(B_23, A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.95/2.38  tff(c_763, plain, (![A_136]: (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'(A_136))=k1_tarski('#skF_1'(A_136)) | v1_xboole_0(u1_struct_0('#skF_4')) | ~r1_tarski(A_136, '#skF_5') | v1_xboole_0(A_136))), inference(resolution, [status(thm)], [c_760, c_30])).
% 6.95/2.38  tff(c_1193, plain, (![A_168]: (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'(A_168))=k1_tarski('#skF_1'(A_168)) | ~r1_tarski(A_168, '#skF_5') | v1_xboole_0(A_168))), inference(negUnitSimplification, [status(thm)], [c_207, c_763])).
% 6.95/2.38  tff(c_50, plain, (![A_37, B_39]: (v2_tex_2(k6_domain_1(u1_struct_0(A_37), B_39), A_37) | ~m1_subset_1(B_39, u1_struct_0(A_37)) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.95/2.38  tff(c_1199, plain, (![A_168]: (v2_tex_2(k1_tarski('#skF_1'(A_168)), '#skF_4') | ~m1_subset_1('#skF_1'(A_168), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(A_168, '#skF_5') | v1_xboole_0(A_168))), inference(superposition, [status(thm), theory('equality')], [c_1193, c_50])).
% 6.95/2.38  tff(c_1213, plain, (![A_168]: (v2_tex_2(k1_tarski('#skF_1'(A_168)), '#skF_4') | ~m1_subset_1('#skF_1'(A_168), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | ~r1_tarski(A_168, '#skF_5') | v1_xboole_0(A_168))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_1199])).
% 6.95/2.38  tff(c_1214, plain, (![A_168]: (v2_tex_2(k1_tarski('#skF_1'(A_168)), '#skF_4') | ~m1_subset_1('#skF_1'(A_168), u1_struct_0('#skF_4')) | ~r1_tarski(A_168, '#skF_5') | v1_xboole_0(A_168))), inference(negUnitSimplification, [status(thm)], [c_62, c_1213])).
% 6.95/2.38  tff(c_22, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.95/2.38  tff(c_604, plain, (![A_124, B_125]: (v1_pre_topc('#skF_3'(A_124, B_125)) | ~v2_tex_2(B_125, A_124) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_124))) | v1_xboole_0(B_125) | ~l1_pre_topc(A_124) | ~v2_pre_topc(A_124) | v2_struct_0(A_124))), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.95/2.38  tff(c_631, plain, (![A_124, A_15]: (v1_pre_topc('#skF_3'(A_124, A_15)) | ~v2_tex_2(A_15, A_124) | v1_xboole_0(A_15) | ~l1_pre_topc(A_124) | ~v2_pre_topc(A_124) | v2_struct_0(A_124) | ~r1_tarski(A_15, u1_struct_0(A_124)))), inference(resolution, [status(thm)], [c_22, c_604])).
% 6.95/2.38  tff(c_5786, plain, (v1_pre_topc('#skF_3'('#skF_4', k1_tarski('#skF_1'('#skF_5')))) | ~v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4') | v1_xboole_0(k1_tarski('#skF_1'('#skF_5'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_5758, c_631])).
% 6.95/2.38  tff(c_5832, plain, (v1_pre_topc('#skF_3'('#skF_4', k1_tarski('#skF_1'('#skF_5')))) | ~v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4') | v1_xboole_0(k1_tarski('#skF_1'('#skF_5'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_5786])).
% 6.95/2.38  tff(c_5833, plain, (v1_pre_topc('#skF_3'('#skF_4', k1_tarski('#skF_1'('#skF_5')))) | ~v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_62, c_12, c_5832])).
% 6.95/2.38  tff(c_5896, plain, (~v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_5833])).
% 6.95/2.38  tff(c_5902, plain, (~m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | ~r1_tarski('#skF_5', '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_1214, c_5896])).
% 6.95/2.38  tff(c_5911, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_5888, c_5902])).
% 6.95/2.38  tff(c_5913, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_5911])).
% 6.95/2.38  tff(c_5915, plain, (v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4')), inference(splitRight, [status(thm)], [c_5833])).
% 6.95/2.38  tff(c_5918, plain, (v2_tex_2('#skF_5', '#skF_4') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_335, c_5915])).
% 6.95/2.39  tff(c_5920, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_5918])).
% 6.95/2.39  tff(c_5922, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_76, c_5920])).
% 6.95/2.39  tff(c_5923, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_70])).
% 6.95/2.39  tff(c_6725, plain, (![A_396, B_397]: (m1_pre_topc('#skF_3'(A_396, B_397), A_396) | ~v2_tex_2(B_397, A_396) | ~m1_subset_1(B_397, k1_zfmisc_1(u1_struct_0(A_396))) | v1_xboole_0(B_397) | ~l1_pre_topc(A_396) | ~v2_pre_topc(A_396) | v2_struct_0(A_396))), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.95/2.39  tff(c_6742, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_6725])).
% 6.95/2.39  tff(c_6750, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_5923, c_6742])).
% 6.95/2.39  tff(c_6751, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_62, c_54, c_6750])).
% 6.95/2.39  tff(c_26, plain, (![B_20, A_18]: (l1_pre_topc(B_20) | ~m1_pre_topc(B_20, A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.95/2.39  tff(c_6757, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6751, c_26])).
% 6.95/2.39  tff(c_6764, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_6757])).
% 6.95/2.39  tff(c_24, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.95/2.39  tff(c_5924, plain, (~v1_zfmisc_1('#skF_5')), inference(splitRight, [status(thm)], [c_70])).
% 6.95/2.39  tff(c_6528, plain, (![A_383, B_384]: (~v2_struct_0('#skF_3'(A_383, B_384)) | ~v2_tex_2(B_384, A_383) | ~m1_subset_1(B_384, k1_zfmisc_1(u1_struct_0(A_383))) | v1_xboole_0(B_384) | ~l1_pre_topc(A_383) | ~v2_pre_topc(A_383) | v2_struct_0(A_383))), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.95/2.39  tff(c_6551, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_6528])).
% 6.95/2.39  tff(c_6559, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_5923, c_6551])).
% 6.95/2.39  tff(c_6560, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_62, c_54, c_6559])).
% 6.95/2.39  tff(c_58, plain, (v2_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_181])).
% 6.95/2.39  tff(c_6437, plain, (![A_375, B_376]: (v1_tdlat_3('#skF_3'(A_375, B_376)) | ~v2_tex_2(B_376, A_375) | ~m1_subset_1(B_376, k1_zfmisc_1(u1_struct_0(A_375))) | v1_xboole_0(B_376) | ~l1_pre_topc(A_375) | ~v2_pre_topc(A_375) | v2_struct_0(A_375))), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.95/2.39  tff(c_6460, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_6437])).
% 6.95/2.39  tff(c_6468, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_5923, c_6460])).
% 6.95/2.39  tff(c_6469, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_62, c_54, c_6468])).
% 6.95/2.39  tff(c_34, plain, (![B_27, A_25]: (~v1_tdlat_3(B_27) | v7_struct_0(B_27) | v2_struct_0(B_27) | ~m1_pre_topc(B_27, A_25) | ~l1_pre_topc(A_25) | ~v2_tdlat_3(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.95/2.39  tff(c_6754, plain, (~v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v7_struct_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_6751, c_34])).
% 6.95/2.39  tff(c_6760, plain, (v7_struct_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_6469, c_6754])).
% 6.95/2.39  tff(c_6761, plain, (v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_62, c_6560, c_6760])).
% 6.95/2.39  tff(c_6908, plain, (![A_413, B_414]: (u1_struct_0('#skF_3'(A_413, B_414))=B_414 | ~v2_tex_2(B_414, A_413) | ~m1_subset_1(B_414, k1_zfmisc_1(u1_struct_0(A_413))) | v1_xboole_0(B_414) | ~l1_pre_topc(A_413) | ~v2_pre_topc(A_413) | v2_struct_0(A_413))), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.95/2.39  tff(c_6931, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_6908])).
% 6.95/2.39  tff(c_6939, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_5923, c_6931])).
% 6.95/2.39  tff(c_6940, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_62, c_54, c_6939])).
% 6.95/2.39  tff(c_28, plain, (![A_21]: (v1_zfmisc_1(u1_struct_0(A_21)) | ~l1_struct_0(A_21) | ~v7_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.95/2.39  tff(c_6961, plain, (v1_zfmisc_1('#skF_5') | ~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_6940, c_28])).
% 6.95/2.39  tff(c_6983, plain, (v1_zfmisc_1('#skF_5') | ~l1_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_6761, c_6961])).
% 6.95/2.39  tff(c_6984, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_5924, c_6983])).
% 6.95/2.39  tff(c_6988, plain, (~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_24, c_6984])).
% 6.95/2.39  tff(c_6992, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6764, c_6988])).
% 6.95/2.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.95/2.39  
% 6.95/2.39  Inference rules
% 6.95/2.39  ----------------------
% 6.95/2.39  #Ref     : 0
% 6.95/2.39  #Sup     : 1631
% 6.95/2.39  #Fact    : 0
% 6.95/2.39  #Define  : 0
% 6.95/2.39  #Split   : 10
% 6.95/2.39  #Chain   : 0
% 6.95/2.39  #Close   : 0
% 6.95/2.39  
% 6.95/2.39  Ordering : KBO
% 6.95/2.39  
% 6.95/2.39  Simplification rules
% 6.95/2.39  ----------------------
% 6.95/2.39  #Subsume      : 445
% 6.95/2.39  #Demod        : 219
% 6.95/2.39  #Tautology    : 223
% 6.95/2.39  #SimpNegUnit  : 352
% 6.95/2.39  #BackRed      : 0
% 6.95/2.39  
% 6.95/2.39  #Partial instantiations: 0
% 6.95/2.39  #Strategies tried      : 1
% 6.95/2.39  
% 6.95/2.39  Timing (in seconds)
% 6.95/2.39  ----------------------
% 6.95/2.39  Preprocessing        : 0.34
% 6.95/2.39  Parsing              : 0.18
% 6.95/2.39  CNF conversion       : 0.03
% 6.95/2.39  Main loop            : 1.27
% 6.95/2.39  Inferencing          : 0.43
% 6.95/2.39  Reduction            : 0.36
% 6.95/2.39  Demodulation         : 0.22
% 6.95/2.39  BG Simplification    : 0.05
% 6.95/2.39  Subsumption          : 0.32
% 6.95/2.39  Abstraction          : 0.06
% 6.95/2.39  MUC search           : 0.00
% 6.95/2.39  Cooper               : 0.00
% 6.95/2.39  Total                : 1.66
% 6.95/2.39  Index Insertion      : 0.00
% 6.95/2.39  Index Deletion       : 0.00
% 6.95/2.39  Index Matching       : 0.00
% 6.95/2.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
