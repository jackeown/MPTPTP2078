%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:51 EST 2020

% Result     : Theorem 11.44s
% Output     : CNFRefutation 11.59s
% Verified   : 
% Statistics : Number of formulae       :  229 (2974 expanded)
%              Number of leaves         :   50 (1007 expanded)
%              Depth                    :   34
%              Number of atoms          :  622 (8466 expanded)
%              Number of equality atoms :   38 ( 517 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    7 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k1_tex_2,type,(
    k1_tex_2: ( $i * $i ) > $i )).

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

tff(f_277,negated_conjecture,(
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

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_208,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_181,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_195,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_117,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ( ~ v2_struct_0(B)
              & v7_struct_0(B)
              & v2_pre_topc(B) )
           => ( ~ v2_struct_0(B)
              & v1_tdlat_3(B)
              & v2_tdlat_3(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc25_tex_2)).

tff(f_167,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_tex_2(A,B)
              <=> u1_struct_0(C) = k6_domain_1(u1_struct_0(A),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tex_2)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_228,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v2_tex_2(C,A)
                <=> v1_tdlat_3(B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

tff(f_257,axiom,(
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

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_147,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc32_tex_2)).

tff(f_81,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

tff(c_86,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_277])).

tff(c_92,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_277])).

tff(c_84,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_277])).

tff(c_90,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_277])).

tff(c_100,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_277])).

tff(c_103,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_94,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_277])).

tff(c_105,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_94])).

tff(c_82,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_277])).

tff(c_143,plain,(
    ! [A_85,B_86] :
      ( r1_tarski(A_85,B_86)
      | ~ m1_subset_1(A_85,k1_zfmisc_1(B_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_156,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_82,c_143])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_188,plain,(
    ! [C_94,B_95,A_96] :
      ( r2_hidden(C_94,B_95)
      | ~ r2_hidden(C_94,A_96)
      | ~ r1_tarski(A_96,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_212,plain,(
    ! [A_104,B_105] :
      ( r2_hidden('#skF_1'(A_104),B_105)
      | ~ r1_tarski(A_104,B_105)
      | v1_xboole_0(A_104) ) ),
    inference(resolution,[status(thm)],[c_4,c_188])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_256,plain,(
    ! [B_109,A_110] :
      ( ~ v1_xboole_0(B_109)
      | ~ r1_tarski(A_110,B_109)
      | v1_xboole_0(A_110) ) ),
    inference(resolution,[status(thm)],[c_212,c_2])).

tff(c_268,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_156,c_256])).

tff(c_277,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_268])).

tff(c_14,plain,(
    ! [A_11] : ~ v1_xboole_0(k1_tarski(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(k1_tarski(A_12),B_13)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_325,plain,(
    ! [B_123,A_124] :
      ( B_123 = A_124
      | ~ r1_tarski(A_124,B_123)
      | ~ v1_zfmisc_1(B_123)
      | v1_xboole_0(B_123)
      | v1_xboole_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_349,plain,(
    ! [A_12,B_13] :
      ( k1_tarski(A_12) = B_13
      | ~ v1_zfmisc_1(B_13)
      | v1_xboole_0(B_13)
      | v1_xboole_0(k1_tarski(A_12))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_18,c_325])).

tff(c_369,plain,(
    ! [A_125,B_126] :
      ( k1_tarski(A_125) = B_126
      | ~ v1_zfmisc_1(B_126)
      | v1_xboole_0(B_126)
      | ~ r2_hidden(A_125,B_126) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_349])).

tff(c_388,plain,(
    ! [A_1] :
      ( k1_tarski('#skF_1'(A_1)) = A_1
      | ~ v1_zfmisc_1(A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_369])).

tff(c_197,plain,(
    ! [A_1,B_95] :
      ( r2_hidden('#skF_1'(A_1),B_95)
      | ~ r1_tarski(A_1,B_95)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_188])).

tff(c_1347,plain,(
    ! [A_221,B_222] :
      ( k1_tarski('#skF_1'(A_221)) = B_222
      | ~ v1_zfmisc_1(B_222)
      | v1_xboole_0(B_222)
      | ~ r1_tarski(A_221,B_222)
      | v1_xboole_0(A_221) ) ),
    inference(resolution,[status(thm)],[c_197,c_369])).

tff(c_1375,plain,(
    ! [A_12,B_13] :
      ( k1_tarski('#skF_1'(k1_tarski(A_12))) = B_13
      | ~ v1_zfmisc_1(B_13)
      | v1_xboole_0(B_13)
      | v1_xboole_0(k1_tarski(A_12))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_18,c_1347])).

tff(c_1397,plain,(
    ! [A_223,B_224] :
      ( k1_tarski('#skF_1'(k1_tarski(A_223))) = B_224
      | ~ v1_zfmisc_1(B_224)
      | v1_xboole_0(B_224)
      | ~ r2_hidden(A_223,B_224) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_1375])).

tff(c_1647,plain,(
    ! [A_230] :
      ( k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_230)))) = A_230
      | ~ v1_zfmisc_1(A_230)
      | v1_xboole_0(A_230) ) ),
    inference(resolution,[status(thm)],[c_4,c_1397])).

tff(c_158,plain,(
    ! [A_89,B_90] :
      ( r2_hidden('#skF_2'(A_89,B_90),A_89)
      | r1_tarski(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_172,plain,(
    ! [A_91] : r1_tarski(A_91,A_91) ),
    inference(resolution,[status(thm)],[c_158,c_8])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | ~ r1_tarski(k1_tarski(A_12),B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_177,plain,(
    ! [A_12] : r2_hidden(A_12,k1_tarski(A_12)) ),
    inference(resolution,[status(thm)],[c_172,c_16])).

tff(c_389,plain,(
    ! [A_127] :
      ( k1_tarski('#skF_1'(A_127)) = A_127
      | ~ v1_zfmisc_1(A_127)
      | v1_xboole_0(A_127) ) ),
    inference(resolution,[status(thm)],[c_4,c_369])).

tff(c_525,plain,(
    ! [A_143,B_144] :
      ( r1_tarski(A_143,B_144)
      | ~ r2_hidden('#skF_1'(A_143),B_144)
      | ~ v1_zfmisc_1(A_143)
      | v1_xboole_0(A_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_18])).

tff(c_537,plain,(
    ! [A_143] :
      ( r1_tarski(A_143,k1_tarski('#skF_1'(A_143)))
      | ~ v1_zfmisc_1(A_143)
      | v1_xboole_0(A_143) ) ),
    inference(resolution,[status(thm)],[c_177,c_525])).

tff(c_1713,plain,(
    ! [A_230] :
      ( r1_tarski(k1_tarski('#skF_1'(A_230)),A_230)
      | ~ v1_zfmisc_1(k1_tarski('#skF_1'(A_230)))
      | v1_xboole_0(k1_tarski('#skF_1'(A_230)))
      | ~ v1_zfmisc_1(A_230)
      | v1_xboole_0(A_230) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1647,c_537])).

tff(c_4773,plain,(
    ! [A_317] :
      ( r1_tarski(k1_tarski('#skF_1'(A_317)),A_317)
      | ~ v1_zfmisc_1(k1_tarski('#skF_1'(A_317)))
      | ~ v1_zfmisc_1(A_317)
      | v1_xboole_0(A_317) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_1713])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_748,plain,(
    ! [A_164,B_165,B_166] :
      ( r2_hidden('#skF_1'(A_164),B_165)
      | ~ r1_tarski(B_166,B_165)
      | ~ r1_tarski(A_164,B_166)
      | v1_xboole_0(A_164) ) ),
    inference(resolution,[status(thm)],[c_212,c_6])).

tff(c_780,plain,(
    ! [A_169] :
      ( r2_hidden('#skF_1'(A_169),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_169,'#skF_5')
      | v1_xboole_0(A_169) ) ),
    inference(resolution,[status(thm)],[c_156,c_748])).

tff(c_404,plain,(
    ! [A_127,B_13] :
      ( r1_tarski(A_127,B_13)
      | ~ r2_hidden('#skF_1'(A_127),B_13)
      | ~ v1_zfmisc_1(A_127)
      | v1_xboole_0(A_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_18])).

tff(c_838,plain,(
    ! [A_174] :
      ( r1_tarski(A_174,u1_struct_0('#skF_4'))
      | ~ v1_zfmisc_1(A_174)
      | ~ r1_tarski(A_174,'#skF_5')
      | v1_xboole_0(A_174) ) ),
    inference(resolution,[status(thm)],[c_780,c_404])).

tff(c_852,plain,(
    ! [A_12] :
      ( r2_hidden(A_12,u1_struct_0('#skF_4'))
      | ~ v1_zfmisc_1(k1_tarski(A_12))
      | ~ r1_tarski(k1_tarski(A_12),'#skF_5')
      | v1_xboole_0(k1_tarski(A_12)) ) ),
    inference(resolution,[status(thm)],[c_838,c_16])).

tff(c_891,plain,(
    ! [A_180] :
      ( r2_hidden(A_180,u1_struct_0('#skF_4'))
      | ~ v1_zfmisc_1(k1_tarski(A_180))
      | ~ r1_tarski(k1_tarski(A_180),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_852])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,B_15)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_916,plain,(
    ! [A_180] :
      ( m1_subset_1(A_180,u1_struct_0('#skF_4'))
      | ~ v1_zfmisc_1(k1_tarski(A_180))
      | ~ r1_tarski(k1_tarski(A_180),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_891,c_20])).

tff(c_4797,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4773,c_916])).

tff(c_4845,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_4797])).

tff(c_4846,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_4845])).

tff(c_4882,plain,(
    ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_4846])).

tff(c_4885,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_4882])).

tff(c_4887,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_103,c_4885])).

tff(c_4889,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_4887])).

tff(c_4890,plain,(
    m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4846])).

tff(c_34,plain,(
    ! [A_26,B_27] :
      ( k6_domain_1(A_26,B_27) = k1_tarski(B_27)
      | ~ m1_subset_1(B_27,A_26)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4991,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')) = k1_tarski('#skF_1'('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4890,c_34])).

tff(c_5013,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')) = k1_tarski('#skF_1'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_277,c_4991])).

tff(c_169,plain,(
    ! [A_89] : r1_tarski(A_89,A_89) ),
    inference(resolution,[status(thm)],[c_158,c_8])).

tff(c_4891,plain,(
    v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_4846])).

tff(c_1725,plain,(
    ! [A_230] :
      ( r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_230))),A_230)
      | ~ v1_zfmisc_1(A_230)
      | v1_xboole_0(A_230) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1647,c_177])).

tff(c_3030,plain,(
    ! [A_256,B_257,A_258] :
      ( r2_hidden('#skF_1'(A_256),B_257)
      | ~ r1_tarski(A_256,k1_tarski(A_258))
      | v1_xboole_0(A_256)
      | ~ r2_hidden(A_258,B_257) ) ),
    inference(resolution,[status(thm)],[c_18,c_748])).

tff(c_3073,plain,(
    ! [A_258,B_257] :
      ( r2_hidden('#skF_1'(k1_tarski(A_258)),B_257)
      | v1_xboole_0(k1_tarski(A_258))
      | ~ r2_hidden(A_258,B_257) ) ),
    inference(resolution,[status(thm)],[c_169,c_3030])).

tff(c_3095,plain,(
    ! [A_259,B_260] :
      ( r2_hidden('#skF_1'(k1_tarski(A_259)),B_260)
      | ~ r2_hidden(A_259,B_260) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_3073])).

tff(c_3269,plain,(
    ! [A_265,B_266,B_267] :
      ( r2_hidden('#skF_1'(k1_tarski(A_265)),B_266)
      | ~ r1_tarski(B_267,B_266)
      | ~ r2_hidden(A_265,B_267) ) ),
    inference(resolution,[status(thm)],[c_3095,c_6])).

tff(c_3319,plain,(
    ! [A_265] :
      ( r2_hidden('#skF_1'(k1_tarski(A_265)),u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_265,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_156,c_3269])).

tff(c_5373,plain,(
    ! [A_333,B_334] :
      ( r1_tarski(A_333,B_334)
      | ~ r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_333))),B_334)
      | ~ v1_zfmisc_1(A_333)
      | v1_xboole_0(A_333) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1647,c_18])).

tff(c_5940,plain,(
    ! [A_342] :
      ( r1_tarski(A_342,u1_struct_0('#skF_4'))
      | ~ v1_zfmisc_1(A_342)
      | v1_xboole_0(A_342)
      | ~ r2_hidden('#skF_1'(A_342),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3319,c_5373])).

tff(c_5968,plain,
    ( r1_tarski(k1_tarski('#skF_1'('#skF_5')),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))
    | v1_xboole_0(k1_tarski('#skF_1'('#skF_5')))
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1725,c_5940])).

tff(c_5993,plain,
    ( r1_tarski(k1_tarski('#skF_1'('#skF_5')),u1_struct_0('#skF_4'))
    | v1_xboole_0(k1_tarski('#skF_1'('#skF_5')))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_4891,c_5968])).

tff(c_5994,plain,(
    r1_tarski(k1_tarski('#skF_1'('#skF_5')),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_14,c_5993])).

tff(c_221,plain,(
    ! [A_104,B_6,B_105] :
      ( r2_hidden('#skF_1'(A_104),B_6)
      | ~ r1_tarski(B_105,B_6)
      | ~ r1_tarski(A_104,B_105)
      | v1_xboole_0(A_104) ) ),
    inference(resolution,[status(thm)],[c_212,c_6])).

tff(c_7031,plain,(
    ! [A_363] :
      ( r2_hidden('#skF_1'(A_363),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_363,k1_tarski('#skF_1'('#skF_5')))
      | v1_xboole_0(A_363) ) ),
    inference(resolution,[status(thm)],[c_5994,c_221])).

tff(c_7180,plain,(
    ! [A_365] :
      ( m1_subset_1('#skF_1'(A_365),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_365,k1_tarski('#skF_1'('#skF_5')))
      | v1_xboole_0(A_365) ) ),
    inference(resolution,[status(thm)],[c_7031,c_20])).

tff(c_7242,plain,
    ( m1_subset_1('#skF_1'(k1_tarski('#skF_1'('#skF_5'))),u1_struct_0('#skF_4'))
    | v1_xboole_0(k1_tarski('#skF_1'('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_169,c_7180])).

tff(c_7272,plain,(
    m1_subset_1('#skF_1'(k1_tarski('#skF_1'('#skF_5'))),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_7242])).

tff(c_7291,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'(k1_tarski('#skF_1'('#skF_5')))) = k1_tarski('#skF_1'(k1_tarski('#skF_1'('#skF_5'))))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_7272,c_34])).

tff(c_7314,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'(k1_tarski('#skF_1'('#skF_5')))) = k1_tarski('#skF_1'(k1_tarski('#skF_1'('#skF_5')))) ),
    inference(negUnitSimplification,[status(thm)],[c_277,c_7291])).

tff(c_7648,plain,
    ( k1_tarski('#skF_1'(k1_tarski('#skF_1'('#skF_5')))) = k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5'))
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_7314])).

tff(c_7659,plain,
    ( k1_tarski('#skF_1'(k1_tarski('#skF_1'('#skF_5')))) = k1_tarski('#skF_1'('#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_5013,c_7648])).

tff(c_7660,plain,(
    k1_tarski('#skF_1'(k1_tarski('#skF_1'('#skF_5')))) = k1_tarski('#skF_1'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_7659])).

tff(c_1830,plain,(
    ! [A_233] :
      ( r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_233))),A_233)
      | ~ v1_zfmisc_1(A_233)
      | v1_xboole_0(A_233) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1647,c_177])).

tff(c_1396,plain,(
    ! [A_12,B_13] :
      ( k1_tarski('#skF_1'(k1_tarski(A_12))) = B_13
      | ~ v1_zfmisc_1(B_13)
      | v1_xboole_0(B_13)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_1375])).

tff(c_1865,plain,(
    ! [A_233] :
      ( k1_tarski('#skF_1'(k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_233)))))) = A_233
      | ~ v1_zfmisc_1(A_233)
      | v1_xboole_0(A_233) ) ),
    inference(resolution,[status(thm)],[c_1830,c_1396])).

tff(c_7804,plain,
    ( k1_tarski('#skF_1'(k1_tarski('#skF_1'('#skF_5')))) = '#skF_5'
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7660,c_1865])).

tff(c_8026,plain,
    ( k1_tarski('#skF_1'('#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_7660,c_7804])).

tff(c_8027,plain,(
    k1_tarski('#skF_1'('#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_8026])).

tff(c_8371,plain,(
    r2_hidden('#skF_1'('#skF_5'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_8027,c_177])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_431,plain,(
    ! [A_130,B_131,B_132] :
      ( r2_hidden('#skF_2'(A_130,B_131),B_132)
      | ~ r1_tarski(A_130,B_132)
      | r1_tarski(A_130,B_131) ) ),
    inference(resolution,[status(thm)],[c_10,c_188])).

tff(c_10113,plain,(
    ! [A_408,B_409,B_410,B_411] :
      ( r2_hidden('#skF_2'(A_408,B_409),B_410)
      | ~ r1_tarski(B_411,B_410)
      | ~ r1_tarski(A_408,B_411)
      | r1_tarski(A_408,B_409) ) ),
    inference(resolution,[status(thm)],[c_431,c_6])).

tff(c_10334,plain,(
    ! [A_418,B_419] :
      ( r2_hidden('#skF_2'(A_418,B_419),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_418,'#skF_5')
      | r1_tarski(A_418,B_419) ) ),
    inference(resolution,[status(thm)],[c_156,c_10113])).

tff(c_10363,plain,(
    ! [A_420] :
      ( ~ r1_tarski(A_420,'#skF_5')
      | r1_tarski(A_420,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_10334,c_8])).

tff(c_10489,plain,(
    ! [A_421] :
      ( r2_hidden(A_421,u1_struct_0('#skF_4'))
      | ~ r1_tarski(k1_tarski(A_421),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_10363,c_16])).

tff(c_10545,plain,(
    ! [A_422] :
      ( m1_subset_1(A_422,u1_struct_0('#skF_4'))
      | ~ r1_tarski(k1_tarski(A_422),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_10489,c_20])).

tff(c_10586,plain,(
    ! [A_423] :
      ( m1_subset_1(A_423,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_423,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_18,c_10545])).

tff(c_54,plain,(
    ! [A_45,B_46] :
      ( m1_pre_topc(k1_tex_2(A_45,B_46),A_45)
      | ~ m1_subset_1(B_46,u1_struct_0(A_45))
      | ~ l1_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_10591,plain,(
    ! [A_423] :
      ( m1_pre_topc(k1_tex_2('#skF_4',A_423),'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r2_hidden(A_423,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_10586,c_54])).

tff(c_10607,plain,(
    ! [A_423] :
      ( m1_pre_topc(k1_tex_2('#skF_4',A_423),'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r2_hidden(A_423,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_10591])).

tff(c_10608,plain,(
    ! [A_423] :
      ( m1_pre_topc(k1_tex_2('#skF_4',A_423),'#skF_4')
      | ~ r2_hidden(A_423,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_10607])).

tff(c_64,plain,(
    ! [A_47,B_48] :
      ( ~ v2_struct_0(k1_tex_2(A_47,B_48))
      | ~ m1_subset_1(B_48,u1_struct_0(A_47))
      | ~ l1_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_4985,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_4','#skF_1'('#skF_5')))
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4890,c_64])).

tff(c_5005,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_4','#skF_1'('#skF_5')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_4985])).

tff(c_5006,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_4','#skF_1'('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_5005])).

tff(c_4979,plain,
    ( m1_pre_topc(k1_tex_2('#skF_4','#skF_1'('#skF_5')),'#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4890,c_54])).

tff(c_4997,plain,
    ( m1_pre_topc(k1_tex_2('#skF_4','#skF_1'('#skF_5')),'#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_4979])).

tff(c_4998,plain,(
    m1_pre_topc(k1_tex_2('#skF_4','#skF_1'('#skF_5')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_4997])).

tff(c_26,plain,(
    ! [B_20,A_18] :
      ( v2_pre_topc(B_20)
      | ~ m1_pre_topc(B_20,A_18)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_5055,plain,
    ( v2_pre_topc(k1_tex_2('#skF_4','#skF_1'('#skF_5')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_4998,c_26])).

tff(c_5077,plain,(
    v2_pre_topc(k1_tex_2('#skF_4','#skF_1'('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_5055])).

tff(c_62,plain,(
    ! [A_47,B_48] :
      ( v7_struct_0(k1_tex_2(A_47,B_48))
      | ~ m1_subset_1(B_48,u1_struct_0(A_47))
      | ~ l1_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_4988,plain,
    ( v7_struct_0(k1_tex_2('#skF_4','#skF_1'('#skF_5')))
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4890,c_62])).

tff(c_5009,plain,
    ( v7_struct_0(k1_tex_2('#skF_4','#skF_1'('#skF_5')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_4988])).

tff(c_5010,plain,(
    v7_struct_0(k1_tex_2('#skF_4','#skF_1'('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_5009])).

tff(c_801,plain,(
    ! [A_170] :
      ( m1_subset_1('#skF_1'(A_170),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_170,'#skF_5')
      | v1_xboole_0(A_170) ) ),
    inference(resolution,[status(thm)],[c_780,c_20])).

tff(c_803,plain,(
    ! [A_170] :
      ( m1_pre_topc(k1_tex_2('#skF_4','#skF_1'(A_170)),'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_170,'#skF_5')
      | v1_xboole_0(A_170) ) ),
    inference(resolution,[status(thm)],[c_801,c_54])).

tff(c_818,plain,(
    ! [A_170] :
      ( m1_pre_topc(k1_tex_2('#skF_4','#skF_1'(A_170)),'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_170,'#skF_5')
      | v1_xboole_0(A_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_803])).

tff(c_819,plain,(
    ! [A_170] :
      ( m1_pre_topc(k1_tex_2('#skF_4','#skF_1'(A_170)),'#skF_4')
      | ~ r1_tarski(A_170,'#skF_5')
      | v1_xboole_0(A_170) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_818])).

tff(c_883,plain,(
    ! [B_178,A_179] :
      ( v1_tdlat_3(B_178)
      | ~ v2_pre_topc(B_178)
      | ~ v7_struct_0(B_178)
      | v2_struct_0(B_178)
      | ~ m1_pre_topc(B_178,A_179)
      | ~ l1_pre_topc(A_179)
      | v2_struct_0(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_886,plain,(
    ! [A_170] :
      ( v1_tdlat_3(k1_tex_2('#skF_4','#skF_1'(A_170)))
      | ~ v2_pre_topc(k1_tex_2('#skF_4','#skF_1'(A_170)))
      | ~ v7_struct_0(k1_tex_2('#skF_4','#skF_1'(A_170)))
      | v2_struct_0(k1_tex_2('#skF_4','#skF_1'(A_170)))
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_170,'#skF_5')
      | v1_xboole_0(A_170) ) ),
    inference(resolution,[status(thm)],[c_819,c_883])).

tff(c_889,plain,(
    ! [A_170] :
      ( v1_tdlat_3(k1_tex_2('#skF_4','#skF_1'(A_170)))
      | ~ v2_pre_topc(k1_tex_2('#skF_4','#skF_1'(A_170)))
      | ~ v7_struct_0(k1_tex_2('#skF_4','#skF_1'(A_170)))
      | v2_struct_0(k1_tex_2('#skF_4','#skF_1'(A_170)))
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_170,'#skF_5')
      | v1_xboole_0(A_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_886])).

tff(c_890,plain,(
    ! [A_170] :
      ( v1_tdlat_3(k1_tex_2('#skF_4','#skF_1'(A_170)))
      | ~ v2_pre_topc(k1_tex_2('#skF_4','#skF_1'(A_170)))
      | ~ v7_struct_0(k1_tex_2('#skF_4','#skF_1'(A_170)))
      | v2_struct_0(k1_tex_2('#skF_4','#skF_1'(A_170)))
      | ~ r1_tarski(A_170,'#skF_5')
      | v1_xboole_0(A_170) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_889])).

tff(c_5019,plain,
    ( v1_tdlat_3(k1_tex_2('#skF_4','#skF_1'('#skF_5')))
    | ~ v2_pre_topc(k1_tex_2('#skF_4','#skF_1'('#skF_5')))
    | v2_struct_0(k1_tex_2('#skF_4','#skF_1'('#skF_5')))
    | ~ r1_tarski('#skF_5','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_5010,c_890])).

tff(c_5032,plain,
    ( v1_tdlat_3(k1_tex_2('#skF_4','#skF_1'('#skF_5')))
    | ~ v2_pre_topc(k1_tex_2('#skF_4','#skF_1'('#skF_5')))
    | v2_struct_0(k1_tex_2('#skF_4','#skF_1'('#skF_5')))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_5019])).

tff(c_5033,plain,
    ( v1_tdlat_3(k1_tex_2('#skF_4','#skF_1'('#skF_5')))
    | ~ v2_pre_topc(k1_tex_2('#skF_4','#skF_1'('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_5006,c_5032])).

tff(c_5242,plain,(
    v1_tdlat_3(k1_tex_2('#skF_4','#skF_1'('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5077,c_5033])).

tff(c_60,plain,(
    ! [A_47,B_48] :
      ( v1_pre_topc(k1_tex_2(A_47,B_48))
      | ~ m1_subset_1(B_48,u1_struct_0(A_47))
      | ~ l1_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_4982,plain,
    ( v1_pre_topc(k1_tex_2('#skF_4','#skF_1'('#skF_5')))
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4890,c_60])).

tff(c_5001,plain,
    ( v1_pre_topc(k1_tex_2('#skF_4','#skF_1'('#skF_5')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_4982])).

tff(c_5002,plain,(
    v1_pre_topc(k1_tex_2('#skF_4','#skF_1'('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_5001])).

tff(c_52,plain,(
    ! [A_38,B_42] :
      ( k6_domain_1(u1_struct_0(A_38),B_42) = u1_struct_0(k1_tex_2(A_38,B_42))
      | ~ m1_pre_topc(k1_tex_2(A_38,B_42),A_38)
      | ~ v1_pre_topc(k1_tex_2(A_38,B_42))
      | v2_struct_0(k1_tex_2(A_38,B_42))
      | ~ m1_subset_1(B_42,u1_struct_0(A_38))
      | ~ l1_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_5043,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')) = u1_struct_0(k1_tex_2('#skF_4','#skF_1'('#skF_5')))
    | ~ v1_pre_topc(k1_tex_2('#skF_4','#skF_1'('#skF_5')))
    | v2_struct_0(k1_tex_2('#skF_4','#skF_1'('#skF_5')))
    | ~ m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4998,c_52])).

tff(c_5061,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')) = u1_struct_0(k1_tex_2('#skF_4','#skF_1'('#skF_5')))
    | v2_struct_0(k1_tex_2('#skF_4','#skF_1'('#skF_5')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_4890,c_5002,c_5043])).

tff(c_5062,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')) = u1_struct_0(k1_tex_2('#skF_4','#skF_1'('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_5006,c_5061])).

tff(c_5105,plain,(
    u1_struct_0(k1_tex_2('#skF_4','#skF_1'('#skF_5'))) = k1_tarski('#skF_1'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5013,c_5062])).

tff(c_8162,plain,(
    u1_struct_0(k1_tex_2('#skF_4','#skF_1'('#skF_5'))) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8027,c_5105])).

tff(c_36,plain,(
    ! [B_30,A_28] :
      ( m1_subset_1(u1_struct_0(B_30),k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_pre_topc(B_30,A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_3321,plain,(
    ! [B_268,A_269] :
      ( v2_tex_2(u1_struct_0(B_268),A_269)
      | ~ v1_tdlat_3(B_268)
      | ~ m1_subset_1(u1_struct_0(B_268),k1_zfmisc_1(u1_struct_0(A_269)))
      | ~ m1_pre_topc(B_268,A_269)
      | v2_struct_0(B_268)
      | ~ l1_pre_topc(A_269)
      | v2_struct_0(A_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_3328,plain,(
    ! [B_30,A_28] :
      ( v2_tex_2(u1_struct_0(B_30),A_28)
      | ~ v1_tdlat_3(B_30)
      | v2_struct_0(B_30)
      | v2_struct_0(A_28)
      | ~ m1_pre_topc(B_30,A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(resolution,[status(thm)],[c_36,c_3321])).

tff(c_8751,plain,(
    ! [A_28] :
      ( v2_tex_2('#skF_5',A_28)
      | ~ v1_tdlat_3(k1_tex_2('#skF_4','#skF_1'('#skF_5')))
      | v2_struct_0(k1_tex_2('#skF_4','#skF_1'('#skF_5')))
      | v2_struct_0(A_28)
      | ~ m1_pre_topc(k1_tex_2('#skF_4','#skF_1'('#skF_5')),A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8162,c_3328])).

tff(c_8839,plain,(
    ! [A_28] :
      ( v2_tex_2('#skF_5',A_28)
      | v2_struct_0(k1_tex_2('#skF_4','#skF_1'('#skF_5')))
      | v2_struct_0(A_28)
      | ~ m1_pre_topc(k1_tex_2('#skF_4','#skF_1'('#skF_5')),A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5242,c_8751])).

tff(c_16227,plain,(
    ! [A_584] :
      ( v2_tex_2('#skF_5',A_584)
      | v2_struct_0(A_584)
      | ~ m1_pre_topc(k1_tex_2('#skF_4','#skF_1'('#skF_5')),A_584)
      | ~ l1_pre_topc(A_584) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5006,c_8839])).

tff(c_16235,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_10608,c_16227])).

tff(c_16249,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8371,c_86,c_16235])).

tff(c_16251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_105,c_16249])).

tff(c_16252,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_19596,plain,(
    ! [A_792,B_793] :
      ( m1_pre_topc('#skF_3'(A_792,B_793),A_792)
      | ~ v2_tex_2(B_793,A_792)
      | ~ m1_subset_1(B_793,k1_zfmisc_1(u1_struct_0(A_792)))
      | v1_xboole_0(B_793)
      | ~ l1_pre_topc(A_792)
      | ~ v2_pre_topc(A_792)
      | v2_struct_0(A_792) ) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_19627,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_19596])).

tff(c_19640,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_16252,c_19627])).

tff(c_19641,plain,(
    m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_84,c_19640])).

tff(c_30,plain,(
    ! [B_24,A_22] :
      ( l1_pre_topc(B_24)
      | ~ m1_pre_topc(B_24,A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_19656,plain,
    ( l1_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_19641,c_30])).

tff(c_19674,plain,(
    l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_19656])).

tff(c_28,plain,(
    ! [A_21] :
      ( l1_struct_0(A_21)
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16253,plain,(
    ~ v1_zfmisc_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_18300,plain,(
    ! [A_753,B_754] :
      ( ~ v2_struct_0('#skF_3'(A_753,B_754))
      | ~ v2_tex_2(B_754,A_753)
      | ~ m1_subset_1(B_754,k1_zfmisc_1(u1_struct_0(A_753)))
      | v1_xboole_0(B_754)
      | ~ l1_pre_topc(A_753)
      | ~ v2_pre_topc(A_753)
      | v2_struct_0(A_753) ) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_18330,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_18300])).

tff(c_18340,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_16252,c_18330])).

tff(c_18341,plain,(
    ~ v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_84,c_18340])).

tff(c_88,plain,(
    v2_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_277])).

tff(c_17690,plain,(
    ! [A_743,B_744] :
      ( v1_tdlat_3('#skF_3'(A_743,B_744))
      | ~ v2_tex_2(B_744,A_743)
      | ~ m1_subset_1(B_744,k1_zfmisc_1(u1_struct_0(A_743)))
      | v1_xboole_0(B_744)
      | ~ l1_pre_topc(A_743)
      | ~ v2_pre_topc(A_743)
      | v2_struct_0(A_743) ) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_17716,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_17690])).

tff(c_17725,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_16252,c_17716])).

tff(c_17726,plain,(
    v1_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_84,c_17725])).

tff(c_46,plain,(
    ! [B_37,A_35] :
      ( ~ v1_tdlat_3(B_37)
      | v7_struct_0(B_37)
      | v2_struct_0(B_37)
      | ~ m1_pre_topc(B_37,A_35)
      | ~ l1_pre_topc(A_35)
      | ~ v2_tdlat_3(A_35)
      | ~ v2_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_19644,plain,
    ( ~ v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v7_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_19641,c_46])).

tff(c_19659,plain,
    ( v7_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_17726,c_19644])).

tff(c_19660,plain,(
    v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_18341,c_19659])).

tff(c_19845,plain,(
    ! [A_799,B_800] :
      ( u1_struct_0('#skF_3'(A_799,B_800)) = B_800
      | ~ v2_tex_2(B_800,A_799)
      | ~ m1_subset_1(B_800,k1_zfmisc_1(u1_struct_0(A_799)))
      | v1_xboole_0(B_800)
      | ~ l1_pre_topc(A_799)
      | ~ v2_pre_topc(A_799)
      | v2_struct_0(A_799) ) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_19887,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_19845])).

tff(c_19900,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_16252,c_19887])).

tff(c_19901,plain,(
    u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_84,c_19900])).

tff(c_32,plain,(
    ! [A_25] :
      ( v1_zfmisc_1(u1_struct_0(A_25))
      | ~ l1_struct_0(A_25)
      | ~ v7_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_19967,plain,
    ( v1_zfmisc_1('#skF_5')
    | ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_19901,c_32])).

tff(c_20026,plain,
    ( v1_zfmisc_1('#skF_5')
    | ~ l1_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19660,c_19967])).

tff(c_20027,plain,(
    ~ l1_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_16253,c_20026])).

tff(c_20031,plain,(
    ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_28,c_20027])).

tff(c_20035,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19674,c_20031])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:40:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.44/4.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.44/4.64  
% 11.44/4.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.44/4.64  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 11.44/4.64  
% 11.44/4.64  %Foreground sorts:
% 11.44/4.64  
% 11.44/4.64  
% 11.44/4.64  %Background operators:
% 11.44/4.64  
% 11.44/4.64  
% 11.44/4.64  %Foreground operators:
% 11.44/4.64  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.44/4.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.44/4.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.44/4.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.44/4.64  tff('#skF_1', type, '#skF_1': $i > $i).
% 11.44/4.64  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 11.44/4.64  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.44/4.64  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 11.44/4.64  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.44/4.64  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 11.44/4.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.44/4.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.44/4.64  tff('#skF_5', type, '#skF_5': $i).
% 11.44/4.64  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 11.44/4.64  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 11.44/4.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.44/4.64  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 11.44/4.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.44/4.64  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 11.44/4.64  tff('#skF_4', type, '#skF_4': $i).
% 11.44/4.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.44/4.64  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.44/4.64  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 11.44/4.64  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 11.44/4.64  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.44/4.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.44/4.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.44/4.64  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 11.44/4.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.44/4.64  
% 11.59/4.68  tff(f_277, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 11.59/4.68  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.59/4.68  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 11.59/4.68  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 11.59/4.68  tff(f_43, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 11.59/4.68  tff(f_47, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 11.59/4.68  tff(f_208, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 11.59/4.68  tff(f_51, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 11.59/4.68  tff(f_88, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 11.59/4.68  tff(f_181, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 11.59/4.68  tff(f_195, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 11.59/4.68  tff(f_64, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 11.59/4.68  tff(f_117, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (((~v2_struct_0(B) & v7_struct_0(B)) & v2_pre_topc(B)) => ((~v2_struct_0(B) & v1_tdlat_3(B)) & v2_tdlat_3(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc25_tex_2)).
% 11.59/4.68  tff(f_167, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ((C = k1_tex_2(A, B)) <=> (u1_struct_0(C) = k6_domain_1(u1_struct_0(A), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tex_2)).
% 11.59/4.68  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 11.59/4.68  tff(f_228, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_tex_2)).
% 11.59/4.68  tff(f_257, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tex_2)).
% 11.59/4.68  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 11.59/4.68  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 11.59/4.68  tff(f_147, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((~v2_struct_0(B) & ~v7_struct_0(B)) => (~v2_struct_0(B) & ~v1_tdlat_3(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc32_tex_2)).
% 11.59/4.68  tff(f_81, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 11.59/4.68  tff(c_86, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_277])).
% 11.59/4.68  tff(c_92, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_277])).
% 11.59/4.68  tff(c_84, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_277])).
% 11.59/4.68  tff(c_90, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_277])).
% 11.59/4.68  tff(c_100, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_277])).
% 11.59/4.68  tff(c_103, plain, (v1_zfmisc_1('#skF_5')), inference(splitLeft, [status(thm)], [c_100])).
% 11.59/4.68  tff(c_94, plain, (~v1_zfmisc_1('#skF_5') | ~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_277])).
% 11.59/4.68  tff(c_105, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_94])).
% 11.59/4.68  tff(c_82, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_277])).
% 11.59/4.68  tff(c_143, plain, (![A_85, B_86]: (r1_tarski(A_85, B_86) | ~m1_subset_1(A_85, k1_zfmisc_1(B_86)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.59/4.68  tff(c_156, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_82, c_143])).
% 11.59/4.68  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.59/4.68  tff(c_188, plain, (![C_94, B_95, A_96]: (r2_hidden(C_94, B_95) | ~r2_hidden(C_94, A_96) | ~r1_tarski(A_96, B_95))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.59/4.68  tff(c_212, plain, (![A_104, B_105]: (r2_hidden('#skF_1'(A_104), B_105) | ~r1_tarski(A_104, B_105) | v1_xboole_0(A_104))), inference(resolution, [status(thm)], [c_4, c_188])).
% 11.59/4.68  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.59/4.68  tff(c_256, plain, (![B_109, A_110]: (~v1_xboole_0(B_109) | ~r1_tarski(A_110, B_109) | v1_xboole_0(A_110))), inference(resolution, [status(thm)], [c_212, c_2])).
% 11.59/4.68  tff(c_268, plain, (~v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_156, c_256])).
% 11.59/4.68  tff(c_277, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_84, c_268])).
% 11.59/4.68  tff(c_14, plain, (![A_11]: (~v1_xboole_0(k1_tarski(A_11)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.59/4.68  tff(c_18, plain, (![A_12, B_13]: (r1_tarski(k1_tarski(A_12), B_13) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.59/4.68  tff(c_325, plain, (![B_123, A_124]: (B_123=A_124 | ~r1_tarski(A_124, B_123) | ~v1_zfmisc_1(B_123) | v1_xboole_0(B_123) | v1_xboole_0(A_124))), inference(cnfTransformation, [status(thm)], [f_208])).
% 11.59/4.68  tff(c_349, plain, (![A_12, B_13]: (k1_tarski(A_12)=B_13 | ~v1_zfmisc_1(B_13) | v1_xboole_0(B_13) | v1_xboole_0(k1_tarski(A_12)) | ~r2_hidden(A_12, B_13))), inference(resolution, [status(thm)], [c_18, c_325])).
% 11.59/4.68  tff(c_369, plain, (![A_125, B_126]: (k1_tarski(A_125)=B_126 | ~v1_zfmisc_1(B_126) | v1_xboole_0(B_126) | ~r2_hidden(A_125, B_126))), inference(negUnitSimplification, [status(thm)], [c_14, c_349])).
% 11.59/4.68  tff(c_388, plain, (![A_1]: (k1_tarski('#skF_1'(A_1))=A_1 | ~v1_zfmisc_1(A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_369])).
% 11.59/4.68  tff(c_197, plain, (![A_1, B_95]: (r2_hidden('#skF_1'(A_1), B_95) | ~r1_tarski(A_1, B_95) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_188])).
% 11.59/4.68  tff(c_1347, plain, (![A_221, B_222]: (k1_tarski('#skF_1'(A_221))=B_222 | ~v1_zfmisc_1(B_222) | v1_xboole_0(B_222) | ~r1_tarski(A_221, B_222) | v1_xboole_0(A_221))), inference(resolution, [status(thm)], [c_197, c_369])).
% 11.59/4.68  tff(c_1375, plain, (![A_12, B_13]: (k1_tarski('#skF_1'(k1_tarski(A_12)))=B_13 | ~v1_zfmisc_1(B_13) | v1_xboole_0(B_13) | v1_xboole_0(k1_tarski(A_12)) | ~r2_hidden(A_12, B_13))), inference(resolution, [status(thm)], [c_18, c_1347])).
% 11.59/4.68  tff(c_1397, plain, (![A_223, B_224]: (k1_tarski('#skF_1'(k1_tarski(A_223)))=B_224 | ~v1_zfmisc_1(B_224) | v1_xboole_0(B_224) | ~r2_hidden(A_223, B_224))), inference(negUnitSimplification, [status(thm)], [c_14, c_1375])).
% 11.59/4.68  tff(c_1647, plain, (![A_230]: (k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_230))))=A_230 | ~v1_zfmisc_1(A_230) | v1_xboole_0(A_230))), inference(resolution, [status(thm)], [c_4, c_1397])).
% 11.59/4.68  tff(c_158, plain, (![A_89, B_90]: (r2_hidden('#skF_2'(A_89, B_90), A_89) | r1_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.59/4.68  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.59/4.68  tff(c_172, plain, (![A_91]: (r1_tarski(A_91, A_91))), inference(resolution, [status(thm)], [c_158, c_8])).
% 11.59/4.68  tff(c_16, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | ~r1_tarski(k1_tarski(A_12), B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.59/4.68  tff(c_177, plain, (![A_12]: (r2_hidden(A_12, k1_tarski(A_12)))), inference(resolution, [status(thm)], [c_172, c_16])).
% 11.59/4.68  tff(c_389, plain, (![A_127]: (k1_tarski('#skF_1'(A_127))=A_127 | ~v1_zfmisc_1(A_127) | v1_xboole_0(A_127))), inference(resolution, [status(thm)], [c_4, c_369])).
% 11.59/4.68  tff(c_525, plain, (![A_143, B_144]: (r1_tarski(A_143, B_144) | ~r2_hidden('#skF_1'(A_143), B_144) | ~v1_zfmisc_1(A_143) | v1_xboole_0(A_143))), inference(superposition, [status(thm), theory('equality')], [c_389, c_18])).
% 11.59/4.68  tff(c_537, plain, (![A_143]: (r1_tarski(A_143, k1_tarski('#skF_1'(A_143))) | ~v1_zfmisc_1(A_143) | v1_xboole_0(A_143))), inference(resolution, [status(thm)], [c_177, c_525])).
% 11.59/4.68  tff(c_1713, plain, (![A_230]: (r1_tarski(k1_tarski('#skF_1'(A_230)), A_230) | ~v1_zfmisc_1(k1_tarski('#skF_1'(A_230))) | v1_xboole_0(k1_tarski('#skF_1'(A_230))) | ~v1_zfmisc_1(A_230) | v1_xboole_0(A_230))), inference(superposition, [status(thm), theory('equality')], [c_1647, c_537])).
% 11.59/4.68  tff(c_4773, plain, (![A_317]: (r1_tarski(k1_tarski('#skF_1'(A_317)), A_317) | ~v1_zfmisc_1(k1_tarski('#skF_1'(A_317))) | ~v1_zfmisc_1(A_317) | v1_xboole_0(A_317))), inference(negUnitSimplification, [status(thm)], [c_14, c_1713])).
% 11.59/4.68  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.59/4.68  tff(c_748, plain, (![A_164, B_165, B_166]: (r2_hidden('#skF_1'(A_164), B_165) | ~r1_tarski(B_166, B_165) | ~r1_tarski(A_164, B_166) | v1_xboole_0(A_164))), inference(resolution, [status(thm)], [c_212, c_6])).
% 11.59/4.68  tff(c_780, plain, (![A_169]: (r2_hidden('#skF_1'(A_169), u1_struct_0('#skF_4')) | ~r1_tarski(A_169, '#skF_5') | v1_xboole_0(A_169))), inference(resolution, [status(thm)], [c_156, c_748])).
% 11.59/4.68  tff(c_404, plain, (![A_127, B_13]: (r1_tarski(A_127, B_13) | ~r2_hidden('#skF_1'(A_127), B_13) | ~v1_zfmisc_1(A_127) | v1_xboole_0(A_127))), inference(superposition, [status(thm), theory('equality')], [c_389, c_18])).
% 11.59/4.68  tff(c_838, plain, (![A_174]: (r1_tarski(A_174, u1_struct_0('#skF_4')) | ~v1_zfmisc_1(A_174) | ~r1_tarski(A_174, '#skF_5') | v1_xboole_0(A_174))), inference(resolution, [status(thm)], [c_780, c_404])).
% 11.59/4.68  tff(c_852, plain, (![A_12]: (r2_hidden(A_12, u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski(A_12)) | ~r1_tarski(k1_tarski(A_12), '#skF_5') | v1_xboole_0(k1_tarski(A_12)))), inference(resolution, [status(thm)], [c_838, c_16])).
% 11.59/4.68  tff(c_891, plain, (![A_180]: (r2_hidden(A_180, u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski(A_180)) | ~r1_tarski(k1_tarski(A_180), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_14, c_852])).
% 11.59/4.68  tff(c_20, plain, (![A_14, B_15]: (m1_subset_1(A_14, B_15) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.59/4.68  tff(c_916, plain, (![A_180]: (m1_subset_1(A_180, u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski(A_180)) | ~r1_tarski(k1_tarski(A_180), '#skF_5'))), inference(resolution, [status(thm)], [c_891, c_20])).
% 11.59/4.68  tff(c_4797, plain, (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4773, c_916])).
% 11.59/4.68  tff(c_4845, plain, (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_4797])).
% 11.59/4.68  tff(c_4846, plain, (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_84, c_4845])).
% 11.59/4.68  tff(c_4882, plain, (~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))), inference(splitLeft, [status(thm)], [c_4846])).
% 11.59/4.68  tff(c_4885, plain, (~v1_zfmisc_1('#skF_5') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_388, c_4882])).
% 11.59/4.68  tff(c_4887, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_103, c_4885])).
% 11.59/4.68  tff(c_4889, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_4887])).
% 11.59/4.68  tff(c_4890, plain, (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_4846])).
% 11.59/4.68  tff(c_34, plain, (![A_26, B_27]: (k6_domain_1(A_26, B_27)=k1_tarski(B_27) | ~m1_subset_1(B_27, A_26) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.59/4.68  tff(c_4991, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'('#skF_5'))=k1_tarski('#skF_1'('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_4890, c_34])).
% 11.59/4.68  tff(c_5013, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'('#skF_5'))=k1_tarski('#skF_1'('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_277, c_4991])).
% 11.59/4.68  tff(c_169, plain, (![A_89]: (r1_tarski(A_89, A_89))), inference(resolution, [status(thm)], [c_158, c_8])).
% 11.59/4.68  tff(c_4891, plain, (v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))), inference(splitRight, [status(thm)], [c_4846])).
% 11.59/4.68  tff(c_1725, plain, (![A_230]: (r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_230))), A_230) | ~v1_zfmisc_1(A_230) | v1_xboole_0(A_230))), inference(superposition, [status(thm), theory('equality')], [c_1647, c_177])).
% 11.59/4.68  tff(c_3030, plain, (![A_256, B_257, A_258]: (r2_hidden('#skF_1'(A_256), B_257) | ~r1_tarski(A_256, k1_tarski(A_258)) | v1_xboole_0(A_256) | ~r2_hidden(A_258, B_257))), inference(resolution, [status(thm)], [c_18, c_748])).
% 11.59/4.68  tff(c_3073, plain, (![A_258, B_257]: (r2_hidden('#skF_1'(k1_tarski(A_258)), B_257) | v1_xboole_0(k1_tarski(A_258)) | ~r2_hidden(A_258, B_257))), inference(resolution, [status(thm)], [c_169, c_3030])).
% 11.59/4.68  tff(c_3095, plain, (![A_259, B_260]: (r2_hidden('#skF_1'(k1_tarski(A_259)), B_260) | ~r2_hidden(A_259, B_260))), inference(negUnitSimplification, [status(thm)], [c_14, c_3073])).
% 11.59/4.68  tff(c_3269, plain, (![A_265, B_266, B_267]: (r2_hidden('#skF_1'(k1_tarski(A_265)), B_266) | ~r1_tarski(B_267, B_266) | ~r2_hidden(A_265, B_267))), inference(resolution, [status(thm)], [c_3095, c_6])).
% 11.59/4.68  tff(c_3319, plain, (![A_265]: (r2_hidden('#skF_1'(k1_tarski(A_265)), u1_struct_0('#skF_4')) | ~r2_hidden(A_265, '#skF_5'))), inference(resolution, [status(thm)], [c_156, c_3269])).
% 11.59/4.68  tff(c_5373, plain, (![A_333, B_334]: (r1_tarski(A_333, B_334) | ~r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_333))), B_334) | ~v1_zfmisc_1(A_333) | v1_xboole_0(A_333))), inference(superposition, [status(thm), theory('equality')], [c_1647, c_18])).
% 11.59/4.68  tff(c_5940, plain, (![A_342]: (r1_tarski(A_342, u1_struct_0('#skF_4')) | ~v1_zfmisc_1(A_342) | v1_xboole_0(A_342) | ~r2_hidden('#skF_1'(A_342), '#skF_5'))), inference(resolution, [status(thm)], [c_3319, c_5373])).
% 11.59/4.68  tff(c_5968, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) | v1_xboole_0(k1_tarski('#skF_1'('#skF_5'))) | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_1725, c_5940])).
% 11.59/4.68  tff(c_5993, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), u1_struct_0('#skF_4')) | v1_xboole_0(k1_tarski('#skF_1'('#skF_5'))) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_4891, c_5968])).
% 11.59/4.68  tff(c_5994, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_84, c_14, c_5993])).
% 11.59/4.68  tff(c_221, plain, (![A_104, B_6, B_105]: (r2_hidden('#skF_1'(A_104), B_6) | ~r1_tarski(B_105, B_6) | ~r1_tarski(A_104, B_105) | v1_xboole_0(A_104))), inference(resolution, [status(thm)], [c_212, c_6])).
% 11.59/4.68  tff(c_7031, plain, (![A_363]: (r2_hidden('#skF_1'(A_363), u1_struct_0('#skF_4')) | ~r1_tarski(A_363, k1_tarski('#skF_1'('#skF_5'))) | v1_xboole_0(A_363))), inference(resolution, [status(thm)], [c_5994, c_221])).
% 11.59/4.68  tff(c_7180, plain, (![A_365]: (m1_subset_1('#skF_1'(A_365), u1_struct_0('#skF_4')) | ~r1_tarski(A_365, k1_tarski('#skF_1'('#skF_5'))) | v1_xboole_0(A_365))), inference(resolution, [status(thm)], [c_7031, c_20])).
% 11.59/4.68  tff(c_7242, plain, (m1_subset_1('#skF_1'(k1_tarski('#skF_1'('#skF_5'))), u1_struct_0('#skF_4')) | v1_xboole_0(k1_tarski('#skF_1'('#skF_5')))), inference(resolution, [status(thm)], [c_169, c_7180])).
% 11.59/4.68  tff(c_7272, plain, (m1_subset_1('#skF_1'(k1_tarski('#skF_1'('#skF_5'))), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_14, c_7242])).
% 11.59/4.68  tff(c_7291, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'(k1_tarski('#skF_1'('#skF_5'))))=k1_tarski('#skF_1'(k1_tarski('#skF_1'('#skF_5')))) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_7272, c_34])).
% 11.59/4.68  tff(c_7314, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'(k1_tarski('#skF_1'('#skF_5'))))=k1_tarski('#skF_1'(k1_tarski('#skF_1'('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_277, c_7291])).
% 11.59/4.68  tff(c_7648, plain, (k1_tarski('#skF_1'(k1_tarski('#skF_1'('#skF_5'))))=k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'('#skF_5')) | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_388, c_7314])).
% 11.59/4.68  tff(c_7659, plain, (k1_tarski('#skF_1'(k1_tarski('#skF_1'('#skF_5'))))=k1_tarski('#skF_1'('#skF_5')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_5013, c_7648])).
% 11.59/4.68  tff(c_7660, plain, (k1_tarski('#skF_1'(k1_tarski('#skF_1'('#skF_5'))))=k1_tarski('#skF_1'('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_84, c_7659])).
% 11.59/4.68  tff(c_1830, plain, (![A_233]: (r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_233))), A_233) | ~v1_zfmisc_1(A_233) | v1_xboole_0(A_233))), inference(superposition, [status(thm), theory('equality')], [c_1647, c_177])).
% 11.59/4.68  tff(c_1396, plain, (![A_12, B_13]: (k1_tarski('#skF_1'(k1_tarski(A_12)))=B_13 | ~v1_zfmisc_1(B_13) | v1_xboole_0(B_13) | ~r2_hidden(A_12, B_13))), inference(negUnitSimplification, [status(thm)], [c_14, c_1375])).
% 11.59/4.68  tff(c_1865, plain, (![A_233]: (k1_tarski('#skF_1'(k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_233))))))=A_233 | ~v1_zfmisc_1(A_233) | v1_xboole_0(A_233))), inference(resolution, [status(thm)], [c_1830, c_1396])).
% 11.59/4.68  tff(c_7804, plain, (k1_tarski('#skF_1'(k1_tarski('#skF_1'('#skF_5'))))='#skF_5' | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7660, c_1865])).
% 11.59/4.68  tff(c_8026, plain, (k1_tarski('#skF_1'('#skF_5'))='#skF_5' | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_7660, c_7804])).
% 11.59/4.68  tff(c_8027, plain, (k1_tarski('#skF_1'('#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_84, c_8026])).
% 11.59/4.68  tff(c_8371, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_8027, c_177])).
% 11.59/4.68  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.59/4.68  tff(c_431, plain, (![A_130, B_131, B_132]: (r2_hidden('#skF_2'(A_130, B_131), B_132) | ~r1_tarski(A_130, B_132) | r1_tarski(A_130, B_131))), inference(resolution, [status(thm)], [c_10, c_188])).
% 11.59/4.68  tff(c_10113, plain, (![A_408, B_409, B_410, B_411]: (r2_hidden('#skF_2'(A_408, B_409), B_410) | ~r1_tarski(B_411, B_410) | ~r1_tarski(A_408, B_411) | r1_tarski(A_408, B_409))), inference(resolution, [status(thm)], [c_431, c_6])).
% 11.59/4.68  tff(c_10334, plain, (![A_418, B_419]: (r2_hidden('#skF_2'(A_418, B_419), u1_struct_0('#skF_4')) | ~r1_tarski(A_418, '#skF_5') | r1_tarski(A_418, B_419))), inference(resolution, [status(thm)], [c_156, c_10113])).
% 11.59/4.68  tff(c_10363, plain, (![A_420]: (~r1_tarski(A_420, '#skF_5') | r1_tarski(A_420, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_10334, c_8])).
% 11.59/4.68  tff(c_10489, plain, (![A_421]: (r2_hidden(A_421, u1_struct_0('#skF_4')) | ~r1_tarski(k1_tarski(A_421), '#skF_5'))), inference(resolution, [status(thm)], [c_10363, c_16])).
% 11.59/4.68  tff(c_10545, plain, (![A_422]: (m1_subset_1(A_422, u1_struct_0('#skF_4')) | ~r1_tarski(k1_tarski(A_422), '#skF_5'))), inference(resolution, [status(thm)], [c_10489, c_20])).
% 11.59/4.68  tff(c_10586, plain, (![A_423]: (m1_subset_1(A_423, u1_struct_0('#skF_4')) | ~r2_hidden(A_423, '#skF_5'))), inference(resolution, [status(thm)], [c_18, c_10545])).
% 11.59/4.68  tff(c_54, plain, (![A_45, B_46]: (m1_pre_topc(k1_tex_2(A_45, B_46), A_45) | ~m1_subset_1(B_46, u1_struct_0(A_45)) | ~l1_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_181])).
% 11.59/4.68  tff(c_10591, plain, (![A_423]: (m1_pre_topc(k1_tex_2('#skF_4', A_423), '#skF_4') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r2_hidden(A_423, '#skF_5'))), inference(resolution, [status(thm)], [c_10586, c_54])).
% 11.59/4.68  tff(c_10607, plain, (![A_423]: (m1_pre_topc(k1_tex_2('#skF_4', A_423), '#skF_4') | v2_struct_0('#skF_4') | ~r2_hidden(A_423, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_10591])).
% 11.59/4.68  tff(c_10608, plain, (![A_423]: (m1_pre_topc(k1_tex_2('#skF_4', A_423), '#skF_4') | ~r2_hidden(A_423, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_92, c_10607])).
% 11.59/4.68  tff(c_64, plain, (![A_47, B_48]: (~v2_struct_0(k1_tex_2(A_47, B_48)) | ~m1_subset_1(B_48, u1_struct_0(A_47)) | ~l1_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_195])).
% 11.59/4.68  tff(c_4985, plain, (~v2_struct_0(k1_tex_2('#skF_4', '#skF_1'('#skF_5'))) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_4890, c_64])).
% 11.59/4.68  tff(c_5005, plain, (~v2_struct_0(k1_tex_2('#skF_4', '#skF_1'('#skF_5'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_4985])).
% 11.59/4.68  tff(c_5006, plain, (~v2_struct_0(k1_tex_2('#skF_4', '#skF_1'('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_92, c_5005])).
% 11.59/4.68  tff(c_4979, plain, (m1_pre_topc(k1_tex_2('#skF_4', '#skF_1'('#skF_5')), '#skF_4') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_4890, c_54])).
% 11.59/4.68  tff(c_4997, plain, (m1_pre_topc(k1_tex_2('#skF_4', '#skF_1'('#skF_5')), '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_4979])).
% 11.59/4.68  tff(c_4998, plain, (m1_pre_topc(k1_tex_2('#skF_4', '#skF_1'('#skF_5')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_92, c_4997])).
% 11.59/4.68  tff(c_26, plain, (![B_20, A_18]: (v2_pre_topc(B_20) | ~m1_pre_topc(B_20, A_18) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.59/4.68  tff(c_5055, plain, (v2_pre_topc(k1_tex_2('#skF_4', '#skF_1'('#skF_5'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_4998, c_26])).
% 11.59/4.68  tff(c_5077, plain, (v2_pre_topc(k1_tex_2('#skF_4', '#skF_1'('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_5055])).
% 11.59/4.68  tff(c_62, plain, (![A_47, B_48]: (v7_struct_0(k1_tex_2(A_47, B_48)) | ~m1_subset_1(B_48, u1_struct_0(A_47)) | ~l1_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_195])).
% 11.59/4.68  tff(c_4988, plain, (v7_struct_0(k1_tex_2('#skF_4', '#skF_1'('#skF_5'))) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_4890, c_62])).
% 11.59/4.68  tff(c_5009, plain, (v7_struct_0(k1_tex_2('#skF_4', '#skF_1'('#skF_5'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_4988])).
% 11.59/4.68  tff(c_5010, plain, (v7_struct_0(k1_tex_2('#skF_4', '#skF_1'('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_92, c_5009])).
% 11.59/4.68  tff(c_801, plain, (![A_170]: (m1_subset_1('#skF_1'(A_170), u1_struct_0('#skF_4')) | ~r1_tarski(A_170, '#skF_5') | v1_xboole_0(A_170))), inference(resolution, [status(thm)], [c_780, c_20])).
% 11.59/4.68  tff(c_803, plain, (![A_170]: (m1_pre_topc(k1_tex_2('#skF_4', '#skF_1'(A_170)), '#skF_4') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(A_170, '#skF_5') | v1_xboole_0(A_170))), inference(resolution, [status(thm)], [c_801, c_54])).
% 11.59/4.68  tff(c_818, plain, (![A_170]: (m1_pre_topc(k1_tex_2('#skF_4', '#skF_1'(A_170)), '#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(A_170, '#skF_5') | v1_xboole_0(A_170))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_803])).
% 11.59/4.68  tff(c_819, plain, (![A_170]: (m1_pre_topc(k1_tex_2('#skF_4', '#skF_1'(A_170)), '#skF_4') | ~r1_tarski(A_170, '#skF_5') | v1_xboole_0(A_170))), inference(negUnitSimplification, [status(thm)], [c_92, c_818])).
% 11.59/4.68  tff(c_883, plain, (![B_178, A_179]: (v1_tdlat_3(B_178) | ~v2_pre_topc(B_178) | ~v7_struct_0(B_178) | v2_struct_0(B_178) | ~m1_pre_topc(B_178, A_179) | ~l1_pre_topc(A_179) | v2_struct_0(A_179))), inference(cnfTransformation, [status(thm)], [f_117])).
% 11.59/4.68  tff(c_886, plain, (![A_170]: (v1_tdlat_3(k1_tex_2('#skF_4', '#skF_1'(A_170))) | ~v2_pre_topc(k1_tex_2('#skF_4', '#skF_1'(A_170))) | ~v7_struct_0(k1_tex_2('#skF_4', '#skF_1'(A_170))) | v2_struct_0(k1_tex_2('#skF_4', '#skF_1'(A_170))) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(A_170, '#skF_5') | v1_xboole_0(A_170))), inference(resolution, [status(thm)], [c_819, c_883])).
% 11.59/4.68  tff(c_889, plain, (![A_170]: (v1_tdlat_3(k1_tex_2('#skF_4', '#skF_1'(A_170))) | ~v2_pre_topc(k1_tex_2('#skF_4', '#skF_1'(A_170))) | ~v7_struct_0(k1_tex_2('#skF_4', '#skF_1'(A_170))) | v2_struct_0(k1_tex_2('#skF_4', '#skF_1'(A_170))) | v2_struct_0('#skF_4') | ~r1_tarski(A_170, '#skF_5') | v1_xboole_0(A_170))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_886])).
% 11.59/4.68  tff(c_890, plain, (![A_170]: (v1_tdlat_3(k1_tex_2('#skF_4', '#skF_1'(A_170))) | ~v2_pre_topc(k1_tex_2('#skF_4', '#skF_1'(A_170))) | ~v7_struct_0(k1_tex_2('#skF_4', '#skF_1'(A_170))) | v2_struct_0(k1_tex_2('#skF_4', '#skF_1'(A_170))) | ~r1_tarski(A_170, '#skF_5') | v1_xboole_0(A_170))), inference(negUnitSimplification, [status(thm)], [c_92, c_889])).
% 11.59/4.68  tff(c_5019, plain, (v1_tdlat_3(k1_tex_2('#skF_4', '#skF_1'('#skF_5'))) | ~v2_pre_topc(k1_tex_2('#skF_4', '#skF_1'('#skF_5'))) | v2_struct_0(k1_tex_2('#skF_4', '#skF_1'('#skF_5'))) | ~r1_tarski('#skF_5', '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_5010, c_890])).
% 11.59/4.68  tff(c_5032, plain, (v1_tdlat_3(k1_tex_2('#skF_4', '#skF_1'('#skF_5'))) | ~v2_pre_topc(k1_tex_2('#skF_4', '#skF_1'('#skF_5'))) | v2_struct_0(k1_tex_2('#skF_4', '#skF_1'('#skF_5'))) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_5019])).
% 11.59/4.68  tff(c_5033, plain, (v1_tdlat_3(k1_tex_2('#skF_4', '#skF_1'('#skF_5'))) | ~v2_pre_topc(k1_tex_2('#skF_4', '#skF_1'('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_84, c_5006, c_5032])).
% 11.59/4.68  tff(c_5242, plain, (v1_tdlat_3(k1_tex_2('#skF_4', '#skF_1'('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_5077, c_5033])).
% 11.59/4.68  tff(c_60, plain, (![A_47, B_48]: (v1_pre_topc(k1_tex_2(A_47, B_48)) | ~m1_subset_1(B_48, u1_struct_0(A_47)) | ~l1_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_195])).
% 11.59/4.68  tff(c_4982, plain, (v1_pre_topc(k1_tex_2('#skF_4', '#skF_1'('#skF_5'))) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_4890, c_60])).
% 11.59/4.68  tff(c_5001, plain, (v1_pre_topc(k1_tex_2('#skF_4', '#skF_1'('#skF_5'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_4982])).
% 11.59/4.68  tff(c_5002, plain, (v1_pre_topc(k1_tex_2('#skF_4', '#skF_1'('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_92, c_5001])).
% 11.59/4.68  tff(c_52, plain, (![A_38, B_42]: (k6_domain_1(u1_struct_0(A_38), B_42)=u1_struct_0(k1_tex_2(A_38, B_42)) | ~m1_pre_topc(k1_tex_2(A_38, B_42), A_38) | ~v1_pre_topc(k1_tex_2(A_38, B_42)) | v2_struct_0(k1_tex_2(A_38, B_42)) | ~m1_subset_1(B_42, u1_struct_0(A_38)) | ~l1_pre_topc(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_167])).
% 11.59/4.68  tff(c_5043, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'('#skF_5'))=u1_struct_0(k1_tex_2('#skF_4', '#skF_1'('#skF_5'))) | ~v1_pre_topc(k1_tex_2('#skF_4', '#skF_1'('#skF_5'))) | v2_struct_0(k1_tex_2('#skF_4', '#skF_1'('#skF_5'))) | ~m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_4998, c_52])).
% 11.59/4.68  tff(c_5061, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'('#skF_5'))=u1_struct_0(k1_tex_2('#skF_4', '#skF_1'('#skF_5'))) | v2_struct_0(k1_tex_2('#skF_4', '#skF_1'('#skF_5'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_4890, c_5002, c_5043])).
% 11.59/4.68  tff(c_5062, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'('#skF_5'))=u1_struct_0(k1_tex_2('#skF_4', '#skF_1'('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_92, c_5006, c_5061])).
% 11.59/4.68  tff(c_5105, plain, (u1_struct_0(k1_tex_2('#skF_4', '#skF_1'('#skF_5')))=k1_tarski('#skF_1'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_5013, c_5062])).
% 11.59/4.68  tff(c_8162, plain, (u1_struct_0(k1_tex_2('#skF_4', '#skF_1'('#skF_5')))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_8027, c_5105])).
% 11.59/4.68  tff(c_36, plain, (![B_30, A_28]: (m1_subset_1(u1_struct_0(B_30), k1_zfmisc_1(u1_struct_0(A_28))) | ~m1_pre_topc(B_30, A_28) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_95])).
% 11.59/4.68  tff(c_3321, plain, (![B_268, A_269]: (v2_tex_2(u1_struct_0(B_268), A_269) | ~v1_tdlat_3(B_268) | ~m1_subset_1(u1_struct_0(B_268), k1_zfmisc_1(u1_struct_0(A_269))) | ~m1_pre_topc(B_268, A_269) | v2_struct_0(B_268) | ~l1_pre_topc(A_269) | v2_struct_0(A_269))), inference(cnfTransformation, [status(thm)], [f_228])).
% 11.59/4.68  tff(c_3328, plain, (![B_30, A_28]: (v2_tex_2(u1_struct_0(B_30), A_28) | ~v1_tdlat_3(B_30) | v2_struct_0(B_30) | v2_struct_0(A_28) | ~m1_pre_topc(B_30, A_28) | ~l1_pre_topc(A_28))), inference(resolution, [status(thm)], [c_36, c_3321])).
% 11.59/4.68  tff(c_8751, plain, (![A_28]: (v2_tex_2('#skF_5', A_28) | ~v1_tdlat_3(k1_tex_2('#skF_4', '#skF_1'('#skF_5'))) | v2_struct_0(k1_tex_2('#skF_4', '#skF_1'('#skF_5'))) | v2_struct_0(A_28) | ~m1_pre_topc(k1_tex_2('#skF_4', '#skF_1'('#skF_5')), A_28) | ~l1_pre_topc(A_28))), inference(superposition, [status(thm), theory('equality')], [c_8162, c_3328])).
% 11.59/4.68  tff(c_8839, plain, (![A_28]: (v2_tex_2('#skF_5', A_28) | v2_struct_0(k1_tex_2('#skF_4', '#skF_1'('#skF_5'))) | v2_struct_0(A_28) | ~m1_pre_topc(k1_tex_2('#skF_4', '#skF_1'('#skF_5')), A_28) | ~l1_pre_topc(A_28))), inference(demodulation, [status(thm), theory('equality')], [c_5242, c_8751])).
% 11.59/4.68  tff(c_16227, plain, (![A_584]: (v2_tex_2('#skF_5', A_584) | v2_struct_0(A_584) | ~m1_pre_topc(k1_tex_2('#skF_4', '#skF_1'('#skF_5')), A_584) | ~l1_pre_topc(A_584))), inference(negUnitSimplification, [status(thm)], [c_5006, c_8839])).
% 11.59/4.68  tff(c_16235, plain, (v2_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~r2_hidden('#skF_1'('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_10608, c_16227])).
% 11.59/4.68  tff(c_16249, plain, (v2_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8371, c_86, c_16235])).
% 11.59/4.68  tff(c_16251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_105, c_16249])).
% 11.59/4.68  tff(c_16252, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_100])).
% 11.59/4.68  tff(c_19596, plain, (![A_792, B_793]: (m1_pre_topc('#skF_3'(A_792, B_793), A_792) | ~v2_tex_2(B_793, A_792) | ~m1_subset_1(B_793, k1_zfmisc_1(u1_struct_0(A_792))) | v1_xboole_0(B_793) | ~l1_pre_topc(A_792) | ~v2_pre_topc(A_792) | v2_struct_0(A_792))), inference(cnfTransformation, [status(thm)], [f_257])).
% 11.59/4.68  tff(c_19627, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_19596])).
% 11.59/4.68  tff(c_19640, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_16252, c_19627])).
% 11.59/4.68  tff(c_19641, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_92, c_84, c_19640])).
% 11.59/4.68  tff(c_30, plain, (![B_24, A_22]: (l1_pre_topc(B_24) | ~m1_pre_topc(B_24, A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.59/4.68  tff(c_19656, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_19641, c_30])).
% 11.59/4.68  tff(c_19674, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_19656])).
% 11.59/4.68  tff(c_28, plain, (![A_21]: (l1_struct_0(A_21) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.59/4.68  tff(c_16253, plain, (~v1_zfmisc_1('#skF_5')), inference(splitRight, [status(thm)], [c_100])).
% 11.59/4.68  tff(c_18300, plain, (![A_753, B_754]: (~v2_struct_0('#skF_3'(A_753, B_754)) | ~v2_tex_2(B_754, A_753) | ~m1_subset_1(B_754, k1_zfmisc_1(u1_struct_0(A_753))) | v1_xboole_0(B_754) | ~l1_pre_topc(A_753) | ~v2_pre_topc(A_753) | v2_struct_0(A_753))), inference(cnfTransformation, [status(thm)], [f_257])).
% 11.59/4.68  tff(c_18330, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_18300])).
% 11.59/4.68  tff(c_18340, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_16252, c_18330])).
% 11.59/4.68  tff(c_18341, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_92, c_84, c_18340])).
% 11.59/4.68  tff(c_88, plain, (v2_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_277])).
% 11.59/4.68  tff(c_17690, plain, (![A_743, B_744]: (v1_tdlat_3('#skF_3'(A_743, B_744)) | ~v2_tex_2(B_744, A_743) | ~m1_subset_1(B_744, k1_zfmisc_1(u1_struct_0(A_743))) | v1_xboole_0(B_744) | ~l1_pre_topc(A_743) | ~v2_pre_topc(A_743) | v2_struct_0(A_743))), inference(cnfTransformation, [status(thm)], [f_257])).
% 11.59/4.68  tff(c_17716, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_17690])).
% 11.59/4.68  tff(c_17725, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_16252, c_17716])).
% 11.59/4.68  tff(c_17726, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_92, c_84, c_17725])).
% 11.59/4.68  tff(c_46, plain, (![B_37, A_35]: (~v1_tdlat_3(B_37) | v7_struct_0(B_37) | v2_struct_0(B_37) | ~m1_pre_topc(B_37, A_35) | ~l1_pre_topc(A_35) | ~v2_tdlat_3(A_35) | ~v2_pre_topc(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_147])).
% 11.59/4.68  tff(c_19644, plain, (~v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v7_struct_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_19641, c_46])).
% 11.59/4.68  tff(c_19659, plain, (v7_struct_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_17726, c_19644])).
% 11.59/4.68  tff(c_19660, plain, (v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_92, c_18341, c_19659])).
% 11.59/4.68  tff(c_19845, plain, (![A_799, B_800]: (u1_struct_0('#skF_3'(A_799, B_800))=B_800 | ~v2_tex_2(B_800, A_799) | ~m1_subset_1(B_800, k1_zfmisc_1(u1_struct_0(A_799))) | v1_xboole_0(B_800) | ~l1_pre_topc(A_799) | ~v2_pre_topc(A_799) | v2_struct_0(A_799))), inference(cnfTransformation, [status(thm)], [f_257])).
% 11.59/4.68  tff(c_19887, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_19845])).
% 11.59/4.68  tff(c_19900, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_16252, c_19887])).
% 11.59/4.68  tff(c_19901, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_92, c_84, c_19900])).
% 11.59/4.68  tff(c_32, plain, (![A_25]: (v1_zfmisc_1(u1_struct_0(A_25)) | ~l1_struct_0(A_25) | ~v7_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.59/4.68  tff(c_19967, plain, (v1_zfmisc_1('#skF_5') | ~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_19901, c_32])).
% 11.59/4.68  tff(c_20026, plain, (v1_zfmisc_1('#skF_5') | ~l1_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_19660, c_19967])).
% 11.59/4.68  tff(c_20027, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_16253, c_20026])).
% 11.59/4.68  tff(c_20031, plain, (~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_28, c_20027])).
% 11.59/4.68  tff(c_20035, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19674, c_20031])).
% 11.59/4.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.59/4.68  
% 11.59/4.68  Inference rules
% 11.59/4.68  ----------------------
% 11.59/4.68  #Ref     : 0
% 11.59/4.68  #Sup     : 4600
% 11.59/4.68  #Fact    : 0
% 11.59/4.68  #Define  : 0
% 11.59/4.68  #Split   : 19
% 11.59/4.68  #Chain   : 0
% 11.59/4.68  #Close   : 0
% 11.59/4.68  
% 11.59/4.68  Ordering : KBO
% 11.59/4.68  
% 11.59/4.68  Simplification rules
% 11.59/4.68  ----------------------
% 11.59/4.68  #Subsume      : 1139
% 11.59/4.68  #Demod        : 1884
% 11.59/4.68  #Tautology    : 759
% 11.59/4.68  #SimpNegUnit  : 1142
% 11.59/4.68  #BackRed      : 35
% 11.59/4.68  
% 11.59/4.68  #Partial instantiations: 0
% 11.59/4.68  #Strategies tried      : 1
% 11.59/4.68  
% 11.59/4.68  Timing (in seconds)
% 11.59/4.68  ----------------------
% 11.59/4.68  Preprocessing        : 0.38
% 11.59/4.68  Parsing              : 0.19
% 11.59/4.68  CNF conversion       : 0.03
% 11.59/4.68  Main loop            : 3.38
% 11.59/4.68  Inferencing          : 1.00
% 11.59/4.68  Reduction            : 1.01
% 11.59/4.68  Demodulation         : 0.66
% 11.59/4.68  BG Simplification    : 0.11
% 11.59/4.68  Subsumption          : 1.00
% 11.59/4.68  Abstraction          : 0.14
% 11.59/4.68  MUC search           : 0.00
% 11.59/4.68  Cooper               : 0.00
% 11.59/4.68  Total                : 3.83
% 11.59/4.68  Index Insertion      : 0.00
% 11.59/4.68  Index Deletion       : 0.00
% 11.59/4.68  Index Matching       : 0.00
% 11.59/4.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
