%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:04 EST 2020

% Result     : Theorem 5.01s
% Output     : CNFRefutation 5.25s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 981 expanded)
%              Number of leaves         :   42 ( 340 expanded)
%              Depth                    :   19
%              Number of atoms          :  391 (2638 expanded)
%              Number of equality atoms :   31 ( 221 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > o_2_0_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(o_2_0_pre_topc,type,(
    o_2_0_pre_topc: ( $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_219,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_157,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_171,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_136,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v1_subset_1(C,u1_struct_0(A)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

tff(f_38,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_143,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_182,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,A)
         => ~ ( v1_subset_1(k6_domain_1(A,B),A)
              & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_193,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,A)
         => v1_subset_1(k6_domain_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

tff(f_206,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
              & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(o_2_0_pre_topc(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_2_0_pre_topc)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_122,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( v1_subset_1(B,A)
           => v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tex_2)).

tff(c_62,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_1757,plain,(
    ! [A_234,B_235] :
      ( m1_pre_topc(k1_tex_2(A_234,B_235),A_234)
      | ~ m1_subset_1(B_235,u1_struct_0(A_234))
      | ~ l1_pre_topc(A_234)
      | v2_struct_0(A_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1763,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1757])).

tff(c_1768,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1763])).

tff(c_1769,plain,(
    m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1768])).

tff(c_14,plain,(
    ! [B_14,A_12] :
      ( l1_pre_topc(B_14)
      | ~ m1_pre_topc(B_14,A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1772,plain,
    ( l1_pre_topc(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1769,c_14])).

tff(c_1775,plain,(
    l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1772])).

tff(c_12,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1665,plain,(
    ! [A_214,B_215] :
      ( ~ v2_struct_0(k1_tex_2(A_214,B_215))
      | ~ m1_subset_1(B_215,u1_struct_0(A_214))
      | ~ l1_pre_topc(A_214)
      | v2_struct_0(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_1668,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1665])).

tff(c_1671,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1668])).

tff(c_1672,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1671])).

tff(c_26,plain,(
    ! [A_30] :
      ( m1_pre_topc(A_30,A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_34,plain,(
    ! [B_40,A_34] :
      ( u1_struct_0(B_40) = '#skF_2'(A_34,B_40)
      | v1_tex_2(B_40,A_34)
      | ~ m1_pre_topc(B_40,A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_4,plain,(
    ! [A_4] : ~ v1_subset_1('#skF_1'(A_4),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1('#skF_1'(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_102,plain,(
    ! [B_78,A_79] :
      ( v1_subset_1(B_78,A_79)
      | B_78 = A_79
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_105,plain,(
    ! [A_4] :
      ( v1_subset_1('#skF_1'(A_4),A_4)
      | '#skF_1'(A_4) = A_4 ) ),
    inference(resolution,[status(thm)],[c_6,c_102])).

tff(c_108,plain,(
    ! [A_4] : '#skF_1'(A_4) = A_4 ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_105])).

tff(c_112,plain,(
    ! [A_4] : ~ v1_subset_1(A_4,A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_4])).

tff(c_111,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_6])).

tff(c_756,plain,(
    ! [B_156,A_157] :
      ( v1_subset_1(u1_struct_0(B_156),u1_struct_0(A_157))
      | ~ m1_subset_1(u1_struct_0(B_156),k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ v1_tex_2(B_156,A_157)
      | ~ m1_pre_topc(B_156,A_157)
      | ~ l1_pre_topc(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_769,plain,(
    ! [B_156] :
      ( v1_subset_1(u1_struct_0(B_156),u1_struct_0(B_156))
      | ~ v1_tex_2(B_156,B_156)
      | ~ m1_pre_topc(B_156,B_156)
      | ~ l1_pre_topc(B_156) ) ),
    inference(resolution,[status(thm)],[c_111,c_756])).

tff(c_777,plain,(
    ! [B_158] :
      ( ~ v1_tex_2(B_158,B_158)
      | ~ m1_pre_topc(B_158,B_158)
      | ~ l1_pre_topc(B_158) ) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_769])).

tff(c_783,plain,(
    ! [A_159] :
      ( u1_struct_0(A_159) = '#skF_2'(A_159,A_159)
      | ~ m1_pre_topc(A_159,A_159)
      | ~ l1_pre_topc(A_159) ) ),
    inference(resolution,[status(thm)],[c_34,c_777])).

tff(c_788,plain,(
    ! [A_160] :
      ( u1_struct_0(A_160) = '#skF_2'(A_160,A_160)
      | ~ l1_pre_topc(A_160) ) ),
    inference(resolution,[status(thm)],[c_26,c_783])).

tff(c_804,plain,(
    u1_struct_0('#skF_3') = '#skF_2'('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_788])).

tff(c_144,plain,(
    ! [A_85,B_86] :
      ( k6_domain_1(A_85,B_86) = k1_tarski(B_86)
      | ~ m1_subset_1(B_86,A_85)
      | v1_xboole_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_152,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_60,c_144])).

tff(c_169,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_18,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(u1_struct_0(A_17))
      | ~ l1_struct_0(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_172,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_169,c_18])).

tff(c_175,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_172])).

tff(c_178,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_175])).

tff(c_182,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_178])).

tff(c_184,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_183,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_66,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_79,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_72,plain,
    ( v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_122,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_72])).

tff(c_185,plain,(
    v1_subset_1(k1_tarski('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_122])).

tff(c_252,plain,(
    ! [A_104,B_105] :
      ( ~ v1_zfmisc_1(A_104)
      | ~ v1_subset_1(k6_domain_1(A_104,B_105),A_104)
      | ~ m1_subset_1(B_105,A_104)
      | v1_xboole_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_261,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_3'))
    | ~ v1_subset_1(k1_tarski('#skF_4'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_252])).

tff(c_266,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_185,c_261])).

tff(c_267,plain,(
    ~ v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_184,c_266])).

tff(c_805,plain,(
    ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_804,c_267])).

tff(c_311,plain,(
    ! [A_117,B_118] :
      ( m1_pre_topc(k1_tex_2(A_117,B_118),A_117)
      | ~ m1_subset_1(B_118,u1_struct_0(A_117))
      | ~ l1_pre_topc(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_317,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_311])).

tff(c_322,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_317])).

tff(c_323,plain,(
    m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_322])).

tff(c_507,plain,(
    ! [A_131,B_132] :
      ( m1_subset_1('#skF_2'(A_131,B_132),k1_zfmisc_1(u1_struct_0(A_131)))
      | v1_tex_2(B_132,A_131)
      | ~ m1_pre_topc(B_132,A_131)
      | ~ l1_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_38,plain,(
    ! [B_45,A_44] :
      ( v1_subset_1(B_45,A_44)
      | B_45 = A_44
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1388,plain,(
    ! [A_177,B_178] :
      ( v1_subset_1('#skF_2'(A_177,B_178),u1_struct_0(A_177))
      | u1_struct_0(A_177) = '#skF_2'(A_177,B_178)
      | v1_tex_2(B_178,A_177)
      | ~ m1_pre_topc(B_178,A_177)
      | ~ l1_pre_topc(A_177) ) ),
    inference(resolution,[status(thm)],[c_507,c_38])).

tff(c_32,plain,(
    ! [A_34,B_40] :
      ( ~ v1_subset_1('#skF_2'(A_34,B_40),u1_struct_0(A_34))
      | v1_tex_2(B_40,A_34)
      | ~ m1_pre_topc(B_40,A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1479,plain,(
    ! [A_181,B_182] :
      ( u1_struct_0(A_181) = '#skF_2'(A_181,B_182)
      | v1_tex_2(B_182,A_181)
      | ~ m1_pre_topc(B_182,A_181)
      | ~ l1_pre_topc(A_181) ) ),
    inference(resolution,[status(thm)],[c_1388,c_32])).

tff(c_1489,plain,
    ( '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')) = u1_struct_0('#skF_3')
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1479,c_79])).

tff(c_1496,plain,(
    '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')) = '#skF_2'('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_323,c_804,c_1489])).

tff(c_326,plain,
    ( l1_pre_topc(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_323,c_14])).

tff(c_329,plain,(
    l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_326])).

tff(c_208,plain,(
    ! [A_94,B_95] :
      ( ~ v2_struct_0(k1_tex_2(A_94,B_95))
      | ~ m1_subset_1(B_95,u1_struct_0(A_94))
      | ~ l1_pre_topc(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_211,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_208])).

tff(c_214,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_211])).

tff(c_215,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_214])).

tff(c_281,plain,(
    ! [B_109,A_110] :
      ( u1_struct_0(B_109) = '#skF_2'(A_110,B_109)
      | v1_tex_2(B_109,A_110)
      | ~ m1_pre_topc(B_109,A_110)
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_284,plain,
    ( u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_281,c_79])).

tff(c_287,plain,
    ( u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_284])).

tff(c_346,plain,(
    u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_287])).

tff(c_400,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_18])).

tff(c_444,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_215,c_400])).

tff(c_446,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_444])).

tff(c_449,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_12,c_446])).

tff(c_453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_449])).

tff(c_454,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_444])).

tff(c_455,plain,(
    l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_444])).

tff(c_268,plain,(
    ! [A_106,B_107] :
      ( v7_struct_0(k1_tex_2(A_106,B_107))
      | ~ m1_subset_1(B_107,u1_struct_0(A_106))
      | ~ l1_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_274,plain,
    ( v7_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_268])).

tff(c_278,plain,
    ( v7_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_274])).

tff(c_279,plain,(
    v7_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_278])).

tff(c_56,plain,(
    ! [A_53,B_55] :
      ( v1_subset_1(k6_domain_1(A_53,B_55),A_53)
      | ~ m1_subset_1(B_55,A_53)
      | v1_zfmisc_1(A_53)
      | v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_611,plain,(
    ! [A_139,B_140] :
      ( ~ v7_struct_0(A_139)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(A_139),B_140),u1_struct_0(A_139))
      | ~ m1_subset_1(B_140,u1_struct_0(A_139))
      | ~ l1_struct_0(A_139)
      | v2_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_645,plain,(
    ! [A_141,B_142] :
      ( ~ v7_struct_0(A_141)
      | ~ l1_struct_0(A_141)
      | v2_struct_0(A_141)
      | ~ m1_subset_1(B_142,u1_struct_0(A_141))
      | v1_zfmisc_1(u1_struct_0(A_141))
      | v1_xboole_0(u1_struct_0(A_141)) ) ),
    inference(resolution,[status(thm)],[c_56,c_611])).

tff(c_651,plain,(
    ! [B_142] :
      ( ~ v7_struct_0(k1_tex_2('#skF_3','#skF_4'))
      | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4'))
      | v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
      | ~ m1_subset_1(B_142,'#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
      | v1_zfmisc_1(u1_struct_0(k1_tex_2('#skF_3','#skF_4')))
      | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_3','#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_645])).

tff(c_663,plain,(
    ! [B_142] :
      ( v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
      | ~ m1_subset_1(B_142,'#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
      | v1_zfmisc_1('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
      | v1_xboole_0('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_346,c_455,c_279,c_651])).

tff(c_664,plain,(
    ! [B_142] :
      ( ~ m1_subset_1(B_142,'#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
      | v1_zfmisc_1('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_454,c_215,c_663])).

tff(c_671,plain,(
    ! [B_142] : ~ m1_subset_1(B_142,'#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_664])).

tff(c_216,plain,(
    ! [A_96,B_97] :
      ( m1_subset_1(o_2_0_pre_topc(A_96,B_97),B_97)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_223,plain,(
    ! [A_96] :
      ( m1_subset_1(o_2_0_pre_topc(A_96,u1_struct_0(A_96)),u1_struct_0(A_96))
      | ~ l1_pre_topc(A_96) ) ),
    inference(resolution,[status(thm)],[c_111,c_216])).

tff(c_381,plain,
    ( m1_subset_1(o_2_0_pre_topc(k1_tex_2('#skF_3','#skF_4'),u1_struct_0(k1_tex_2('#skF_3','#skF_4'))),'#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_223])).

tff(c_431,plain,(
    m1_subset_1(o_2_0_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))),'#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_346,c_381])).

tff(c_673,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_671,c_431])).

tff(c_674,plain,(
    v1_zfmisc_1('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_664])).

tff(c_1503,plain,(
    v1_zfmisc_1('#skF_2'('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1496,c_674])).

tff(c_1520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_805,c_1503])).

tff(c_1522,plain,(
    v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_1547,plain,(
    ! [B_195,A_196] :
      ( v1_subset_1(B_195,A_196)
      | B_195 = A_196
      | ~ m1_subset_1(B_195,k1_zfmisc_1(A_196)) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1550,plain,(
    ! [A_4] :
      ( v1_subset_1('#skF_1'(A_4),A_4)
      | '#skF_1'(A_4) = A_4 ) ),
    inference(resolution,[status(thm)],[c_6,c_1547])).

tff(c_1553,plain,(
    ! [A_4] : '#skF_1'(A_4) = A_4 ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_1550])).

tff(c_1557,plain,(
    ! [A_4] : ~ v1_subset_1(A_4,A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1553,c_4])).

tff(c_1556,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1553,c_6])).

tff(c_1958,plain,(
    ! [B_275,A_276] :
      ( v1_subset_1(u1_struct_0(B_275),u1_struct_0(A_276))
      | ~ m1_subset_1(u1_struct_0(B_275),k1_zfmisc_1(u1_struct_0(A_276)))
      | ~ v1_tex_2(B_275,A_276)
      | ~ m1_pre_topc(B_275,A_276)
      | ~ l1_pre_topc(A_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1965,plain,(
    ! [B_275] :
      ( v1_subset_1(u1_struct_0(B_275),u1_struct_0(B_275))
      | ~ v1_tex_2(B_275,B_275)
      | ~ m1_pre_topc(B_275,B_275)
      | ~ l1_pre_topc(B_275) ) ),
    inference(resolution,[status(thm)],[c_1556,c_1958])).

tff(c_1970,plain,(
    ! [B_277] :
      ( ~ v1_tex_2(B_277,B_277)
      | ~ m1_pre_topc(B_277,B_277)
      | ~ l1_pre_topc(B_277) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1557,c_1965])).

tff(c_1976,plain,(
    ! [A_278] :
      ( u1_struct_0(A_278) = '#skF_2'(A_278,A_278)
      | ~ m1_pre_topc(A_278,A_278)
      | ~ l1_pre_topc(A_278) ) ),
    inference(resolution,[status(thm)],[c_34,c_1970])).

tff(c_1981,plain,(
    ! [A_279] :
      ( u1_struct_0(A_279) = '#skF_2'(A_279,A_279)
      | ~ l1_pre_topc(A_279) ) ),
    inference(resolution,[status(thm)],[c_26,c_1976])).

tff(c_1993,plain,(
    u1_struct_0('#skF_3') = '#skF_2'('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_1981])).

tff(c_24,plain,(
    ! [B_29,A_27] :
      ( m1_subset_1(u1_struct_0(B_29),k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ m1_pre_topc(B_29,A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2196,plain,(
    ! [B_280,A_281] :
      ( v1_subset_1(u1_struct_0(B_280),u1_struct_0(A_281))
      | ~ v1_tex_2(B_280,A_281)
      | ~ m1_pre_topc(B_280,A_281)
      | ~ l1_pre_topc(A_281) ) ),
    inference(resolution,[status(thm)],[c_24,c_1958])).

tff(c_2206,plain,(
    ! [B_280] :
      ( v1_subset_1(u1_struct_0(B_280),'#skF_2'('#skF_3','#skF_3'))
      | ~ v1_tex_2(B_280,'#skF_3')
      | ~ m1_pre_topc(B_280,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1993,c_2196])).

tff(c_2209,plain,(
    ! [B_280] :
      ( v1_subset_1(u1_struct_0(B_280),'#skF_2'('#skF_3','#skF_3'))
      | ~ v1_tex_2(B_280,'#skF_3')
      | ~ m1_pre_topc(B_280,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2206])).

tff(c_1567,plain,(
    ! [A_198,B_199] :
      ( k6_domain_1(A_198,B_199) = k1_tarski(B_199)
      | ~ m1_subset_1(B_199,A_198)
      | v1_xboole_0(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1571,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_60,c_1567])).

tff(c_1597,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1571])).

tff(c_1600,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1597,c_18])).

tff(c_1603,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1600])).

tff(c_1606,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_1603])).

tff(c_1610,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1606])).

tff(c_1612,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1571])).

tff(c_1997,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1993,c_1612])).

tff(c_1611,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1571])).

tff(c_1521,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_1613,plain,(
    ~ v1_subset_1(k1_tarski('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1611,c_1521])).

tff(c_1709,plain,(
    ! [A_224,B_225] :
      ( v1_subset_1(k6_domain_1(A_224,B_225),A_224)
      | ~ m1_subset_1(B_225,A_224)
      | v1_zfmisc_1(A_224)
      | v1_xboole_0(A_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_1718,plain,
    ( v1_subset_1(k1_tarski('#skF_4'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_zfmisc_1(u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1611,c_1709])).

tff(c_1723,plain,
    ( v1_subset_1(k1_tarski('#skF_4'),u1_struct_0('#skF_3'))
    | v1_zfmisc_1(u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1718])).

tff(c_1724,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_1612,c_1613,c_1723])).

tff(c_1994,plain,(
    v1_zfmisc_1('#skF_2'('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1993,c_1724])).

tff(c_1730,plain,(
    ! [B_227,A_228] :
      ( v1_xboole_0(B_227)
      | ~ v1_subset_1(B_227,A_228)
      | ~ m1_subset_1(B_227,k1_zfmisc_1(A_228))
      | ~ v1_zfmisc_1(A_228)
      | v1_xboole_0(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2404,plain,(
    ! [B_289,A_290] :
      ( v1_xboole_0(u1_struct_0(B_289))
      | ~ v1_subset_1(u1_struct_0(B_289),u1_struct_0(A_290))
      | ~ v1_zfmisc_1(u1_struct_0(A_290))
      | v1_xboole_0(u1_struct_0(A_290))
      | ~ m1_pre_topc(B_289,A_290)
      | ~ l1_pre_topc(A_290) ) ),
    inference(resolution,[status(thm)],[c_24,c_1730])).

tff(c_2413,plain,(
    ! [B_289] :
      ( v1_xboole_0(u1_struct_0(B_289))
      | ~ v1_subset_1(u1_struct_0(B_289),'#skF_2'('#skF_3','#skF_3'))
      | ~ v1_zfmisc_1(u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_289,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1993,c_2404])).

tff(c_2421,plain,(
    ! [B_289] :
      ( v1_xboole_0(u1_struct_0(B_289))
      | ~ v1_subset_1(u1_struct_0(B_289),'#skF_2'('#skF_3','#skF_3'))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_3'))
      | ~ m1_pre_topc(B_289,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1993,c_1994,c_1993,c_2413])).

tff(c_2557,plain,(
    ! [B_298] :
      ( v1_xboole_0(u1_struct_0(B_298))
      | ~ v1_subset_1(u1_struct_0(B_298),'#skF_2'('#skF_3','#skF_3'))
      | ~ m1_pre_topc(B_298,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1997,c_2421])).

tff(c_2569,plain,(
    ! [B_300] :
      ( v1_xboole_0(u1_struct_0(B_300))
      | ~ v1_tex_2(B_300,'#skF_3')
      | ~ m1_pre_topc(B_300,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2209,c_2557])).

tff(c_2593,plain,(
    ! [B_301] :
      ( ~ l1_struct_0(B_301)
      | v2_struct_0(B_301)
      | ~ v1_tex_2(B_301,'#skF_3')
      | ~ m1_pre_topc(B_301,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2569,c_18])).

tff(c_2600,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1522,c_2593])).

tff(c_2606,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1769,c_2600])).

tff(c_2607,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_1672,c_2606])).

tff(c_2610,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_12,c_2607])).

tff(c_2614,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1775,c_2610])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:26:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.01/1.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.01/1.97  
% 5.01/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.01/1.97  %$ v1_tex_2 > v1_subset_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > o_2_0_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 5.01/1.97  
% 5.01/1.97  %Foreground sorts:
% 5.01/1.97  
% 5.01/1.97  
% 5.01/1.97  %Background operators:
% 5.01/1.97  
% 5.01/1.97  
% 5.01/1.97  %Foreground operators:
% 5.01/1.97  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.01/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.01/1.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.01/1.97  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 5.01/1.97  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.01/1.97  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.01/1.97  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 5.01/1.97  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 5.01/1.97  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.01/1.97  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 5.01/1.97  tff(o_2_0_pre_topc, type, o_2_0_pre_topc: ($i * $i) > $i).
% 5.01/1.97  tff('#skF_3', type, '#skF_3': $i).
% 5.01/1.97  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 5.01/1.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.01/1.97  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.01/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.01/1.97  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 5.01/1.97  tff('#skF_4', type, '#skF_4': $i).
% 5.01/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.01/1.97  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.01/1.97  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 5.01/1.97  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.01/1.97  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.01/1.97  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.01/1.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.01/1.97  
% 5.25/2.01  tff(f_219, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 5.25/2.01  tff(f_157, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 5.25/2.01  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.25/2.01  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.25/2.01  tff(f_171, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 5.25/2.01  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 5.25/2.01  tff(f_136, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 5.25/2.01  tff(f_38, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 5.25/2.01  tff(f_143, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 5.25/2.01  tff(f_99, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 5.25/2.01  tff(f_76, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.25/2.01  tff(f_182, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 5.25/2.01  tff(f_193, axiom, (![A]: ((~v1_xboole_0(A) & ~v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, A) => v1_subset_1(k6_domain_1(A, B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tex_2)).
% 5.25/2.01  tff(f_206, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)) & v7_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_tex_2)).
% 5.25/2.01  tff(f_68, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(o_2_0_pre_topc(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_o_2_0_pre_topc)).
% 5.25/2.01  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 5.25/2.01  tff(f_122, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) => v1_xboole_0(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tex_2)).
% 5.25/2.01  tff(c_62, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_219])).
% 5.25/2.01  tff(c_64, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_219])).
% 5.25/2.01  tff(c_60, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_219])).
% 5.25/2.01  tff(c_1757, plain, (![A_234, B_235]: (m1_pre_topc(k1_tex_2(A_234, B_235), A_234) | ~m1_subset_1(B_235, u1_struct_0(A_234)) | ~l1_pre_topc(A_234) | v2_struct_0(A_234))), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.25/2.01  tff(c_1763, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_1757])).
% 5.25/2.01  tff(c_1768, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1763])).
% 5.25/2.01  tff(c_1769, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_1768])).
% 5.25/2.01  tff(c_14, plain, (![B_14, A_12]: (l1_pre_topc(B_14) | ~m1_pre_topc(B_14, A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.25/2.01  tff(c_1772, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1769, c_14])).
% 5.25/2.01  tff(c_1775, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1772])).
% 5.25/2.01  tff(c_12, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.25/2.01  tff(c_1665, plain, (![A_214, B_215]: (~v2_struct_0(k1_tex_2(A_214, B_215)) | ~m1_subset_1(B_215, u1_struct_0(A_214)) | ~l1_pre_topc(A_214) | v2_struct_0(A_214))), inference(cnfTransformation, [status(thm)], [f_171])).
% 5.25/2.01  tff(c_1668, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_1665])).
% 5.25/2.01  tff(c_1671, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1668])).
% 5.25/2.01  tff(c_1672, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_64, c_1671])).
% 5.25/2.01  tff(c_26, plain, (![A_30]: (m1_pre_topc(A_30, A_30) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.25/2.01  tff(c_34, plain, (![B_40, A_34]: (u1_struct_0(B_40)='#skF_2'(A_34, B_40) | v1_tex_2(B_40, A_34) | ~m1_pre_topc(B_40, A_34) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.25/2.01  tff(c_4, plain, (![A_4]: (~v1_subset_1('#skF_1'(A_4), A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.25/2.01  tff(c_6, plain, (![A_4]: (m1_subset_1('#skF_1'(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.25/2.01  tff(c_102, plain, (![B_78, A_79]: (v1_subset_1(B_78, A_79) | B_78=A_79 | ~m1_subset_1(B_78, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.25/2.01  tff(c_105, plain, (![A_4]: (v1_subset_1('#skF_1'(A_4), A_4) | '#skF_1'(A_4)=A_4)), inference(resolution, [status(thm)], [c_6, c_102])).
% 5.25/2.01  tff(c_108, plain, (![A_4]: ('#skF_1'(A_4)=A_4)), inference(negUnitSimplification, [status(thm)], [c_4, c_105])).
% 5.25/2.01  tff(c_112, plain, (![A_4]: (~v1_subset_1(A_4, A_4))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_4])).
% 5.25/2.01  tff(c_111, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_6])).
% 5.25/2.01  tff(c_756, plain, (![B_156, A_157]: (v1_subset_1(u1_struct_0(B_156), u1_struct_0(A_157)) | ~m1_subset_1(u1_struct_0(B_156), k1_zfmisc_1(u1_struct_0(A_157))) | ~v1_tex_2(B_156, A_157) | ~m1_pre_topc(B_156, A_157) | ~l1_pre_topc(A_157))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.25/2.01  tff(c_769, plain, (![B_156]: (v1_subset_1(u1_struct_0(B_156), u1_struct_0(B_156)) | ~v1_tex_2(B_156, B_156) | ~m1_pre_topc(B_156, B_156) | ~l1_pre_topc(B_156))), inference(resolution, [status(thm)], [c_111, c_756])).
% 5.25/2.01  tff(c_777, plain, (![B_158]: (~v1_tex_2(B_158, B_158) | ~m1_pre_topc(B_158, B_158) | ~l1_pre_topc(B_158))), inference(negUnitSimplification, [status(thm)], [c_112, c_769])).
% 5.25/2.01  tff(c_783, plain, (![A_159]: (u1_struct_0(A_159)='#skF_2'(A_159, A_159) | ~m1_pre_topc(A_159, A_159) | ~l1_pre_topc(A_159))), inference(resolution, [status(thm)], [c_34, c_777])).
% 5.25/2.01  tff(c_788, plain, (![A_160]: (u1_struct_0(A_160)='#skF_2'(A_160, A_160) | ~l1_pre_topc(A_160))), inference(resolution, [status(thm)], [c_26, c_783])).
% 5.25/2.01  tff(c_804, plain, (u1_struct_0('#skF_3')='#skF_2'('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_788])).
% 5.25/2.01  tff(c_144, plain, (![A_85, B_86]: (k6_domain_1(A_85, B_86)=k1_tarski(B_86) | ~m1_subset_1(B_86, A_85) | v1_xboole_0(A_85))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.25/2.01  tff(c_152, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_60, c_144])).
% 5.25/2.01  tff(c_169, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_152])).
% 5.25/2.01  tff(c_18, plain, (![A_17]: (~v1_xboole_0(u1_struct_0(A_17)) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.25/2.01  tff(c_172, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_169, c_18])).
% 5.25/2.01  tff(c_175, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_172])).
% 5.25/2.01  tff(c_178, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_12, c_175])).
% 5.25/2.01  tff(c_182, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_178])).
% 5.25/2.01  tff(c_184, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_152])).
% 5.25/2.01  tff(c_183, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_152])).
% 5.25/2.01  tff(c_66, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | ~v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_219])).
% 5.25/2.01  tff(c_79, plain, (~v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_66])).
% 5.25/2.01  tff(c_72, plain, (v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_219])).
% 5.25/2.01  tff(c_122, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_79, c_72])).
% 5.25/2.01  tff(c_185, plain, (v1_subset_1(k1_tarski('#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_183, c_122])).
% 5.25/2.01  tff(c_252, plain, (![A_104, B_105]: (~v1_zfmisc_1(A_104) | ~v1_subset_1(k6_domain_1(A_104, B_105), A_104) | ~m1_subset_1(B_105, A_104) | v1_xboole_0(A_104))), inference(cnfTransformation, [status(thm)], [f_182])).
% 5.25/2.01  tff(c_261, plain, (~v1_zfmisc_1(u1_struct_0('#skF_3')) | ~v1_subset_1(k1_tarski('#skF_4'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_183, c_252])).
% 5.25/2.01  tff(c_266, plain, (~v1_zfmisc_1(u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_185, c_261])).
% 5.25/2.01  tff(c_267, plain, (~v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_184, c_266])).
% 5.25/2.01  tff(c_805, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_804, c_267])).
% 5.25/2.01  tff(c_311, plain, (![A_117, B_118]: (m1_pre_topc(k1_tex_2(A_117, B_118), A_117) | ~m1_subset_1(B_118, u1_struct_0(A_117)) | ~l1_pre_topc(A_117) | v2_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.25/2.01  tff(c_317, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_311])).
% 5.25/2.01  tff(c_322, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_317])).
% 5.25/2.01  tff(c_323, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_322])).
% 5.25/2.01  tff(c_507, plain, (![A_131, B_132]: (m1_subset_1('#skF_2'(A_131, B_132), k1_zfmisc_1(u1_struct_0(A_131))) | v1_tex_2(B_132, A_131) | ~m1_pre_topc(B_132, A_131) | ~l1_pre_topc(A_131))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.25/2.01  tff(c_38, plain, (![B_45, A_44]: (v1_subset_1(B_45, A_44) | B_45=A_44 | ~m1_subset_1(B_45, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.25/2.01  tff(c_1388, plain, (![A_177, B_178]: (v1_subset_1('#skF_2'(A_177, B_178), u1_struct_0(A_177)) | u1_struct_0(A_177)='#skF_2'(A_177, B_178) | v1_tex_2(B_178, A_177) | ~m1_pre_topc(B_178, A_177) | ~l1_pre_topc(A_177))), inference(resolution, [status(thm)], [c_507, c_38])).
% 5.25/2.01  tff(c_32, plain, (![A_34, B_40]: (~v1_subset_1('#skF_2'(A_34, B_40), u1_struct_0(A_34)) | v1_tex_2(B_40, A_34) | ~m1_pre_topc(B_40, A_34) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.25/2.01  tff(c_1479, plain, (![A_181, B_182]: (u1_struct_0(A_181)='#skF_2'(A_181, B_182) | v1_tex_2(B_182, A_181) | ~m1_pre_topc(B_182, A_181) | ~l1_pre_topc(A_181))), inference(resolution, [status(thm)], [c_1388, c_32])).
% 5.25/2.01  tff(c_1489, plain, ('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))=u1_struct_0('#skF_3') | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1479, c_79])).
% 5.25/2.01  tff(c_1496, plain, ('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))='#skF_2'('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_323, c_804, c_1489])).
% 5.25/2.01  tff(c_326, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_323, c_14])).
% 5.25/2.01  tff(c_329, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_326])).
% 5.25/2.01  tff(c_208, plain, (![A_94, B_95]: (~v2_struct_0(k1_tex_2(A_94, B_95)) | ~m1_subset_1(B_95, u1_struct_0(A_94)) | ~l1_pre_topc(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_171])).
% 5.25/2.01  tff(c_211, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_208])).
% 5.25/2.01  tff(c_214, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_211])).
% 5.25/2.01  tff(c_215, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_64, c_214])).
% 5.25/2.01  tff(c_281, plain, (![B_109, A_110]: (u1_struct_0(B_109)='#skF_2'(A_110, B_109) | v1_tex_2(B_109, A_110) | ~m1_pre_topc(B_109, A_110) | ~l1_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.25/2.01  tff(c_284, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))='#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')) | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_281, c_79])).
% 5.25/2.01  tff(c_287, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))='#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')) | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_284])).
% 5.25/2.01  tff(c_346, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))='#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_323, c_287])).
% 5.25/2.01  tff(c_400, plain, (~v1_xboole_0('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_346, c_18])).
% 5.25/2.01  tff(c_444, plain, (~v1_xboole_0('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_215, c_400])).
% 5.25/2.01  tff(c_446, plain, (~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_444])).
% 5.25/2.01  tff(c_449, plain, (~l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_12, c_446])).
% 5.25/2.01  tff(c_453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_329, c_449])).
% 5.25/2.01  tff(c_454, plain, (~v1_xboole_0('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_444])).
% 5.25/2.01  tff(c_455, plain, (l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_444])).
% 5.25/2.01  tff(c_268, plain, (![A_106, B_107]: (v7_struct_0(k1_tex_2(A_106, B_107)) | ~m1_subset_1(B_107, u1_struct_0(A_106)) | ~l1_pre_topc(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_171])).
% 5.25/2.01  tff(c_274, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_268])).
% 5.25/2.01  tff(c_278, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_274])).
% 5.25/2.01  tff(c_279, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_64, c_278])).
% 5.25/2.01  tff(c_56, plain, (![A_53, B_55]: (v1_subset_1(k6_domain_1(A_53, B_55), A_53) | ~m1_subset_1(B_55, A_53) | v1_zfmisc_1(A_53) | v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_193])).
% 5.25/2.01  tff(c_611, plain, (![A_139, B_140]: (~v7_struct_0(A_139) | ~v1_subset_1(k6_domain_1(u1_struct_0(A_139), B_140), u1_struct_0(A_139)) | ~m1_subset_1(B_140, u1_struct_0(A_139)) | ~l1_struct_0(A_139) | v2_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_206])).
% 5.25/2.01  tff(c_645, plain, (![A_141, B_142]: (~v7_struct_0(A_141) | ~l1_struct_0(A_141) | v2_struct_0(A_141) | ~m1_subset_1(B_142, u1_struct_0(A_141)) | v1_zfmisc_1(u1_struct_0(A_141)) | v1_xboole_0(u1_struct_0(A_141)))), inference(resolution, [status(thm)], [c_56, c_611])).
% 5.25/2.01  tff(c_651, plain, (![B_142]: (~v7_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~m1_subset_1(B_142, '#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | v1_zfmisc_1(u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))) | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_346, c_645])).
% 5.25/2.01  tff(c_663, plain, (![B_142]: (v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~m1_subset_1(B_142, '#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | v1_zfmisc_1('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | v1_xboole_0('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_346, c_346, c_455, c_279, c_651])).
% 5.25/2.01  tff(c_664, plain, (![B_142]: (~m1_subset_1(B_142, '#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | v1_zfmisc_1('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_454, c_215, c_663])).
% 5.25/2.01  tff(c_671, plain, (![B_142]: (~m1_subset_1(B_142, '#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))))), inference(splitLeft, [status(thm)], [c_664])).
% 5.25/2.01  tff(c_216, plain, (![A_96, B_97]: (m1_subset_1(o_2_0_pre_topc(A_96, B_97), B_97) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.25/2.01  tff(c_223, plain, (![A_96]: (m1_subset_1(o_2_0_pre_topc(A_96, u1_struct_0(A_96)), u1_struct_0(A_96)) | ~l1_pre_topc(A_96))), inference(resolution, [status(thm)], [c_111, c_216])).
% 5.25/2.01  tff(c_381, plain, (m1_subset_1(o_2_0_pre_topc(k1_tex_2('#skF_3', '#skF_4'), u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), '#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_346, c_223])).
% 5.25/2.01  tff(c_431, plain, (m1_subset_1(o_2_0_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))), '#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_329, c_346, c_381])).
% 5.25/2.01  tff(c_673, plain, $false, inference(negUnitSimplification, [status(thm)], [c_671, c_431])).
% 5.25/2.01  tff(c_674, plain, (v1_zfmisc_1('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_664])).
% 5.25/2.01  tff(c_1503, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1496, c_674])).
% 5.25/2.01  tff(c_1520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_805, c_1503])).
% 5.25/2.01  tff(c_1522, plain, (v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_66])).
% 5.25/2.01  tff(c_1547, plain, (![B_195, A_196]: (v1_subset_1(B_195, A_196) | B_195=A_196 | ~m1_subset_1(B_195, k1_zfmisc_1(A_196)))), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.25/2.01  tff(c_1550, plain, (![A_4]: (v1_subset_1('#skF_1'(A_4), A_4) | '#skF_1'(A_4)=A_4)), inference(resolution, [status(thm)], [c_6, c_1547])).
% 5.25/2.01  tff(c_1553, plain, (![A_4]: ('#skF_1'(A_4)=A_4)), inference(negUnitSimplification, [status(thm)], [c_4, c_1550])).
% 5.25/2.01  tff(c_1557, plain, (![A_4]: (~v1_subset_1(A_4, A_4))), inference(demodulation, [status(thm), theory('equality')], [c_1553, c_4])).
% 5.25/2.01  tff(c_1556, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_1553, c_6])).
% 5.25/2.01  tff(c_1958, plain, (![B_275, A_276]: (v1_subset_1(u1_struct_0(B_275), u1_struct_0(A_276)) | ~m1_subset_1(u1_struct_0(B_275), k1_zfmisc_1(u1_struct_0(A_276))) | ~v1_tex_2(B_275, A_276) | ~m1_pre_topc(B_275, A_276) | ~l1_pre_topc(A_276))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.25/2.01  tff(c_1965, plain, (![B_275]: (v1_subset_1(u1_struct_0(B_275), u1_struct_0(B_275)) | ~v1_tex_2(B_275, B_275) | ~m1_pre_topc(B_275, B_275) | ~l1_pre_topc(B_275))), inference(resolution, [status(thm)], [c_1556, c_1958])).
% 5.25/2.01  tff(c_1970, plain, (![B_277]: (~v1_tex_2(B_277, B_277) | ~m1_pre_topc(B_277, B_277) | ~l1_pre_topc(B_277))), inference(negUnitSimplification, [status(thm)], [c_1557, c_1965])).
% 5.25/2.01  tff(c_1976, plain, (![A_278]: (u1_struct_0(A_278)='#skF_2'(A_278, A_278) | ~m1_pre_topc(A_278, A_278) | ~l1_pre_topc(A_278))), inference(resolution, [status(thm)], [c_34, c_1970])).
% 5.25/2.01  tff(c_1981, plain, (![A_279]: (u1_struct_0(A_279)='#skF_2'(A_279, A_279) | ~l1_pre_topc(A_279))), inference(resolution, [status(thm)], [c_26, c_1976])).
% 5.25/2.01  tff(c_1993, plain, (u1_struct_0('#skF_3')='#skF_2'('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_1981])).
% 5.25/2.01  tff(c_24, plain, (![B_29, A_27]: (m1_subset_1(u1_struct_0(B_29), k1_zfmisc_1(u1_struct_0(A_27))) | ~m1_pre_topc(B_29, A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.25/2.01  tff(c_2196, plain, (![B_280, A_281]: (v1_subset_1(u1_struct_0(B_280), u1_struct_0(A_281)) | ~v1_tex_2(B_280, A_281) | ~m1_pre_topc(B_280, A_281) | ~l1_pre_topc(A_281))), inference(resolution, [status(thm)], [c_24, c_1958])).
% 5.25/2.01  tff(c_2206, plain, (![B_280]: (v1_subset_1(u1_struct_0(B_280), '#skF_2'('#skF_3', '#skF_3')) | ~v1_tex_2(B_280, '#skF_3') | ~m1_pre_topc(B_280, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1993, c_2196])).
% 5.25/2.01  tff(c_2209, plain, (![B_280]: (v1_subset_1(u1_struct_0(B_280), '#skF_2'('#skF_3', '#skF_3')) | ~v1_tex_2(B_280, '#skF_3') | ~m1_pre_topc(B_280, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2206])).
% 5.25/2.01  tff(c_1567, plain, (![A_198, B_199]: (k6_domain_1(A_198, B_199)=k1_tarski(B_199) | ~m1_subset_1(B_199, A_198) | v1_xboole_0(A_198))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.25/2.01  tff(c_1571, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_60, c_1567])).
% 5.25/2.01  tff(c_1597, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_1571])).
% 5.25/2.01  tff(c_1600, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1597, c_18])).
% 5.25/2.01  tff(c_1603, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_1600])).
% 5.25/2.01  tff(c_1606, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_12, c_1603])).
% 5.25/2.01  tff(c_1610, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_1606])).
% 5.25/2.01  tff(c_1612, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_1571])).
% 5.25/2.01  tff(c_1997, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1993, c_1612])).
% 5.25/2.01  tff(c_1611, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_1571])).
% 5.25/2.01  tff(c_1521, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_66])).
% 5.25/2.01  tff(c_1613, plain, (~v1_subset_1(k1_tarski('#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1611, c_1521])).
% 5.25/2.01  tff(c_1709, plain, (![A_224, B_225]: (v1_subset_1(k6_domain_1(A_224, B_225), A_224) | ~m1_subset_1(B_225, A_224) | v1_zfmisc_1(A_224) | v1_xboole_0(A_224))), inference(cnfTransformation, [status(thm)], [f_193])).
% 5.25/2.01  tff(c_1718, plain, (v1_subset_1(k1_tarski('#skF_4'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_zfmisc_1(u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1611, c_1709])).
% 5.25/2.01  tff(c_1723, plain, (v1_subset_1(k1_tarski('#skF_4'), u1_struct_0('#skF_3')) | v1_zfmisc_1(u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1718])).
% 5.25/2.01  tff(c_1724, plain, (v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1612, c_1613, c_1723])).
% 5.25/2.01  tff(c_1994, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1993, c_1724])).
% 5.25/2.01  tff(c_1730, plain, (![B_227, A_228]: (v1_xboole_0(B_227) | ~v1_subset_1(B_227, A_228) | ~m1_subset_1(B_227, k1_zfmisc_1(A_228)) | ~v1_zfmisc_1(A_228) | v1_xboole_0(A_228))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.25/2.01  tff(c_2404, plain, (![B_289, A_290]: (v1_xboole_0(u1_struct_0(B_289)) | ~v1_subset_1(u1_struct_0(B_289), u1_struct_0(A_290)) | ~v1_zfmisc_1(u1_struct_0(A_290)) | v1_xboole_0(u1_struct_0(A_290)) | ~m1_pre_topc(B_289, A_290) | ~l1_pre_topc(A_290))), inference(resolution, [status(thm)], [c_24, c_1730])).
% 5.25/2.01  tff(c_2413, plain, (![B_289]: (v1_xboole_0(u1_struct_0(B_289)) | ~v1_subset_1(u1_struct_0(B_289), '#skF_2'('#skF_3', '#skF_3')) | ~v1_zfmisc_1(u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_289, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1993, c_2404])).
% 5.25/2.01  tff(c_2421, plain, (![B_289]: (v1_xboole_0(u1_struct_0(B_289)) | ~v1_subset_1(u1_struct_0(B_289), '#skF_2'('#skF_3', '#skF_3')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_3')) | ~m1_pre_topc(B_289, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1993, c_1994, c_1993, c_2413])).
% 5.25/2.01  tff(c_2557, plain, (![B_298]: (v1_xboole_0(u1_struct_0(B_298)) | ~v1_subset_1(u1_struct_0(B_298), '#skF_2'('#skF_3', '#skF_3')) | ~m1_pre_topc(B_298, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1997, c_2421])).
% 5.25/2.01  tff(c_2569, plain, (![B_300]: (v1_xboole_0(u1_struct_0(B_300)) | ~v1_tex_2(B_300, '#skF_3') | ~m1_pre_topc(B_300, '#skF_3'))), inference(resolution, [status(thm)], [c_2209, c_2557])).
% 5.25/2.01  tff(c_2593, plain, (![B_301]: (~l1_struct_0(B_301) | v2_struct_0(B_301) | ~v1_tex_2(B_301, '#skF_3') | ~m1_pre_topc(B_301, '#skF_3'))), inference(resolution, [status(thm)], [c_2569, c_18])).
% 5.25/2.01  tff(c_2600, plain, (~l1_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_1522, c_2593])).
% 5.25/2.01  tff(c_2606, plain, (~l1_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1769, c_2600])).
% 5.25/2.01  tff(c_2607, plain, (~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1672, c_2606])).
% 5.25/2.01  tff(c_2610, plain, (~l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_12, c_2607])).
% 5.25/2.01  tff(c_2614, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1775, c_2610])).
% 5.25/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.25/2.01  
% 5.25/2.01  Inference rules
% 5.25/2.01  ----------------------
% 5.25/2.01  #Ref     : 0
% 5.25/2.01  #Sup     : 504
% 5.25/2.01  #Fact    : 0
% 5.25/2.01  #Define  : 0
% 5.25/2.01  #Split   : 9
% 5.25/2.01  #Chain   : 0
% 5.25/2.01  #Close   : 0
% 5.25/2.01  
% 5.25/2.01  Ordering : KBO
% 5.25/2.01  
% 5.25/2.01  Simplification rules
% 5.25/2.01  ----------------------
% 5.25/2.01  #Subsume      : 81
% 5.25/2.01  #Demod        : 383
% 5.25/2.01  #Tautology    : 120
% 5.25/2.01  #SimpNegUnit  : 121
% 5.25/2.01  #BackRed      : 40
% 5.25/2.01  
% 5.25/2.01  #Partial instantiations: 0
% 5.25/2.01  #Strategies tried      : 1
% 5.25/2.01  
% 5.25/2.01  Timing (in seconds)
% 5.25/2.01  ----------------------
% 5.25/2.01  Preprocessing        : 0.37
% 5.25/2.01  Parsing              : 0.20
% 5.25/2.01  CNF conversion       : 0.03
% 5.25/2.01  Main loop            : 0.80
% 5.25/2.01  Inferencing          : 0.29
% 5.25/2.01  Reduction            : 0.26
% 5.25/2.01  Demodulation         : 0.16
% 5.25/2.01  BG Simplification    : 0.03
% 5.25/2.01  Subsumption          : 0.16
% 5.25/2.01  Abstraction          : 0.04
% 5.25/2.01  MUC search           : 0.00
% 5.25/2.01  Cooper               : 0.00
% 5.25/2.01  Total                : 1.25
% 5.25/2.01  Index Insertion      : 0.00
% 5.25/2.01  Index Deletion       : 0.00
% 5.25/2.01  Index Matching       : 0.00
% 5.25/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
