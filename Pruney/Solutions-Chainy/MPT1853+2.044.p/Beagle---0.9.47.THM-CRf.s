%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:06 EST 2020

% Result     : Theorem 4.97s
% Output     : CNFRefutation 5.31s
% Verified   : 
% Statistics : Number of formulae       :  199 (1533 expanded)
%              Number of leaves         :   47 ( 486 expanded)
%              Depth                    :   22
%              Number of atoms          :  389 (3828 expanded)
%              Number of equality atoms :   34 ( 534 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tex_2 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_4

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

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_36,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_149,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_190,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_118,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v7_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ~ v1_xboole_0(B)
           => ( ~ v1_xboole_0(B)
              & ~ v1_subset_1(B,u1_struct_0(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tex_2)).

tff(f_163,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

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

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_177,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_128,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(c_16,plain,(
    ! [A_7] : k2_subset_1(A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    ! [A_8] : m1_subset_1(k2_subset_1(A_8),k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_85,plain,(
    ! [A_8] : m1_subset_1(A_8,k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_58,plain,(
    ! [B_44] :
      ( ~ v1_subset_1(B_44,B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_87,plain,(
    ! [B_44] : ~ v1_subset_1(B_44,B_44) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_58])).

tff(c_74,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_22,plain,(
    ! [A_12] :
      ( l1_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_72,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_1619,plain,(
    ! [A_218,B_219] :
      ( k6_domain_1(A_218,B_219) = k1_tarski(B_219)
      | ~ m1_subset_1(B_219,A_218)
      | v1_xboole_0(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1631,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_72,c_1619])).

tff(c_1662,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1631])).

tff(c_26,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0(u1_struct_0(A_16))
      | ~ l1_struct_0(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1665,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1662,c_26])).

tff(c_1668,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1665])).

tff(c_1671,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_1668])).

tff(c_1675,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1671])).

tff(c_1676,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1631])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_126,plain,(
    ! [C_64,B_65,A_66] :
      ( ~ v1_xboole_0(C_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(C_64))
      | ~ r2_hidden(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_134,plain,(
    ! [A_67,A_68] :
      ( ~ v1_xboole_0(A_67)
      | ~ r2_hidden(A_68,A_67) ) ),
    inference(resolution,[status(thm)],[c_85,c_126])).

tff(c_138,plain,(
    ! [C_5] : ~ v1_xboole_0(k1_tarski(C_5)) ),
    inference(resolution,[status(thm)],[c_4,c_134])).

tff(c_163,plain,(
    ! [A_73,B_74] :
      ( k6_domain_1(A_73,B_74) = k1_tarski(B_74)
      | ~ m1_subset_1(B_74,A_73)
      | v1_xboole_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_175,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_72,c_163])).

tff(c_197,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_200,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_197,c_26])).

tff(c_203,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_200])).

tff(c_206,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_203])).

tff(c_210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_206])).

tff(c_211,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_78,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5'))
    | ~ v1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_110,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_84,plain,
    ( v1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_139,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_84])).

tff(c_213,plain,(
    v1_subset_1(k1_tarski('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_139])).

tff(c_212,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_219,plain,(
    ! [A_80,B_81] :
      ( m1_subset_1(k6_domain_1(A_80,B_81),k1_zfmisc_1(A_80))
      | ~ m1_subset_1(B_81,A_80)
      | v1_xboole_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_230,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_219])).

tff(c_241,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_230])).

tff(c_242,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_241])).

tff(c_746,plain,(
    ! [B_136,A_137] :
      ( ~ v1_subset_1(B_136,u1_struct_0(A_137))
      | v1_xboole_0(B_136)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ l1_struct_0(A_137)
      | ~ v7_struct_0(A_137)
      | v2_struct_0(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_755,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_6'),u1_struct_0('#skF_5'))
    | v1_xboole_0(k1_tarski('#skF_6'))
    | ~ l1_struct_0('#skF_5')
    | ~ v7_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_242,c_746])).

tff(c_777,plain,
    ( v1_xboole_0(k1_tarski('#skF_6'))
    | ~ l1_struct_0('#skF_5')
    | ~ v7_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_755])).

tff(c_778,plain,
    ( ~ l1_struct_0('#skF_5')
    | ~ v7_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_138,c_777])).

tff(c_783,plain,(
    ~ v7_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_778])).

tff(c_396,plain,(
    ! [A_103,B_104] :
      ( m1_pre_topc(k1_tex_2(A_103,B_104),A_103)
      | ~ m1_subset_1(B_104,u1_struct_0(A_103))
      | ~ l1_pre_topc(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_401,plain,
    ( m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_396])).

tff(c_405,plain,
    ( m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_401])).

tff(c_406,plain,(
    m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_405])).

tff(c_605,plain,(
    ! [A_122,B_123] :
      ( m1_subset_1('#skF_4'(A_122,B_123),k1_zfmisc_1(u1_struct_0(A_122)))
      | v1_tex_2(B_123,A_122)
      | ~ m1_pre_topc(B_123,A_122)
      | ~ l1_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_56,plain,(
    ! [B_44,A_43] :
      ( v1_subset_1(B_44,A_43)
      | B_44 = A_43
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1407,plain,(
    ! [A_188,B_189] :
      ( v1_subset_1('#skF_4'(A_188,B_189),u1_struct_0(A_188))
      | u1_struct_0(A_188) = '#skF_4'(A_188,B_189)
      | v1_tex_2(B_189,A_188)
      | ~ m1_pre_topc(B_189,A_188)
      | ~ l1_pre_topc(A_188) ) ),
    inference(resolution,[status(thm)],[c_605,c_56])).

tff(c_50,plain,(
    ! [A_33,B_39] :
      ( ~ v1_subset_1('#skF_4'(A_33,B_39),u1_struct_0(A_33))
      | v1_tex_2(B_39,A_33)
      | ~ m1_pre_topc(B_39,A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1417,plain,(
    ! [A_190,B_191] :
      ( u1_struct_0(A_190) = '#skF_4'(A_190,B_191)
      | v1_tex_2(B_191,A_190)
      | ~ m1_pre_topc(B_191,A_190)
      | ~ l1_pre_topc(A_190) ) ),
    inference(resolution,[status(thm)],[c_1407,c_50])).

tff(c_1430,plain,
    ( '#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6')) = u1_struct_0('#skF_5')
    | ~ m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_1417,c_110])).

tff(c_1438,plain,(
    '#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6')) = u1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_406,c_1430])).

tff(c_24,plain,(
    ! [B_15,A_13] :
      ( l1_pre_topc(B_15)
      | ~ m1_pre_topc(B_15,A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_409,plain,
    ( l1_pre_topc(k1_tex_2('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_406,c_24])).

tff(c_412,plain,(
    l1_pre_topc(k1_tex_2('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_409])).

tff(c_379,plain,(
    ! [A_97,B_98] :
      ( v7_struct_0(k1_tex_2(A_97,B_98))
      | ~ m1_subset_1(B_98,u1_struct_0(A_97))
      | ~ l1_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_386,plain,
    ( v7_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_379])).

tff(c_390,plain,
    ( v7_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_386])).

tff(c_391,plain,(
    v7_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_390])).

tff(c_465,plain,(
    ! [B_110,A_111] :
      ( u1_struct_0(B_110) = '#skF_4'(A_111,B_110)
      | v1_tex_2(B_110,A_111)
      | ~ m1_pre_topc(B_110,A_111)
      | ~ l1_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_468,plain,
    ( u1_struct_0(k1_tex_2('#skF_5','#skF_6')) = '#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6'))
    | ~ m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_465,c_110])).

tff(c_471,plain,(
    u1_struct_0(k1_tex_2('#skF_5','#skF_6')) = '#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_406,c_468])).

tff(c_30,plain,(
    ! [A_18] :
      ( v1_zfmisc_1(u1_struct_0(A_18))
      | ~ l1_struct_0(A_18)
      | ~ v7_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_512,plain,
    ( v1_zfmisc_1('#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6')))
    | ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | ~ v7_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_30])).

tff(c_536,plain,
    ( v1_zfmisc_1('#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6')))
    | ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_512])).

tff(c_539,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_536])).

tff(c_542,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_22,c_539])).

tff(c_546,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_542])).

tff(c_547,plain,(
    v1_zfmisc_1('#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_536])).

tff(c_1458,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1438,c_547])).

tff(c_28,plain,(
    ! [A_17] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_17))
      | ~ l1_struct_0(A_17)
      | v7_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1524,plain,
    ( ~ l1_struct_0('#skF_5')
    | v7_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1458,c_28])).

tff(c_1530,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_783,c_1524])).

tff(c_1533,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_1530])).

tff(c_1537,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1533])).

tff(c_1538,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_778])).

tff(c_1542,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_1538])).

tff(c_1546,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1542])).

tff(c_1547,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_1678,plain,(
    ~ v1_subset_1(k1_tarski('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1676,c_1547])).

tff(c_1677,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1631])).

tff(c_32,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k6_domain_1(A_19,B_20),k1_zfmisc_1(A_19))
      | ~ m1_subset_1(B_20,A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1682,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1676,c_32])).

tff(c_1686,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1682])).

tff(c_1687,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1677,c_1686])).

tff(c_1694,plain,
    ( v1_subset_1(k1_tarski('#skF_6'),u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = k1_tarski('#skF_6') ),
    inference(resolution,[status(thm)],[c_1687,c_56])).

tff(c_1700,plain,(
    u1_struct_0('#skF_5') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_1678,c_1694])).

tff(c_1706,plain,(
    m1_subset_1('#skF_6',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1700,c_72])).

tff(c_2101,plain,(
    ! [A_263,B_264] :
      ( m1_pre_topc(k1_tex_2(A_263,B_264),A_263)
      | ~ m1_subset_1(B_264,u1_struct_0(A_263))
      | ~ l1_pre_topc(A_263)
      | v2_struct_0(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_2103,plain,(
    ! [B_264] :
      ( m1_pre_topc(k1_tex_2('#skF_5',B_264),'#skF_5')
      | ~ m1_subset_1(B_264,k1_tarski('#skF_6'))
      | ~ l1_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1700,c_2101])).

tff(c_2108,plain,(
    ! [B_264] :
      ( m1_pre_topc(k1_tex_2('#skF_5',B_264),'#skF_5')
      | ~ m1_subset_1(B_264,k1_tarski('#skF_6'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2103])).

tff(c_2111,plain,(
    ! [B_265] :
      ( m1_pre_topc(k1_tex_2('#skF_5',B_265),'#skF_5')
      | ~ m1_subset_1(B_265,k1_tarski('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2108])).

tff(c_2119,plain,(
    m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_1706,c_2111])).

tff(c_1548,plain,(
    v1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_2126,plain,
    ( l1_pre_topc(k1_tex_2('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_2119,c_24])).

tff(c_2129,plain,(
    l1_pre_topc(k1_tex_2('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2126])).

tff(c_1887,plain,(
    ! [A_233,B_234] :
      ( ~ v2_struct_0(k1_tex_2(A_233,B_234))
      | ~ m1_subset_1(B_234,u1_struct_0(A_233))
      | ~ l1_pre_topc(A_233)
      | v2_struct_0(A_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_1890,plain,(
    ! [B_234] :
      ( ~ v2_struct_0(k1_tex_2('#skF_5',B_234))
      | ~ m1_subset_1(B_234,k1_tarski('#skF_6'))
      | ~ l1_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1700,c_1887])).

tff(c_1896,plain,(
    ! [B_234] :
      ( ~ v2_struct_0(k1_tex_2('#skF_5',B_234))
      | ~ m1_subset_1(B_234,k1_tarski('#skF_6'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1890])).

tff(c_1899,plain,(
    ! [B_235] :
      ( ~ v2_struct_0(k1_tex_2('#skF_5',B_235))
      | ~ m1_subset_1(B_235,k1_tarski('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1896])).

tff(c_1907,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_1706,c_1899])).

tff(c_1783,plain,(
    ! [B_225,A_226] :
      ( m1_subset_1(u1_struct_0(B_225),k1_zfmisc_1(u1_struct_0(A_226)))
      | ~ m1_pre_topc(B_225,A_226)
      | ~ l1_pre_topc(A_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1800,plain,(
    ! [B_225] :
      ( m1_subset_1(u1_struct_0(B_225),k1_zfmisc_1(k1_tarski('#skF_6')))
      | ~ m1_pre_topc(B_225,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1700,c_1783])).

tff(c_1827,plain,(
    ! [B_228] :
      ( m1_subset_1(u1_struct_0(B_228),k1_zfmisc_1(k1_tarski('#skF_6')))
      | ~ m1_pre_topc(B_228,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1800])).

tff(c_1844,plain,(
    ! [B_228] :
      ( v1_subset_1(u1_struct_0(B_228),k1_tarski('#skF_6'))
      | u1_struct_0(B_228) = k1_tarski('#skF_6')
      | ~ m1_pre_topc(B_228,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1827,c_56])).

tff(c_1806,plain,(
    ! [B_225] :
      ( m1_subset_1(u1_struct_0(B_225),k1_zfmisc_1(k1_tarski('#skF_6')))
      | ~ m1_pre_topc(B_225,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1800])).

tff(c_1717,plain,
    ( v1_zfmisc_1(k1_tarski('#skF_6'))
    | ~ l1_struct_0('#skF_5')
    | ~ v7_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1700,c_30])).

tff(c_1758,plain,(
    ~ v7_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1717])).

tff(c_1704,plain,(
    k6_domain_1(k1_tarski('#skF_6'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1700,c_1676])).

tff(c_1583,plain,(
    ! [C_209,B_210,A_211] :
      ( ~ v1_xboole_0(C_209)
      | ~ m1_subset_1(B_210,k1_zfmisc_1(C_209))
      | ~ r2_hidden(A_211,B_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1600,plain,(
    ! [A_213,A_214] :
      ( ~ v1_xboole_0(A_213)
      | ~ r2_hidden(A_214,A_213) ) ),
    inference(resolution,[status(thm)],[c_85,c_1583])).

tff(c_1604,plain,(
    ! [C_5] : ~ v1_xboole_0(k1_tarski(C_5)) ),
    inference(resolution,[status(thm)],[c_4,c_1600])).

tff(c_1728,plain,(
    ! [A_223,B_224] :
      ( v1_zfmisc_1(A_223)
      | k6_domain_1(A_223,B_224) != A_223
      | ~ m1_subset_1(B_224,A_223)
      | v1_xboole_0(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1731,plain,
    ( v1_zfmisc_1(k1_tarski('#skF_6'))
    | k6_domain_1(k1_tarski('#skF_6'),'#skF_6') != k1_tarski('#skF_6')
    | v1_xboole_0(k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_1706,c_1728])).

tff(c_1743,plain,
    ( v1_zfmisc_1(k1_tarski('#skF_6'))
    | k6_domain_1(k1_tarski('#skF_6'),'#skF_6') != k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_1604,c_1731])).

tff(c_1760,plain,(
    v1_zfmisc_1(k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1704,c_1743])).

tff(c_1714,plain,
    ( ~ v1_zfmisc_1(k1_tarski('#skF_6'))
    | ~ l1_struct_0('#skF_5')
    | v7_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1700,c_28])).

tff(c_1762,plain,
    ( ~ l1_struct_0('#skF_5')
    | v7_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1760,c_1714])).

tff(c_1763,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1758,c_1762])).

tff(c_1766,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_1763])).

tff(c_1770,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1766])).

tff(c_1772,plain,(
    v7_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1717])).

tff(c_1771,plain,
    ( ~ l1_struct_0('#skF_5')
    | v1_zfmisc_1(k1_tarski('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1717])).

tff(c_1773,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1771])).

tff(c_1776,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_1773])).

tff(c_1780,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1776])).

tff(c_1782,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1771])).

tff(c_2350,plain,(
    ! [B_290,A_291] :
      ( ~ v1_subset_1(B_290,u1_struct_0(A_291))
      | v1_xboole_0(B_290)
      | ~ m1_subset_1(B_290,k1_zfmisc_1(u1_struct_0(A_291)))
      | ~ l1_struct_0(A_291)
      | ~ v7_struct_0(A_291)
      | v2_struct_0(A_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2362,plain,(
    ! [B_290] :
      ( ~ v1_subset_1(B_290,u1_struct_0('#skF_5'))
      | v1_xboole_0(B_290)
      | ~ m1_subset_1(B_290,k1_zfmisc_1(k1_tarski('#skF_6')))
      | ~ l1_struct_0('#skF_5')
      | ~ v7_struct_0('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1700,c_2350])).

tff(c_2381,plain,(
    ! [B_290] :
      ( ~ v1_subset_1(B_290,k1_tarski('#skF_6'))
      | v1_xboole_0(B_290)
      | ~ m1_subset_1(B_290,k1_zfmisc_1(k1_tarski('#skF_6')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1772,c_1782,c_1700,c_2362])).

tff(c_2386,plain,(
    ! [B_292] :
      ( ~ v1_subset_1(B_292,k1_tarski('#skF_6'))
      | v1_xboole_0(B_292)
      | ~ m1_subset_1(B_292,k1_zfmisc_1(k1_tarski('#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2381])).

tff(c_2413,plain,(
    ! [B_293] :
      ( ~ v1_subset_1(u1_struct_0(B_293),k1_tarski('#skF_6'))
      | v1_xboole_0(u1_struct_0(B_293))
      | ~ m1_pre_topc(B_293,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1806,c_2386])).

tff(c_2423,plain,(
    ! [B_294] :
      ( v1_xboole_0(u1_struct_0(B_294))
      | u1_struct_0(B_294) = k1_tarski('#skF_6')
      | ~ m1_pre_topc(B_294,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1844,c_2413])).

tff(c_2449,plain,(
    ! [B_295] :
      ( ~ l1_struct_0(B_295)
      | v2_struct_0(B_295)
      | u1_struct_0(B_295) = k1_tarski('#skF_6')
      | ~ m1_pre_topc(B_295,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2423,c_26])).

tff(c_2452,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | u1_struct_0(k1_tex_2('#skF_5','#skF_6')) = k1_tarski('#skF_6') ),
    inference(resolution,[status(thm)],[c_2119,c_2449])).

tff(c_2455,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | u1_struct_0(k1_tex_2('#skF_5','#skF_6')) = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_1907,c_2452])).

tff(c_2456,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_2455])).

tff(c_2480,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_22,c_2456])).

tff(c_2484,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2129,c_2480])).

tff(c_2485,plain,(
    u1_struct_0(k1_tex_2('#skF_5','#skF_6')) = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_2455])).

tff(c_36,plain,(
    ! [B_25,A_23] :
      ( m1_subset_1(u1_struct_0(B_25),k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ m1_pre_topc(B_25,A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2652,plain,(
    ! [B_304,A_305] :
      ( v1_subset_1(u1_struct_0(B_304),u1_struct_0(A_305))
      | ~ m1_subset_1(u1_struct_0(B_304),k1_zfmisc_1(u1_struct_0(A_305)))
      | ~ v1_tex_2(B_304,A_305)
      | ~ m1_pre_topc(B_304,A_305)
      | ~ l1_pre_topc(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_2705,plain,(
    ! [B_310,A_311] :
      ( v1_subset_1(u1_struct_0(B_310),u1_struct_0(A_311))
      | ~ v1_tex_2(B_310,A_311)
      | ~ m1_pre_topc(B_310,A_311)
      | ~ l1_pre_topc(A_311) ) ),
    inference(resolution,[status(thm)],[c_36,c_2652])).

tff(c_2721,plain,(
    ! [B_310] :
      ( v1_subset_1(u1_struct_0(B_310),k1_tarski('#skF_6'))
      | ~ v1_tex_2(B_310,'#skF_5')
      | ~ m1_pre_topc(B_310,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1700,c_2705])).

tff(c_2727,plain,(
    ! [B_312] :
      ( v1_subset_1(u1_struct_0(B_312),k1_tarski('#skF_6'))
      | ~ v1_tex_2(B_312,'#skF_5')
      | ~ m1_pre_topc(B_312,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2721])).

tff(c_2736,plain,
    ( v1_subset_1(k1_tarski('#skF_6'),k1_tarski('#skF_6'))
    | ~ v1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | ~ m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2485,c_2727])).

tff(c_2743,plain,(
    v1_subset_1(k1_tarski('#skF_6'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2119,c_1548,c_2736])).

tff(c_2745,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_2743])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:15:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.97/1.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.97/1.99  
% 4.97/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.31/1.99  %$ v1_tex_2 > v1_subset_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tex_2 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_4
% 5.31/1.99  
% 5.31/1.99  %Foreground sorts:
% 5.31/1.99  
% 5.31/1.99  
% 5.31/1.99  %Background operators:
% 5.31/1.99  
% 5.31/1.99  
% 5.31/1.99  %Foreground operators:
% 5.31/1.99  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.31/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.31/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.31/1.99  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 5.31/1.99  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.31/1.99  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 5.31/1.99  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 5.31/1.99  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.31/1.99  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 5.31/1.99  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.31/1.99  tff('#skF_5', type, '#skF_5': $i).
% 5.31/1.99  tff('#skF_6', type, '#skF_6': $i).
% 5.31/1.99  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 5.31/1.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.31/1.99  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.31/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.31/1.99  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 5.31/1.99  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.31/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.31/1.99  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.31/1.99  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 5.31/1.99  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.31/1.99  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.31/1.99  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.31/1.99  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.31/1.99  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.31/1.99  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.31/1.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.31/1.99  
% 5.31/2.02  tff(f_36, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.31/2.02  tff(f_38, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.31/2.02  tff(f_149, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 5.31/2.02  tff(f_190, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tex_2)).
% 5.31/2.02  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.31/2.02  tff(f_92, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 5.31/2.02  tff(f_64, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.31/2.02  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 5.31/2.02  tff(f_45, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 5.31/2.02  tff(f_85, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 5.31/2.02  tff(f_118, axiom, (![A]: (((~v2_struct_0(A) & v7_struct_0(A)) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (~v1_xboole_0(B) => (~v1_xboole_0(B) & ~v1_subset_1(B, u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_tex_2)).
% 5.31/2.02  tff(f_163, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 5.31/2.02  tff(f_142, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 5.31/2.02  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.31/2.02  tff(f_177, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_tex_2)).
% 5.31/2.02  tff(f_78, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 5.31/2.02  tff(f_72, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_struct_0)).
% 5.31/2.02  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 5.31/2.02  tff(f_128, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 5.31/2.02  tff(c_16, plain, (![A_7]: (k2_subset_1(A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.31/2.02  tff(c_18, plain, (![A_8]: (m1_subset_1(k2_subset_1(A_8), k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.31/2.02  tff(c_85, plain, (![A_8]: (m1_subset_1(A_8, k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18])).
% 5.31/2.02  tff(c_58, plain, (![B_44]: (~v1_subset_1(B_44, B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(B_44)))), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.31/2.02  tff(c_87, plain, (![B_44]: (~v1_subset_1(B_44, B_44))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_58])).
% 5.31/2.02  tff(c_74, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_190])).
% 5.31/2.02  tff(c_22, plain, (![A_12]: (l1_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.31/2.02  tff(c_76, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_190])).
% 5.31/2.02  tff(c_72, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_190])).
% 5.31/2.02  tff(c_1619, plain, (![A_218, B_219]: (k6_domain_1(A_218, B_219)=k1_tarski(B_219) | ~m1_subset_1(B_219, A_218) | v1_xboole_0(A_218))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.31/2.02  tff(c_1631, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_72, c_1619])).
% 5.31/2.02  tff(c_1662, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_1631])).
% 5.31/2.02  tff(c_26, plain, (![A_16]: (~v1_xboole_0(u1_struct_0(A_16)) | ~l1_struct_0(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.31/2.02  tff(c_1665, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1662, c_26])).
% 5.31/2.02  tff(c_1668, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_76, c_1665])).
% 5.31/2.02  tff(c_1671, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_22, c_1668])).
% 5.31/2.02  tff(c_1675, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_1671])).
% 5.31/2.02  tff(c_1676, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_1631])).
% 5.31/2.02  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.31/2.02  tff(c_126, plain, (![C_64, B_65, A_66]: (~v1_xboole_0(C_64) | ~m1_subset_1(B_65, k1_zfmisc_1(C_64)) | ~r2_hidden(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.31/2.02  tff(c_134, plain, (![A_67, A_68]: (~v1_xboole_0(A_67) | ~r2_hidden(A_68, A_67))), inference(resolution, [status(thm)], [c_85, c_126])).
% 5.31/2.02  tff(c_138, plain, (![C_5]: (~v1_xboole_0(k1_tarski(C_5)))), inference(resolution, [status(thm)], [c_4, c_134])).
% 5.31/2.02  tff(c_163, plain, (![A_73, B_74]: (k6_domain_1(A_73, B_74)=k1_tarski(B_74) | ~m1_subset_1(B_74, A_73) | v1_xboole_0(A_73))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.31/2.02  tff(c_175, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_72, c_163])).
% 5.31/2.02  tff(c_197, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_175])).
% 5.31/2.02  tff(c_200, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_197, c_26])).
% 5.31/2.02  tff(c_203, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_76, c_200])).
% 5.31/2.02  tff(c_206, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_22, c_203])).
% 5.31/2.02  tff(c_210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_206])).
% 5.31/2.02  tff(c_211, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_175])).
% 5.31/2.02  tff(c_78, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5')) | ~v1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_190])).
% 5.31/2.02  tff(c_110, plain, (~v1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_78])).
% 5.31/2.02  tff(c_84, plain, (v1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_190])).
% 5.31/2.02  tff(c_139, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_110, c_84])).
% 5.31/2.02  tff(c_213, plain, (v1_subset_1(k1_tarski('#skF_6'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_139])).
% 5.31/2.02  tff(c_212, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_175])).
% 5.31/2.02  tff(c_219, plain, (![A_80, B_81]: (m1_subset_1(k6_domain_1(A_80, B_81), k1_zfmisc_1(A_80)) | ~m1_subset_1(B_81, A_80) | v1_xboole_0(A_80))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.31/2.02  tff(c_230, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_211, c_219])).
% 5.31/2.02  tff(c_241, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_230])).
% 5.31/2.02  tff(c_242, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_212, c_241])).
% 5.31/2.02  tff(c_746, plain, (![B_136, A_137]: (~v1_subset_1(B_136, u1_struct_0(A_137)) | v1_xboole_0(B_136) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_137))) | ~l1_struct_0(A_137) | ~v7_struct_0(A_137) | v2_struct_0(A_137))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.31/2.02  tff(c_755, plain, (~v1_subset_1(k1_tarski('#skF_6'), u1_struct_0('#skF_5')) | v1_xboole_0(k1_tarski('#skF_6')) | ~l1_struct_0('#skF_5') | ~v7_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_242, c_746])).
% 5.31/2.02  tff(c_777, plain, (v1_xboole_0(k1_tarski('#skF_6')) | ~l1_struct_0('#skF_5') | ~v7_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_213, c_755])).
% 5.31/2.02  tff(c_778, plain, (~l1_struct_0('#skF_5') | ~v7_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_76, c_138, c_777])).
% 5.31/2.02  tff(c_783, plain, (~v7_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_778])).
% 5.31/2.02  tff(c_396, plain, (![A_103, B_104]: (m1_pre_topc(k1_tex_2(A_103, B_104), A_103) | ~m1_subset_1(B_104, u1_struct_0(A_103)) | ~l1_pre_topc(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.31/2.02  tff(c_401, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_72, c_396])).
% 5.31/2.02  tff(c_405, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_401])).
% 5.31/2.02  tff(c_406, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_76, c_405])).
% 5.31/2.02  tff(c_605, plain, (![A_122, B_123]: (m1_subset_1('#skF_4'(A_122, B_123), k1_zfmisc_1(u1_struct_0(A_122))) | v1_tex_2(B_123, A_122) | ~m1_pre_topc(B_123, A_122) | ~l1_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.31/2.02  tff(c_56, plain, (![B_44, A_43]: (v1_subset_1(B_44, A_43) | B_44=A_43 | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.31/2.02  tff(c_1407, plain, (![A_188, B_189]: (v1_subset_1('#skF_4'(A_188, B_189), u1_struct_0(A_188)) | u1_struct_0(A_188)='#skF_4'(A_188, B_189) | v1_tex_2(B_189, A_188) | ~m1_pre_topc(B_189, A_188) | ~l1_pre_topc(A_188))), inference(resolution, [status(thm)], [c_605, c_56])).
% 5.31/2.02  tff(c_50, plain, (![A_33, B_39]: (~v1_subset_1('#skF_4'(A_33, B_39), u1_struct_0(A_33)) | v1_tex_2(B_39, A_33) | ~m1_pre_topc(B_39, A_33) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.31/2.02  tff(c_1417, plain, (![A_190, B_191]: (u1_struct_0(A_190)='#skF_4'(A_190, B_191) | v1_tex_2(B_191, A_190) | ~m1_pre_topc(B_191, A_190) | ~l1_pre_topc(A_190))), inference(resolution, [status(thm)], [c_1407, c_50])).
% 5.31/2.02  tff(c_1430, plain, ('#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6'))=u1_struct_0('#skF_5') | ~m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_1417, c_110])).
% 5.31/2.02  tff(c_1438, plain, ('#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6'))=u1_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_406, c_1430])).
% 5.31/2.02  tff(c_24, plain, (![B_15, A_13]: (l1_pre_topc(B_15) | ~m1_pre_topc(B_15, A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.31/2.02  tff(c_409, plain, (l1_pre_topc(k1_tex_2('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_406, c_24])).
% 5.31/2.02  tff(c_412, plain, (l1_pre_topc(k1_tex_2('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_409])).
% 5.31/2.02  tff(c_379, plain, (![A_97, B_98]: (v7_struct_0(k1_tex_2(A_97, B_98)) | ~m1_subset_1(B_98, u1_struct_0(A_97)) | ~l1_pre_topc(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_177])).
% 5.31/2.02  tff(c_386, plain, (v7_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_72, c_379])).
% 5.31/2.02  tff(c_390, plain, (v7_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_386])).
% 5.31/2.02  tff(c_391, plain, (v7_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_76, c_390])).
% 5.31/2.02  tff(c_465, plain, (![B_110, A_111]: (u1_struct_0(B_110)='#skF_4'(A_111, B_110) | v1_tex_2(B_110, A_111) | ~m1_pre_topc(B_110, A_111) | ~l1_pre_topc(A_111))), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.31/2.02  tff(c_468, plain, (u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))='#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6')) | ~m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_465, c_110])).
% 5.31/2.02  tff(c_471, plain, (u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))='#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_406, c_468])).
% 5.31/2.02  tff(c_30, plain, (![A_18]: (v1_zfmisc_1(u1_struct_0(A_18)) | ~l1_struct_0(A_18) | ~v7_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.31/2.02  tff(c_512, plain, (v1_zfmisc_1('#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6'))) | ~l1_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~v7_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_471, c_30])).
% 5.31/2.02  tff(c_536, plain, (v1_zfmisc_1('#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6'))) | ~l1_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_391, c_512])).
% 5.31/2.02  tff(c_539, plain, (~l1_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_536])).
% 5.31/2.02  tff(c_542, plain, (~l1_pre_topc(k1_tex_2('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_22, c_539])).
% 5.31/2.02  tff(c_546, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_412, c_542])).
% 5.31/2.02  tff(c_547, plain, (v1_zfmisc_1('#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_536])).
% 5.31/2.02  tff(c_1458, plain, (v1_zfmisc_1(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1438, c_547])).
% 5.31/2.02  tff(c_28, plain, (![A_17]: (~v1_zfmisc_1(u1_struct_0(A_17)) | ~l1_struct_0(A_17) | v7_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.31/2.02  tff(c_1524, plain, (~l1_struct_0('#skF_5') | v7_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1458, c_28])).
% 5.31/2.02  tff(c_1530, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_783, c_1524])).
% 5.31/2.02  tff(c_1533, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_22, c_1530])).
% 5.31/2.02  tff(c_1537, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_1533])).
% 5.31/2.02  tff(c_1538, plain, (~l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_778])).
% 5.31/2.02  tff(c_1542, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_22, c_1538])).
% 5.31/2.02  tff(c_1546, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_1542])).
% 5.31/2.02  tff(c_1547, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_78])).
% 5.31/2.02  tff(c_1678, plain, (~v1_subset_1(k1_tarski('#skF_6'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1676, c_1547])).
% 5.31/2.02  tff(c_1677, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_1631])).
% 5.31/2.02  tff(c_32, plain, (![A_19, B_20]: (m1_subset_1(k6_domain_1(A_19, B_20), k1_zfmisc_1(A_19)) | ~m1_subset_1(B_20, A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.31/2.02  tff(c_1682, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1676, c_32])).
% 5.31/2.02  tff(c_1686, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1682])).
% 5.31/2.02  tff(c_1687, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_1677, c_1686])).
% 5.31/2.02  tff(c_1694, plain, (v1_subset_1(k1_tarski('#skF_6'), u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')=k1_tarski('#skF_6')), inference(resolution, [status(thm)], [c_1687, c_56])).
% 5.31/2.02  tff(c_1700, plain, (u1_struct_0('#skF_5')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_1678, c_1694])).
% 5.31/2.02  tff(c_1706, plain, (m1_subset_1('#skF_6', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1700, c_72])).
% 5.31/2.02  tff(c_2101, plain, (![A_263, B_264]: (m1_pre_topc(k1_tex_2(A_263, B_264), A_263) | ~m1_subset_1(B_264, u1_struct_0(A_263)) | ~l1_pre_topc(A_263) | v2_struct_0(A_263))), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.31/2.02  tff(c_2103, plain, (![B_264]: (m1_pre_topc(k1_tex_2('#skF_5', B_264), '#skF_5') | ~m1_subset_1(B_264, k1_tarski('#skF_6')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1700, c_2101])).
% 5.31/2.02  tff(c_2108, plain, (![B_264]: (m1_pre_topc(k1_tex_2('#skF_5', B_264), '#skF_5') | ~m1_subset_1(B_264, k1_tarski('#skF_6')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2103])).
% 5.31/2.02  tff(c_2111, plain, (![B_265]: (m1_pre_topc(k1_tex_2('#skF_5', B_265), '#skF_5') | ~m1_subset_1(B_265, k1_tarski('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_76, c_2108])).
% 5.31/2.02  tff(c_2119, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_1706, c_2111])).
% 5.31/2.02  tff(c_1548, plain, (v1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_78])).
% 5.31/2.02  tff(c_2126, plain, (l1_pre_topc(k1_tex_2('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_2119, c_24])).
% 5.31/2.02  tff(c_2129, plain, (l1_pre_topc(k1_tex_2('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2126])).
% 5.31/2.02  tff(c_1887, plain, (![A_233, B_234]: (~v2_struct_0(k1_tex_2(A_233, B_234)) | ~m1_subset_1(B_234, u1_struct_0(A_233)) | ~l1_pre_topc(A_233) | v2_struct_0(A_233))), inference(cnfTransformation, [status(thm)], [f_177])).
% 5.31/2.02  tff(c_1890, plain, (![B_234]: (~v2_struct_0(k1_tex_2('#skF_5', B_234)) | ~m1_subset_1(B_234, k1_tarski('#skF_6')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1700, c_1887])).
% 5.31/2.02  tff(c_1896, plain, (![B_234]: (~v2_struct_0(k1_tex_2('#skF_5', B_234)) | ~m1_subset_1(B_234, k1_tarski('#skF_6')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1890])).
% 5.31/2.02  tff(c_1899, plain, (![B_235]: (~v2_struct_0(k1_tex_2('#skF_5', B_235)) | ~m1_subset_1(B_235, k1_tarski('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_76, c_1896])).
% 5.31/2.02  tff(c_1907, plain, (~v2_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_1706, c_1899])).
% 5.31/2.02  tff(c_1783, plain, (![B_225, A_226]: (m1_subset_1(u1_struct_0(B_225), k1_zfmisc_1(u1_struct_0(A_226))) | ~m1_pre_topc(B_225, A_226) | ~l1_pre_topc(A_226))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.31/2.02  tff(c_1800, plain, (![B_225]: (m1_subset_1(u1_struct_0(B_225), k1_zfmisc_1(k1_tarski('#skF_6'))) | ~m1_pre_topc(B_225, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1700, c_1783])).
% 5.31/2.02  tff(c_1827, plain, (![B_228]: (m1_subset_1(u1_struct_0(B_228), k1_zfmisc_1(k1_tarski('#skF_6'))) | ~m1_pre_topc(B_228, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1800])).
% 5.31/2.02  tff(c_1844, plain, (![B_228]: (v1_subset_1(u1_struct_0(B_228), k1_tarski('#skF_6')) | u1_struct_0(B_228)=k1_tarski('#skF_6') | ~m1_pre_topc(B_228, '#skF_5'))), inference(resolution, [status(thm)], [c_1827, c_56])).
% 5.31/2.02  tff(c_1806, plain, (![B_225]: (m1_subset_1(u1_struct_0(B_225), k1_zfmisc_1(k1_tarski('#skF_6'))) | ~m1_pre_topc(B_225, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1800])).
% 5.31/2.02  tff(c_1717, plain, (v1_zfmisc_1(k1_tarski('#skF_6')) | ~l1_struct_0('#skF_5') | ~v7_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1700, c_30])).
% 5.31/2.02  tff(c_1758, plain, (~v7_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_1717])).
% 5.31/2.02  tff(c_1704, plain, (k6_domain_1(k1_tarski('#skF_6'), '#skF_6')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1700, c_1676])).
% 5.31/2.02  tff(c_1583, plain, (![C_209, B_210, A_211]: (~v1_xboole_0(C_209) | ~m1_subset_1(B_210, k1_zfmisc_1(C_209)) | ~r2_hidden(A_211, B_210))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.31/2.02  tff(c_1600, plain, (![A_213, A_214]: (~v1_xboole_0(A_213) | ~r2_hidden(A_214, A_213))), inference(resolution, [status(thm)], [c_85, c_1583])).
% 5.31/2.02  tff(c_1604, plain, (![C_5]: (~v1_xboole_0(k1_tarski(C_5)))), inference(resolution, [status(thm)], [c_4, c_1600])).
% 5.31/2.02  tff(c_1728, plain, (![A_223, B_224]: (v1_zfmisc_1(A_223) | k6_domain_1(A_223, B_224)!=A_223 | ~m1_subset_1(B_224, A_223) | v1_xboole_0(A_223))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.31/2.02  tff(c_1731, plain, (v1_zfmisc_1(k1_tarski('#skF_6')) | k6_domain_1(k1_tarski('#skF_6'), '#skF_6')!=k1_tarski('#skF_6') | v1_xboole_0(k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_1706, c_1728])).
% 5.31/2.02  tff(c_1743, plain, (v1_zfmisc_1(k1_tarski('#skF_6')) | k6_domain_1(k1_tarski('#skF_6'), '#skF_6')!=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_1604, c_1731])).
% 5.31/2.02  tff(c_1760, plain, (v1_zfmisc_1(k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1704, c_1743])).
% 5.31/2.02  tff(c_1714, plain, (~v1_zfmisc_1(k1_tarski('#skF_6')) | ~l1_struct_0('#skF_5') | v7_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1700, c_28])).
% 5.31/2.02  tff(c_1762, plain, (~l1_struct_0('#skF_5') | v7_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1760, c_1714])).
% 5.31/2.02  tff(c_1763, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_1758, c_1762])).
% 5.31/2.02  tff(c_1766, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_22, c_1763])).
% 5.31/2.02  tff(c_1770, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_1766])).
% 5.31/2.02  tff(c_1772, plain, (v7_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_1717])).
% 5.31/2.02  tff(c_1771, plain, (~l1_struct_0('#skF_5') | v1_zfmisc_1(k1_tarski('#skF_6'))), inference(splitRight, [status(thm)], [c_1717])).
% 5.31/2.02  tff(c_1773, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_1771])).
% 5.31/2.02  tff(c_1776, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_22, c_1773])).
% 5.31/2.02  tff(c_1780, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_1776])).
% 5.31/2.02  tff(c_1782, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_1771])).
% 5.31/2.02  tff(c_2350, plain, (![B_290, A_291]: (~v1_subset_1(B_290, u1_struct_0(A_291)) | v1_xboole_0(B_290) | ~m1_subset_1(B_290, k1_zfmisc_1(u1_struct_0(A_291))) | ~l1_struct_0(A_291) | ~v7_struct_0(A_291) | v2_struct_0(A_291))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.31/2.02  tff(c_2362, plain, (![B_290]: (~v1_subset_1(B_290, u1_struct_0('#skF_5')) | v1_xboole_0(B_290) | ~m1_subset_1(B_290, k1_zfmisc_1(k1_tarski('#skF_6'))) | ~l1_struct_0('#skF_5') | ~v7_struct_0('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1700, c_2350])).
% 5.31/2.02  tff(c_2381, plain, (![B_290]: (~v1_subset_1(B_290, k1_tarski('#skF_6')) | v1_xboole_0(B_290) | ~m1_subset_1(B_290, k1_zfmisc_1(k1_tarski('#skF_6'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1772, c_1782, c_1700, c_2362])).
% 5.31/2.02  tff(c_2386, plain, (![B_292]: (~v1_subset_1(B_292, k1_tarski('#skF_6')) | v1_xboole_0(B_292) | ~m1_subset_1(B_292, k1_zfmisc_1(k1_tarski('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_2381])).
% 5.31/2.02  tff(c_2413, plain, (![B_293]: (~v1_subset_1(u1_struct_0(B_293), k1_tarski('#skF_6')) | v1_xboole_0(u1_struct_0(B_293)) | ~m1_pre_topc(B_293, '#skF_5'))), inference(resolution, [status(thm)], [c_1806, c_2386])).
% 5.31/2.02  tff(c_2423, plain, (![B_294]: (v1_xboole_0(u1_struct_0(B_294)) | u1_struct_0(B_294)=k1_tarski('#skF_6') | ~m1_pre_topc(B_294, '#skF_5'))), inference(resolution, [status(thm)], [c_1844, c_2413])).
% 5.31/2.02  tff(c_2449, plain, (![B_295]: (~l1_struct_0(B_295) | v2_struct_0(B_295) | u1_struct_0(B_295)=k1_tarski('#skF_6') | ~m1_pre_topc(B_295, '#skF_5'))), inference(resolution, [status(thm)], [c_2423, c_26])).
% 5.31/2.02  tff(c_2452, plain, (~l1_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))=k1_tarski('#skF_6')), inference(resolution, [status(thm)], [c_2119, c_2449])).
% 5.31/2.02  tff(c_2455, plain, (~l1_struct_0(k1_tex_2('#skF_5', '#skF_6')) | u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_1907, c_2452])).
% 5.31/2.02  tff(c_2456, plain, (~l1_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_2455])).
% 5.31/2.02  tff(c_2480, plain, (~l1_pre_topc(k1_tex_2('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_22, c_2456])).
% 5.31/2.02  tff(c_2484, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2129, c_2480])).
% 5.31/2.02  tff(c_2485, plain, (u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_2455])).
% 5.31/2.02  tff(c_36, plain, (![B_25, A_23]: (m1_subset_1(u1_struct_0(B_25), k1_zfmisc_1(u1_struct_0(A_23))) | ~m1_pre_topc(B_25, A_23) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.31/2.02  tff(c_2652, plain, (![B_304, A_305]: (v1_subset_1(u1_struct_0(B_304), u1_struct_0(A_305)) | ~m1_subset_1(u1_struct_0(B_304), k1_zfmisc_1(u1_struct_0(A_305))) | ~v1_tex_2(B_304, A_305) | ~m1_pre_topc(B_304, A_305) | ~l1_pre_topc(A_305))), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.31/2.02  tff(c_2705, plain, (![B_310, A_311]: (v1_subset_1(u1_struct_0(B_310), u1_struct_0(A_311)) | ~v1_tex_2(B_310, A_311) | ~m1_pre_topc(B_310, A_311) | ~l1_pre_topc(A_311))), inference(resolution, [status(thm)], [c_36, c_2652])).
% 5.31/2.02  tff(c_2721, plain, (![B_310]: (v1_subset_1(u1_struct_0(B_310), k1_tarski('#skF_6')) | ~v1_tex_2(B_310, '#skF_5') | ~m1_pre_topc(B_310, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1700, c_2705])).
% 5.31/2.02  tff(c_2727, plain, (![B_312]: (v1_subset_1(u1_struct_0(B_312), k1_tarski('#skF_6')) | ~v1_tex_2(B_312, '#skF_5') | ~m1_pre_topc(B_312, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2721])).
% 5.31/2.02  tff(c_2736, plain, (v1_subset_1(k1_tarski('#skF_6'), k1_tarski('#skF_6')) | ~v1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | ~m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2485, c_2727])).
% 5.31/2.02  tff(c_2743, plain, (v1_subset_1(k1_tarski('#skF_6'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2119, c_1548, c_2736])).
% 5.31/2.02  tff(c_2745, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_2743])).
% 5.31/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.31/2.02  
% 5.31/2.02  Inference rules
% 5.31/2.02  ----------------------
% 5.31/2.02  #Ref     : 0
% 5.31/2.02  #Sup     : 537
% 5.31/2.02  #Fact    : 0
% 5.31/2.02  #Define  : 0
% 5.31/2.02  #Split   : 18
% 5.31/2.02  #Chain   : 0
% 5.31/2.02  #Close   : 0
% 5.31/2.02  
% 5.31/2.02  Ordering : KBO
% 5.31/2.02  
% 5.31/2.02  Simplification rules
% 5.31/2.02  ----------------------
% 5.31/2.02  #Subsume      : 75
% 5.31/2.02  #Demod        : 303
% 5.31/2.02  #Tautology    : 159
% 5.31/2.02  #SimpNegUnit  : 117
% 5.31/2.02  #BackRed      : 31
% 5.31/2.02  
% 5.31/2.02  #Partial instantiations: 0
% 5.31/2.02  #Strategies tried      : 1
% 5.31/2.02  
% 5.31/2.02  Timing (in seconds)
% 5.31/2.02  ----------------------
% 5.31/2.03  Preprocessing        : 0.36
% 5.31/2.03  Parsing              : 0.19
% 5.31/2.03  CNF conversion       : 0.03
% 5.31/2.03  Main loop            : 0.82
% 5.31/2.03  Inferencing          : 0.30
% 5.31/2.03  Reduction            : 0.25
% 5.31/2.03  Demodulation         : 0.16
% 5.31/2.03  BG Simplification    : 0.05
% 5.31/2.03  Subsumption          : 0.16
% 5.31/2.03  Abstraction          : 0.04
% 5.31/2.03  MUC search           : 0.00
% 5.31/2.03  Cooper               : 0.00
% 5.31/2.03  Total                : 1.25
% 5.31/2.03  Index Insertion      : 0.00
% 5.31/2.03  Index Deletion       : 0.00
% 5.31/2.03  Index Matching       : 0.00
% 5.31/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
