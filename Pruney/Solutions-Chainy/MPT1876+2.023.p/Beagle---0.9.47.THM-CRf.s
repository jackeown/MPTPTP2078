%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:53 EST 2020

% Result     : Theorem 6.12s
% Output     : CNFRefutation 6.12s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 324 expanded)
%              Number of leaves         :   43 ( 135 expanded)
%              Depth                    :   19
%              Number of atoms          :  360 (1254 expanded)
%              Number of equality atoms :   21 (  39 expanded)
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

tff(f_214,negated_conjecture,(
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

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_140,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ? [C] :
              ( ~ v2_struct_0(C)
              & v1_pre_topc(C)
              & m1_pre_topc(C,A)
              & B = u1_struct_0(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

tff(f_34,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_153,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_194,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_182,axiom,(
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

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_119,axiom,(
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

tff(f_66,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

tff(c_58,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_62,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_90,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(A_56,B_57)
      | ~ r2_hidden(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_94,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_90])).

tff(c_66,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_75,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_559,plain,(
    ! [A_112,B_113] :
      ( m1_pre_topc('#skF_2'(A_112,B_113),A_112)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_112)))
      | v1_xboole_0(B_113)
      | ~ l1_pre_topc(A_112)
      | v2_struct_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_569,plain,
    ( m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_559])).

tff(c_575,plain,
    ( m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_569])).

tff(c_576,plain,(
    m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_56,c_575])).

tff(c_72,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_76,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_72])).

tff(c_260,plain,(
    ! [A_89,B_90] :
      ( ~ v2_struct_0('#skF_2'(A_89,B_90))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_89)))
      | v1_xboole_0(B_90)
      | ~ l1_pre_topc(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_267,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_260])).

tff(c_271,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_267])).

tff(c_272,plain,(
    ~ v2_struct_0('#skF_2'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_56,c_271])).

tff(c_389,plain,(
    ! [A_103,B_104] :
      ( u1_struct_0('#skF_2'(A_103,B_104)) = B_104
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | v1_xboole_0(B_104)
      | ~ l1_pre_topc(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_400,plain,
    ( u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_389])).

tff(c_405,plain,
    ( u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_400])).

tff(c_406,plain,(
    u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_56,c_405])).

tff(c_853,plain,(
    ! [C_124,A_125,B_126] :
      ( m1_subset_1(C_124,u1_struct_0(A_125))
      | ~ m1_subset_1(C_124,u1_struct_0(B_126))
      | ~ m1_pre_topc(B_126,A_125)
      | v2_struct_0(B_126)
      | ~ l1_pre_topc(A_125)
      | v2_struct_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1863,plain,(
    ! [B_166,A_167] :
      ( m1_subset_1('#skF_1'(u1_struct_0(B_166)),u1_struct_0(A_167))
      | ~ m1_pre_topc(B_166,A_167)
      | v2_struct_0(B_166)
      | ~ l1_pre_topc(A_167)
      | v2_struct_0(A_167)
      | v1_xboole_0(u1_struct_0(B_166)) ) ),
    inference(resolution,[status(thm)],[c_94,c_853])).

tff(c_1877,plain,(
    ! [A_167] :
      ( m1_subset_1('#skF_1'('#skF_5'),u1_struct_0(A_167))
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_167)
      | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_167)
      | v2_struct_0(A_167)
      | v1_xboole_0(u1_struct_0('#skF_2'('#skF_4','#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_1863])).

tff(c_1883,plain,(
    ! [A_167] :
      ( m1_subset_1('#skF_1'('#skF_5'),u1_struct_0(A_167))
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_167)
      | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_167)
      | v2_struct_0(A_167)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_1877])).

tff(c_1884,plain,(
    ! [A_167] :
      ( m1_subset_1('#skF_1'('#skF_5'),u1_struct_0(A_167))
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_167)
      | ~ l1_pre_topc(A_167)
      | v2_struct_0(A_167) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_272,c_1883])).

tff(c_6,plain,(
    ! [A_5] : ~ v1_xboole_0(k1_tarski(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k1_tarski(A_6),B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_135,plain,(
    ! [B_72,A_73] :
      ( B_72 = A_73
      | ~ r1_tarski(A_73,B_72)
      | ~ v1_zfmisc_1(B_72)
      | v1_xboole_0(B_72)
      | v1_xboole_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_138,plain,(
    ! [A_6,B_7] :
      ( k1_tarski(A_6) = B_7
      | ~ v1_zfmisc_1(B_7)
      | v1_xboole_0(B_7)
      | v1_xboole_0(k1_tarski(A_6))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_135])).

tff(c_142,plain,(
    ! [A_74,B_75] :
      ( k1_tarski(A_74) = B_75
      | ~ v1_zfmisc_1(B_75)
      | v1_xboole_0(B_75)
      | ~ r2_hidden(A_74,B_75) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_138])).

tff(c_146,plain,(
    ! [A_1] :
      ( k1_tarski('#skF_1'(A_1)) = A_1
      | ~ v1_zfmisc_1(A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_142])).

tff(c_104,plain,(
    ! [B_66,A_67] :
      ( v1_xboole_0(B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_67))
      | ~ v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_111,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_54,c_104])).

tff(c_115,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_111])).

tff(c_858,plain,(
    ! [C_124,A_125] :
      ( m1_subset_1(C_124,u1_struct_0(A_125))
      | ~ m1_subset_1(C_124,'#skF_5')
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_125)
      | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_125)
      | v2_struct_0(A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_853])).

tff(c_1097,plain,(
    ! [C_137,A_138] :
      ( m1_subset_1(C_137,u1_struct_0(A_138))
      | ~ m1_subset_1(C_137,'#skF_5')
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_138)
      | ~ l1_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_858])).

tff(c_24,plain,(
    ! [A_25,B_26] :
      ( k6_domain_1(A_25,B_26) = k1_tarski(B_26)
      | ~ m1_subset_1(B_26,A_25)
      | v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3025,plain,(
    ! [A_210,C_211] :
      ( k6_domain_1(u1_struct_0(A_210),C_211) = k1_tarski(C_211)
      | v1_xboole_0(u1_struct_0(A_210))
      | ~ m1_subset_1(C_211,'#skF_5')
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_210)
      | ~ l1_pre_topc(A_210)
      | v2_struct_0(A_210) ) ),
    inference(resolution,[status(thm)],[c_1097,c_24])).

tff(c_3027,plain,(
    ! [C_211] :
      ( k6_domain_1(u1_struct_0('#skF_4'),C_211) = k1_tarski(C_211)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_211,'#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_576,c_3025])).

tff(c_3030,plain,(
    ! [C_211] :
      ( k6_domain_1(u1_struct_0('#skF_4'),C_211) = k1_tarski(C_211)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_211,'#skF_5')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_3027])).

tff(c_3032,plain,(
    ! [C_212] :
      ( k6_domain_1(u1_struct_0('#skF_4'),C_212) = k1_tarski(C_212)
      | ~ m1_subset_1(C_212,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_115,c_3030])).

tff(c_52,plain,(
    ! [A_46,B_48] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_46),B_48),A_46)
      | ~ m1_subset_1(B_48,u1_struct_0(A_46))
      | ~ l1_pre_topc(A_46)
      | ~ v2_pre_topc(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_3050,plain,(
    ! [C_212] :
      ( v2_tex_2(k1_tarski(C_212),'#skF_4')
      | ~ m1_subset_1(C_212,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_212,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3032,c_52])).

tff(c_3084,plain,(
    ! [C_212] :
      ( v2_tex_2(k1_tarski(C_212),'#skF_4')
      | ~ m1_subset_1(C_212,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_212,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_3050])).

tff(c_3099,plain,(
    ! [C_213] :
      ( v2_tex_2(k1_tarski(C_213),'#skF_4')
      | ~ m1_subset_1(C_213,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_213,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3084])).

tff(c_3112,plain,(
    ! [A_214] :
      ( v2_tex_2(A_214,'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_214),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(A_214),'#skF_5')
      | ~ v1_zfmisc_1(A_214)
      | v1_xboole_0(A_214) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_3099])).

tff(c_3120,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_5')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5')
    | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1884,c_3112])).

tff(c_3149,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_5')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_576,c_76,c_3120])).

tff(c_3150,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_56,c_75,c_3149])).

tff(c_3174,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_94,c_3150])).

tff(c_3182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_3174])).

tff(c_3184,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_4575,plain,(
    ! [A_325,B_326] :
      ( m1_pre_topc('#skF_3'(A_325,B_326),A_325)
      | ~ v2_tex_2(B_326,A_325)
      | ~ m1_subset_1(B_326,k1_zfmisc_1(u1_struct_0(A_325)))
      | v1_xboole_0(B_326)
      | ~ l1_pre_topc(A_325)
      | ~ v2_pre_topc(A_325)
      | v2_struct_0(A_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_4590,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_4575])).

tff(c_4599,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_3184,c_4590])).

tff(c_4600,plain,(
    m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_56,c_4599])).

tff(c_18,plain,(
    ! [B_16,A_14] :
      ( l1_pre_topc(B_16)
      | ~ m1_pre_topc(B_16,A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4606,plain,
    ( l1_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_4600,c_18])).

tff(c_4613,plain,(
    l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_4606])).

tff(c_16,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3183,plain,(
    ~ v1_zfmisc_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_4298,plain,(
    ! [A_311,B_312] :
      ( ~ v2_struct_0('#skF_3'(A_311,B_312))
      | ~ v2_tex_2(B_312,A_311)
      | ~ m1_subset_1(B_312,k1_zfmisc_1(u1_struct_0(A_311)))
      | v1_xboole_0(B_312)
      | ~ l1_pre_topc(A_311)
      | ~ v2_pre_topc(A_311)
      | v2_struct_0(A_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_4319,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_4298])).

tff(c_4328,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_3184,c_4319])).

tff(c_4329,plain,(
    ~ v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_56,c_4328])).

tff(c_60,plain,(
    v2_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_4129,plain,(
    ! [A_301,B_302] :
      ( v1_tdlat_3('#skF_3'(A_301,B_302))
      | ~ v2_tex_2(B_302,A_301)
      | ~ m1_subset_1(B_302,k1_zfmisc_1(u1_struct_0(A_301)))
      | v1_xboole_0(B_302)
      | ~ l1_pre_topc(A_301)
      | ~ v2_pre_topc(A_301)
      | v2_struct_0(A_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_4150,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_4129])).

tff(c_4159,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_3184,c_4150])).

tff(c_4160,plain,(
    v1_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_56,c_4159])).

tff(c_28,plain,(
    ! [B_30,A_28] :
      ( ~ v1_tdlat_3(B_30)
      | v7_struct_0(B_30)
      | v2_struct_0(B_30)
      | ~ m1_pre_topc(B_30,A_28)
      | ~ l1_pre_topc(A_28)
      | ~ v2_tdlat_3(A_28)
      | ~ v2_pre_topc(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_4603,plain,
    ( ~ v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v7_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4600,c_28])).

tff(c_4609,plain,
    ( v7_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_4160,c_4603])).

tff(c_4610,plain,(
    v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_4329,c_4609])).

tff(c_4911,plain,(
    ! [A_334,B_335] :
      ( u1_struct_0('#skF_3'(A_334,B_335)) = B_335
      | ~ v2_tex_2(B_335,A_334)
      | ~ m1_subset_1(B_335,k1_zfmisc_1(u1_struct_0(A_334)))
      | v1_xboole_0(B_335)
      | ~ l1_pre_topc(A_334)
      | ~ v2_pre_topc(A_334)
      | v2_struct_0(A_334) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_4932,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_4911])).

tff(c_4941,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_3184,c_4932])).

tff(c_4942,plain,(
    u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_56,c_4941])).

tff(c_20,plain,(
    ! [A_17] :
      ( v1_zfmisc_1(u1_struct_0(A_17))
      | ~ l1_struct_0(A_17)
      | ~ v7_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4979,plain,
    ( v1_zfmisc_1('#skF_5')
    | ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4942,c_20])).

tff(c_5017,plain,
    ( v1_zfmisc_1('#skF_5')
    | ~ l1_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4610,c_4979])).

tff(c_5018,plain,(
    ~ l1_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_3183,c_5017])).

tff(c_5022,plain,(
    ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_16,c_5018])).

tff(c_5026,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4613,c_5022])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:17:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.12/2.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.12/2.24  
% 6.12/2.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.12/2.24  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 6.12/2.24  
% 6.12/2.24  %Foreground sorts:
% 6.12/2.24  
% 6.12/2.24  
% 6.12/2.24  %Background operators:
% 6.12/2.24  
% 6.12/2.24  
% 6.12/2.24  %Foreground operators:
% 6.12/2.24  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.12/2.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.12/2.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.12/2.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.12/2.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.12/2.24  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 6.12/2.24  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.12/2.24  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 6.12/2.24  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.12/2.24  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 6.12/2.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.12/2.24  tff('#skF_5', type, '#skF_5': $i).
% 6.12/2.24  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 6.12/2.24  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 6.12/2.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.12/2.24  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.12/2.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.12/2.24  tff('#skF_4', type, '#skF_4': $i).
% 6.12/2.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.12/2.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.12/2.24  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 6.12/2.24  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.12/2.24  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.12/2.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.12/2.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.12/2.24  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 6.12/2.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.12/2.24  
% 6.12/2.26  tff(f_214, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 6.12/2.26  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.12/2.26  tff(f_49, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 6.12/2.26  tff(f_140, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (?[C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) & (B = u1_struct_0(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_tsep_1)).
% 6.12/2.26  tff(f_82, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 6.12/2.26  tff(f_34, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 6.12/2.26  tff(f_38, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 6.12/2.26  tff(f_153, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 6.12/2.26  tff(f_45, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 6.12/2.26  tff(f_89, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 6.12/2.26  tff(f_194, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 6.12/2.26  tff(f_182, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tex_2)).
% 6.12/2.26  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 6.12/2.26  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.12/2.26  tff(f_119, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((~v2_struct_0(B) & ~v7_struct_0(B)) => (~v2_struct_0(B) & ~v1_tdlat_3(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc32_tex_2)).
% 6.12/2.26  tff(f_66, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 6.12/2.26  tff(c_58, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_214])).
% 6.12/2.26  tff(c_64, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_214])).
% 6.12/2.26  tff(c_56, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_214])).
% 6.12/2.26  tff(c_62, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_214])).
% 6.12/2.26  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.12/2.26  tff(c_90, plain, (![A_56, B_57]: (m1_subset_1(A_56, B_57) | ~r2_hidden(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.12/2.26  tff(c_94, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_90])).
% 6.12/2.26  tff(c_66, plain, (~v1_zfmisc_1('#skF_5') | ~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_214])).
% 6.12/2.26  tff(c_75, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_66])).
% 6.12/2.26  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_214])).
% 6.12/2.26  tff(c_559, plain, (![A_112, B_113]: (m1_pre_topc('#skF_2'(A_112, B_113), A_112) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(A_112))) | v1_xboole_0(B_113) | ~l1_pre_topc(A_112) | v2_struct_0(A_112))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.12/2.26  tff(c_569, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_559])).
% 6.12/2.26  tff(c_575, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_569])).
% 6.12/2.26  tff(c_576, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_64, c_56, c_575])).
% 6.12/2.26  tff(c_72, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_214])).
% 6.12/2.26  tff(c_76, plain, (v1_zfmisc_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_75, c_72])).
% 6.12/2.26  tff(c_260, plain, (![A_89, B_90]: (~v2_struct_0('#skF_2'(A_89, B_90)) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_89))) | v1_xboole_0(B_90) | ~l1_pre_topc(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.12/2.26  tff(c_267, plain, (~v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_260])).
% 6.12/2.26  tff(c_271, plain, (~v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_267])).
% 6.12/2.26  tff(c_272, plain, (~v2_struct_0('#skF_2'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_56, c_271])).
% 6.12/2.26  tff(c_389, plain, (![A_103, B_104]: (u1_struct_0('#skF_2'(A_103, B_104))=B_104 | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | v1_xboole_0(B_104) | ~l1_pre_topc(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.12/2.26  tff(c_400, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_389])).
% 6.12/2.26  tff(c_405, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_400])).
% 6.12/2.26  tff(c_406, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_64, c_56, c_405])).
% 6.12/2.26  tff(c_853, plain, (![C_124, A_125, B_126]: (m1_subset_1(C_124, u1_struct_0(A_125)) | ~m1_subset_1(C_124, u1_struct_0(B_126)) | ~m1_pre_topc(B_126, A_125) | v2_struct_0(B_126) | ~l1_pre_topc(A_125) | v2_struct_0(A_125))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.12/2.26  tff(c_1863, plain, (![B_166, A_167]: (m1_subset_1('#skF_1'(u1_struct_0(B_166)), u1_struct_0(A_167)) | ~m1_pre_topc(B_166, A_167) | v2_struct_0(B_166) | ~l1_pre_topc(A_167) | v2_struct_0(A_167) | v1_xboole_0(u1_struct_0(B_166)))), inference(resolution, [status(thm)], [c_94, c_853])).
% 6.12/2.26  tff(c_1877, plain, (![A_167]: (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0(A_167)) | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_167) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | ~l1_pre_topc(A_167) | v2_struct_0(A_167) | v1_xboole_0(u1_struct_0('#skF_2'('#skF_4', '#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_406, c_1863])).
% 6.12/2.26  tff(c_1883, plain, (![A_167]: (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0(A_167)) | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_167) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | ~l1_pre_topc(A_167) | v2_struct_0(A_167) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_406, c_1877])).
% 6.12/2.26  tff(c_1884, plain, (![A_167]: (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0(A_167)) | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_167) | ~l1_pre_topc(A_167) | v2_struct_0(A_167))), inference(negUnitSimplification, [status(thm)], [c_56, c_272, c_1883])).
% 6.12/2.26  tff(c_6, plain, (![A_5]: (~v1_xboole_0(k1_tarski(A_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.12/2.26  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k1_tarski(A_6), B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.12/2.26  tff(c_135, plain, (![B_72, A_73]: (B_72=A_73 | ~r1_tarski(A_73, B_72) | ~v1_zfmisc_1(B_72) | v1_xboole_0(B_72) | v1_xboole_0(A_73))), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.12/2.26  tff(c_138, plain, (![A_6, B_7]: (k1_tarski(A_6)=B_7 | ~v1_zfmisc_1(B_7) | v1_xboole_0(B_7) | v1_xboole_0(k1_tarski(A_6)) | ~r2_hidden(A_6, B_7))), inference(resolution, [status(thm)], [c_10, c_135])).
% 6.12/2.26  tff(c_142, plain, (![A_74, B_75]: (k1_tarski(A_74)=B_75 | ~v1_zfmisc_1(B_75) | v1_xboole_0(B_75) | ~r2_hidden(A_74, B_75))), inference(negUnitSimplification, [status(thm)], [c_6, c_138])).
% 6.12/2.26  tff(c_146, plain, (![A_1]: (k1_tarski('#skF_1'(A_1))=A_1 | ~v1_zfmisc_1(A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_142])).
% 6.12/2.26  tff(c_104, plain, (![B_66, A_67]: (v1_xboole_0(B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(A_67)) | ~v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.12/2.26  tff(c_111, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_104])).
% 6.12/2.26  tff(c_115, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_56, c_111])).
% 6.12/2.26  tff(c_858, plain, (![C_124, A_125]: (m1_subset_1(C_124, u1_struct_0(A_125)) | ~m1_subset_1(C_124, '#skF_5') | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_125) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | ~l1_pre_topc(A_125) | v2_struct_0(A_125))), inference(superposition, [status(thm), theory('equality')], [c_406, c_853])).
% 6.12/2.26  tff(c_1097, plain, (![C_137, A_138]: (m1_subset_1(C_137, u1_struct_0(A_138)) | ~m1_subset_1(C_137, '#skF_5') | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_138) | ~l1_pre_topc(A_138) | v2_struct_0(A_138))), inference(negUnitSimplification, [status(thm)], [c_272, c_858])).
% 6.12/2.26  tff(c_24, plain, (![A_25, B_26]: (k6_domain_1(A_25, B_26)=k1_tarski(B_26) | ~m1_subset_1(B_26, A_25) | v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.12/2.26  tff(c_3025, plain, (![A_210, C_211]: (k6_domain_1(u1_struct_0(A_210), C_211)=k1_tarski(C_211) | v1_xboole_0(u1_struct_0(A_210)) | ~m1_subset_1(C_211, '#skF_5') | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_210) | ~l1_pre_topc(A_210) | v2_struct_0(A_210))), inference(resolution, [status(thm)], [c_1097, c_24])).
% 6.12/2.26  tff(c_3027, plain, (![C_211]: (k6_domain_1(u1_struct_0('#skF_4'), C_211)=k1_tarski(C_211) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(C_211, '#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_576, c_3025])).
% 6.12/2.26  tff(c_3030, plain, (![C_211]: (k6_domain_1(u1_struct_0('#skF_4'), C_211)=k1_tarski(C_211) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(C_211, '#skF_5') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_3027])).
% 6.12/2.26  tff(c_3032, plain, (![C_212]: (k6_domain_1(u1_struct_0('#skF_4'), C_212)=k1_tarski(C_212) | ~m1_subset_1(C_212, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_115, c_3030])).
% 6.12/2.26  tff(c_52, plain, (![A_46, B_48]: (v2_tex_2(k6_domain_1(u1_struct_0(A_46), B_48), A_46) | ~m1_subset_1(B_48, u1_struct_0(A_46)) | ~l1_pre_topc(A_46) | ~v2_pre_topc(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_194])).
% 6.12/2.26  tff(c_3050, plain, (![C_212]: (v2_tex_2(k1_tarski(C_212), '#skF_4') | ~m1_subset_1(C_212, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_subset_1(C_212, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3032, c_52])).
% 6.12/2.26  tff(c_3084, plain, (![C_212]: (v2_tex_2(k1_tarski(C_212), '#skF_4') | ~m1_subset_1(C_212, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | ~m1_subset_1(C_212, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_3050])).
% 6.12/2.26  tff(c_3099, plain, (![C_213]: (v2_tex_2(k1_tarski(C_213), '#skF_4') | ~m1_subset_1(C_213, u1_struct_0('#skF_4')) | ~m1_subset_1(C_213, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_3084])).
% 6.12/2.26  tff(c_3112, plain, (![A_214]: (v2_tex_2(A_214, '#skF_4') | ~m1_subset_1('#skF_1'(A_214), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(A_214), '#skF_5') | ~v1_zfmisc_1(A_214) | v1_xboole_0(A_214))), inference(superposition, [status(thm), theory('equality')], [c_146, c_3099])).
% 6.12/2.26  tff(c_3120, plain, (v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_1'('#skF_5'), '#skF_5') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5') | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1884, c_3112])).
% 6.12/2.26  tff(c_3149, plain, (v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_1'('#skF_5'), '#skF_5') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_576, c_76, c_3120])).
% 6.12/2.26  tff(c_3150, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_56, c_75, c_3149])).
% 6.12/2.26  tff(c_3174, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_94, c_3150])).
% 6.12/2.26  tff(c_3182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_3174])).
% 6.12/2.26  tff(c_3184, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_66])).
% 6.12/2.26  tff(c_4575, plain, (![A_325, B_326]: (m1_pre_topc('#skF_3'(A_325, B_326), A_325) | ~v2_tex_2(B_326, A_325) | ~m1_subset_1(B_326, k1_zfmisc_1(u1_struct_0(A_325))) | v1_xboole_0(B_326) | ~l1_pre_topc(A_325) | ~v2_pre_topc(A_325) | v2_struct_0(A_325))), inference(cnfTransformation, [status(thm)], [f_182])).
% 6.12/2.26  tff(c_4590, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_4575])).
% 6.12/2.26  tff(c_4599, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_3184, c_4590])).
% 6.12/2.26  tff(c_4600, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_64, c_56, c_4599])).
% 6.12/2.26  tff(c_18, plain, (![B_16, A_14]: (l1_pre_topc(B_16) | ~m1_pre_topc(B_16, A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.12/2.26  tff(c_4606, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_4600, c_18])).
% 6.12/2.26  tff(c_4613, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_4606])).
% 6.12/2.26  tff(c_16, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.12/2.26  tff(c_3183, plain, (~v1_zfmisc_1('#skF_5')), inference(splitRight, [status(thm)], [c_66])).
% 6.12/2.26  tff(c_4298, plain, (![A_311, B_312]: (~v2_struct_0('#skF_3'(A_311, B_312)) | ~v2_tex_2(B_312, A_311) | ~m1_subset_1(B_312, k1_zfmisc_1(u1_struct_0(A_311))) | v1_xboole_0(B_312) | ~l1_pre_topc(A_311) | ~v2_pre_topc(A_311) | v2_struct_0(A_311))), inference(cnfTransformation, [status(thm)], [f_182])).
% 6.12/2.26  tff(c_4319, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_4298])).
% 6.12/2.26  tff(c_4328, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_3184, c_4319])).
% 6.12/2.26  tff(c_4329, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_56, c_4328])).
% 6.12/2.26  tff(c_60, plain, (v2_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_214])).
% 6.12/2.26  tff(c_4129, plain, (![A_301, B_302]: (v1_tdlat_3('#skF_3'(A_301, B_302)) | ~v2_tex_2(B_302, A_301) | ~m1_subset_1(B_302, k1_zfmisc_1(u1_struct_0(A_301))) | v1_xboole_0(B_302) | ~l1_pre_topc(A_301) | ~v2_pre_topc(A_301) | v2_struct_0(A_301))), inference(cnfTransformation, [status(thm)], [f_182])).
% 6.12/2.26  tff(c_4150, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_4129])).
% 6.12/2.26  tff(c_4159, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_3184, c_4150])).
% 6.12/2.26  tff(c_4160, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_56, c_4159])).
% 6.12/2.26  tff(c_28, plain, (![B_30, A_28]: (~v1_tdlat_3(B_30) | v7_struct_0(B_30) | v2_struct_0(B_30) | ~m1_pre_topc(B_30, A_28) | ~l1_pre_topc(A_28) | ~v2_tdlat_3(A_28) | ~v2_pre_topc(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.12/2.26  tff(c_4603, plain, (~v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v7_struct_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_4600, c_28])).
% 6.12/2.26  tff(c_4609, plain, (v7_struct_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_4160, c_4603])).
% 6.12/2.26  tff(c_4610, plain, (v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_4329, c_4609])).
% 6.12/2.26  tff(c_4911, plain, (![A_334, B_335]: (u1_struct_0('#skF_3'(A_334, B_335))=B_335 | ~v2_tex_2(B_335, A_334) | ~m1_subset_1(B_335, k1_zfmisc_1(u1_struct_0(A_334))) | v1_xboole_0(B_335) | ~l1_pre_topc(A_334) | ~v2_pre_topc(A_334) | v2_struct_0(A_334))), inference(cnfTransformation, [status(thm)], [f_182])).
% 6.12/2.26  tff(c_4932, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_4911])).
% 6.12/2.26  tff(c_4941, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_3184, c_4932])).
% 6.12/2.26  tff(c_4942, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_64, c_56, c_4941])).
% 6.12/2.26  tff(c_20, plain, (![A_17]: (v1_zfmisc_1(u1_struct_0(A_17)) | ~l1_struct_0(A_17) | ~v7_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.12/2.26  tff(c_4979, plain, (v1_zfmisc_1('#skF_5') | ~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4942, c_20])).
% 6.12/2.26  tff(c_5017, plain, (v1_zfmisc_1('#skF_5') | ~l1_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4610, c_4979])).
% 6.12/2.26  tff(c_5018, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_3183, c_5017])).
% 6.12/2.26  tff(c_5022, plain, (~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_16, c_5018])).
% 6.12/2.26  tff(c_5026, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4613, c_5022])).
% 6.12/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.12/2.26  
% 6.12/2.26  Inference rules
% 6.12/2.26  ----------------------
% 6.12/2.26  #Ref     : 0
% 6.12/2.26  #Sup     : 1159
% 6.12/2.26  #Fact    : 0
% 6.12/2.26  #Define  : 0
% 6.12/2.26  #Split   : 12
% 6.12/2.26  #Chain   : 0
% 6.12/2.26  #Close   : 0
% 6.12/2.26  
% 6.12/2.26  Ordering : KBO
% 6.12/2.26  
% 6.12/2.26  Simplification rules
% 6.12/2.26  ----------------------
% 6.12/2.26  #Subsume      : 377
% 6.12/2.26  #Demod        : 166
% 6.12/2.26  #Tautology    : 207
% 6.12/2.26  #SimpNegUnit  : 365
% 6.12/2.26  #BackRed      : 0
% 6.12/2.26  
% 6.12/2.26  #Partial instantiations: 0
% 6.12/2.26  #Strategies tried      : 1
% 6.12/2.26  
% 6.12/2.26  Timing (in seconds)
% 6.12/2.26  ----------------------
% 6.12/2.26  Preprocessing        : 0.37
% 6.12/2.26  Parsing              : 0.21
% 6.12/2.26  CNF conversion       : 0.03
% 6.12/2.26  Main loop            : 1.08
% 6.12/2.26  Inferencing          : 0.37
% 6.12/2.26  Reduction            : 0.32
% 6.12/2.26  Demodulation         : 0.20
% 6.12/2.26  BG Simplification    : 0.05
% 6.12/2.26  Subsumption          : 0.27
% 6.12/2.26  Abstraction          : 0.06
% 6.12/2.26  MUC search           : 0.00
% 6.12/2.26  Cooper               : 0.00
% 6.12/2.26  Total                : 1.49
% 6.12/2.26  Index Insertion      : 0.00
% 6.12/2.26  Index Deletion       : 0.00
% 6.12/2.26  Index Matching       : 0.00
% 6.12/2.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
