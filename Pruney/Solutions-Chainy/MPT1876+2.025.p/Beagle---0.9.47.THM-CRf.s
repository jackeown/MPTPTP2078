%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:53 EST 2020

% Result     : Theorem 9.40s
% Output     : CNFRefutation 9.63s
% Verified   : 
% Statistics : Number of formulae       :  182 (1316 expanded)
%              Number of leaves         :   44 ( 492 expanded)
%              Depth                    :   19
%              Number of atoms          :  528 (5195 expanded)
%              Number of equality atoms :   38 ( 299 expanded)
%              Maximal formula depth    :   12 (   5 average)
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

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_218,negated_conjecture,(
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

tff(f_144,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_86,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_34,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_157,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_198,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_186,axiom,(
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

tff(f_70,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_123,axiom,(
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

tff(c_18,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_64,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_60,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_344,plain,(
    ! [A_98,B_99] :
      ( m1_pre_topc('#skF_2'(A_98,B_99),A_98)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | v1_xboole_0(B_99)
      | ~ l1_pre_topc(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_358,plain,
    ( m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_344])).

tff(c_367,plain,
    ( m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_358])).

tff(c_368,plain,(
    m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_367])).

tff(c_291,plain,(
    ! [A_93,B_94] :
      ( ~ v2_struct_0('#skF_2'(A_93,B_94))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | v1_xboole_0(B_94)
      | ~ l1_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_306,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_291])).

tff(c_314,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_306])).

tff(c_315,plain,(
    ~ v2_struct_0('#skF_2'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_314])).

tff(c_451,plain,(
    ! [A_113,B_114] :
      ( u1_struct_0('#skF_2'(A_113,B_114)) = B_114
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_113)))
      | v1_xboole_0(B_114)
      | ~ l1_pre_topc(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_470,plain,
    ( u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_451])).

tff(c_479,plain,
    ( u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_470])).

tff(c_480,plain,(
    u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_479])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    ! [A_58,B_59] :
      ( m1_subset_1(A_58,B_59)
      | ~ r2_hidden(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_97,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_93])).

tff(c_705,plain,(
    ! [C_129,A_130,B_131] :
      ( m1_subset_1(C_129,u1_struct_0(A_130))
      | ~ m1_subset_1(C_129,u1_struct_0(B_131))
      | ~ m1_pre_topc(B_131,A_130)
      | v2_struct_0(B_131)
      | ~ l1_pre_topc(A_130)
      | v2_struct_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2893,plain,(
    ! [B_188,A_189] :
      ( m1_subset_1('#skF_1'(u1_struct_0(B_188)),u1_struct_0(A_189))
      | ~ m1_pre_topc(B_188,A_189)
      | v2_struct_0(B_188)
      | ~ l1_pre_topc(A_189)
      | v2_struct_0(A_189)
      | v1_xboole_0(u1_struct_0(B_188)) ) ),
    inference(resolution,[status(thm)],[c_97,c_705])).

tff(c_2985,plain,(
    ! [A_189] :
      ( m1_subset_1('#skF_1'('#skF_5'),u1_struct_0(A_189))
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_189)
      | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_189)
      | v2_struct_0(A_189)
      | v1_xboole_0(u1_struct_0('#skF_2'('#skF_4','#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_2893])).

tff(c_3021,plain,(
    ! [A_189] :
      ( m1_subset_1('#skF_1'('#skF_5'),u1_struct_0(A_189))
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_189)
      | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_189)
      | v2_struct_0(A_189)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_2985])).

tff(c_3022,plain,(
    ! [A_189] :
      ( m1_subset_1('#skF_1'('#skF_5'),u1_struct_0(A_189))
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_189)
      | ~ l1_pre_topc(A_189)
      | v2_struct_0(A_189) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_315,c_3021])).

tff(c_74,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_77,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_68,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_80,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_68])).

tff(c_20,plain,(
    ! [B_18,A_16] :
      ( l1_pre_topc(B_18)
      | ~ m1_pre_topc(B_18,A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_371,plain,
    ( l1_pre_topc('#skF_2'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_368,c_20])).

tff(c_374,plain,(
    l1_pre_topc('#skF_2'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_371])).

tff(c_6,plain,(
    ! [A_5] : ~ v1_xboole_0(k1_tarski(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_116,plain,(
    ! [A_68,B_69] :
      ( m1_subset_1(k1_tarski(A_68),k1_zfmisc_1(B_69))
      | ~ r2_hidden(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_120,plain,(
    ! [A_68,B_69] :
      ( r1_tarski(k1_tarski(A_68),B_69)
      | ~ r2_hidden(A_68,B_69) ) ),
    inference(resolution,[status(thm)],[c_116,c_14])).

tff(c_187,plain,(
    ! [B_81,A_82] :
      ( B_81 = A_82
      | ~ r1_tarski(A_82,B_81)
      | ~ v1_zfmisc_1(B_81)
      | v1_xboole_0(B_81)
      | v1_xboole_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_193,plain,(
    ! [A_68,B_69] :
      ( k1_tarski(A_68) = B_69
      | ~ v1_zfmisc_1(B_69)
      | v1_xboole_0(B_69)
      | v1_xboole_0(k1_tarski(A_68))
      | ~ r2_hidden(A_68,B_69) ) ),
    inference(resolution,[status(thm)],[c_120,c_187])).

tff(c_235,plain,(
    ! [A_85,B_86] :
      ( k1_tarski(A_85) = B_86
      | ~ v1_zfmisc_1(B_86)
      | v1_xboole_0(B_86)
      | ~ r2_hidden(A_85,B_86) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_193])).

tff(c_240,plain,(
    ! [A_87] :
      ( k1_tarski('#skF_1'(A_87)) = A_87
      | ~ v1_zfmisc_1(A_87)
      | v1_xboole_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_4,c_235])).

tff(c_257,plain,(
    ! [A_88,B_89] :
      ( r1_tarski(A_88,B_89)
      | ~ r2_hidden('#skF_1'(A_88),B_89)
      | ~ v1_zfmisc_1(A_88)
      | v1_xboole_0(A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_120])).

tff(c_261,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,A_1)
      | ~ v1_zfmisc_1(A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_257])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_594,plain,(
    ! [A_123,A_124] :
      ( ~ v2_struct_0('#skF_2'(A_123,A_124))
      | v1_xboole_0(A_124)
      | ~ l1_pre_topc(A_123)
      | v2_struct_0(A_123)
      | ~ r1_tarski(A_124,u1_struct_0(A_123)) ) ),
    inference(resolution,[status(thm)],[c_16,c_291])).

tff(c_912,plain,(
    ! [A_144] :
      ( ~ v2_struct_0('#skF_2'(A_144,u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144)
      | v2_struct_0(A_144)
      | ~ v1_zfmisc_1(u1_struct_0(A_144))
      | v1_xboole_0(u1_struct_0(A_144)) ) ),
    inference(resolution,[status(thm)],[c_261,c_594])).

tff(c_924,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5'))
    | ~ l1_pre_topc('#skF_2'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | ~ v1_zfmisc_1(u1_struct_0('#skF_2'('#skF_4','#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_2'('#skF_4','#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_912])).

tff(c_926,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5'))
    | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_77,c_480,c_374,c_924])).

tff(c_927,plain,(
    ~ v2_struct_0('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_315,c_926])).

tff(c_628,plain,(
    ! [A_126,A_127] :
      ( u1_struct_0('#skF_2'(A_126,A_127)) = A_127
      | v1_xboole_0(A_127)
      | ~ l1_pre_topc(A_126)
      | v2_struct_0(A_126)
      | ~ r1_tarski(A_127,u1_struct_0(A_126)) ) ),
    inference(resolution,[status(thm)],[c_16,c_451])).

tff(c_1115,plain,(
    ! [A_160] :
      ( u1_struct_0('#skF_2'(A_160,u1_struct_0(A_160))) = u1_struct_0(A_160)
      | ~ l1_pre_topc(A_160)
      | v2_struct_0(A_160)
      | ~ v1_zfmisc_1(u1_struct_0(A_160))
      | v1_xboole_0(u1_struct_0(A_160)) ) ),
    inference(resolution,[status(thm)],[c_261,c_628])).

tff(c_1215,plain,
    ( u1_struct_0('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5')) = u1_struct_0('#skF_2'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_2'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | ~ v1_zfmisc_1(u1_struct_0('#skF_2'('#skF_4','#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_2'('#skF_4','#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_1115])).

tff(c_1231,plain,
    ( u1_struct_0('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5')) = '#skF_5'
    | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_77,c_480,c_374,c_480,c_1215])).

tff(c_1232,plain,(
    u1_struct_0('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_315,c_1231])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k1_tarski(A_6),k1_zfmisc_1(B_7))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_316,plain,(
    ! [A_95,B_96] :
      ( m1_subset_1(A_95,k1_zfmisc_1(B_96))
      | ~ r2_hidden('#skF_1'(A_95),B_96)
      | ~ v1_zfmisc_1(A_95)
      | v1_xboole_0(A_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_8])).

tff(c_320,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,k1_zfmisc_1(A_1))
      | ~ v1_zfmisc_1(A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_316])).

tff(c_951,plain,(
    ! [A_147] :
      ( m1_pre_topc('#skF_2'(A_147,u1_struct_0(A_147)),A_147)
      | ~ l1_pre_topc(A_147)
      | v2_struct_0(A_147)
      | ~ v1_zfmisc_1(u1_struct_0(A_147))
      | v1_xboole_0(u1_struct_0(A_147)) ) ),
    inference(resolution,[status(thm)],[c_320,c_344])).

tff(c_969,plain,
    ( m1_pre_topc('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5'),'#skF_2'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_2'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | ~ v1_zfmisc_1(u1_struct_0('#skF_2'('#skF_4','#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_2'('#skF_4','#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_951])).

tff(c_973,plain,
    ( m1_pre_topc('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5'),'#skF_2'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_77,c_480,c_374,c_969])).

tff(c_974,plain,(
    m1_pre_topc('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5'),'#skF_2'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_315,c_973])).

tff(c_2988,plain,(
    ! [B_188] :
      ( m1_subset_1('#skF_1'(u1_struct_0(B_188)),'#skF_5')
      | ~ m1_pre_topc(B_188,'#skF_2'('#skF_4','#skF_5'))
      | v2_struct_0(B_188)
      | ~ l1_pre_topc('#skF_2'('#skF_4','#skF_5'))
      | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
      | v1_xboole_0(u1_struct_0(B_188)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_2893])).

tff(c_3024,plain,(
    ! [B_188] :
      ( m1_subset_1('#skF_1'(u1_struct_0(B_188)),'#skF_5')
      | ~ m1_pre_topc(B_188,'#skF_2'('#skF_4','#skF_5'))
      | v2_struct_0(B_188)
      | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
      | v1_xboole_0(u1_struct_0(B_188)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_2988])).

tff(c_3106,plain,(
    ! [B_193] :
      ( m1_subset_1('#skF_1'(u1_struct_0(B_193)),'#skF_5')
      | ~ m1_pre_topc(B_193,'#skF_2'('#skF_4','#skF_5'))
      | v2_struct_0(B_193)
      | v1_xboole_0(u1_struct_0(B_193)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_3024])).

tff(c_3139,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),'#skF_5')
    | ~ m1_pre_topc('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5'),'#skF_2'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1232,c_3106])).

tff(c_3169,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),'#skF_5')
    | v2_struct_0('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1232,c_974,c_3139])).

tff(c_3170,plain,(
    m1_subset_1('#skF_1'('#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_927,c_3169])).

tff(c_239,plain,(
    ! [A_1] :
      ( k1_tarski('#skF_1'(A_1)) = A_1
      | ~ v1_zfmisc_1(A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_235])).

tff(c_459,plain,(
    ! [A_113,A_6] :
      ( u1_struct_0('#skF_2'(A_113,k1_tarski(A_6))) = k1_tarski(A_6)
      | v1_xboole_0(k1_tarski(A_6))
      | ~ l1_pre_topc(A_113)
      | v2_struct_0(A_113)
      | ~ r2_hidden(A_6,u1_struct_0(A_113)) ) ),
    inference(resolution,[status(thm)],[c_8,c_451])).

tff(c_717,plain,(
    ! [A_132,A_133] :
      ( u1_struct_0('#skF_2'(A_132,k1_tarski(A_133))) = k1_tarski(A_133)
      | ~ l1_pre_topc(A_132)
      | v2_struct_0(A_132)
      | ~ r2_hidden(A_133,u1_struct_0(A_132)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_459])).

tff(c_5356,plain,(
    ! [A_258,A_259] :
      ( u1_struct_0('#skF_2'(A_258,A_259)) = k1_tarski('#skF_1'(A_259))
      | ~ l1_pre_topc(A_258)
      | v2_struct_0(A_258)
      | ~ r2_hidden('#skF_1'(A_259),u1_struct_0(A_258))
      | ~ v1_zfmisc_1(A_259)
      | v1_xboole_0(A_259) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_717])).

tff(c_5413,plain,(
    ! [A_259] :
      ( u1_struct_0('#skF_2'('#skF_2'('#skF_4','#skF_5'),A_259)) = k1_tarski('#skF_1'(A_259))
      | ~ l1_pre_topc('#skF_2'('#skF_4','#skF_5'))
      | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
      | ~ r2_hidden('#skF_1'(A_259),'#skF_5')
      | ~ v1_zfmisc_1(A_259)
      | v1_xboole_0(A_259) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_5356])).

tff(c_5440,plain,(
    ! [A_259] :
      ( u1_struct_0('#skF_2'('#skF_2'('#skF_4','#skF_5'),A_259)) = k1_tarski('#skF_1'(A_259))
      | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
      | ~ r2_hidden('#skF_1'(A_259),'#skF_5')
      | ~ v1_zfmisc_1(A_259)
      | v1_xboole_0(A_259) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_5413])).

tff(c_5443,plain,(
    ! [A_260] :
      ( u1_struct_0('#skF_2'('#skF_2'('#skF_4','#skF_5'),A_260)) = k1_tarski('#skF_1'(A_260))
      | ~ r2_hidden('#skF_1'(A_260),'#skF_5')
      | ~ v1_zfmisc_1(A_260)
      | v1_xboole_0(A_260) ) ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_5440])).

tff(c_653,plain,(
    ! [A_126] :
      ( u1_struct_0('#skF_2'(A_126,u1_struct_0(A_126))) = u1_struct_0(A_126)
      | ~ l1_pre_topc(A_126)
      | v2_struct_0(A_126)
      | ~ v1_zfmisc_1(u1_struct_0(A_126))
      | v1_xboole_0(u1_struct_0(A_126)) ) ),
    inference(resolution,[status(thm)],[c_261,c_628])).

tff(c_5519,plain,
    ( k1_tarski('#skF_1'(u1_struct_0('#skF_2'('#skF_4','#skF_5')))) = u1_struct_0('#skF_2'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_2'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | ~ v1_zfmisc_1(u1_struct_0('#skF_2'('#skF_4','#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_2'('#skF_4','#skF_5')))
    | ~ r2_hidden('#skF_1'(u1_struct_0('#skF_2'('#skF_4','#skF_5'))),'#skF_5')
    | ~ v1_zfmisc_1(u1_struct_0('#skF_2'('#skF_4','#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_2'('#skF_4','#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_5443,c_653])).

tff(c_5615,plain,
    ( k1_tarski('#skF_1'('#skF_5')) = '#skF_5'
    | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | ~ r2_hidden('#skF_1'('#skF_5'),'#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_77,c_480,c_480,c_480,c_77,c_480,c_374,c_480,c_480,c_5519])).

tff(c_5616,plain,
    ( k1_tarski('#skF_1'('#skF_5')) = '#skF_5'
    | ~ r2_hidden('#skF_1'('#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_315,c_5615])).

tff(c_5630,plain,(
    ~ r2_hidden('#skF_1'('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_5616])).

tff(c_5633,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_5630])).

tff(c_5637,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_5633])).

tff(c_5638,plain,(
    k1_tarski('#skF_1'('#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_5616])).

tff(c_122,plain,(
    ! [B_72,A_73] :
      ( v1_xboole_0(B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_73))
      | ~ v1_xboole_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_135,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_122])).

tff(c_142,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_135])).

tff(c_711,plain,(
    ! [C_129,A_130] :
      ( m1_subset_1(C_129,u1_struct_0(A_130))
      | ~ m1_subset_1(C_129,'#skF_5')
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_130)
      | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_130)
      | v2_struct_0(A_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_705])).

tff(c_928,plain,(
    ! [C_145,A_146] :
      ( m1_subset_1(C_145,u1_struct_0(A_146))
      | ~ m1_subset_1(C_145,'#skF_5')
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_146)
      | ~ l1_pre_topc(A_146)
      | v2_struct_0(A_146) ) ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_711])).

tff(c_26,plain,(
    ! [A_27,B_28] :
      ( k6_domain_1(A_27,B_28) = k1_tarski(B_28)
      | ~ m1_subset_1(B_28,A_27)
      | v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_8451,plain,(
    ! [A_296,C_297] :
      ( k6_domain_1(u1_struct_0(A_296),C_297) = k1_tarski(C_297)
      | v1_xboole_0(u1_struct_0(A_296))
      | ~ m1_subset_1(C_297,'#skF_5')
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_296)
      | ~ l1_pre_topc(A_296)
      | v2_struct_0(A_296) ) ),
    inference(resolution,[status(thm)],[c_928,c_26])).

tff(c_8453,plain,(
    ! [C_297] :
      ( k6_domain_1(u1_struct_0('#skF_4'),C_297) = k1_tarski(C_297)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_297,'#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_368,c_8451])).

tff(c_8456,plain,(
    ! [C_297] :
      ( k6_domain_1(u1_struct_0('#skF_4'),C_297) = k1_tarski(C_297)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_297,'#skF_5')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_8453])).

tff(c_8458,plain,(
    ! [C_298] :
      ( k6_domain_1(u1_struct_0('#skF_4'),C_298) = k1_tarski(C_298)
      | ~ m1_subset_1(C_298,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_142,c_8456])).

tff(c_54,plain,(
    ! [A_48,B_50] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_48),B_50),A_48)
      | ~ m1_subset_1(B_50,u1_struct_0(A_48))
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_8468,plain,(
    ! [C_298] :
      ( v2_tex_2(k1_tarski(C_298),'#skF_4')
      | ~ m1_subset_1(C_298,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_298,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8458,c_54])).

tff(c_8489,plain,(
    ! [C_298] :
      ( v2_tex_2(k1_tarski(C_298),'#skF_4')
      | ~ m1_subset_1(C_298,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_298,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_8468])).

tff(c_8499,plain,(
    ! [C_299] :
      ( v2_tex_2(k1_tarski(C_299),'#skF_4')
      | ~ m1_subset_1(C_299,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_299,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_8489])).

tff(c_8502,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5638,c_8499])).

tff(c_8513,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3170,c_8502])).

tff(c_8514,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_8513])).

tff(c_8520,plain,
    ( ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_3022,c_8514])).

tff(c_8530,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_368,c_8520])).

tff(c_8532,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_8530])).

tff(c_8533,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_10276,plain,(
    ! [A_450,B_451] :
      ( ~ v2_struct_0('#skF_3'(A_450,B_451))
      | ~ v2_tex_2(B_451,A_450)
      | ~ m1_subset_1(B_451,k1_zfmisc_1(u1_struct_0(A_450)))
      | v1_xboole_0(B_451)
      | ~ l1_pre_topc(A_450)
      | ~ v2_pre_topc(A_450)
      | v2_struct_0(A_450) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_10310,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_10276])).

tff(c_10322,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_8533,c_10310])).

tff(c_10323,plain,(
    ~ v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_10322])).

tff(c_8534,plain,(
    ~ v1_zfmisc_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_10548,plain,(
    ! [A_464,B_465] :
      ( u1_struct_0('#skF_3'(A_464,B_465)) = B_465
      | ~ v2_tex_2(B_465,A_464)
      | ~ m1_subset_1(B_465,k1_zfmisc_1(u1_struct_0(A_464)))
      | v1_xboole_0(B_465)
      | ~ l1_pre_topc(A_464)
      | ~ v2_pre_topc(A_464)
      | v2_struct_0(A_464) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_10586,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_10548])).

tff(c_10599,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_8533,c_10586])).

tff(c_10600,plain,(
    u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_10599])).

tff(c_22,plain,(
    ! [A_19] :
      ( v1_zfmisc_1(u1_struct_0(A_19))
      | ~ l1_struct_0(A_19)
      | ~ v7_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10699,plain,
    ( v1_zfmisc_1('#skF_5')
    | ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10600,c_22])).

tff(c_10745,plain,
    ( ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_8534,c_10699])).

tff(c_10747,plain,(
    ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_10745])).

tff(c_62,plain,(
    v2_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_9856,plain,(
    ! [A_427,B_428] :
      ( v1_tdlat_3('#skF_3'(A_427,B_428))
      | ~ v2_tex_2(B_428,A_427)
      | ~ m1_subset_1(B_428,k1_zfmisc_1(u1_struct_0(A_427)))
      | v1_xboole_0(B_428)
      | ~ l1_pre_topc(A_427)
      | ~ v2_pre_topc(A_427)
      | v2_struct_0(A_427) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_9890,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_9856])).

tff(c_9902,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_8533,c_9890])).

tff(c_9903,plain,(
    v1_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_9902])).

tff(c_10780,plain,(
    ! [A_467,B_468] :
      ( m1_pre_topc('#skF_3'(A_467,B_468),A_467)
      | ~ v2_tex_2(B_468,A_467)
      | ~ m1_subset_1(B_468,k1_zfmisc_1(u1_struct_0(A_467)))
      | v1_xboole_0(B_468)
      | ~ l1_pre_topc(A_467)
      | ~ v2_pre_topc(A_467)
      | v2_struct_0(A_467) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_10809,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_10780])).

tff(c_10823,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_8533,c_10809])).

tff(c_10824,plain,(
    m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_10823])).

tff(c_30,plain,(
    ! [B_32,A_30] :
      ( ~ v1_tdlat_3(B_32)
      | v7_struct_0(B_32)
      | v2_struct_0(B_32)
      | ~ m1_pre_topc(B_32,A_30)
      | ~ l1_pre_topc(A_30)
      | ~ v2_tdlat_3(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_10827,plain,
    ( ~ v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v7_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_10824,c_30])).

tff(c_10833,plain,
    ( v7_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_9903,c_10827])).

tff(c_10835,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_10323,c_10747,c_10833])).

tff(c_10836,plain,(
    ~ l1_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_10745])).

tff(c_10841,plain,(
    ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_18,c_10836])).

tff(c_10873,plain,(
    ! [A_470,B_471] :
      ( m1_pre_topc('#skF_3'(A_470,B_471),A_470)
      | ~ v2_tex_2(B_471,A_470)
      | ~ m1_subset_1(B_471,k1_zfmisc_1(u1_struct_0(A_470)))
      | v1_xboole_0(B_471)
      | ~ l1_pre_topc(A_470)
      | ~ v2_pre_topc(A_470)
      | v2_struct_0(A_470) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_10902,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_10873])).

tff(c_10916,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_8533,c_10902])).

tff(c_10917,plain,(
    m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_10916])).

tff(c_10923,plain,
    ( l1_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_10917,c_20])).

tff(c_10930,plain,(
    l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_10923])).

tff(c_10932,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10841,c_10930])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:54:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.40/3.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.49/3.75  
% 9.49/3.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.49/3.75  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 9.49/3.75  
% 9.49/3.75  %Foreground sorts:
% 9.49/3.75  
% 9.49/3.75  
% 9.49/3.75  %Background operators:
% 9.49/3.75  
% 9.49/3.75  
% 9.49/3.75  %Foreground operators:
% 9.49/3.75  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.49/3.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.49/3.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.49/3.75  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.49/3.75  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.49/3.75  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 9.49/3.75  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.49/3.75  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 9.49/3.75  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.49/3.75  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 9.49/3.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.49/3.75  tff('#skF_5', type, '#skF_5': $i).
% 9.49/3.75  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 9.49/3.75  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 9.49/3.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.49/3.75  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 9.49/3.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.49/3.75  tff('#skF_4', type, '#skF_4': $i).
% 9.49/3.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.49/3.75  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.49/3.75  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 9.49/3.75  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 9.49/3.75  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.49/3.75  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.49/3.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.49/3.75  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 9.49/3.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.49/3.75  
% 9.63/3.78  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 9.63/3.78  tff(f_218, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 9.63/3.78  tff(f_144, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (?[C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) & (B = u1_struct_0(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_tsep_1)).
% 9.63/3.78  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.63/3.78  tff(f_49, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 9.63/3.78  tff(f_86, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 9.63/3.78  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 9.63/3.78  tff(f_34, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 9.63/3.78  tff(f_38, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 9.63/3.78  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.63/3.78  tff(f_157, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 9.63/3.78  tff(f_45, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 9.63/3.78  tff(f_93, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 9.63/3.78  tff(f_198, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 9.63/3.78  tff(f_186, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tex_2)).
% 9.63/3.78  tff(f_70, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 9.63/3.78  tff(f_123, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((~v2_struct_0(B) & ~v7_struct_0(B)) => (~v2_struct_0(B) & ~v1_tdlat_3(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc32_tex_2)).
% 9.63/3.78  tff(c_18, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.63/3.78  tff(c_66, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_218])).
% 9.63/3.78  tff(c_58, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_218])).
% 9.63/3.78  tff(c_64, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_218])).
% 9.63/3.78  tff(c_60, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_218])).
% 9.63/3.78  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_218])).
% 9.63/3.78  tff(c_344, plain, (![A_98, B_99]: (m1_pre_topc('#skF_2'(A_98, B_99), A_98) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_98))) | v1_xboole_0(B_99) | ~l1_pre_topc(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.63/3.78  tff(c_358, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_344])).
% 9.63/3.78  tff(c_367, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_358])).
% 9.63/3.78  tff(c_368, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_367])).
% 9.63/3.78  tff(c_291, plain, (![A_93, B_94]: (~v2_struct_0('#skF_2'(A_93, B_94)) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | v1_xboole_0(B_94) | ~l1_pre_topc(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.63/3.78  tff(c_306, plain, (~v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_291])).
% 9.63/3.78  tff(c_314, plain, (~v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_306])).
% 9.63/3.78  tff(c_315, plain, (~v2_struct_0('#skF_2'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_314])).
% 9.63/3.78  tff(c_451, plain, (![A_113, B_114]: (u1_struct_0('#skF_2'(A_113, B_114))=B_114 | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_113))) | v1_xboole_0(B_114) | ~l1_pre_topc(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.63/3.78  tff(c_470, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_451])).
% 9.63/3.78  tff(c_479, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_470])).
% 9.63/3.78  tff(c_480, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_479])).
% 9.63/3.78  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.63/3.78  tff(c_93, plain, (![A_58, B_59]: (m1_subset_1(A_58, B_59) | ~r2_hidden(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.63/3.78  tff(c_97, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_93])).
% 9.63/3.78  tff(c_705, plain, (![C_129, A_130, B_131]: (m1_subset_1(C_129, u1_struct_0(A_130)) | ~m1_subset_1(C_129, u1_struct_0(B_131)) | ~m1_pre_topc(B_131, A_130) | v2_struct_0(B_131) | ~l1_pre_topc(A_130) | v2_struct_0(A_130))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.63/3.78  tff(c_2893, plain, (![B_188, A_189]: (m1_subset_1('#skF_1'(u1_struct_0(B_188)), u1_struct_0(A_189)) | ~m1_pre_topc(B_188, A_189) | v2_struct_0(B_188) | ~l1_pre_topc(A_189) | v2_struct_0(A_189) | v1_xboole_0(u1_struct_0(B_188)))), inference(resolution, [status(thm)], [c_97, c_705])).
% 9.63/3.78  tff(c_2985, plain, (![A_189]: (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0(A_189)) | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_189) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | ~l1_pre_topc(A_189) | v2_struct_0(A_189) | v1_xboole_0(u1_struct_0('#skF_2'('#skF_4', '#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_480, c_2893])).
% 9.63/3.78  tff(c_3021, plain, (![A_189]: (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0(A_189)) | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_189) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | ~l1_pre_topc(A_189) | v2_struct_0(A_189) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_480, c_2985])).
% 9.63/3.78  tff(c_3022, plain, (![A_189]: (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0(A_189)) | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_189) | ~l1_pre_topc(A_189) | v2_struct_0(A_189))), inference(negUnitSimplification, [status(thm)], [c_58, c_315, c_3021])).
% 9.63/3.78  tff(c_74, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_218])).
% 9.63/3.78  tff(c_77, plain, (v1_zfmisc_1('#skF_5')), inference(splitLeft, [status(thm)], [c_74])).
% 9.63/3.78  tff(c_68, plain, (~v1_zfmisc_1('#skF_5') | ~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_218])).
% 9.63/3.78  tff(c_80, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_68])).
% 9.63/3.78  tff(c_20, plain, (![B_18, A_16]: (l1_pre_topc(B_18) | ~m1_pre_topc(B_18, A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.63/3.78  tff(c_371, plain, (l1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_368, c_20])).
% 9.63/3.78  tff(c_374, plain, (l1_pre_topc('#skF_2'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_371])).
% 9.63/3.78  tff(c_6, plain, (![A_5]: (~v1_xboole_0(k1_tarski(A_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.63/3.78  tff(c_116, plain, (![A_68, B_69]: (m1_subset_1(k1_tarski(A_68), k1_zfmisc_1(B_69)) | ~r2_hidden(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.63/3.78  tff(c_14, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.63/3.78  tff(c_120, plain, (![A_68, B_69]: (r1_tarski(k1_tarski(A_68), B_69) | ~r2_hidden(A_68, B_69))), inference(resolution, [status(thm)], [c_116, c_14])).
% 9.63/3.78  tff(c_187, plain, (![B_81, A_82]: (B_81=A_82 | ~r1_tarski(A_82, B_81) | ~v1_zfmisc_1(B_81) | v1_xboole_0(B_81) | v1_xboole_0(A_82))), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.63/3.78  tff(c_193, plain, (![A_68, B_69]: (k1_tarski(A_68)=B_69 | ~v1_zfmisc_1(B_69) | v1_xboole_0(B_69) | v1_xboole_0(k1_tarski(A_68)) | ~r2_hidden(A_68, B_69))), inference(resolution, [status(thm)], [c_120, c_187])).
% 9.63/3.78  tff(c_235, plain, (![A_85, B_86]: (k1_tarski(A_85)=B_86 | ~v1_zfmisc_1(B_86) | v1_xboole_0(B_86) | ~r2_hidden(A_85, B_86))), inference(negUnitSimplification, [status(thm)], [c_6, c_193])).
% 9.63/3.78  tff(c_240, plain, (![A_87]: (k1_tarski('#skF_1'(A_87))=A_87 | ~v1_zfmisc_1(A_87) | v1_xboole_0(A_87))), inference(resolution, [status(thm)], [c_4, c_235])).
% 9.63/3.78  tff(c_257, plain, (![A_88, B_89]: (r1_tarski(A_88, B_89) | ~r2_hidden('#skF_1'(A_88), B_89) | ~v1_zfmisc_1(A_88) | v1_xboole_0(A_88))), inference(superposition, [status(thm), theory('equality')], [c_240, c_120])).
% 9.63/3.78  tff(c_261, plain, (![A_1]: (r1_tarski(A_1, A_1) | ~v1_zfmisc_1(A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_257])).
% 9.63/3.78  tff(c_16, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.63/3.78  tff(c_594, plain, (![A_123, A_124]: (~v2_struct_0('#skF_2'(A_123, A_124)) | v1_xboole_0(A_124) | ~l1_pre_topc(A_123) | v2_struct_0(A_123) | ~r1_tarski(A_124, u1_struct_0(A_123)))), inference(resolution, [status(thm)], [c_16, c_291])).
% 9.63/3.78  tff(c_912, plain, (![A_144]: (~v2_struct_0('#skF_2'(A_144, u1_struct_0(A_144))) | ~l1_pre_topc(A_144) | v2_struct_0(A_144) | ~v1_zfmisc_1(u1_struct_0(A_144)) | v1_xboole_0(u1_struct_0(A_144)))), inference(resolution, [status(thm)], [c_261, c_594])).
% 9.63/3.78  tff(c_924, plain, (~v2_struct_0('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5')) | ~l1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | ~v1_zfmisc_1(u1_struct_0('#skF_2'('#skF_4', '#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_2'('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_480, c_912])).
% 9.63/3.78  tff(c_926, plain, (~v2_struct_0('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5')) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_480, c_77, c_480, c_374, c_924])).
% 9.63/3.78  tff(c_927, plain, (~v2_struct_0('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_58, c_315, c_926])).
% 9.63/3.78  tff(c_628, plain, (![A_126, A_127]: (u1_struct_0('#skF_2'(A_126, A_127))=A_127 | v1_xboole_0(A_127) | ~l1_pre_topc(A_126) | v2_struct_0(A_126) | ~r1_tarski(A_127, u1_struct_0(A_126)))), inference(resolution, [status(thm)], [c_16, c_451])).
% 9.63/3.78  tff(c_1115, plain, (![A_160]: (u1_struct_0('#skF_2'(A_160, u1_struct_0(A_160)))=u1_struct_0(A_160) | ~l1_pre_topc(A_160) | v2_struct_0(A_160) | ~v1_zfmisc_1(u1_struct_0(A_160)) | v1_xboole_0(u1_struct_0(A_160)))), inference(resolution, [status(thm)], [c_261, c_628])).
% 9.63/3.78  tff(c_1215, plain, (u1_struct_0('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5'))=u1_struct_0('#skF_2'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | ~v1_zfmisc_1(u1_struct_0('#skF_2'('#skF_4', '#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_2'('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_480, c_1115])).
% 9.63/3.78  tff(c_1231, plain, (u1_struct_0('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5'))='#skF_5' | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_480, c_77, c_480, c_374, c_480, c_1215])).
% 9.63/3.78  tff(c_1232, plain, (u1_struct_0('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_58, c_315, c_1231])).
% 9.63/3.78  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(k1_tarski(A_6), k1_zfmisc_1(B_7)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.63/3.78  tff(c_316, plain, (![A_95, B_96]: (m1_subset_1(A_95, k1_zfmisc_1(B_96)) | ~r2_hidden('#skF_1'(A_95), B_96) | ~v1_zfmisc_1(A_95) | v1_xboole_0(A_95))), inference(superposition, [status(thm), theory('equality')], [c_240, c_8])).
% 9.63/3.78  tff(c_320, plain, (![A_1]: (m1_subset_1(A_1, k1_zfmisc_1(A_1)) | ~v1_zfmisc_1(A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_316])).
% 9.63/3.78  tff(c_951, plain, (![A_147]: (m1_pre_topc('#skF_2'(A_147, u1_struct_0(A_147)), A_147) | ~l1_pre_topc(A_147) | v2_struct_0(A_147) | ~v1_zfmisc_1(u1_struct_0(A_147)) | v1_xboole_0(u1_struct_0(A_147)))), inference(resolution, [status(thm)], [c_320, c_344])).
% 9.63/3.78  tff(c_969, plain, (m1_pre_topc('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5'), '#skF_2'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | ~v1_zfmisc_1(u1_struct_0('#skF_2'('#skF_4', '#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_2'('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_480, c_951])).
% 9.63/3.78  tff(c_973, plain, (m1_pre_topc('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5'), '#skF_2'('#skF_4', '#skF_5')) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_480, c_77, c_480, c_374, c_969])).
% 9.63/3.78  tff(c_974, plain, (m1_pre_topc('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5'), '#skF_2'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_58, c_315, c_973])).
% 9.63/3.78  tff(c_2988, plain, (![B_188]: (m1_subset_1('#skF_1'(u1_struct_0(B_188)), '#skF_5') | ~m1_pre_topc(B_188, '#skF_2'('#skF_4', '#skF_5')) | v2_struct_0(B_188) | ~l1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0(u1_struct_0(B_188)))), inference(superposition, [status(thm), theory('equality')], [c_480, c_2893])).
% 9.63/3.78  tff(c_3024, plain, (![B_188]: (m1_subset_1('#skF_1'(u1_struct_0(B_188)), '#skF_5') | ~m1_pre_topc(B_188, '#skF_2'('#skF_4', '#skF_5')) | v2_struct_0(B_188) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0(u1_struct_0(B_188)))), inference(demodulation, [status(thm), theory('equality')], [c_374, c_2988])).
% 9.63/3.78  tff(c_3106, plain, (![B_193]: (m1_subset_1('#skF_1'(u1_struct_0(B_193)), '#skF_5') | ~m1_pre_topc(B_193, '#skF_2'('#skF_4', '#skF_5')) | v2_struct_0(B_193) | v1_xboole_0(u1_struct_0(B_193)))), inference(negUnitSimplification, [status(thm)], [c_315, c_3024])).
% 9.63/3.78  tff(c_3139, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_5') | ~m1_pre_topc('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5'), '#skF_2'('#skF_4', '#skF_5')) | v2_struct_0('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1232, c_3106])).
% 9.63/3.78  tff(c_3169, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_5') | v2_struct_0('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1232, c_974, c_3139])).
% 9.63/3.78  tff(c_3170, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_58, c_927, c_3169])).
% 9.63/3.78  tff(c_239, plain, (![A_1]: (k1_tarski('#skF_1'(A_1))=A_1 | ~v1_zfmisc_1(A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_235])).
% 9.63/3.78  tff(c_459, plain, (![A_113, A_6]: (u1_struct_0('#skF_2'(A_113, k1_tarski(A_6)))=k1_tarski(A_6) | v1_xboole_0(k1_tarski(A_6)) | ~l1_pre_topc(A_113) | v2_struct_0(A_113) | ~r2_hidden(A_6, u1_struct_0(A_113)))), inference(resolution, [status(thm)], [c_8, c_451])).
% 9.63/3.78  tff(c_717, plain, (![A_132, A_133]: (u1_struct_0('#skF_2'(A_132, k1_tarski(A_133)))=k1_tarski(A_133) | ~l1_pre_topc(A_132) | v2_struct_0(A_132) | ~r2_hidden(A_133, u1_struct_0(A_132)))), inference(negUnitSimplification, [status(thm)], [c_6, c_459])).
% 9.63/3.78  tff(c_5356, plain, (![A_258, A_259]: (u1_struct_0('#skF_2'(A_258, A_259))=k1_tarski('#skF_1'(A_259)) | ~l1_pre_topc(A_258) | v2_struct_0(A_258) | ~r2_hidden('#skF_1'(A_259), u1_struct_0(A_258)) | ~v1_zfmisc_1(A_259) | v1_xboole_0(A_259))), inference(superposition, [status(thm), theory('equality')], [c_239, c_717])).
% 9.63/3.78  tff(c_5413, plain, (![A_259]: (u1_struct_0('#skF_2'('#skF_2'('#skF_4', '#skF_5'), A_259))=k1_tarski('#skF_1'(A_259)) | ~l1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | ~r2_hidden('#skF_1'(A_259), '#skF_5') | ~v1_zfmisc_1(A_259) | v1_xboole_0(A_259))), inference(superposition, [status(thm), theory('equality')], [c_480, c_5356])).
% 9.63/3.78  tff(c_5440, plain, (![A_259]: (u1_struct_0('#skF_2'('#skF_2'('#skF_4', '#skF_5'), A_259))=k1_tarski('#skF_1'(A_259)) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | ~r2_hidden('#skF_1'(A_259), '#skF_5') | ~v1_zfmisc_1(A_259) | v1_xboole_0(A_259))), inference(demodulation, [status(thm), theory('equality')], [c_374, c_5413])).
% 9.63/3.78  tff(c_5443, plain, (![A_260]: (u1_struct_0('#skF_2'('#skF_2'('#skF_4', '#skF_5'), A_260))=k1_tarski('#skF_1'(A_260)) | ~r2_hidden('#skF_1'(A_260), '#skF_5') | ~v1_zfmisc_1(A_260) | v1_xboole_0(A_260))), inference(negUnitSimplification, [status(thm)], [c_315, c_5440])).
% 9.63/3.78  tff(c_653, plain, (![A_126]: (u1_struct_0('#skF_2'(A_126, u1_struct_0(A_126)))=u1_struct_0(A_126) | ~l1_pre_topc(A_126) | v2_struct_0(A_126) | ~v1_zfmisc_1(u1_struct_0(A_126)) | v1_xboole_0(u1_struct_0(A_126)))), inference(resolution, [status(thm)], [c_261, c_628])).
% 9.63/3.78  tff(c_5519, plain, (k1_tarski('#skF_1'(u1_struct_0('#skF_2'('#skF_4', '#skF_5'))))=u1_struct_0('#skF_2'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | ~v1_zfmisc_1(u1_struct_0('#skF_2'('#skF_4', '#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_2'('#skF_4', '#skF_5'))) | ~r2_hidden('#skF_1'(u1_struct_0('#skF_2'('#skF_4', '#skF_5'))), '#skF_5') | ~v1_zfmisc_1(u1_struct_0('#skF_2'('#skF_4', '#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_2'('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_5443, c_653])).
% 9.63/3.78  tff(c_5615, plain, (k1_tarski('#skF_1'('#skF_5'))='#skF_5' | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | ~r2_hidden('#skF_1'('#skF_5'), '#skF_5') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_480, c_77, c_480, c_480, c_480, c_77, c_480, c_374, c_480, c_480, c_5519])).
% 9.63/3.78  tff(c_5616, plain, (k1_tarski('#skF_1'('#skF_5'))='#skF_5' | ~r2_hidden('#skF_1'('#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_58, c_315, c_5615])).
% 9.63/3.78  tff(c_5630, plain, (~r2_hidden('#skF_1'('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_5616])).
% 9.63/3.78  tff(c_5633, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_5630])).
% 9.63/3.78  tff(c_5637, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_5633])).
% 9.63/3.78  tff(c_5638, plain, (k1_tarski('#skF_1'('#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_5616])).
% 9.63/3.78  tff(c_122, plain, (![B_72, A_73]: (v1_xboole_0(B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(A_73)) | ~v1_xboole_0(A_73))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.63/3.78  tff(c_135, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_122])).
% 9.63/3.78  tff(c_142, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_135])).
% 9.63/3.78  tff(c_711, plain, (![C_129, A_130]: (m1_subset_1(C_129, u1_struct_0(A_130)) | ~m1_subset_1(C_129, '#skF_5') | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_130) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | ~l1_pre_topc(A_130) | v2_struct_0(A_130))), inference(superposition, [status(thm), theory('equality')], [c_480, c_705])).
% 9.63/3.78  tff(c_928, plain, (![C_145, A_146]: (m1_subset_1(C_145, u1_struct_0(A_146)) | ~m1_subset_1(C_145, '#skF_5') | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_146) | ~l1_pre_topc(A_146) | v2_struct_0(A_146))), inference(negUnitSimplification, [status(thm)], [c_315, c_711])).
% 9.63/3.78  tff(c_26, plain, (![A_27, B_28]: (k6_domain_1(A_27, B_28)=k1_tarski(B_28) | ~m1_subset_1(B_28, A_27) | v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.63/3.78  tff(c_8451, plain, (![A_296, C_297]: (k6_domain_1(u1_struct_0(A_296), C_297)=k1_tarski(C_297) | v1_xboole_0(u1_struct_0(A_296)) | ~m1_subset_1(C_297, '#skF_5') | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_296) | ~l1_pre_topc(A_296) | v2_struct_0(A_296))), inference(resolution, [status(thm)], [c_928, c_26])).
% 9.63/3.78  tff(c_8453, plain, (![C_297]: (k6_domain_1(u1_struct_0('#skF_4'), C_297)=k1_tarski(C_297) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(C_297, '#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_368, c_8451])).
% 9.63/3.78  tff(c_8456, plain, (![C_297]: (k6_domain_1(u1_struct_0('#skF_4'), C_297)=k1_tarski(C_297) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(C_297, '#skF_5') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_8453])).
% 9.63/3.78  tff(c_8458, plain, (![C_298]: (k6_domain_1(u1_struct_0('#skF_4'), C_298)=k1_tarski(C_298) | ~m1_subset_1(C_298, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_142, c_8456])).
% 9.63/3.78  tff(c_54, plain, (![A_48, B_50]: (v2_tex_2(k6_domain_1(u1_struct_0(A_48), B_50), A_48) | ~m1_subset_1(B_50, u1_struct_0(A_48)) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_198])).
% 9.63/3.78  tff(c_8468, plain, (![C_298]: (v2_tex_2(k1_tarski(C_298), '#skF_4') | ~m1_subset_1(C_298, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_subset_1(C_298, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8458, c_54])).
% 9.63/3.78  tff(c_8489, plain, (![C_298]: (v2_tex_2(k1_tarski(C_298), '#skF_4') | ~m1_subset_1(C_298, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | ~m1_subset_1(C_298, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_8468])).
% 9.63/3.78  tff(c_8499, plain, (![C_299]: (v2_tex_2(k1_tarski(C_299), '#skF_4') | ~m1_subset_1(C_299, u1_struct_0('#skF_4')) | ~m1_subset_1(C_299, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_8489])).
% 9.63/3.78  tff(c_8502, plain, (v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'('#skF_5'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5638, c_8499])).
% 9.63/3.78  tff(c_8513, plain, (v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3170, c_8502])).
% 9.63/3.78  tff(c_8514, plain, (~m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_80, c_8513])).
% 9.63/3.78  tff(c_8520, plain, (~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_3022, c_8514])).
% 9.63/3.78  tff(c_8530, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_368, c_8520])).
% 9.63/3.78  tff(c_8532, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_8530])).
% 9.63/3.78  tff(c_8533, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_74])).
% 9.63/3.78  tff(c_10276, plain, (![A_450, B_451]: (~v2_struct_0('#skF_3'(A_450, B_451)) | ~v2_tex_2(B_451, A_450) | ~m1_subset_1(B_451, k1_zfmisc_1(u1_struct_0(A_450))) | v1_xboole_0(B_451) | ~l1_pre_topc(A_450) | ~v2_pre_topc(A_450) | v2_struct_0(A_450))), inference(cnfTransformation, [status(thm)], [f_186])).
% 9.63/3.78  tff(c_10310, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_10276])).
% 9.63/3.78  tff(c_10322, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_8533, c_10310])).
% 9.63/3.78  tff(c_10323, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_10322])).
% 9.63/3.78  tff(c_8534, plain, (~v1_zfmisc_1('#skF_5')), inference(splitRight, [status(thm)], [c_74])).
% 9.63/3.78  tff(c_10548, plain, (![A_464, B_465]: (u1_struct_0('#skF_3'(A_464, B_465))=B_465 | ~v2_tex_2(B_465, A_464) | ~m1_subset_1(B_465, k1_zfmisc_1(u1_struct_0(A_464))) | v1_xboole_0(B_465) | ~l1_pre_topc(A_464) | ~v2_pre_topc(A_464) | v2_struct_0(A_464))), inference(cnfTransformation, [status(thm)], [f_186])).
% 9.63/3.78  tff(c_10586, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_10548])).
% 9.63/3.78  tff(c_10599, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_8533, c_10586])).
% 9.63/3.78  tff(c_10600, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_10599])).
% 9.63/3.78  tff(c_22, plain, (![A_19]: (v1_zfmisc_1(u1_struct_0(A_19)) | ~l1_struct_0(A_19) | ~v7_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.63/3.78  tff(c_10699, plain, (v1_zfmisc_1('#skF_5') | ~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_10600, c_22])).
% 9.63/3.78  tff(c_10745, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_8534, c_10699])).
% 9.63/3.78  tff(c_10747, plain, (~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_10745])).
% 9.63/3.78  tff(c_62, plain, (v2_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_218])).
% 9.63/3.78  tff(c_9856, plain, (![A_427, B_428]: (v1_tdlat_3('#skF_3'(A_427, B_428)) | ~v2_tex_2(B_428, A_427) | ~m1_subset_1(B_428, k1_zfmisc_1(u1_struct_0(A_427))) | v1_xboole_0(B_428) | ~l1_pre_topc(A_427) | ~v2_pre_topc(A_427) | v2_struct_0(A_427))), inference(cnfTransformation, [status(thm)], [f_186])).
% 9.63/3.78  tff(c_9890, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_9856])).
% 9.63/3.78  tff(c_9902, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_8533, c_9890])).
% 9.63/3.78  tff(c_9903, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_9902])).
% 9.63/3.78  tff(c_10780, plain, (![A_467, B_468]: (m1_pre_topc('#skF_3'(A_467, B_468), A_467) | ~v2_tex_2(B_468, A_467) | ~m1_subset_1(B_468, k1_zfmisc_1(u1_struct_0(A_467))) | v1_xboole_0(B_468) | ~l1_pre_topc(A_467) | ~v2_pre_topc(A_467) | v2_struct_0(A_467))), inference(cnfTransformation, [status(thm)], [f_186])).
% 9.63/3.78  tff(c_10809, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_10780])).
% 9.63/3.78  tff(c_10823, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_8533, c_10809])).
% 9.63/3.78  tff(c_10824, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_10823])).
% 9.63/3.78  tff(c_30, plain, (![B_32, A_30]: (~v1_tdlat_3(B_32) | v7_struct_0(B_32) | v2_struct_0(B_32) | ~m1_pre_topc(B_32, A_30) | ~l1_pre_topc(A_30) | ~v2_tdlat_3(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_123])).
% 9.63/3.78  tff(c_10827, plain, (~v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v7_struct_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_10824, c_30])).
% 9.63/3.78  tff(c_10833, plain, (v7_struct_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_9903, c_10827])).
% 9.63/3.78  tff(c_10835, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_10323, c_10747, c_10833])).
% 9.63/3.78  tff(c_10836, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_10745])).
% 9.63/3.78  tff(c_10841, plain, (~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_18, c_10836])).
% 9.63/3.78  tff(c_10873, plain, (![A_470, B_471]: (m1_pre_topc('#skF_3'(A_470, B_471), A_470) | ~v2_tex_2(B_471, A_470) | ~m1_subset_1(B_471, k1_zfmisc_1(u1_struct_0(A_470))) | v1_xboole_0(B_471) | ~l1_pre_topc(A_470) | ~v2_pre_topc(A_470) | v2_struct_0(A_470))), inference(cnfTransformation, [status(thm)], [f_186])).
% 9.63/3.78  tff(c_10902, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_10873])).
% 9.63/3.78  tff(c_10916, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_8533, c_10902])).
% 9.63/3.78  tff(c_10917, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_10916])).
% 9.63/3.78  tff(c_10923, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_10917, c_20])).
% 9.63/3.78  tff(c_10930, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_10923])).
% 9.63/3.78  tff(c_10932, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10841, c_10930])).
% 9.63/3.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.63/3.78  
% 9.63/3.78  Inference rules
% 9.63/3.78  ----------------------
% 9.63/3.78  #Ref     : 0
% 9.63/3.78  #Sup     : 2539
% 9.63/3.78  #Fact    : 0
% 9.63/3.78  #Define  : 0
% 9.63/3.78  #Split   : 25
% 9.63/3.78  #Chain   : 0
% 9.63/3.78  #Close   : 0
% 9.63/3.78  
% 9.63/3.78  Ordering : KBO
% 9.63/3.78  
% 9.63/3.78  Simplification rules
% 9.63/3.78  ----------------------
% 9.63/3.78  #Subsume      : 219
% 9.63/3.78  #Demod        : 2031
% 9.63/3.78  #Tautology    : 455
% 9.63/3.78  #SimpNegUnit  : 848
% 9.63/3.78  #BackRed      : 2
% 9.63/3.78  
% 9.63/3.78  #Partial instantiations: 0
% 9.63/3.78  #Strategies tried      : 1
% 9.63/3.78  
% 9.63/3.78  Timing (in seconds)
% 9.63/3.78  ----------------------
% 9.63/3.78  Preprocessing        : 0.52
% 9.63/3.78  Parsing              : 0.28
% 9.63/3.78  CNF conversion       : 0.04
% 9.63/3.78  Main loop            : 2.36
% 9.63/3.78  Inferencing          : 0.63
% 9.63/3.78  Reduction            : 0.80
% 9.63/3.78  Demodulation         : 0.52
% 9.63/3.79  BG Simplification    : 0.09
% 9.63/3.79  Subsumption          : 0.70
% 9.63/3.79  Abstraction          : 0.11
% 9.63/3.79  MUC search           : 0.00
% 9.63/3.79  Cooper               : 0.00
% 9.63/3.79  Total                : 2.94
% 9.63/3.79  Index Insertion      : 0.00
% 9.63/3.79  Index Deletion       : 0.00
% 9.63/3.79  Index Matching       : 0.00
% 9.63/3.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
