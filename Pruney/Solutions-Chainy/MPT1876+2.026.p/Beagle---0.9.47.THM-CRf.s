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
% DateTime   : Thu Dec  3 10:29:54 EST 2020

% Result     : Theorem 9.33s
% Output     : CNFRefutation 9.33s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 918 expanded)
%              Number of leaves         :   42 ( 341 expanded)
%              Depth                    :   26
%              Number of atoms          :  566 (3596 expanded)
%              Number of equality atoms :   41 ( 183 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).

tff(f_31,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_75,axiom,(
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

tff(f_28,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_153,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_194,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc32_tex_2)).

tff(c_12,plain,(
    ! [A_9] :
      ( l1_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_60,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_56,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_739,plain,(
    ! [A_109,B_110] :
      ( m1_pre_topc('#skF_2'(A_109,B_110),A_109)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | v1_xboole_0(B_110)
      | ~ l1_pre_topc(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_757,plain,
    ( m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_739])).

tff(c_772,plain,
    ( m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_757])).

tff(c_773,plain,(
    m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_54,c_772])).

tff(c_229,plain,(
    ! [A_76,B_77] :
      ( ~ v2_struct_0('#skF_2'(A_76,B_77))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | v1_xboole_0(B_77)
      | ~ l1_pre_topc(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_244,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_229])).

tff(c_256,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_244])).

tff(c_257,plain,(
    ~ v2_struct_0('#skF_2'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_54,c_256])).

tff(c_369,plain,(
    ! [A_86,B_87] :
      ( u1_struct_0('#skF_2'(A_86,B_87)) = B_87
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | v1_xboole_0(B_87)
      | ~ l1_pre_topc(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_388,plain,
    ( u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_369])).

tff(c_401,plain,
    ( u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_388])).

tff(c_402,plain,(
    u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_54,c_401])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1('#skF_1'(A_2),A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1069,plain,(
    ! [C_128,A_129,B_130] :
      ( m1_subset_1(C_128,u1_struct_0(A_129))
      | ~ m1_subset_1(C_128,u1_struct_0(B_130))
      | ~ m1_pre_topc(B_130,A_129)
      | v2_struct_0(B_130)
      | ~ l1_pre_topc(A_129)
      | v2_struct_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1122,plain,(
    ! [B_134,A_135] :
      ( m1_subset_1('#skF_1'(u1_struct_0(B_134)),u1_struct_0(A_135))
      | ~ m1_pre_topc(B_134,A_135)
      | v2_struct_0(B_134)
      | ~ l1_pre_topc(A_135)
      | v2_struct_0(A_135) ) ),
    inference(resolution,[status(thm)],[c_4,c_1069])).

tff(c_1136,plain,(
    ! [A_135] :
      ( m1_subset_1('#skF_1'('#skF_5'),u1_struct_0(A_135))
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_135)
      | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_135)
      | v2_struct_0(A_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_1122])).

tff(c_1142,plain,(
    ! [A_135] :
      ( m1_subset_1('#skF_1'('#skF_5'),u1_struct_0(A_135))
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_135)
      | ~ l1_pre_topc(A_135)
      | v2_struct_0(A_135) ) ),
    inference(negUnitSimplification,[status(thm)],[c_257,c_1136])).

tff(c_70,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_74,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_64,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_76,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_64])).

tff(c_2,plain,(
    ! [A_1] : ~ v1_xboole_0(k1_tarski(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_129,plain,(
    ! [A_65,B_66] :
      ( k6_domain_1(A_65,B_66) = k1_tarski(B_66)
      | ~ m1_subset_1(B_66,A_65)
      | v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_141,plain,(
    ! [A_2] :
      ( k6_domain_1(A_2,'#skF_1'(A_2)) = k1_tarski('#skF_1'(A_2))
      | v1_xboole_0(A_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_129])).

tff(c_151,plain,(
    ! [A_68,B_69] :
      ( m1_subset_1(k6_domain_1(A_68,B_69),k1_zfmisc_1(A_68))
      | ~ m1_subset_1(B_69,A_68)
      | v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_163,plain,(
    ! [A_2] :
      ( m1_subset_1(k1_tarski('#skF_1'(A_2)),k1_zfmisc_1(A_2))
      | ~ m1_subset_1('#skF_1'(A_2),A_2)
      | v1_xboole_0(A_2)
      | v1_xboole_0(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_151])).

tff(c_169,plain,(
    ! [A_70] :
      ( m1_subset_1(k1_tarski('#skF_1'(A_70)),k1_zfmisc_1(A_70))
      | v1_xboole_0(A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_163])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_183,plain,(
    ! [A_70] :
      ( r1_tarski(k1_tarski('#skF_1'(A_70)),A_70)
      | v1_xboole_0(A_70) ) ),
    inference(resolution,[status(thm)],[c_169,c_8])).

tff(c_202,plain,(
    ! [B_74,A_75] :
      ( B_74 = A_75
      | ~ r1_tarski(A_75,B_74)
      | ~ v1_zfmisc_1(B_74)
      | v1_xboole_0(B_74)
      | v1_xboole_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_208,plain,(
    ! [A_70] :
      ( k1_tarski('#skF_1'(A_70)) = A_70
      | ~ v1_zfmisc_1(A_70)
      | v1_xboole_0(k1_tarski('#skF_1'(A_70)))
      | v1_xboole_0(A_70) ) ),
    inference(resolution,[status(thm)],[c_183,c_202])).

tff(c_218,plain,(
    ! [A_70] :
      ( k1_tarski('#skF_1'(A_70)) = A_70
      | ~ v1_zfmisc_1(A_70)
      | v1_xboole_0(A_70) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2,c_208])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_276,plain,(
    ! [A_79,B_80] :
      ( v1_pre_topc('#skF_2'(A_79,B_80))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | v1_xboole_0(B_80)
      | ~ l1_pre_topc(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_448,plain,(
    ! [A_89,A_90] :
      ( v1_pre_topc('#skF_2'(A_89,A_90))
      | v1_xboole_0(A_90)
      | ~ l1_pre_topc(A_89)
      | v2_struct_0(A_89)
      | ~ r1_tarski(A_90,u1_struct_0(A_89)) ) ),
    inference(resolution,[status(thm)],[c_10,c_276])).

tff(c_451,plain,(
    ! [A_90] :
      ( v1_pre_topc('#skF_2'('#skF_2'('#skF_4','#skF_5'),A_90))
      | v1_xboole_0(A_90)
      | ~ l1_pre_topc('#skF_2'('#skF_4','#skF_5'))
      | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
      | ~ r1_tarski(A_90,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_448])).

tff(c_471,plain,(
    ! [A_90] :
      ( v1_pre_topc('#skF_2'('#skF_2'('#skF_4','#skF_5'),A_90))
      | v1_xboole_0(A_90)
      | ~ l1_pre_topc('#skF_2'('#skF_4','#skF_5'))
      | ~ r1_tarski(A_90,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_257,c_451])).

tff(c_482,plain,(
    ~ l1_pre_topc('#skF_2'('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_471])).

tff(c_535,plain,(
    ! [A_95,B_96] :
      ( m1_pre_topc('#skF_2'(A_95,B_96),A_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | v1_xboole_0(B_96)
      | ~ l1_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_551,plain,
    ( m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_535])).

tff(c_564,plain,
    ( m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_551])).

tff(c_565,plain,(
    m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_54,c_564])).

tff(c_14,plain,(
    ! [B_12,A_10] :
      ( l1_pre_topc(B_12)
      | ~ m1_pre_topc(B_12,A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_569,plain,
    ( l1_pre_topc('#skF_2'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_565,c_14])).

tff(c_572,plain,(
    l1_pre_topc('#skF_2'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_569])).

tff(c_574,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_482,c_572])).

tff(c_576,plain,(
    l1_pre_topc('#skF_2'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_471])).

tff(c_168,plain,(
    ! [A_2] :
      ( m1_subset_1(k1_tarski('#skF_1'(A_2)),k1_zfmisc_1(A_2))
      | v1_xboole_0(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_163])).

tff(c_233,plain,(
    ! [A_76] :
      ( ~ v2_struct_0('#skF_2'(A_76,k1_tarski('#skF_1'(u1_struct_0(A_76)))))
      | v1_xboole_0(k1_tarski('#skF_1'(u1_struct_0(A_76))))
      | ~ l1_pre_topc(A_76)
      | v2_struct_0(A_76)
      | v1_xboole_0(u1_struct_0(A_76)) ) ),
    inference(resolution,[status(thm)],[c_168,c_229])).

tff(c_648,plain,(
    ! [A_105] :
      ( ~ v2_struct_0('#skF_2'(A_105,k1_tarski('#skF_1'(u1_struct_0(A_105)))))
      | ~ l1_pre_topc(A_105)
      | v2_struct_0(A_105)
      | v1_xboole_0(u1_struct_0(A_105)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2,c_233])).

tff(c_651,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_2'('#skF_4','#skF_5'),k1_tarski('#skF_1'('#skF_5'))))
    | ~ l1_pre_topc('#skF_2'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_2'('#skF_4','#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_648])).

tff(c_656,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_2'('#skF_4','#skF_5'),k1_tarski('#skF_1'('#skF_5'))))
    | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_576,c_651])).

tff(c_657,plain,(
    ~ v2_struct_0('#skF_2'('#skF_2'('#skF_4','#skF_5'),k1_tarski('#skF_1'('#skF_5')))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_257,c_656])).

tff(c_660,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5'))
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_657])).

tff(c_662,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_660])).

tff(c_663,plain,(
    ~ v2_struct_0('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_662])).

tff(c_749,plain,(
    ! [A_109] :
      ( m1_pre_topc('#skF_2'(A_109,k1_tarski('#skF_1'(u1_struct_0(A_109)))),A_109)
      | v1_xboole_0(k1_tarski('#skF_1'(u1_struct_0(A_109))))
      | ~ l1_pre_topc(A_109)
      | v2_struct_0(A_109)
      | v1_xboole_0(u1_struct_0(A_109)) ) ),
    inference(resolution,[status(thm)],[c_168,c_739])).

tff(c_1023,plain,(
    ! [A_127] :
      ( m1_pre_topc('#skF_2'(A_127,k1_tarski('#skF_1'(u1_struct_0(A_127)))),A_127)
      | ~ l1_pre_topc(A_127)
      | v2_struct_0(A_127)
      | v1_xboole_0(u1_struct_0(A_127)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2,c_749])).

tff(c_1035,plain,
    ( m1_pre_topc('#skF_2'('#skF_2'('#skF_4','#skF_5'),k1_tarski('#skF_1'('#skF_5'))),'#skF_2'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_2'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_2'('#skF_4','#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_1023])).

tff(c_1042,plain,
    ( m1_pre_topc('#skF_2'('#skF_2'('#skF_4','#skF_5'),k1_tarski('#skF_1'('#skF_5'))),'#skF_2'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_576,c_1035])).

tff(c_1043,plain,(
    m1_pre_topc('#skF_2'('#skF_2'('#skF_4','#skF_5'),k1_tarski('#skF_1'('#skF_5'))),'#skF_2'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_257,c_1042])).

tff(c_1052,plain,
    ( m1_pre_topc('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5'),'#skF_2'('#skF_4','#skF_5'))
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_1043])).

tff(c_1061,plain,
    ( m1_pre_topc('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5'),'#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1052])).

tff(c_1062,plain,(
    m1_pre_topc('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5'),'#skF_2'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1061])).

tff(c_166,plain,(
    ! [A_68,B_69] :
      ( r1_tarski(k6_domain_1(A_68,B_69),A_68)
      | ~ m1_subset_1(B_69,A_68)
      | v1_xboole_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_151,c_8])).

tff(c_842,plain,(
    ! [A_118,B_119] :
      ( k6_domain_1(A_118,B_119) = A_118
      | ~ v1_zfmisc_1(A_118)
      | v1_xboole_0(k6_domain_1(A_118,B_119))
      | ~ m1_subset_1(B_119,A_118)
      | v1_xboole_0(A_118) ) ),
    inference(resolution,[status(thm)],[c_166,c_202])).

tff(c_851,plain,(
    ! [A_2] :
      ( k6_domain_1(A_2,'#skF_1'(A_2)) = A_2
      | ~ v1_zfmisc_1(A_2)
      | v1_xboole_0(k1_tarski('#skF_1'(A_2)))
      | ~ m1_subset_1('#skF_1'(A_2),A_2)
      | v1_xboole_0(A_2)
      | v1_xboole_0(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_842])).

tff(c_855,plain,(
    ! [A_2] :
      ( k6_domain_1(A_2,'#skF_1'(A_2)) = A_2
      | ~ v1_zfmisc_1(A_2)
      | v1_xboole_0(k1_tarski('#skF_1'(A_2)))
      | v1_xboole_0(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_851])).

tff(c_857,plain,(
    ! [A_120] :
      ( k6_domain_1(A_120,'#skF_1'(A_120)) = A_120
      | ~ v1_zfmisc_1(A_120)
      | v1_xboole_0(A_120) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2,c_855])).

tff(c_874,plain,(
    ! [A_120] :
      ( r1_tarski(A_120,A_120)
      | ~ m1_subset_1('#skF_1'(A_120),A_120)
      | v1_xboole_0(A_120)
      | ~ v1_zfmisc_1(A_120)
      | v1_xboole_0(A_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_857,c_166])).

tff(c_927,plain,(
    ! [A_123] :
      ( r1_tarski(A_123,A_123)
      | ~ v1_zfmisc_1(A_123)
      | v1_xboole_0(A_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_874])).

tff(c_398,plain,(
    ! [A_86,A_7] :
      ( u1_struct_0('#skF_2'(A_86,A_7)) = A_7
      | v1_xboole_0(A_7)
      | ~ l1_pre_topc(A_86)
      | v2_struct_0(A_86)
      | ~ r1_tarski(A_7,u1_struct_0(A_86)) ) ),
    inference(resolution,[status(thm)],[c_10,c_369])).

tff(c_2088,plain,(
    ! [A_169] :
      ( u1_struct_0('#skF_2'(A_169,u1_struct_0(A_169))) = u1_struct_0(A_169)
      | ~ l1_pre_topc(A_169)
      | v2_struct_0(A_169)
      | ~ v1_zfmisc_1(u1_struct_0(A_169))
      | v1_xboole_0(u1_struct_0(A_169)) ) ),
    inference(resolution,[status(thm)],[c_927,c_398])).

tff(c_2241,plain,
    ( u1_struct_0('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5')) = u1_struct_0('#skF_2'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_2'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | ~ v1_zfmisc_1(u1_struct_0('#skF_2'('#skF_4','#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_2'('#skF_4','#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_2088])).

tff(c_2257,plain,
    ( u1_struct_0('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5')) = '#skF_5'
    | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_74,c_402,c_576,c_402,c_2241])).

tff(c_2258,plain,(
    u1_struct_0('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_257,c_2257])).

tff(c_1139,plain,(
    ! [B_134] :
      ( m1_subset_1('#skF_1'(u1_struct_0(B_134)),'#skF_5')
      | ~ m1_pre_topc(B_134,'#skF_2'('#skF_4','#skF_5'))
      | v2_struct_0(B_134)
      | ~ l1_pre_topc('#skF_2'('#skF_4','#skF_5'))
      | v2_struct_0('#skF_2'('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_1122])).

tff(c_1144,plain,(
    ! [B_134] :
      ( m1_subset_1('#skF_1'(u1_struct_0(B_134)),'#skF_5')
      | ~ m1_pre_topc(B_134,'#skF_2'('#skF_4','#skF_5'))
      | v2_struct_0(B_134)
      | v2_struct_0('#skF_2'('#skF_4','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_576,c_1139])).

tff(c_1145,plain,(
    ! [B_134] :
      ( m1_subset_1('#skF_1'(u1_struct_0(B_134)),'#skF_5')
      | ~ m1_pre_topc(B_134,'#skF_2'('#skF_4','#skF_5'))
      | v2_struct_0(B_134) ) ),
    inference(negUnitSimplification,[status(thm)],[c_257,c_1144])).

tff(c_1146,plain,(
    ! [B_136] :
      ( m1_subset_1('#skF_1'(u1_struct_0(B_136)),'#skF_5')
      | ~ m1_pre_topc(B_136,'#skF_2'('#skF_4','#skF_5'))
      | v2_struct_0(B_136) ) ),
    inference(negUnitSimplification,[status(thm)],[c_257,c_1144])).

tff(c_22,plain,(
    ! [A_23,B_24] :
      ( k6_domain_1(A_23,B_24) = k1_tarski(B_24)
      | ~ m1_subset_1(B_24,A_23)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1149,plain,(
    ! [B_136] :
      ( k6_domain_1('#skF_5','#skF_1'(u1_struct_0(B_136))) = k1_tarski('#skF_1'(u1_struct_0(B_136)))
      | v1_xboole_0('#skF_5')
      | ~ m1_pre_topc(B_136,'#skF_2'('#skF_4','#skF_5'))
      | v2_struct_0(B_136) ) ),
    inference(resolution,[status(thm)],[c_1146,c_22])).

tff(c_1242,plain,(
    ! [B_142] :
      ( k6_domain_1('#skF_5','#skF_1'(u1_struct_0(B_142))) = k1_tarski('#skF_1'(u1_struct_0(B_142)))
      | ~ m1_pre_topc(B_142,'#skF_2'('#skF_4','#skF_5'))
      | v2_struct_0(B_142) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1149])).

tff(c_1251,plain,(
    ! [B_142] :
      ( r1_tarski(k1_tarski('#skF_1'(u1_struct_0(B_142))),'#skF_5')
      | ~ m1_subset_1('#skF_1'(u1_struct_0(B_142)),'#skF_5')
      | v1_xboole_0('#skF_5')
      | ~ m1_pre_topc(B_142,'#skF_2'('#skF_4','#skF_5'))
      | v2_struct_0(B_142) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1242,c_166])).

tff(c_1329,plain,(
    ! [B_146] :
      ( r1_tarski(k1_tarski('#skF_1'(u1_struct_0(B_146))),'#skF_5')
      | ~ m1_subset_1('#skF_1'(u1_struct_0(B_146)),'#skF_5')
      | ~ m1_pre_topc(B_146,'#skF_2'('#skF_4','#skF_5'))
      | v2_struct_0(B_146) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1251])).

tff(c_38,plain,(
    ! [B_37,A_35] :
      ( B_37 = A_35
      | ~ r1_tarski(A_35,B_37)
      | ~ v1_zfmisc_1(B_37)
      | v1_xboole_0(B_37)
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_1332,plain,(
    ! [B_146] :
      ( k1_tarski('#skF_1'(u1_struct_0(B_146))) = '#skF_5'
      | ~ v1_zfmisc_1('#skF_5')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(k1_tarski('#skF_1'(u1_struct_0(B_146))))
      | ~ m1_subset_1('#skF_1'(u1_struct_0(B_146)),'#skF_5')
      | ~ m1_pre_topc(B_146,'#skF_2'('#skF_4','#skF_5'))
      | v2_struct_0(B_146) ) ),
    inference(resolution,[status(thm)],[c_1329,c_38])).

tff(c_1347,plain,(
    ! [B_146] :
      ( k1_tarski('#skF_1'(u1_struct_0(B_146))) = '#skF_5'
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(k1_tarski('#skF_1'(u1_struct_0(B_146))))
      | ~ m1_subset_1('#skF_1'(u1_struct_0(B_146)),'#skF_5')
      | ~ m1_pre_topc(B_146,'#skF_2'('#skF_4','#skF_5'))
      | v2_struct_0(B_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1332])).

tff(c_1446,plain,(
    ! [B_153] :
      ( k1_tarski('#skF_1'(u1_struct_0(B_153))) = '#skF_5'
      | ~ m1_subset_1('#skF_1'(u1_struct_0(B_153)),'#skF_5')
      | ~ m1_pre_topc(B_153,'#skF_2'('#skF_4','#skF_5'))
      | v2_struct_0(B_153) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2,c_54,c_1347])).

tff(c_1456,plain,(
    ! [B_134] :
      ( k1_tarski('#skF_1'(u1_struct_0(B_134))) = '#skF_5'
      | ~ m1_pre_topc(B_134,'#skF_2'('#skF_4','#skF_5'))
      | v2_struct_0(B_134) ) ),
    inference(resolution,[status(thm)],[c_1145,c_1446])).

tff(c_2286,plain,
    ( k1_tarski('#skF_1'('#skF_5')) = '#skF_5'
    | ~ m1_pre_topc('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5'),'#skF_2'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2258,c_1456])).

tff(c_2418,plain,
    ( k1_tarski('#skF_1'('#skF_5')) = '#skF_5'
    | v2_struct_0('#skF_2'('#skF_2'('#skF_4','#skF_5'),'#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1062,c_2286])).

tff(c_2419,plain,(
    k1_tarski('#skF_1'('#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_663,c_2418])).

tff(c_102,plain,(
    ! [B_60,A_61] :
      ( v1_xboole_0(B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_61))
      | ~ v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_108,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_102])).

tff(c_116,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_108])).

tff(c_1073,plain,(
    ! [C_128,A_129] :
      ( m1_subset_1(C_128,u1_struct_0(A_129))
      | ~ m1_subset_1(C_128,'#skF_5')
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_129)
      | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_129)
      | v2_struct_0(A_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_1069])).

tff(c_1105,plain,(
    ! [C_132,A_133] :
      ( m1_subset_1(C_132,u1_struct_0(A_133))
      | ~ m1_subset_1(C_132,'#skF_5')
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_133)
      | ~ l1_pre_topc(A_133)
      | v2_struct_0(A_133) ) ),
    inference(negUnitSimplification,[status(thm)],[c_257,c_1073])).

tff(c_11041,plain,(
    ! [A_293,C_294] :
      ( k6_domain_1(u1_struct_0(A_293),C_294) = k1_tarski(C_294)
      | v1_xboole_0(u1_struct_0(A_293))
      | ~ m1_subset_1(C_294,'#skF_5')
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_293)
      | ~ l1_pre_topc(A_293)
      | v2_struct_0(A_293) ) ),
    inference(resolution,[status(thm)],[c_1105,c_22])).

tff(c_11046,plain,(
    ! [C_294] :
      ( k6_domain_1(u1_struct_0('#skF_4'),C_294) = k1_tarski(C_294)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_294,'#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_773,c_11041])).

tff(c_11053,plain,(
    ! [C_294] :
      ( k6_domain_1(u1_struct_0('#skF_4'),C_294) = k1_tarski(C_294)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_294,'#skF_5')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_11046])).

tff(c_11055,plain,(
    ! [C_295] :
      ( k6_domain_1(u1_struct_0('#skF_4'),C_295) = k1_tarski(C_295)
      | ~ m1_subset_1(C_295,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_116,c_11053])).

tff(c_50,plain,(
    ! [A_44,B_46] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_44),B_46),A_44)
      | ~ m1_subset_1(B_46,u1_struct_0(A_44))
      | ~ l1_pre_topc(A_44)
      | ~ v2_pre_topc(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_11107,plain,(
    ! [C_295] :
      ( v2_tex_2(k1_tarski(C_295),'#skF_4')
      | ~ m1_subset_1(C_295,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_295,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11055,c_50])).

tff(c_11171,plain,(
    ! [C_295] :
      ( v2_tex_2(k1_tarski(C_295),'#skF_4')
      | ~ m1_subset_1(C_295,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_295,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_11107])).

tff(c_11184,plain,(
    ! [C_296] :
      ( v2_tex_2(k1_tarski(C_296),'#skF_4')
      | ~ m1_subset_1(C_296,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_296,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_11171])).

tff(c_11199,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2419,c_11184])).

tff(c_11207,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_11199])).

tff(c_11208,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_11207])).

tff(c_11215,plain,
    ( ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1142,c_11208])).

tff(c_11225,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_773,c_11215])).

tff(c_11227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_11225])).

tff(c_11228,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_12031,plain,(
    ! [A_366,B_367] :
      ( ~ v2_struct_0('#skF_3'(A_366,B_367))
      | ~ v2_tex_2(B_367,A_366)
      | ~ m1_subset_1(B_367,k1_zfmisc_1(u1_struct_0(A_366)))
      | v1_xboole_0(B_367)
      | ~ l1_pre_topc(A_366)
      | ~ v2_pre_topc(A_366)
      | v2_struct_0(A_366) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_12059,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_12031])).

tff(c_12075,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_11228,c_12059])).

tff(c_12076,plain,(
    ~ v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_54,c_12075])).

tff(c_11229,plain,(
    ~ v1_zfmisc_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_12543,plain,(
    ! [A_388,B_389] :
      ( u1_struct_0('#skF_3'(A_388,B_389)) = B_389
      | ~ v2_tex_2(B_389,A_388)
      | ~ m1_subset_1(B_389,k1_zfmisc_1(u1_struct_0(A_388)))
      | v1_xboole_0(B_389)
      | ~ l1_pre_topc(A_388)
      | ~ v2_pre_topc(A_388)
      | v2_struct_0(A_388) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_12571,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_12543])).

tff(c_12587,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_11228,c_12571])).

tff(c_12588,plain,(
    u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_54,c_12587])).

tff(c_16,plain,(
    ! [A_13] :
      ( v1_zfmisc_1(u1_struct_0(A_13))
      | ~ l1_struct_0(A_13)
      | ~ v7_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12674,plain,
    ( v1_zfmisc_1('#skF_5')
    | ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12588,c_16])).

tff(c_12720,plain,
    ( ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_11229,c_12674])).

tff(c_12722,plain,(
    ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_12720])).

tff(c_58,plain,(
    v2_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_12218,plain,(
    ! [A_375,B_376] :
      ( v1_tdlat_3('#skF_3'(A_375,B_376))
      | ~ v2_tex_2(B_376,A_375)
      | ~ m1_subset_1(B_376,k1_zfmisc_1(u1_struct_0(A_375)))
      | v1_xboole_0(B_376)
      | ~ l1_pre_topc(A_375)
      | ~ v2_pre_topc(A_375)
      | v2_struct_0(A_375) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_12246,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_12218])).

tff(c_12262,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_11228,c_12246])).

tff(c_12263,plain,(
    v1_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_54,c_12262])).

tff(c_12725,plain,(
    ! [A_390,B_391] :
      ( m1_pre_topc('#skF_3'(A_390,B_391),A_390)
      | ~ v2_tex_2(B_391,A_390)
      | ~ m1_subset_1(B_391,k1_zfmisc_1(u1_struct_0(A_390)))
      | v1_xboole_0(B_391)
      | ~ l1_pre_topc(A_390)
      | ~ v2_pre_topc(A_390)
      | v2_struct_0(A_390) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_12747,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_12725])).

tff(c_12763,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_11228,c_12747])).

tff(c_12764,plain,(
    m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_54,c_12763])).

tff(c_26,plain,(
    ! [B_28,A_26] :
      ( ~ v1_tdlat_3(B_28)
      | v7_struct_0(B_28)
      | v2_struct_0(B_28)
      | ~ m1_pre_topc(B_28,A_26)
      | ~ l1_pre_topc(A_26)
      | ~ v2_tdlat_3(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_12768,plain,
    ( ~ v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v7_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_12764,c_26])).

tff(c_12774,plain,
    ( v7_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_12263,c_12768])).

tff(c_12776,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_12076,c_12722,c_12774])).

tff(c_12777,plain,(
    ~ l1_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_12720])).

tff(c_12782,plain,(
    ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_12,c_12777])).

tff(c_12785,plain,(
    ! [A_392,B_393] :
      ( m1_pre_topc('#skF_3'(A_392,B_393),A_392)
      | ~ v2_tex_2(B_393,A_392)
      | ~ m1_subset_1(B_393,k1_zfmisc_1(u1_struct_0(A_392)))
      | v1_xboole_0(B_393)
      | ~ l1_pre_topc(A_392)
      | ~ v2_pre_topc(A_392)
      | v2_struct_0(A_392) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_12807,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_12785])).

tff(c_12823,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_11228,c_12807])).

tff(c_12824,plain,(
    m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_54,c_12823])).

tff(c_12831,plain,
    ( l1_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_12824,c_14])).

tff(c_12838,plain,(
    l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_12831])).

tff(c_12840,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12782,c_12838])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:41:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.33/3.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.33/3.62  
% 9.33/3.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.33/3.63  %$ v2_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 9.33/3.63  
% 9.33/3.63  %Foreground sorts:
% 9.33/3.63  
% 9.33/3.63  
% 9.33/3.63  %Background operators:
% 9.33/3.63  
% 9.33/3.63  
% 9.33/3.63  %Foreground operators:
% 9.33/3.63  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.33/3.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.33/3.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.33/3.63  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.33/3.63  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 9.33/3.63  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.33/3.63  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 9.33/3.63  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.33/3.63  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 9.33/3.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.33/3.63  tff('#skF_5', type, '#skF_5': $i).
% 9.33/3.63  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 9.33/3.63  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 9.33/3.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.33/3.63  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 9.33/3.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.33/3.63  tff('#skF_4', type, '#skF_4': $i).
% 9.33/3.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.33/3.63  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.33/3.63  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 9.33/3.63  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 9.33/3.63  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.33/3.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.33/3.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.33/3.63  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 9.33/3.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.33/3.63  
% 9.33/3.65  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 9.33/3.65  tff(f_214, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 9.33/3.65  tff(f_140, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (?[C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) & (B = u1_struct_0(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_tsep_1)).
% 9.33/3.65  tff(f_31, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 9.33/3.65  tff(f_75, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 9.33/3.65  tff(f_28, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 9.33/3.65  tff(f_89, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 9.33/3.65  tff(f_82, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 9.33/3.65  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.33/3.65  tff(f_153, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 9.33/3.65  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 9.33/3.65  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 9.33/3.65  tff(f_194, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 9.33/3.65  tff(f_182, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tex_2)).
% 9.33/3.65  tff(f_59, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 9.33/3.65  tff(f_119, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((~v2_struct_0(B) & ~v7_struct_0(B)) => (~v2_struct_0(B) & ~v1_tdlat_3(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc32_tex_2)).
% 9.33/3.65  tff(c_12, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.33/3.65  tff(c_62, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_214])).
% 9.33/3.65  tff(c_54, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_214])).
% 9.33/3.65  tff(c_60, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_214])).
% 9.33/3.65  tff(c_56, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_214])).
% 9.33/3.65  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_214])).
% 9.33/3.65  tff(c_739, plain, (![A_109, B_110]: (m1_pre_topc('#skF_2'(A_109, B_110), A_109) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | v1_xboole_0(B_110) | ~l1_pre_topc(A_109) | v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.33/3.65  tff(c_757, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_739])).
% 9.33/3.65  tff(c_772, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_757])).
% 9.33/3.65  tff(c_773, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_62, c_54, c_772])).
% 9.33/3.65  tff(c_229, plain, (![A_76, B_77]: (~v2_struct_0('#skF_2'(A_76, B_77)) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | v1_xboole_0(B_77) | ~l1_pre_topc(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.33/3.65  tff(c_244, plain, (~v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_229])).
% 9.33/3.65  tff(c_256, plain, (~v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_244])).
% 9.33/3.65  tff(c_257, plain, (~v2_struct_0('#skF_2'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_62, c_54, c_256])).
% 9.33/3.65  tff(c_369, plain, (![A_86, B_87]: (u1_struct_0('#skF_2'(A_86, B_87))=B_87 | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | v1_xboole_0(B_87) | ~l1_pre_topc(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.33/3.65  tff(c_388, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_369])).
% 9.33/3.65  tff(c_401, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_388])).
% 9.33/3.65  tff(c_402, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_62, c_54, c_401])).
% 9.33/3.65  tff(c_4, plain, (![A_2]: (m1_subset_1('#skF_1'(A_2), A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.33/3.65  tff(c_1069, plain, (![C_128, A_129, B_130]: (m1_subset_1(C_128, u1_struct_0(A_129)) | ~m1_subset_1(C_128, u1_struct_0(B_130)) | ~m1_pre_topc(B_130, A_129) | v2_struct_0(B_130) | ~l1_pre_topc(A_129) | v2_struct_0(A_129))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.33/3.65  tff(c_1122, plain, (![B_134, A_135]: (m1_subset_1('#skF_1'(u1_struct_0(B_134)), u1_struct_0(A_135)) | ~m1_pre_topc(B_134, A_135) | v2_struct_0(B_134) | ~l1_pre_topc(A_135) | v2_struct_0(A_135))), inference(resolution, [status(thm)], [c_4, c_1069])).
% 9.33/3.65  tff(c_1136, plain, (![A_135]: (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0(A_135)) | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_135) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | ~l1_pre_topc(A_135) | v2_struct_0(A_135))), inference(superposition, [status(thm), theory('equality')], [c_402, c_1122])).
% 9.33/3.65  tff(c_1142, plain, (![A_135]: (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0(A_135)) | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_135) | ~l1_pre_topc(A_135) | v2_struct_0(A_135))), inference(negUnitSimplification, [status(thm)], [c_257, c_1136])).
% 9.33/3.65  tff(c_70, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_214])).
% 9.33/3.65  tff(c_74, plain, (v1_zfmisc_1('#skF_5')), inference(splitLeft, [status(thm)], [c_70])).
% 9.33/3.65  tff(c_64, plain, (~v1_zfmisc_1('#skF_5') | ~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_214])).
% 9.33/3.65  tff(c_76, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_64])).
% 9.33/3.65  tff(c_2, plain, (![A_1]: (~v1_xboole_0(k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_28])).
% 9.33/3.65  tff(c_129, plain, (![A_65, B_66]: (k6_domain_1(A_65, B_66)=k1_tarski(B_66) | ~m1_subset_1(B_66, A_65) | v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.33/3.65  tff(c_141, plain, (![A_2]: (k6_domain_1(A_2, '#skF_1'(A_2))=k1_tarski('#skF_1'(A_2)) | v1_xboole_0(A_2))), inference(resolution, [status(thm)], [c_4, c_129])).
% 9.33/3.65  tff(c_151, plain, (![A_68, B_69]: (m1_subset_1(k6_domain_1(A_68, B_69), k1_zfmisc_1(A_68)) | ~m1_subset_1(B_69, A_68) | v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.33/3.65  tff(c_163, plain, (![A_2]: (m1_subset_1(k1_tarski('#skF_1'(A_2)), k1_zfmisc_1(A_2)) | ~m1_subset_1('#skF_1'(A_2), A_2) | v1_xboole_0(A_2) | v1_xboole_0(A_2))), inference(superposition, [status(thm), theory('equality')], [c_141, c_151])).
% 9.33/3.65  tff(c_169, plain, (![A_70]: (m1_subset_1(k1_tarski('#skF_1'(A_70)), k1_zfmisc_1(A_70)) | v1_xboole_0(A_70))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_163])).
% 9.33/3.65  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.33/3.65  tff(c_183, plain, (![A_70]: (r1_tarski(k1_tarski('#skF_1'(A_70)), A_70) | v1_xboole_0(A_70))), inference(resolution, [status(thm)], [c_169, c_8])).
% 9.33/3.65  tff(c_202, plain, (![B_74, A_75]: (B_74=A_75 | ~r1_tarski(A_75, B_74) | ~v1_zfmisc_1(B_74) | v1_xboole_0(B_74) | v1_xboole_0(A_75))), inference(cnfTransformation, [status(thm)], [f_153])).
% 9.33/3.65  tff(c_208, plain, (![A_70]: (k1_tarski('#skF_1'(A_70))=A_70 | ~v1_zfmisc_1(A_70) | v1_xboole_0(k1_tarski('#skF_1'(A_70))) | v1_xboole_0(A_70))), inference(resolution, [status(thm)], [c_183, c_202])).
% 9.33/3.65  tff(c_218, plain, (![A_70]: (k1_tarski('#skF_1'(A_70))=A_70 | ~v1_zfmisc_1(A_70) | v1_xboole_0(A_70))), inference(negUnitSimplification, [status(thm)], [c_2, c_208])).
% 9.33/3.65  tff(c_10, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.33/3.65  tff(c_276, plain, (![A_79, B_80]: (v1_pre_topc('#skF_2'(A_79, B_80)) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | v1_xboole_0(B_80) | ~l1_pre_topc(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.33/3.65  tff(c_448, plain, (![A_89, A_90]: (v1_pre_topc('#skF_2'(A_89, A_90)) | v1_xboole_0(A_90) | ~l1_pre_topc(A_89) | v2_struct_0(A_89) | ~r1_tarski(A_90, u1_struct_0(A_89)))), inference(resolution, [status(thm)], [c_10, c_276])).
% 9.33/3.65  tff(c_451, plain, (![A_90]: (v1_pre_topc('#skF_2'('#skF_2'('#skF_4', '#skF_5'), A_90)) | v1_xboole_0(A_90) | ~l1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | ~r1_tarski(A_90, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_402, c_448])).
% 9.33/3.65  tff(c_471, plain, (![A_90]: (v1_pre_topc('#skF_2'('#skF_2'('#skF_4', '#skF_5'), A_90)) | v1_xboole_0(A_90) | ~l1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | ~r1_tarski(A_90, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_257, c_451])).
% 9.33/3.65  tff(c_482, plain, (~l1_pre_topc('#skF_2'('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_471])).
% 9.33/3.65  tff(c_535, plain, (![A_95, B_96]: (m1_pre_topc('#skF_2'(A_95, B_96), A_95) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | v1_xboole_0(B_96) | ~l1_pre_topc(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.33/3.65  tff(c_551, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_535])).
% 9.33/3.65  tff(c_564, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_551])).
% 9.33/3.65  tff(c_565, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_62, c_54, c_564])).
% 9.33/3.65  tff(c_14, plain, (![B_12, A_10]: (l1_pre_topc(B_12) | ~m1_pre_topc(B_12, A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.33/3.65  tff(c_569, plain, (l1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_565, c_14])).
% 9.33/3.65  tff(c_572, plain, (l1_pre_topc('#skF_2'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_569])).
% 9.33/3.65  tff(c_574, plain, $false, inference(negUnitSimplification, [status(thm)], [c_482, c_572])).
% 9.33/3.65  tff(c_576, plain, (l1_pre_topc('#skF_2'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_471])).
% 9.33/3.65  tff(c_168, plain, (![A_2]: (m1_subset_1(k1_tarski('#skF_1'(A_2)), k1_zfmisc_1(A_2)) | v1_xboole_0(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_163])).
% 9.33/3.65  tff(c_233, plain, (![A_76]: (~v2_struct_0('#skF_2'(A_76, k1_tarski('#skF_1'(u1_struct_0(A_76))))) | v1_xboole_0(k1_tarski('#skF_1'(u1_struct_0(A_76)))) | ~l1_pre_topc(A_76) | v2_struct_0(A_76) | v1_xboole_0(u1_struct_0(A_76)))), inference(resolution, [status(thm)], [c_168, c_229])).
% 9.33/3.65  tff(c_648, plain, (![A_105]: (~v2_struct_0('#skF_2'(A_105, k1_tarski('#skF_1'(u1_struct_0(A_105))))) | ~l1_pre_topc(A_105) | v2_struct_0(A_105) | v1_xboole_0(u1_struct_0(A_105)))), inference(negUnitSimplification, [status(thm)], [c_2, c_233])).
% 9.33/3.65  tff(c_651, plain, (~v2_struct_0('#skF_2'('#skF_2'('#skF_4', '#skF_5'), k1_tarski('#skF_1'('#skF_5')))) | ~l1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_2'('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_402, c_648])).
% 9.33/3.65  tff(c_656, plain, (~v2_struct_0('#skF_2'('#skF_2'('#skF_4', '#skF_5'), k1_tarski('#skF_1'('#skF_5')))) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_402, c_576, c_651])).
% 9.33/3.65  tff(c_657, plain, (~v2_struct_0('#skF_2'('#skF_2'('#skF_4', '#skF_5'), k1_tarski('#skF_1'('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_257, c_656])).
% 9.33/3.65  tff(c_660, plain, (~v2_struct_0('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5')) | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_218, c_657])).
% 9.33/3.65  tff(c_662, plain, (~v2_struct_0('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_660])).
% 9.33/3.65  tff(c_663, plain, (~v2_struct_0('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_54, c_662])).
% 9.33/3.65  tff(c_749, plain, (![A_109]: (m1_pre_topc('#skF_2'(A_109, k1_tarski('#skF_1'(u1_struct_0(A_109)))), A_109) | v1_xboole_0(k1_tarski('#skF_1'(u1_struct_0(A_109)))) | ~l1_pre_topc(A_109) | v2_struct_0(A_109) | v1_xboole_0(u1_struct_0(A_109)))), inference(resolution, [status(thm)], [c_168, c_739])).
% 9.33/3.65  tff(c_1023, plain, (![A_127]: (m1_pre_topc('#skF_2'(A_127, k1_tarski('#skF_1'(u1_struct_0(A_127)))), A_127) | ~l1_pre_topc(A_127) | v2_struct_0(A_127) | v1_xboole_0(u1_struct_0(A_127)))), inference(negUnitSimplification, [status(thm)], [c_2, c_749])).
% 9.33/3.65  tff(c_1035, plain, (m1_pre_topc('#skF_2'('#skF_2'('#skF_4', '#skF_5'), k1_tarski('#skF_1'('#skF_5'))), '#skF_2'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_2'('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_402, c_1023])).
% 9.33/3.65  tff(c_1042, plain, (m1_pre_topc('#skF_2'('#skF_2'('#skF_4', '#skF_5'), k1_tarski('#skF_1'('#skF_5'))), '#skF_2'('#skF_4', '#skF_5')) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_402, c_576, c_1035])).
% 9.33/3.65  tff(c_1043, plain, (m1_pre_topc('#skF_2'('#skF_2'('#skF_4', '#skF_5'), k1_tarski('#skF_1'('#skF_5'))), '#skF_2'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_54, c_257, c_1042])).
% 9.33/3.65  tff(c_1052, plain, (m1_pre_topc('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5'), '#skF_2'('#skF_4', '#skF_5')) | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_218, c_1043])).
% 9.33/3.65  tff(c_1061, plain, (m1_pre_topc('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5'), '#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1052])).
% 9.33/3.65  tff(c_1062, plain, (m1_pre_topc('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5'), '#skF_2'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_54, c_1061])).
% 9.33/3.65  tff(c_166, plain, (![A_68, B_69]: (r1_tarski(k6_domain_1(A_68, B_69), A_68) | ~m1_subset_1(B_69, A_68) | v1_xboole_0(A_68))), inference(resolution, [status(thm)], [c_151, c_8])).
% 9.33/3.65  tff(c_842, plain, (![A_118, B_119]: (k6_domain_1(A_118, B_119)=A_118 | ~v1_zfmisc_1(A_118) | v1_xboole_0(k6_domain_1(A_118, B_119)) | ~m1_subset_1(B_119, A_118) | v1_xboole_0(A_118))), inference(resolution, [status(thm)], [c_166, c_202])).
% 9.33/3.65  tff(c_851, plain, (![A_2]: (k6_domain_1(A_2, '#skF_1'(A_2))=A_2 | ~v1_zfmisc_1(A_2) | v1_xboole_0(k1_tarski('#skF_1'(A_2))) | ~m1_subset_1('#skF_1'(A_2), A_2) | v1_xboole_0(A_2) | v1_xboole_0(A_2))), inference(superposition, [status(thm), theory('equality')], [c_141, c_842])).
% 9.33/3.65  tff(c_855, plain, (![A_2]: (k6_domain_1(A_2, '#skF_1'(A_2))=A_2 | ~v1_zfmisc_1(A_2) | v1_xboole_0(k1_tarski('#skF_1'(A_2))) | v1_xboole_0(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_851])).
% 9.33/3.65  tff(c_857, plain, (![A_120]: (k6_domain_1(A_120, '#skF_1'(A_120))=A_120 | ~v1_zfmisc_1(A_120) | v1_xboole_0(A_120))), inference(negUnitSimplification, [status(thm)], [c_2, c_855])).
% 9.33/3.65  tff(c_874, plain, (![A_120]: (r1_tarski(A_120, A_120) | ~m1_subset_1('#skF_1'(A_120), A_120) | v1_xboole_0(A_120) | ~v1_zfmisc_1(A_120) | v1_xboole_0(A_120))), inference(superposition, [status(thm), theory('equality')], [c_857, c_166])).
% 9.33/3.65  tff(c_927, plain, (![A_123]: (r1_tarski(A_123, A_123) | ~v1_zfmisc_1(A_123) | v1_xboole_0(A_123))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_874])).
% 9.33/3.65  tff(c_398, plain, (![A_86, A_7]: (u1_struct_0('#skF_2'(A_86, A_7))=A_7 | v1_xboole_0(A_7) | ~l1_pre_topc(A_86) | v2_struct_0(A_86) | ~r1_tarski(A_7, u1_struct_0(A_86)))), inference(resolution, [status(thm)], [c_10, c_369])).
% 9.33/3.65  tff(c_2088, plain, (![A_169]: (u1_struct_0('#skF_2'(A_169, u1_struct_0(A_169)))=u1_struct_0(A_169) | ~l1_pre_topc(A_169) | v2_struct_0(A_169) | ~v1_zfmisc_1(u1_struct_0(A_169)) | v1_xboole_0(u1_struct_0(A_169)))), inference(resolution, [status(thm)], [c_927, c_398])).
% 9.33/3.65  tff(c_2241, plain, (u1_struct_0('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5'))=u1_struct_0('#skF_2'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | ~v1_zfmisc_1(u1_struct_0('#skF_2'('#skF_4', '#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_2'('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_402, c_2088])).
% 9.33/3.65  tff(c_2257, plain, (u1_struct_0('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5'))='#skF_5' | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_402, c_74, c_402, c_576, c_402, c_2241])).
% 9.33/3.65  tff(c_2258, plain, (u1_struct_0('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_54, c_257, c_2257])).
% 9.33/3.65  tff(c_1139, plain, (![B_134]: (m1_subset_1('#skF_1'(u1_struct_0(B_134)), '#skF_5') | ~m1_pre_topc(B_134, '#skF_2'('#skF_4', '#skF_5')) | v2_struct_0(B_134) | ~l1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_402, c_1122])).
% 9.33/3.65  tff(c_1144, plain, (![B_134]: (m1_subset_1('#skF_1'(u1_struct_0(B_134)), '#skF_5') | ~m1_pre_topc(B_134, '#skF_2'('#skF_4', '#skF_5')) | v2_struct_0(B_134) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_576, c_1139])).
% 9.33/3.65  tff(c_1145, plain, (![B_134]: (m1_subset_1('#skF_1'(u1_struct_0(B_134)), '#skF_5') | ~m1_pre_topc(B_134, '#skF_2'('#skF_4', '#skF_5')) | v2_struct_0(B_134))), inference(negUnitSimplification, [status(thm)], [c_257, c_1144])).
% 9.33/3.65  tff(c_1146, plain, (![B_136]: (m1_subset_1('#skF_1'(u1_struct_0(B_136)), '#skF_5') | ~m1_pre_topc(B_136, '#skF_2'('#skF_4', '#skF_5')) | v2_struct_0(B_136))), inference(negUnitSimplification, [status(thm)], [c_257, c_1144])).
% 9.33/3.65  tff(c_22, plain, (![A_23, B_24]: (k6_domain_1(A_23, B_24)=k1_tarski(B_24) | ~m1_subset_1(B_24, A_23) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.33/3.65  tff(c_1149, plain, (![B_136]: (k6_domain_1('#skF_5', '#skF_1'(u1_struct_0(B_136)))=k1_tarski('#skF_1'(u1_struct_0(B_136))) | v1_xboole_0('#skF_5') | ~m1_pre_topc(B_136, '#skF_2'('#skF_4', '#skF_5')) | v2_struct_0(B_136))), inference(resolution, [status(thm)], [c_1146, c_22])).
% 9.33/3.65  tff(c_1242, plain, (![B_142]: (k6_domain_1('#skF_5', '#skF_1'(u1_struct_0(B_142)))=k1_tarski('#skF_1'(u1_struct_0(B_142))) | ~m1_pre_topc(B_142, '#skF_2'('#skF_4', '#skF_5')) | v2_struct_0(B_142))), inference(negUnitSimplification, [status(thm)], [c_54, c_1149])).
% 9.33/3.65  tff(c_1251, plain, (![B_142]: (r1_tarski(k1_tarski('#skF_1'(u1_struct_0(B_142))), '#skF_5') | ~m1_subset_1('#skF_1'(u1_struct_0(B_142)), '#skF_5') | v1_xboole_0('#skF_5') | ~m1_pre_topc(B_142, '#skF_2'('#skF_4', '#skF_5')) | v2_struct_0(B_142))), inference(superposition, [status(thm), theory('equality')], [c_1242, c_166])).
% 9.33/3.65  tff(c_1329, plain, (![B_146]: (r1_tarski(k1_tarski('#skF_1'(u1_struct_0(B_146))), '#skF_5') | ~m1_subset_1('#skF_1'(u1_struct_0(B_146)), '#skF_5') | ~m1_pre_topc(B_146, '#skF_2'('#skF_4', '#skF_5')) | v2_struct_0(B_146))), inference(negUnitSimplification, [status(thm)], [c_54, c_1251])).
% 9.33/3.65  tff(c_38, plain, (![B_37, A_35]: (B_37=A_35 | ~r1_tarski(A_35, B_37) | ~v1_zfmisc_1(B_37) | v1_xboole_0(B_37) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_153])).
% 9.33/3.65  tff(c_1332, plain, (![B_146]: (k1_tarski('#skF_1'(u1_struct_0(B_146)))='#skF_5' | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5') | v1_xboole_0(k1_tarski('#skF_1'(u1_struct_0(B_146)))) | ~m1_subset_1('#skF_1'(u1_struct_0(B_146)), '#skF_5') | ~m1_pre_topc(B_146, '#skF_2'('#skF_4', '#skF_5')) | v2_struct_0(B_146))), inference(resolution, [status(thm)], [c_1329, c_38])).
% 9.33/3.65  tff(c_1347, plain, (![B_146]: (k1_tarski('#skF_1'(u1_struct_0(B_146)))='#skF_5' | v1_xboole_0('#skF_5') | v1_xboole_0(k1_tarski('#skF_1'(u1_struct_0(B_146)))) | ~m1_subset_1('#skF_1'(u1_struct_0(B_146)), '#skF_5') | ~m1_pre_topc(B_146, '#skF_2'('#skF_4', '#skF_5')) | v2_struct_0(B_146))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1332])).
% 9.33/3.65  tff(c_1446, plain, (![B_153]: (k1_tarski('#skF_1'(u1_struct_0(B_153)))='#skF_5' | ~m1_subset_1('#skF_1'(u1_struct_0(B_153)), '#skF_5') | ~m1_pre_topc(B_153, '#skF_2'('#skF_4', '#skF_5')) | v2_struct_0(B_153))), inference(negUnitSimplification, [status(thm)], [c_2, c_54, c_1347])).
% 9.33/3.65  tff(c_1456, plain, (![B_134]: (k1_tarski('#skF_1'(u1_struct_0(B_134)))='#skF_5' | ~m1_pre_topc(B_134, '#skF_2'('#skF_4', '#skF_5')) | v2_struct_0(B_134))), inference(resolution, [status(thm)], [c_1145, c_1446])).
% 9.33/3.65  tff(c_2286, plain, (k1_tarski('#skF_1'('#skF_5'))='#skF_5' | ~m1_pre_topc('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5'), '#skF_2'('#skF_4', '#skF_5')) | v2_struct_0('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2258, c_1456])).
% 9.33/3.65  tff(c_2418, plain, (k1_tarski('#skF_1'('#skF_5'))='#skF_5' | v2_struct_0('#skF_2'('#skF_2'('#skF_4', '#skF_5'), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1062, c_2286])).
% 9.33/3.65  tff(c_2419, plain, (k1_tarski('#skF_1'('#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_663, c_2418])).
% 9.33/3.65  tff(c_102, plain, (![B_60, A_61]: (v1_xboole_0(B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_61)) | ~v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.33/3.65  tff(c_108, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_52, c_102])).
% 9.33/3.65  tff(c_116, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_108])).
% 9.33/3.65  tff(c_1073, plain, (![C_128, A_129]: (m1_subset_1(C_128, u1_struct_0(A_129)) | ~m1_subset_1(C_128, '#skF_5') | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_129) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | ~l1_pre_topc(A_129) | v2_struct_0(A_129))), inference(superposition, [status(thm), theory('equality')], [c_402, c_1069])).
% 9.33/3.65  tff(c_1105, plain, (![C_132, A_133]: (m1_subset_1(C_132, u1_struct_0(A_133)) | ~m1_subset_1(C_132, '#skF_5') | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_133) | ~l1_pre_topc(A_133) | v2_struct_0(A_133))), inference(negUnitSimplification, [status(thm)], [c_257, c_1073])).
% 9.33/3.65  tff(c_11041, plain, (![A_293, C_294]: (k6_domain_1(u1_struct_0(A_293), C_294)=k1_tarski(C_294) | v1_xboole_0(u1_struct_0(A_293)) | ~m1_subset_1(C_294, '#skF_5') | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_293) | ~l1_pre_topc(A_293) | v2_struct_0(A_293))), inference(resolution, [status(thm)], [c_1105, c_22])).
% 9.33/3.65  tff(c_11046, plain, (![C_294]: (k6_domain_1(u1_struct_0('#skF_4'), C_294)=k1_tarski(C_294) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(C_294, '#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_773, c_11041])).
% 9.33/3.65  tff(c_11053, plain, (![C_294]: (k6_domain_1(u1_struct_0('#skF_4'), C_294)=k1_tarski(C_294) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(C_294, '#skF_5') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_11046])).
% 9.33/3.65  tff(c_11055, plain, (![C_295]: (k6_domain_1(u1_struct_0('#skF_4'), C_295)=k1_tarski(C_295) | ~m1_subset_1(C_295, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_62, c_116, c_11053])).
% 9.33/3.65  tff(c_50, plain, (![A_44, B_46]: (v2_tex_2(k6_domain_1(u1_struct_0(A_44), B_46), A_44) | ~m1_subset_1(B_46, u1_struct_0(A_44)) | ~l1_pre_topc(A_44) | ~v2_pre_topc(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_194])).
% 9.33/3.65  tff(c_11107, plain, (![C_295]: (v2_tex_2(k1_tarski(C_295), '#skF_4') | ~m1_subset_1(C_295, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_subset_1(C_295, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_11055, c_50])).
% 9.33/3.65  tff(c_11171, plain, (![C_295]: (v2_tex_2(k1_tarski(C_295), '#skF_4') | ~m1_subset_1(C_295, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | ~m1_subset_1(C_295, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_11107])).
% 9.33/3.65  tff(c_11184, plain, (![C_296]: (v2_tex_2(k1_tarski(C_296), '#skF_4') | ~m1_subset_1(C_296, u1_struct_0('#skF_4')) | ~m1_subset_1(C_296, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_62, c_11171])).
% 9.33/3.65  tff(c_11199, plain, (v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'('#skF_5'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2419, c_11184])).
% 9.33/3.65  tff(c_11207, plain, (v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_11199])).
% 9.33/3.65  tff(c_11208, plain, (~m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_76, c_11207])).
% 9.33/3.65  tff(c_11215, plain, (~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1142, c_11208])).
% 9.33/3.65  tff(c_11225, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_773, c_11215])).
% 9.33/3.65  tff(c_11227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_11225])).
% 9.33/3.65  tff(c_11228, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_70])).
% 9.33/3.65  tff(c_12031, plain, (![A_366, B_367]: (~v2_struct_0('#skF_3'(A_366, B_367)) | ~v2_tex_2(B_367, A_366) | ~m1_subset_1(B_367, k1_zfmisc_1(u1_struct_0(A_366))) | v1_xboole_0(B_367) | ~l1_pre_topc(A_366) | ~v2_pre_topc(A_366) | v2_struct_0(A_366))), inference(cnfTransformation, [status(thm)], [f_182])).
% 9.33/3.65  tff(c_12059, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_12031])).
% 9.33/3.65  tff(c_12075, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_11228, c_12059])).
% 9.33/3.65  tff(c_12076, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_62, c_54, c_12075])).
% 9.33/3.65  tff(c_11229, plain, (~v1_zfmisc_1('#skF_5')), inference(splitRight, [status(thm)], [c_70])).
% 9.33/3.65  tff(c_12543, plain, (![A_388, B_389]: (u1_struct_0('#skF_3'(A_388, B_389))=B_389 | ~v2_tex_2(B_389, A_388) | ~m1_subset_1(B_389, k1_zfmisc_1(u1_struct_0(A_388))) | v1_xboole_0(B_389) | ~l1_pre_topc(A_388) | ~v2_pre_topc(A_388) | v2_struct_0(A_388))), inference(cnfTransformation, [status(thm)], [f_182])).
% 9.33/3.65  tff(c_12571, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_12543])).
% 9.33/3.66  tff(c_12587, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_11228, c_12571])).
% 9.33/3.66  tff(c_12588, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_62, c_54, c_12587])).
% 9.33/3.66  tff(c_16, plain, (![A_13]: (v1_zfmisc_1(u1_struct_0(A_13)) | ~l1_struct_0(A_13) | ~v7_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.33/3.66  tff(c_12674, plain, (v1_zfmisc_1('#skF_5') | ~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_12588, c_16])).
% 9.33/3.66  tff(c_12720, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_11229, c_12674])).
% 9.33/3.66  tff(c_12722, plain, (~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_12720])).
% 9.33/3.66  tff(c_58, plain, (v2_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_214])).
% 9.33/3.66  tff(c_12218, plain, (![A_375, B_376]: (v1_tdlat_3('#skF_3'(A_375, B_376)) | ~v2_tex_2(B_376, A_375) | ~m1_subset_1(B_376, k1_zfmisc_1(u1_struct_0(A_375))) | v1_xboole_0(B_376) | ~l1_pre_topc(A_375) | ~v2_pre_topc(A_375) | v2_struct_0(A_375))), inference(cnfTransformation, [status(thm)], [f_182])).
% 9.33/3.66  tff(c_12246, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_12218])).
% 9.33/3.66  tff(c_12262, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_11228, c_12246])).
% 9.33/3.66  tff(c_12263, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_62, c_54, c_12262])).
% 9.33/3.66  tff(c_12725, plain, (![A_390, B_391]: (m1_pre_topc('#skF_3'(A_390, B_391), A_390) | ~v2_tex_2(B_391, A_390) | ~m1_subset_1(B_391, k1_zfmisc_1(u1_struct_0(A_390))) | v1_xboole_0(B_391) | ~l1_pre_topc(A_390) | ~v2_pre_topc(A_390) | v2_struct_0(A_390))), inference(cnfTransformation, [status(thm)], [f_182])).
% 9.33/3.66  tff(c_12747, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_12725])).
% 9.33/3.66  tff(c_12763, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_11228, c_12747])).
% 9.33/3.66  tff(c_12764, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_62, c_54, c_12763])).
% 9.33/3.66  tff(c_26, plain, (![B_28, A_26]: (~v1_tdlat_3(B_28) | v7_struct_0(B_28) | v2_struct_0(B_28) | ~m1_pre_topc(B_28, A_26) | ~l1_pre_topc(A_26) | ~v2_tdlat_3(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.33/3.66  tff(c_12768, plain, (~v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v7_struct_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_12764, c_26])).
% 9.33/3.66  tff(c_12774, plain, (v7_struct_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_12263, c_12768])).
% 9.33/3.66  tff(c_12776, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_12076, c_12722, c_12774])).
% 9.33/3.66  tff(c_12777, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_12720])).
% 9.33/3.66  tff(c_12782, plain, (~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_12, c_12777])).
% 9.33/3.66  tff(c_12785, plain, (![A_392, B_393]: (m1_pre_topc('#skF_3'(A_392, B_393), A_392) | ~v2_tex_2(B_393, A_392) | ~m1_subset_1(B_393, k1_zfmisc_1(u1_struct_0(A_392))) | v1_xboole_0(B_393) | ~l1_pre_topc(A_392) | ~v2_pre_topc(A_392) | v2_struct_0(A_392))), inference(cnfTransformation, [status(thm)], [f_182])).
% 9.33/3.66  tff(c_12807, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_12785])).
% 9.33/3.66  tff(c_12823, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_11228, c_12807])).
% 9.33/3.66  tff(c_12824, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_62, c_54, c_12823])).
% 9.33/3.66  tff(c_12831, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_12824, c_14])).
% 9.33/3.66  tff(c_12838, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_12831])).
% 9.33/3.66  tff(c_12840, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12782, c_12838])).
% 9.33/3.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.33/3.66  
% 9.33/3.66  Inference rules
% 9.33/3.66  ----------------------
% 9.33/3.66  #Ref     : 0
% 9.33/3.66  #Sup     : 2853
% 9.33/3.66  #Fact    : 0
% 9.33/3.66  #Define  : 0
% 9.33/3.66  #Split   : 26
% 9.33/3.66  #Chain   : 0
% 9.33/3.66  #Close   : 0
% 9.33/3.66  
% 9.33/3.66  Ordering : KBO
% 9.33/3.66  
% 9.33/3.66  Simplification rules
% 9.33/3.66  ----------------------
% 9.33/3.66  #Subsume      : 301
% 9.33/3.66  #Demod        : 3217
% 9.33/3.66  #Tautology    : 610
% 9.33/3.66  #SimpNegUnit  : 1063
% 9.33/3.66  #BackRed      : 5
% 9.33/3.66  
% 9.33/3.66  #Partial instantiations: 0
% 9.33/3.66  #Strategies tried      : 1
% 9.33/3.66  
% 9.33/3.66  Timing (in seconds)
% 9.33/3.66  ----------------------
% 9.33/3.66  Preprocessing        : 0.35
% 9.33/3.66  Parsing              : 0.19
% 9.33/3.66  CNF conversion       : 0.03
% 9.33/3.66  Main loop            : 2.52
% 9.33/3.66  Inferencing          : 0.62
% 9.33/3.66  Reduction            : 0.99
% 9.33/3.66  Demodulation         : 0.67
% 9.33/3.66  BG Simplification    : 0.08
% 9.33/3.66  Subsumption          : 0.68
% 9.33/3.66  Abstraction          : 0.11
% 9.33/3.66  MUC search           : 0.00
% 9.33/3.66  Cooper               : 0.00
% 9.33/3.66  Total                : 2.93
% 9.33/3.66  Index Insertion      : 0.00
% 9.33/3.66  Index Deletion       : 0.00
% 9.33/3.66  Index Matching       : 0.00
% 9.33/3.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
