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
% DateTime   : Thu Dec  3 10:29:55 EST 2020

% Result     : Theorem 10.82s
% Output     : CNFRefutation 11.21s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 940 expanded)
%              Number of leaves         :   44 ( 339 expanded)
%              Depth                    :   26
%              Number of atoms          :  463 (2876 expanded)
%              Number of equality atoms :   19 (  81 expanded)
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

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_128,axiom,(
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

tff(f_169,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_115,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_tdlat_3(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_tdlat_3(A)
       => v2_pre_topc(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(c_22,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_58,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_62,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_72,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_76,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_66,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_78,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_66])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_10] : ~ v1_xboole_0(k1_tarski(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_114,plain,(
    ! [A_58,B_59] :
      ( m1_subset_1(k1_tarski(A_58),k1_zfmisc_1(B_59))
      | ~ r2_hidden(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_118,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(k1_tarski(A_58),B_59)
      | ~ r2_hidden(A_58,B_59) ) ),
    inference(resolution,[status(thm)],[c_114,c_18])).

tff(c_217,plain,(
    ! [B_82,A_83] :
      ( B_82 = A_83
      | ~ r1_tarski(A_83,B_82)
      | ~ v1_zfmisc_1(B_82)
      | v1_xboole_0(B_82)
      | v1_xboole_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_229,plain,(
    ! [A_58,B_59] :
      ( k1_tarski(A_58) = B_59
      | ~ v1_zfmisc_1(B_59)
      | v1_xboole_0(B_59)
      | v1_xboole_0(k1_tarski(A_58))
      | ~ r2_hidden(A_58,B_59) ) ),
    inference(resolution,[status(thm)],[c_118,c_217])).

tff(c_278,plain,(
    ! [A_90,B_91] :
      ( k1_tarski(A_90) = B_91
      | ~ v1_zfmisc_1(B_91)
      | v1_xboole_0(B_91)
      | ~ r2_hidden(A_90,B_91) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_229])).

tff(c_290,plain,(
    ! [A_1] :
      ( k1_tarski('#skF_1'(A_1)) = A_1
      | ~ v1_zfmisc_1(A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_278])).

tff(c_121,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_2'(A_64,B_65),A_64)
      | r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_132,plain,(
    ! [A_64] : r1_tarski(A_64,A_64) ),
    inference(resolution,[status(thm)],[c_121,c_8])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_98,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(A_52,B_53)
      | ~ m1_subset_1(A_52,k1_zfmisc_1(B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_107,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_54,c_98])).

tff(c_135,plain,(
    ! [C_66,B_67,A_68] :
      ( r2_hidden(C_66,B_67)
      | ~ r2_hidden(C_66,A_68)
      | ~ r1_tarski(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_172,plain,(
    ! [A_77,B_78] :
      ( r2_hidden('#skF_1'(A_77),B_78)
      | ~ r1_tarski(A_77,B_78)
      | v1_xboole_0(A_77) ) ),
    inference(resolution,[status(thm)],[c_4,c_135])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_517,plain,(
    ! [A_123,B_124,B_125] :
      ( r2_hidden('#skF_1'(A_123),B_124)
      | ~ r1_tarski(B_125,B_124)
      | ~ r1_tarski(A_123,B_125)
      | v1_xboole_0(A_123) ) ),
    inference(resolution,[status(thm)],[c_172,c_6])).

tff(c_542,plain,(
    ! [A_126] :
      ( r2_hidden('#skF_1'(A_126),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_126,'#skF_5')
      | v1_xboole_0(A_126) ) ),
    inference(resolution,[status(thm)],[c_107,c_517])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,B_14)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_561,plain,(
    ! [A_126] :
      ( m1_subset_1('#skF_1'(A_126),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_126,'#skF_5')
      | v1_xboole_0(A_126) ) ),
    inference(resolution,[status(thm)],[c_542,c_16])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_184,plain,(
    ! [B_79,A_80] :
      ( ~ v1_xboole_0(B_79)
      | ~ r1_tarski(A_80,B_79)
      | v1_xboole_0(A_80) ) ),
    inference(resolution,[status(thm)],[c_172,c_2])).

tff(c_199,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_107,c_184])).

tff(c_207,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_199])).

tff(c_603,plain,(
    ! [A_129] :
      ( m1_subset_1('#skF_1'(A_129),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_129,'#skF_5')
      | v1_xboole_0(A_129) ) ),
    inference(resolution,[status(thm)],[c_542,c_16])).

tff(c_28,plain,(
    ! [A_22,B_23] :
      ( k6_domain_1(A_22,B_23) = k1_tarski(B_23)
      | ~ m1_subset_1(B_23,A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_606,plain,(
    ! [A_129] :
      ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'(A_129)) = k1_tarski('#skF_1'(A_129))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_129,'#skF_5')
      | v1_xboole_0(A_129) ) ),
    inference(resolution,[status(thm)],[c_603,c_28])).

tff(c_646,plain,(
    ! [A_134] :
      ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'(A_134)) = k1_tarski('#skF_1'(A_134))
      | ~ r1_tarski(A_134,'#skF_5')
      | v1_xboole_0(A_134) ) ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_606])).

tff(c_52,plain,(
    ! [A_38,B_40] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_38),B_40),A_38)
      | ~ m1_subset_1(B_40,u1_struct_0(A_38))
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_652,plain,(
    ! [A_134] :
      ( v2_tex_2(k1_tarski('#skF_1'(A_134)),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_134),u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_134,'#skF_5')
      | v1_xboole_0(A_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_646,c_52])).

tff(c_666,plain,(
    ! [A_134] :
      ( v2_tex_2(k1_tarski('#skF_1'(A_134)),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_134),u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_134,'#skF_5')
      | v1_xboole_0(A_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_652])).

tff(c_667,plain,(
    ! [A_134] :
      ( v2_tex_2(k1_tarski('#skF_1'(A_134)),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_134),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_134,'#skF_5')
      | v1_xboole_0(A_134) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_666])).

tff(c_141,plain,(
    ! [A_1,B_67] :
      ( r2_hidden('#skF_1'(A_1),B_67)
      | ~ r1_tarski(A_1,B_67)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_135])).

tff(c_903,plain,(
    ! [A_155,B_156] :
      ( k1_tarski('#skF_1'(A_155)) = B_156
      | ~ v1_zfmisc_1(B_156)
      | v1_xboole_0(B_156)
      | ~ r1_tarski(A_155,B_156)
      | v1_xboole_0(A_155) ) ),
    inference(resolution,[status(thm)],[c_141,c_278])).

tff(c_925,plain,(
    ! [A_58,B_59] :
      ( k1_tarski('#skF_1'(k1_tarski(A_58))) = B_59
      | ~ v1_zfmisc_1(B_59)
      | v1_xboole_0(B_59)
      | v1_xboole_0(k1_tarski(A_58))
      | ~ r2_hidden(A_58,B_59) ) ),
    inference(resolution,[status(thm)],[c_118,c_903])).

tff(c_944,plain,(
    ! [A_157,B_158] :
      ( k1_tarski('#skF_1'(k1_tarski(A_157))) = B_158
      | ~ v1_zfmisc_1(B_158)
      | v1_xboole_0(B_158)
      | ~ r2_hidden(A_157,B_158) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_925])).

tff(c_960,plain,(
    ! [A_1] :
      ( k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_1)))) = A_1
      | ~ v1_zfmisc_1(A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_944])).

tff(c_999,plain,(
    ! [A_160,B_161,A_162] :
      ( r2_hidden('#skF_1'(A_160),B_161)
      | ~ r1_tarski(A_160,k1_tarski(A_162))
      | v1_xboole_0(A_160)
      | ~ r2_hidden(A_162,B_161) ) ),
    inference(resolution,[status(thm)],[c_118,c_517])).

tff(c_1032,plain,(
    ! [A_162,B_161] :
      ( r2_hidden('#skF_1'(k1_tarski(A_162)),B_161)
      | v1_xboole_0(k1_tarski(A_162))
      | ~ r2_hidden(A_162,B_161) ) ),
    inference(resolution,[status(thm)],[c_132,c_999])).

tff(c_1050,plain,(
    ! [A_163,B_164] :
      ( r2_hidden('#skF_1'(k1_tarski(A_163)),B_164)
      | ~ r2_hidden(A_163,B_164) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_1032])).

tff(c_5777,plain,(
    ! [A_337,B_338] :
      ( r2_hidden('#skF_1'(A_337),B_338)
      | ~ r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_337))),B_338)
      | ~ v1_zfmisc_1(A_337)
      | v1_xboole_0(A_337) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_960,c_1050])).

tff(c_5841,plain,(
    ! [A_337] :
      ( r2_hidden('#skF_1'(A_337),k1_tarski('#skF_1'(A_337)))
      | ~ v1_zfmisc_1(A_337)
      | v1_xboole_0(A_337)
      | v1_xboole_0(k1_tarski('#skF_1'(A_337))) ) ),
    inference(resolution,[status(thm)],[c_4,c_5777])).

tff(c_5874,plain,(
    ! [A_339] :
      ( r2_hidden('#skF_1'(A_339),k1_tarski('#skF_1'(A_339)))
      | ~ v1_zfmisc_1(A_339)
      | v1_xboole_0(A_339) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_5841])).

tff(c_1035,plain,(
    ! [A_58,B_161,A_162] :
      ( r2_hidden('#skF_1'(k1_tarski(A_58)),B_161)
      | v1_xboole_0(k1_tarski(A_58))
      | ~ r2_hidden(A_162,B_161)
      | ~ r2_hidden(A_58,k1_tarski(A_162)) ) ),
    inference(resolution,[status(thm)],[c_118,c_999])).

tff(c_1349,plain,(
    ! [A_178,B_179,A_180] :
      ( r2_hidden('#skF_1'(k1_tarski(A_178)),B_179)
      | ~ r2_hidden(A_180,B_179)
      | ~ r2_hidden(A_178,k1_tarski(A_180)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_1035])).

tff(c_1370,plain,(
    ! [A_178,A_1] :
      ( r2_hidden('#skF_1'(k1_tarski(A_178)),A_1)
      | ~ r2_hidden(A_178,k1_tarski('#skF_1'(A_1)))
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_1349])).

tff(c_1217,plain,(
    ! [A_171,B_172,B_173] :
      ( r2_hidden('#skF_1'(k1_tarski(A_171)),B_172)
      | ~ r1_tarski(B_173,B_172)
      | ~ r2_hidden(A_171,B_173) ) ),
    inference(resolution,[status(thm)],[c_1050,c_6])).

tff(c_1256,plain,(
    ! [A_171] :
      ( r2_hidden('#skF_1'(k1_tarski(A_171)),u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_171,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_107,c_1217])).

tff(c_961,plain,(
    ! [A_159] :
      ( k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_159)))) = A_159
      | ~ v1_zfmisc_1(A_159)
      | v1_xboole_0(A_159) ) ),
    inference(resolution,[status(thm)],[c_4,c_944])).

tff(c_2518,plain,(
    ! [A_231,B_232] :
      ( r1_tarski(A_231,B_232)
      | ~ r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_231))),B_232)
      | ~ v1_zfmisc_1(A_231)
      | v1_xboole_0(A_231) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_961,c_118])).

tff(c_2626,plain,(
    ! [A_234] :
      ( r1_tarski(A_234,u1_struct_0('#skF_4'))
      | ~ v1_zfmisc_1(A_234)
      | v1_xboole_0(A_234)
      | ~ r2_hidden('#skF_1'(A_234),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1256,c_2518])).

tff(c_2642,plain,(
    ! [A_178] :
      ( r1_tarski(k1_tarski(A_178),u1_struct_0('#skF_4'))
      | ~ v1_zfmisc_1(k1_tarski(A_178))
      | v1_xboole_0(k1_tarski(A_178))
      | ~ r2_hidden(A_178,k1_tarski('#skF_1'('#skF_5')))
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1370,c_2626])).

tff(c_2663,plain,(
    ! [A_178] :
      ( r1_tarski(k1_tarski(A_178),u1_struct_0('#skF_4'))
      | ~ v1_zfmisc_1(k1_tarski(A_178))
      | ~ r2_hidden(A_178,k1_tarski('#skF_1'('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_12,c_2642])).

tff(c_5889,plain,
    ( r1_tarski(k1_tarski('#skF_1'('#skF_5')),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_5874,c_2663])).

tff(c_5941,plain,
    ( r1_tarski(k1_tarski('#skF_1'('#skF_5')),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_5889])).

tff(c_5942,plain,
    ( r1_tarski(k1_tarski('#skF_1'('#skF_5')),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_5941])).

tff(c_5963,plain,(
    ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_5942])).

tff(c_5966,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_5963])).

tff(c_5968,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_76,c_5966])).

tff(c_5970,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_5968])).

tff(c_5971,plain,(
    r1_tarski(k1_tarski('#skF_1'('#skF_5')),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_5942])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_444,plain,(
    ! [A_116,B_117] :
      ( v1_pre_topc('#skF_3'(A_116,B_117))
      | ~ v2_tex_2(B_117,A_116)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | v1_xboole_0(B_117)
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116)
      | v2_struct_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_478,plain,(
    ! [A_116,A_15] :
      ( v1_pre_topc('#skF_3'(A_116,A_15))
      | ~ v2_tex_2(A_15,A_116)
      | v1_xboole_0(A_15)
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116)
      | v2_struct_0(A_116)
      | ~ r1_tarski(A_15,u1_struct_0(A_116)) ) ),
    inference(resolution,[status(thm)],[c_20,c_444])).

tff(c_5990,plain,
    ( v1_pre_topc('#skF_3'('#skF_4',k1_tarski('#skF_1'('#skF_5'))))
    | ~ v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4')
    | v1_xboole_0(k1_tarski('#skF_1'('#skF_5')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_5971,c_478])).

tff(c_6030,plain,
    ( v1_pre_topc('#skF_3'('#skF_4',k1_tarski('#skF_1'('#skF_5'))))
    | ~ v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4')
    | v1_xboole_0(k1_tarski('#skF_1'('#skF_5')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_5990])).

tff(c_6031,plain,
    ( v1_pre_topc('#skF_3'('#skF_4',k1_tarski('#skF_1'('#skF_5'))))
    | ~ v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_12,c_6030])).

tff(c_6080,plain,(
    ~ v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_6031])).

tff(c_6157,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_667,c_6080])).

tff(c_6163,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_6157])).

tff(c_6164,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_6163])).

tff(c_6173,plain,
    ( ~ r1_tarski('#skF_5','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_561,c_6164])).

tff(c_6183,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_6173])).

tff(c_6185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_6183])).

tff(c_6187,plain,(
    v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_6031])).

tff(c_6190,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_6187])).

tff(c_6192,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_6190])).

tff(c_6194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_78,c_6192])).

tff(c_6195,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_7359,plain,(
    ! [A_468,B_469] :
      ( m1_pre_topc('#skF_3'(A_468,B_469),A_468)
      | ~ v2_tex_2(B_469,A_468)
      | ~ m1_subset_1(B_469,k1_zfmisc_1(u1_struct_0(A_468)))
      | v1_xboole_0(B_469)
      | ~ l1_pre_topc(A_468)
      | ~ v2_pre_topc(A_468)
      | v2_struct_0(A_468) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_7389,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_7359])).

tff(c_7407,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_6195,c_7389])).

tff(c_7408,plain,(
    m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_56,c_7407])).

tff(c_24,plain,(
    ! [B_20,A_18] :
      ( l1_pre_topc(B_20)
      | ~ m1_pre_topc(B_20,A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_7414,plain,
    ( l1_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_7408,c_24])).

tff(c_7421,plain,(
    l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_7414])).

tff(c_60,plain,(
    v2_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_38,plain,(
    ! [B_28,A_26] :
      ( v2_tdlat_3(B_28)
      | ~ m1_pre_topc(B_28,A_26)
      | ~ l1_pre_topc(A_26)
      | ~ v2_tdlat_3(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_7411,plain,
    ( v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_7408,c_38])).

tff(c_7417,plain,
    ( v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_7411])).

tff(c_7418,plain,(
    v2_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_7417])).

tff(c_30,plain,(
    ! [A_24] :
      ( v2_pre_topc(A_24)
      | ~ v2_tdlat_3(A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_7425,plain,
    ( v2_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_7418,c_30])).

tff(c_7428,plain,(
    v2_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7421,c_7425])).

tff(c_6637,plain,(
    ! [A_420,B_421] :
      ( ~ v2_struct_0('#skF_3'(A_420,B_421))
      | ~ v2_tex_2(B_421,A_420)
      | ~ m1_subset_1(B_421,k1_zfmisc_1(u1_struct_0(A_420)))
      | v1_xboole_0(B_421)
      | ~ l1_pre_topc(A_420)
      | ~ v2_pre_topc(A_420)
      | v2_struct_0(A_420) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_6664,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_6637])).

tff(c_6675,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_6195,c_6664])).

tff(c_6676,plain,(
    ~ v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_56,c_6675])).

tff(c_6519,plain,(
    ! [A_411,B_412] :
      ( v1_tdlat_3('#skF_3'(A_411,B_412))
      | ~ v2_tex_2(B_412,A_411)
      | ~ m1_subset_1(B_412,k1_zfmisc_1(u1_struct_0(A_411)))
      | v1_xboole_0(B_412)
      | ~ l1_pre_topc(A_411)
      | ~ v2_pre_topc(A_411)
      | v2_struct_0(A_411) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_6546,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_6519])).

tff(c_6557,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_6195,c_6546])).

tff(c_6558,plain,(
    v1_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_56,c_6557])).

tff(c_34,plain,(
    ! [A_25] :
      ( v7_struct_0(A_25)
      | ~ v2_tdlat_3(A_25)
      | ~ v1_tdlat_3(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_6196,plain,(
    ~ v1_zfmisc_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_7111,plain,(
    ! [A_456,B_457] :
      ( u1_struct_0('#skF_3'(A_456,B_457)) = B_457
      | ~ v2_tex_2(B_457,A_456)
      | ~ m1_subset_1(B_457,k1_zfmisc_1(u1_struct_0(A_456)))
      | v1_xboole_0(B_457)
      | ~ l1_pre_topc(A_456)
      | ~ v2_pre_topc(A_456)
      | v2_struct_0(A_456) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_7145,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_7111])).

tff(c_7161,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_6195,c_7145])).

tff(c_7162,plain,(
    u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_56,c_7161])).

tff(c_26,plain,(
    ! [A_21] :
      ( v1_zfmisc_1(u1_struct_0(A_21))
      | ~ l1_struct_0(A_21)
      | ~ v7_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_7181,plain,
    ( v1_zfmisc_1('#skF_5')
    | ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7162,c_26])).

tff(c_7190,plain,
    ( ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_6196,c_7181])).

tff(c_7192,plain,(
    ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_7190])).

tff(c_7195,plain,
    ( ~ v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_34,c_7192])).

tff(c_7198,plain,
    ( ~ v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6558,c_7195])).

tff(c_7199,plain,
    ( ~ v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_6676,c_7198])).

tff(c_7456,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7421,c_7428,c_7418,c_7199])).

tff(c_7457,plain,(
    ~ l1_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_7190])).

tff(c_7462,plain,(
    ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_22,c_7457])).

tff(c_7463,plain,(
    ! [A_472,B_473] :
      ( m1_pre_topc('#skF_3'(A_472,B_473),A_472)
      | ~ v2_tex_2(B_473,A_472)
      | ~ m1_subset_1(B_473,k1_zfmisc_1(u1_struct_0(A_472)))
      | v1_xboole_0(B_473)
      | ~ l1_pre_topc(A_472)
      | ~ v2_pre_topc(A_472)
      | v2_struct_0(A_472) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_7490,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_7463])).

tff(c_7507,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_6195,c_7490])).

tff(c_7508,plain,(
    m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_56,c_7507])).

tff(c_7514,plain,
    ( l1_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_7508,c_24])).

tff(c_7521,plain,(
    l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_7514])).

tff(c_7523,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7462,c_7521])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:41:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.82/3.94  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.82/3.96  
% 10.82/3.96  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.08/3.97  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 11.08/3.97  
% 11.08/3.97  %Foreground sorts:
% 11.08/3.97  
% 11.08/3.97  
% 11.08/3.97  %Background operators:
% 11.08/3.97  
% 11.08/3.97  
% 11.08/3.97  %Foreground operators:
% 11.08/3.97  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.08/3.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.08/3.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.08/3.97  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.08/3.97  tff('#skF_1', type, '#skF_1': $i > $i).
% 11.08/3.97  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 11.08/3.97  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.08/3.97  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 11.08/3.97  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.08/3.97  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 11.08/3.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.08/3.97  tff('#skF_5', type, '#skF_5': $i).
% 11.08/3.97  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 11.08/3.97  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 11.08/3.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.08/3.97  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 11.08/3.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.08/3.97  tff('#skF_4', type, '#skF_4': $i).
% 11.08/3.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.08/3.97  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.08/3.97  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 11.08/3.97  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 11.08/3.97  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.08/3.97  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.08/3.97  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.08/3.97  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 11.08/3.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.08/3.97  
% 11.21/4.00  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 11.21/4.00  tff(f_189, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 11.21/4.00  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 11.21/4.00  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 11.21/4.00  tff(f_45, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 11.21/4.00  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 11.21/4.00  tff(f_128, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 11.21/4.00  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 11.21/4.00  tff(f_49, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 11.21/4.00  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 11.21/4.00  tff(f_169, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 11.21/4.00  tff(f_157, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tex_2)).
% 11.21/4.00  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 11.21/4.00  tff(f_115, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_tdlat_3(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_tdlat_3)).
% 11.21/4.00  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (v2_tdlat_3(A) => v2_pre_topc(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tdlat_3)).
% 11.21/4.00  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & v2_tdlat_3(A)) => ((~v2_struct_0(A) & v7_struct_0(A)) & v2_pre_topc(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_1)).
% 11.21/4.00  tff(f_70, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 11.21/4.00  tff(c_22, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.21/4.00  tff(c_58, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_189])).
% 11.21/4.00  tff(c_64, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_189])).
% 11.21/4.00  tff(c_56, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_189])).
% 11.21/4.00  tff(c_62, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_189])).
% 11.21/4.00  tff(c_72, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_189])).
% 11.21/4.00  tff(c_76, plain, (v1_zfmisc_1('#skF_5')), inference(splitLeft, [status(thm)], [c_72])).
% 11.21/4.00  tff(c_66, plain, (~v1_zfmisc_1('#skF_5') | ~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_189])).
% 11.21/4.00  tff(c_78, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_66])).
% 11.21/4.00  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.21/4.00  tff(c_12, plain, (![A_10]: (~v1_xboole_0(k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.21/4.00  tff(c_114, plain, (![A_58, B_59]: (m1_subset_1(k1_tarski(A_58), k1_zfmisc_1(B_59)) | ~r2_hidden(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.21/4.00  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.21/4.00  tff(c_118, plain, (![A_58, B_59]: (r1_tarski(k1_tarski(A_58), B_59) | ~r2_hidden(A_58, B_59))), inference(resolution, [status(thm)], [c_114, c_18])).
% 11.21/4.00  tff(c_217, plain, (![B_82, A_83]: (B_82=A_83 | ~r1_tarski(A_83, B_82) | ~v1_zfmisc_1(B_82) | v1_xboole_0(B_82) | v1_xboole_0(A_83))), inference(cnfTransformation, [status(thm)], [f_128])).
% 11.21/4.00  tff(c_229, plain, (![A_58, B_59]: (k1_tarski(A_58)=B_59 | ~v1_zfmisc_1(B_59) | v1_xboole_0(B_59) | v1_xboole_0(k1_tarski(A_58)) | ~r2_hidden(A_58, B_59))), inference(resolution, [status(thm)], [c_118, c_217])).
% 11.21/4.00  tff(c_278, plain, (![A_90, B_91]: (k1_tarski(A_90)=B_91 | ~v1_zfmisc_1(B_91) | v1_xboole_0(B_91) | ~r2_hidden(A_90, B_91))), inference(negUnitSimplification, [status(thm)], [c_12, c_229])).
% 11.21/4.00  tff(c_290, plain, (![A_1]: (k1_tarski('#skF_1'(A_1))=A_1 | ~v1_zfmisc_1(A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_278])).
% 11.21/4.00  tff(c_121, plain, (![A_64, B_65]: (r2_hidden('#skF_2'(A_64, B_65), A_64) | r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.21/4.00  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.21/4.00  tff(c_132, plain, (![A_64]: (r1_tarski(A_64, A_64))), inference(resolution, [status(thm)], [c_121, c_8])).
% 11.21/4.00  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_189])).
% 11.21/4.00  tff(c_98, plain, (![A_52, B_53]: (r1_tarski(A_52, B_53) | ~m1_subset_1(A_52, k1_zfmisc_1(B_53)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.21/4.00  tff(c_107, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_98])).
% 11.21/4.00  tff(c_135, plain, (![C_66, B_67, A_68]: (r2_hidden(C_66, B_67) | ~r2_hidden(C_66, A_68) | ~r1_tarski(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.21/4.00  tff(c_172, plain, (![A_77, B_78]: (r2_hidden('#skF_1'(A_77), B_78) | ~r1_tarski(A_77, B_78) | v1_xboole_0(A_77))), inference(resolution, [status(thm)], [c_4, c_135])).
% 11.21/4.00  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.21/4.00  tff(c_517, plain, (![A_123, B_124, B_125]: (r2_hidden('#skF_1'(A_123), B_124) | ~r1_tarski(B_125, B_124) | ~r1_tarski(A_123, B_125) | v1_xboole_0(A_123))), inference(resolution, [status(thm)], [c_172, c_6])).
% 11.21/4.00  tff(c_542, plain, (![A_126]: (r2_hidden('#skF_1'(A_126), u1_struct_0('#skF_4')) | ~r1_tarski(A_126, '#skF_5') | v1_xboole_0(A_126))), inference(resolution, [status(thm)], [c_107, c_517])).
% 11.21/4.00  tff(c_16, plain, (![A_13, B_14]: (m1_subset_1(A_13, B_14) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.21/4.00  tff(c_561, plain, (![A_126]: (m1_subset_1('#skF_1'(A_126), u1_struct_0('#skF_4')) | ~r1_tarski(A_126, '#skF_5') | v1_xboole_0(A_126))), inference(resolution, [status(thm)], [c_542, c_16])).
% 11.21/4.00  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.21/4.00  tff(c_184, plain, (![B_79, A_80]: (~v1_xboole_0(B_79) | ~r1_tarski(A_80, B_79) | v1_xboole_0(A_80))), inference(resolution, [status(thm)], [c_172, c_2])).
% 11.21/4.00  tff(c_199, plain, (~v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_107, c_184])).
% 11.21/4.01  tff(c_207, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_56, c_199])).
% 11.21/4.01  tff(c_603, plain, (![A_129]: (m1_subset_1('#skF_1'(A_129), u1_struct_0('#skF_4')) | ~r1_tarski(A_129, '#skF_5') | v1_xboole_0(A_129))), inference(resolution, [status(thm)], [c_542, c_16])).
% 11.21/4.01  tff(c_28, plain, (![A_22, B_23]: (k6_domain_1(A_22, B_23)=k1_tarski(B_23) | ~m1_subset_1(B_23, A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.21/4.01  tff(c_606, plain, (![A_129]: (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'(A_129))=k1_tarski('#skF_1'(A_129)) | v1_xboole_0(u1_struct_0('#skF_4')) | ~r1_tarski(A_129, '#skF_5') | v1_xboole_0(A_129))), inference(resolution, [status(thm)], [c_603, c_28])).
% 11.21/4.01  tff(c_646, plain, (![A_134]: (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'(A_134))=k1_tarski('#skF_1'(A_134)) | ~r1_tarski(A_134, '#skF_5') | v1_xboole_0(A_134))), inference(negUnitSimplification, [status(thm)], [c_207, c_606])).
% 11.21/4.01  tff(c_52, plain, (![A_38, B_40]: (v2_tex_2(k6_domain_1(u1_struct_0(A_38), B_40), A_38) | ~m1_subset_1(B_40, u1_struct_0(A_38)) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_169])).
% 11.21/4.01  tff(c_652, plain, (![A_134]: (v2_tex_2(k1_tarski('#skF_1'(A_134)), '#skF_4') | ~m1_subset_1('#skF_1'(A_134), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(A_134, '#skF_5') | v1_xboole_0(A_134))), inference(superposition, [status(thm), theory('equality')], [c_646, c_52])).
% 11.21/4.01  tff(c_666, plain, (![A_134]: (v2_tex_2(k1_tarski('#skF_1'(A_134)), '#skF_4') | ~m1_subset_1('#skF_1'(A_134), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | ~r1_tarski(A_134, '#skF_5') | v1_xboole_0(A_134))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_652])).
% 11.21/4.01  tff(c_667, plain, (![A_134]: (v2_tex_2(k1_tarski('#skF_1'(A_134)), '#skF_4') | ~m1_subset_1('#skF_1'(A_134), u1_struct_0('#skF_4')) | ~r1_tarski(A_134, '#skF_5') | v1_xboole_0(A_134))), inference(negUnitSimplification, [status(thm)], [c_64, c_666])).
% 11.21/4.01  tff(c_141, plain, (![A_1, B_67]: (r2_hidden('#skF_1'(A_1), B_67) | ~r1_tarski(A_1, B_67) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_135])).
% 11.21/4.01  tff(c_903, plain, (![A_155, B_156]: (k1_tarski('#skF_1'(A_155))=B_156 | ~v1_zfmisc_1(B_156) | v1_xboole_0(B_156) | ~r1_tarski(A_155, B_156) | v1_xboole_0(A_155))), inference(resolution, [status(thm)], [c_141, c_278])).
% 11.21/4.01  tff(c_925, plain, (![A_58, B_59]: (k1_tarski('#skF_1'(k1_tarski(A_58)))=B_59 | ~v1_zfmisc_1(B_59) | v1_xboole_0(B_59) | v1_xboole_0(k1_tarski(A_58)) | ~r2_hidden(A_58, B_59))), inference(resolution, [status(thm)], [c_118, c_903])).
% 11.21/4.01  tff(c_944, plain, (![A_157, B_158]: (k1_tarski('#skF_1'(k1_tarski(A_157)))=B_158 | ~v1_zfmisc_1(B_158) | v1_xboole_0(B_158) | ~r2_hidden(A_157, B_158))), inference(negUnitSimplification, [status(thm)], [c_12, c_925])).
% 11.21/4.01  tff(c_960, plain, (![A_1]: (k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_1))))=A_1 | ~v1_zfmisc_1(A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_944])).
% 11.21/4.01  tff(c_999, plain, (![A_160, B_161, A_162]: (r2_hidden('#skF_1'(A_160), B_161) | ~r1_tarski(A_160, k1_tarski(A_162)) | v1_xboole_0(A_160) | ~r2_hidden(A_162, B_161))), inference(resolution, [status(thm)], [c_118, c_517])).
% 11.21/4.01  tff(c_1032, plain, (![A_162, B_161]: (r2_hidden('#skF_1'(k1_tarski(A_162)), B_161) | v1_xboole_0(k1_tarski(A_162)) | ~r2_hidden(A_162, B_161))), inference(resolution, [status(thm)], [c_132, c_999])).
% 11.21/4.01  tff(c_1050, plain, (![A_163, B_164]: (r2_hidden('#skF_1'(k1_tarski(A_163)), B_164) | ~r2_hidden(A_163, B_164))), inference(negUnitSimplification, [status(thm)], [c_12, c_1032])).
% 11.21/4.01  tff(c_5777, plain, (![A_337, B_338]: (r2_hidden('#skF_1'(A_337), B_338) | ~r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_337))), B_338) | ~v1_zfmisc_1(A_337) | v1_xboole_0(A_337))), inference(superposition, [status(thm), theory('equality')], [c_960, c_1050])).
% 11.21/4.01  tff(c_5841, plain, (![A_337]: (r2_hidden('#skF_1'(A_337), k1_tarski('#skF_1'(A_337))) | ~v1_zfmisc_1(A_337) | v1_xboole_0(A_337) | v1_xboole_0(k1_tarski('#skF_1'(A_337))))), inference(resolution, [status(thm)], [c_4, c_5777])).
% 11.21/4.01  tff(c_5874, plain, (![A_339]: (r2_hidden('#skF_1'(A_339), k1_tarski('#skF_1'(A_339))) | ~v1_zfmisc_1(A_339) | v1_xboole_0(A_339))), inference(negUnitSimplification, [status(thm)], [c_12, c_5841])).
% 11.21/4.01  tff(c_1035, plain, (![A_58, B_161, A_162]: (r2_hidden('#skF_1'(k1_tarski(A_58)), B_161) | v1_xboole_0(k1_tarski(A_58)) | ~r2_hidden(A_162, B_161) | ~r2_hidden(A_58, k1_tarski(A_162)))), inference(resolution, [status(thm)], [c_118, c_999])).
% 11.21/4.01  tff(c_1349, plain, (![A_178, B_179, A_180]: (r2_hidden('#skF_1'(k1_tarski(A_178)), B_179) | ~r2_hidden(A_180, B_179) | ~r2_hidden(A_178, k1_tarski(A_180)))), inference(negUnitSimplification, [status(thm)], [c_12, c_1035])).
% 11.21/4.01  tff(c_1370, plain, (![A_178, A_1]: (r2_hidden('#skF_1'(k1_tarski(A_178)), A_1) | ~r2_hidden(A_178, k1_tarski('#skF_1'(A_1))) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_1349])).
% 11.21/4.01  tff(c_1217, plain, (![A_171, B_172, B_173]: (r2_hidden('#skF_1'(k1_tarski(A_171)), B_172) | ~r1_tarski(B_173, B_172) | ~r2_hidden(A_171, B_173))), inference(resolution, [status(thm)], [c_1050, c_6])).
% 11.21/4.01  tff(c_1256, plain, (![A_171]: (r2_hidden('#skF_1'(k1_tarski(A_171)), u1_struct_0('#skF_4')) | ~r2_hidden(A_171, '#skF_5'))), inference(resolution, [status(thm)], [c_107, c_1217])).
% 11.21/4.01  tff(c_961, plain, (![A_159]: (k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_159))))=A_159 | ~v1_zfmisc_1(A_159) | v1_xboole_0(A_159))), inference(resolution, [status(thm)], [c_4, c_944])).
% 11.21/4.01  tff(c_2518, plain, (![A_231, B_232]: (r1_tarski(A_231, B_232) | ~r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_231))), B_232) | ~v1_zfmisc_1(A_231) | v1_xboole_0(A_231))), inference(superposition, [status(thm), theory('equality')], [c_961, c_118])).
% 11.21/4.01  tff(c_2626, plain, (![A_234]: (r1_tarski(A_234, u1_struct_0('#skF_4')) | ~v1_zfmisc_1(A_234) | v1_xboole_0(A_234) | ~r2_hidden('#skF_1'(A_234), '#skF_5'))), inference(resolution, [status(thm)], [c_1256, c_2518])).
% 11.21/4.01  tff(c_2642, plain, (![A_178]: (r1_tarski(k1_tarski(A_178), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski(A_178)) | v1_xboole_0(k1_tarski(A_178)) | ~r2_hidden(A_178, k1_tarski('#skF_1'('#skF_5'))) | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_1370, c_2626])).
% 11.21/4.01  tff(c_2663, plain, (![A_178]: (r1_tarski(k1_tarski(A_178), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski(A_178)) | ~r2_hidden(A_178, k1_tarski('#skF_1'('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_12, c_2642])).
% 11.21/4.01  tff(c_5889, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_5874, c_2663])).
% 11.21/4.01  tff(c_5941, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_5889])).
% 11.21/4.01  tff(c_5942, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_56, c_5941])).
% 11.21/4.01  tff(c_5963, plain, (~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))), inference(splitLeft, [status(thm)], [c_5942])).
% 11.21/4.01  tff(c_5966, plain, (~v1_zfmisc_1('#skF_5') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_290, c_5963])).
% 11.21/4.01  tff(c_5968, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_76, c_5966])).
% 11.21/4.01  tff(c_5970, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_5968])).
% 11.21/4.01  tff(c_5971, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_5942])).
% 11.21/4.01  tff(c_20, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.21/4.01  tff(c_444, plain, (![A_116, B_117]: (v1_pre_topc('#skF_3'(A_116, B_117)) | ~v2_tex_2(B_117, A_116) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | v1_xboole_0(B_117) | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116) | v2_struct_0(A_116))), inference(cnfTransformation, [status(thm)], [f_157])).
% 11.21/4.01  tff(c_478, plain, (![A_116, A_15]: (v1_pre_topc('#skF_3'(A_116, A_15)) | ~v2_tex_2(A_15, A_116) | v1_xboole_0(A_15) | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116) | v2_struct_0(A_116) | ~r1_tarski(A_15, u1_struct_0(A_116)))), inference(resolution, [status(thm)], [c_20, c_444])).
% 11.21/4.01  tff(c_5990, plain, (v1_pre_topc('#skF_3'('#skF_4', k1_tarski('#skF_1'('#skF_5')))) | ~v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4') | v1_xboole_0(k1_tarski('#skF_1'('#skF_5'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_5971, c_478])).
% 11.21/4.01  tff(c_6030, plain, (v1_pre_topc('#skF_3'('#skF_4', k1_tarski('#skF_1'('#skF_5')))) | ~v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4') | v1_xboole_0(k1_tarski('#skF_1'('#skF_5'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_5990])).
% 11.21/4.01  tff(c_6031, plain, (v1_pre_topc('#skF_3'('#skF_4', k1_tarski('#skF_1'('#skF_5')))) | ~v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_64, c_12, c_6030])).
% 11.21/4.01  tff(c_6080, plain, (~v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_6031])).
% 11.21/4.01  tff(c_6157, plain, (~m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | ~r1_tarski('#skF_5', '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_667, c_6080])).
% 11.21/4.01  tff(c_6163, plain, (~m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_6157])).
% 11.21/4.01  tff(c_6164, plain, (~m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_56, c_6163])).
% 11.21/4.01  tff(c_6173, plain, (~r1_tarski('#skF_5', '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_561, c_6164])).
% 11.21/4.01  tff(c_6183, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_6173])).
% 11.21/4.01  tff(c_6185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_6183])).
% 11.21/4.01  tff(c_6187, plain, (v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4')), inference(splitRight, [status(thm)], [c_6031])).
% 11.21/4.01  tff(c_6190, plain, (v2_tex_2('#skF_5', '#skF_4') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_290, c_6187])).
% 11.21/4.01  tff(c_6192, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_6190])).
% 11.21/4.01  tff(c_6194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_78, c_6192])).
% 11.21/4.01  tff(c_6195, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_72])).
% 11.21/4.01  tff(c_7359, plain, (![A_468, B_469]: (m1_pre_topc('#skF_3'(A_468, B_469), A_468) | ~v2_tex_2(B_469, A_468) | ~m1_subset_1(B_469, k1_zfmisc_1(u1_struct_0(A_468))) | v1_xboole_0(B_469) | ~l1_pre_topc(A_468) | ~v2_pre_topc(A_468) | v2_struct_0(A_468))), inference(cnfTransformation, [status(thm)], [f_157])).
% 11.21/4.01  tff(c_7389, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_7359])).
% 11.21/4.01  tff(c_7407, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_6195, c_7389])).
% 11.21/4.01  tff(c_7408, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_64, c_56, c_7407])).
% 11.21/4.01  tff(c_24, plain, (![B_20, A_18]: (l1_pre_topc(B_20) | ~m1_pre_topc(B_20, A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.21/4.01  tff(c_7414, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_7408, c_24])).
% 11.21/4.01  tff(c_7421, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_7414])).
% 11.21/4.01  tff(c_60, plain, (v2_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_189])).
% 11.21/4.01  tff(c_38, plain, (![B_28, A_26]: (v2_tdlat_3(B_28) | ~m1_pre_topc(B_28, A_26) | ~l1_pre_topc(A_26) | ~v2_tdlat_3(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.21/4.01  tff(c_7411, plain, (v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_7408, c_38])).
% 11.21/4.01  tff(c_7417, plain, (v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_7411])).
% 11.21/4.01  tff(c_7418, plain, (v2_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_7417])).
% 11.21/4.01  tff(c_30, plain, (![A_24]: (v2_pre_topc(A_24) | ~v2_tdlat_3(A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.21/4.01  tff(c_7425, plain, (v2_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_7418, c_30])).
% 11.21/4.01  tff(c_7428, plain, (v2_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_7421, c_7425])).
% 11.21/4.01  tff(c_6637, plain, (![A_420, B_421]: (~v2_struct_0('#skF_3'(A_420, B_421)) | ~v2_tex_2(B_421, A_420) | ~m1_subset_1(B_421, k1_zfmisc_1(u1_struct_0(A_420))) | v1_xboole_0(B_421) | ~l1_pre_topc(A_420) | ~v2_pre_topc(A_420) | v2_struct_0(A_420))), inference(cnfTransformation, [status(thm)], [f_157])).
% 11.21/4.01  tff(c_6664, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_6637])).
% 11.21/4.01  tff(c_6675, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_6195, c_6664])).
% 11.21/4.01  tff(c_6676, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_56, c_6675])).
% 11.21/4.01  tff(c_6519, plain, (![A_411, B_412]: (v1_tdlat_3('#skF_3'(A_411, B_412)) | ~v2_tex_2(B_412, A_411) | ~m1_subset_1(B_412, k1_zfmisc_1(u1_struct_0(A_411))) | v1_xboole_0(B_412) | ~l1_pre_topc(A_411) | ~v2_pre_topc(A_411) | v2_struct_0(A_411))), inference(cnfTransformation, [status(thm)], [f_157])).
% 11.21/4.01  tff(c_6546, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_6519])).
% 11.21/4.01  tff(c_6557, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_6195, c_6546])).
% 11.21/4.01  tff(c_6558, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_56, c_6557])).
% 11.21/4.01  tff(c_34, plain, (![A_25]: (v7_struct_0(A_25) | ~v2_tdlat_3(A_25) | ~v1_tdlat_3(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.21/4.01  tff(c_6196, plain, (~v1_zfmisc_1('#skF_5')), inference(splitRight, [status(thm)], [c_72])).
% 11.21/4.01  tff(c_7111, plain, (![A_456, B_457]: (u1_struct_0('#skF_3'(A_456, B_457))=B_457 | ~v2_tex_2(B_457, A_456) | ~m1_subset_1(B_457, k1_zfmisc_1(u1_struct_0(A_456))) | v1_xboole_0(B_457) | ~l1_pre_topc(A_456) | ~v2_pre_topc(A_456) | v2_struct_0(A_456))), inference(cnfTransformation, [status(thm)], [f_157])).
% 11.21/4.01  tff(c_7145, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_7111])).
% 11.21/4.01  tff(c_7161, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_6195, c_7145])).
% 11.21/4.01  tff(c_7162, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_64, c_56, c_7161])).
% 11.21/4.01  tff(c_26, plain, (![A_21]: (v1_zfmisc_1(u1_struct_0(A_21)) | ~l1_struct_0(A_21) | ~v7_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.21/4.01  tff(c_7181, plain, (v1_zfmisc_1('#skF_5') | ~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_7162, c_26])).
% 11.21/4.01  tff(c_7190, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_6196, c_7181])).
% 11.21/4.01  tff(c_7192, plain, (~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_7190])).
% 11.21/4.01  tff(c_7195, plain, (~v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_34, c_7192])).
% 11.21/4.01  tff(c_7198, plain, (~v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_6558, c_7195])).
% 11.21/4.01  tff(c_7199, plain, (~v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_6676, c_7198])).
% 11.21/4.01  tff(c_7456, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7421, c_7428, c_7418, c_7199])).
% 11.21/4.01  tff(c_7457, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_7190])).
% 11.21/4.01  tff(c_7462, plain, (~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_22, c_7457])).
% 11.21/4.01  tff(c_7463, plain, (![A_472, B_473]: (m1_pre_topc('#skF_3'(A_472, B_473), A_472) | ~v2_tex_2(B_473, A_472) | ~m1_subset_1(B_473, k1_zfmisc_1(u1_struct_0(A_472))) | v1_xboole_0(B_473) | ~l1_pre_topc(A_472) | ~v2_pre_topc(A_472) | v2_struct_0(A_472))), inference(cnfTransformation, [status(thm)], [f_157])).
% 11.21/4.01  tff(c_7490, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_7463])).
% 11.21/4.01  tff(c_7507, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_6195, c_7490])).
% 11.21/4.01  tff(c_7508, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_64, c_56, c_7507])).
% 11.21/4.01  tff(c_7514, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_7508, c_24])).
% 11.21/4.01  tff(c_7521, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_7514])).
% 11.21/4.01  tff(c_7523, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7462, c_7521])).
% 11.21/4.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.21/4.01  
% 11.21/4.01  Inference rules
% 11.21/4.01  ----------------------
% 11.21/4.01  #Ref     : 0
% 11.21/4.01  #Sup     : 1705
% 11.21/4.01  #Fact    : 0
% 11.21/4.01  #Define  : 0
% 11.21/4.01  #Split   : 12
% 11.21/4.01  #Chain   : 0
% 11.21/4.01  #Close   : 0
% 11.21/4.01  
% 11.21/4.01  Ordering : KBO
% 11.21/4.01  
% 11.21/4.01  Simplification rules
% 11.21/4.01  ----------------------
% 11.21/4.01  #Subsume      : 360
% 11.21/4.01  #Demod        : 194
% 11.21/4.01  #Tautology    : 159
% 11.21/4.01  #SimpNegUnit  : 369
% 11.21/4.01  #BackRed      : 0
% 11.21/4.01  
% 11.21/4.01  #Partial instantiations: 0
% 11.21/4.01  #Strategies tried      : 1
% 11.21/4.01  
% 11.21/4.01  Timing (in seconds)
% 11.21/4.01  ----------------------
% 11.21/4.01  Preprocessing        : 0.54
% 11.21/4.01  Parsing              : 0.28
% 11.21/4.01  CNF conversion       : 0.04
% 11.21/4.01  Main loop            : 2.51
% 11.21/4.01  Inferencing          : 0.81
% 11.21/4.01  Reduction            : 0.66
% 11.21/4.01  Demodulation         : 0.38
% 11.21/4.01  BG Simplification    : 0.10
% 11.21/4.01  Subsumption          : 0.71
% 11.21/4.01  Abstraction          : 0.13
% 11.21/4.01  MUC search           : 0.00
% 11.21/4.01  Cooper               : 0.00
% 11.21/4.01  Total                : 3.14
% 11.21/4.01  Index Insertion      : 0.00
% 11.21/4.01  Index Deletion       : 0.00
% 11.21/4.01  Index Matching       : 0.00
% 11.21/4.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
