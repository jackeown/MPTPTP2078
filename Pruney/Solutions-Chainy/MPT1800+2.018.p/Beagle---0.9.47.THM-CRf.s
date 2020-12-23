%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:00 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 140 expanded)
%              Number of leaves         :   26 (  61 expanded)
%              Depth                    :   14
%              Number of atoms          :  265 ( 567 expanded)
%              Number of equality atoms :   41 (  72 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k8_tmap_1 > k6_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k8_tmap_1,type,(
    k8_tmap_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ( ( v1_tsep_1(B,A)
                & m1_pre_topc(B,A) )
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k8_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_tmap_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B))
        & l1_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_51,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( ( v1_pre_topc(C)
                & v2_pre_topc(C)
                & l1_pre_topc(C) )
             => ( C = k8_tmap_1(A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( D = u1_struct_0(B)
                     => C = k6_tmap_1(A,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_tmap_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_tsep_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

tff(c_28,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_34,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_10,plain,(
    ! [A_23,B_24] :
      ( l1_pre_topc(k8_tmap_1(A_23,B_24))
      | ~ m1_pre_topc(B_24,A_23)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14,plain,(
    ! [A_23,B_24] :
      ( v1_pre_topc(k8_tmap_1(A_23,B_24))
      | ~ m1_pre_topc(B_24,A_23)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_12,plain,(
    ! [A_23,B_24] :
      ( v2_pre_topc(k8_tmap_1(A_23,B_24))
      | ~ m1_pre_topc(B_24,A_23)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,(
    ! [B_37,A_35] :
      ( m1_subset_1(u1_struct_0(B_37),k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ m1_pre_topc(B_37,A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_311,plain,(
    ! [A_83,B_84] :
      ( k6_tmap_1(A_83,u1_struct_0(B_84)) = k8_tmap_1(A_83,B_84)
      | ~ m1_subset_1(u1_struct_0(B_84),k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(k8_tmap_1(A_83,B_84))
      | ~ v2_pre_topc(k8_tmap_1(A_83,B_84))
      | ~ v1_pre_topc(k8_tmap_1(A_83,B_84))
      | ~ m1_pre_topc(B_84,A_83)
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_316,plain,(
    ! [A_85,B_86] :
      ( k6_tmap_1(A_85,u1_struct_0(B_86)) = k8_tmap_1(A_85,B_86)
      | ~ l1_pre_topc(k8_tmap_1(A_85,B_86))
      | ~ v2_pre_topc(k8_tmap_1(A_85,B_86))
      | ~ v1_pre_topc(k8_tmap_1(A_85,B_86))
      | ~ v2_pre_topc(A_85)
      | v2_struct_0(A_85)
      | ~ m1_pre_topc(B_86,A_85)
      | ~ l1_pre_topc(A_85) ) ),
    inference(resolution,[status(thm)],[c_26,c_311])).

tff(c_321,plain,(
    ! [A_87,B_88] :
      ( k6_tmap_1(A_87,u1_struct_0(B_88)) = k8_tmap_1(A_87,B_88)
      | ~ l1_pre_topc(k8_tmap_1(A_87,B_88))
      | ~ v1_pre_topc(k8_tmap_1(A_87,B_88))
      | ~ m1_pre_topc(B_88,A_87)
      | ~ l1_pre_topc(A_87)
      | ~ v2_pre_topc(A_87)
      | v2_struct_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_12,c_316])).

tff(c_326,plain,(
    ! [A_89,B_90] :
      ( k6_tmap_1(A_89,u1_struct_0(B_90)) = k8_tmap_1(A_89,B_90)
      | ~ l1_pre_topc(k8_tmap_1(A_89,B_90))
      | ~ m1_pre_topc(B_90,A_89)
      | ~ l1_pre_topc(A_89)
      | ~ v2_pre_topc(A_89)
      | v2_struct_0(A_89) ) ),
    inference(resolution,[status(thm)],[c_14,c_321])).

tff(c_331,plain,(
    ! [A_91,B_92] :
      ( k6_tmap_1(A_91,u1_struct_0(B_92)) = k8_tmap_1(A_91,B_92)
      | ~ m1_pre_topc(B_92,A_91)
      | ~ l1_pre_topc(A_91)
      | ~ v2_pre_topc(A_91)
      | v2_struct_0(A_91) ) ),
    inference(resolution,[status(thm)],[c_10,c_326])).

tff(c_48,plain,
    ( v1_tsep_1('#skF_3','#skF_2')
    | g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k8_tmap_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_52,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k8_tmap_1('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_74,plain,(
    ! [B_53,A_54] :
      ( v3_pre_topc(B_53,A_54)
      | k6_tmap_1(A_54,B_53) != g1_pre_topc(u1_struct_0(A_54),u1_pre_topc(A_54))
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54)
      | ~ v2_pre_topc(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_76,plain,(
    ! [B_53] :
      ( v3_pre_topc(B_53,'#skF_2')
      | k8_tmap_1('#skF_2','#skF_3') != k6_tmap_1('#skF_2',B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_74])).

tff(c_78,plain,(
    ! [B_53] :
      ( v3_pre_topc(B_53,'#skF_2')
      | k8_tmap_1('#skF_2','#skF_3') != k6_tmap_1('#skF_2',B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_76])).

tff(c_85,plain,(
    ! [B_57] :
      ( v3_pre_topc(B_57,'#skF_2')
      | k8_tmap_1('#skF_2','#skF_3') != k6_tmap_1('#skF_2',B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_78])).

tff(c_89,plain,(
    ! [B_37] :
      ( v3_pre_topc(u1_struct_0(B_37),'#skF_2')
      | k6_tmap_1('#skF_2',u1_struct_0(B_37)) != k8_tmap_1('#skF_2','#skF_3')
      | ~ m1_pre_topc(B_37,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_85])).

tff(c_93,plain,(
    ! [B_58] :
      ( v3_pre_topc(u1_struct_0(B_58),'#skF_2')
      | k6_tmap_1('#skF_2',u1_struct_0(B_58)) != k8_tmap_1('#skF_2','#skF_3')
      | ~ m1_pre_topc(B_58,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_89])).

tff(c_63,plain,(
    ! [B_47,A_48] :
      ( v1_tsep_1(B_47,A_48)
      | ~ v3_pre_topc(u1_struct_0(B_47),A_48)
      | ~ m1_subset_1(u1_struct_0(B_47),k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ m1_pre_topc(B_47,A_48)
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_67,plain,(
    ! [B_37,A_35] :
      ( v1_tsep_1(B_37,A_35)
      | ~ v3_pre_topc(u1_struct_0(B_37),A_35)
      | ~ v2_pre_topc(A_35)
      | ~ m1_pre_topc(B_37,A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(resolution,[status(thm)],[c_26,c_63])).

tff(c_96,plain,(
    ! [B_58] :
      ( v1_tsep_1(B_58,'#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | k6_tmap_1('#skF_2',u1_struct_0(B_58)) != k8_tmap_1('#skF_2','#skF_3')
      | ~ m1_pre_topc(B_58,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_93,c_67])).

tff(c_99,plain,(
    ! [B_58] :
      ( v1_tsep_1(B_58,'#skF_2')
      | k6_tmap_1('#skF_2',u1_struct_0(B_58)) != k8_tmap_1('#skF_2','#skF_3')
      | ~ m1_pre_topc(B_58,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_96])).

tff(c_351,plain,(
    ! [B_92] :
      ( v1_tsep_1(B_92,'#skF_2')
      | k8_tmap_1('#skF_2',B_92) != k8_tmap_1('#skF_2','#skF_3')
      | ~ m1_pre_topc(B_92,'#skF_2')
      | ~ m1_pre_topc(B_92,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_99])).

tff(c_374,plain,(
    ! [B_92] :
      ( v1_tsep_1(B_92,'#skF_2')
      | k8_tmap_1('#skF_2',B_92) != k8_tmap_1('#skF_2','#skF_3')
      | ~ m1_pre_topc(B_92,'#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_351])).

tff(c_381,plain,(
    ! [B_94] :
      ( v1_tsep_1(B_94,'#skF_2')
      | k8_tmap_1('#skF_2',B_94) != k8_tmap_1('#skF_2','#skF_3')
      | ~ m1_pre_topc(B_94,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_374])).

tff(c_38,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k8_tmap_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ v1_tsep_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_51,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k8_tmap_1('#skF_2','#skF_3')
    | ~ v1_tsep_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_38])).

tff(c_58,plain,(
    ~ v1_tsep_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_51])).

tff(c_387,plain,(
    ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_381,c_58])).

tff(c_392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_387])).

tff(c_393,plain,(
    v1_tsep_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_530,plain,(
    ! [A_132,B_133] :
      ( k6_tmap_1(A_132,u1_struct_0(B_133)) = k8_tmap_1(A_132,B_133)
      | ~ m1_subset_1(u1_struct_0(B_133),k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(k8_tmap_1(A_132,B_133))
      | ~ v2_pre_topc(k8_tmap_1(A_132,B_133))
      | ~ v1_pre_topc(k8_tmap_1(A_132,B_133))
      | ~ m1_pre_topc(B_133,A_132)
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_535,plain,(
    ! [A_134,B_135] :
      ( k6_tmap_1(A_134,u1_struct_0(B_135)) = k8_tmap_1(A_134,B_135)
      | ~ l1_pre_topc(k8_tmap_1(A_134,B_135))
      | ~ v2_pre_topc(k8_tmap_1(A_134,B_135))
      | ~ v1_pre_topc(k8_tmap_1(A_134,B_135))
      | ~ v2_pre_topc(A_134)
      | v2_struct_0(A_134)
      | ~ m1_pre_topc(B_135,A_134)
      | ~ l1_pre_topc(A_134) ) ),
    inference(resolution,[status(thm)],[c_26,c_530])).

tff(c_540,plain,(
    ! [A_136,B_137] :
      ( k6_tmap_1(A_136,u1_struct_0(B_137)) = k8_tmap_1(A_136,B_137)
      | ~ l1_pre_topc(k8_tmap_1(A_136,B_137))
      | ~ v1_pre_topc(k8_tmap_1(A_136,B_137))
      | ~ m1_pre_topc(B_137,A_136)
      | ~ l1_pre_topc(A_136)
      | ~ v2_pre_topc(A_136)
      | v2_struct_0(A_136) ) ),
    inference(resolution,[status(thm)],[c_12,c_535])).

tff(c_545,plain,(
    ! [A_138,B_139] :
      ( k6_tmap_1(A_138,u1_struct_0(B_139)) = k8_tmap_1(A_138,B_139)
      | ~ l1_pre_topc(k8_tmap_1(A_138,B_139))
      | ~ m1_pre_topc(B_139,A_138)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(resolution,[status(thm)],[c_14,c_540])).

tff(c_550,plain,(
    ! [A_140,B_141] :
      ( k6_tmap_1(A_140,u1_struct_0(B_141)) = k8_tmap_1(A_140,B_141)
      | ~ m1_pre_topc(B_141,A_140)
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140) ) ),
    inference(resolution,[status(thm)],[c_10,c_545])).

tff(c_407,plain,(
    ! [B_107,A_108] :
      ( v3_pre_topc(u1_struct_0(B_107),A_108)
      | ~ v1_tsep_1(B_107,A_108)
      | ~ m1_subset_1(u1_struct_0(B_107),k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ m1_pre_topc(B_107,A_108)
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_411,plain,(
    ! [B_37,A_35] :
      ( v3_pre_topc(u1_struct_0(B_37),A_35)
      | ~ v1_tsep_1(B_37,A_35)
      | ~ v2_pre_topc(A_35)
      | ~ m1_pre_topc(B_37,A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(resolution,[status(thm)],[c_26,c_407])).

tff(c_418,plain,(
    ! [A_113,B_114] :
      ( k6_tmap_1(A_113,B_114) = g1_pre_topc(u1_struct_0(A_113),u1_pre_topc(A_113))
      | ~ v3_pre_topc(B_114,A_113)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113)
      | ~ v2_pre_topc(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_432,plain,(
    ! [A_118,B_119] :
      ( k6_tmap_1(A_118,u1_struct_0(B_119)) = g1_pre_topc(u1_struct_0(A_118),u1_pre_topc(A_118))
      | ~ v3_pre_topc(u1_struct_0(B_119),A_118)
      | ~ v2_pre_topc(A_118)
      | v2_struct_0(A_118)
      | ~ m1_pre_topc(B_119,A_118)
      | ~ l1_pre_topc(A_118) ) ),
    inference(resolution,[status(thm)],[c_26,c_418])).

tff(c_437,plain,(
    ! [A_123,B_124] :
      ( k6_tmap_1(A_123,u1_struct_0(B_124)) = g1_pre_topc(u1_struct_0(A_123),u1_pre_topc(A_123))
      | v2_struct_0(A_123)
      | ~ v1_tsep_1(B_124,A_123)
      | ~ v2_pre_topc(A_123)
      | ~ m1_pre_topc(B_124,A_123)
      | ~ l1_pre_topc(A_123) ) ),
    inference(resolution,[status(thm)],[c_411,c_432])).

tff(c_394,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k8_tmap_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_450,plain,(
    ! [B_124] :
      ( k6_tmap_1('#skF_2',u1_struct_0(B_124)) != k8_tmap_1('#skF_2','#skF_3')
      | v2_struct_0('#skF_2')
      | ~ v1_tsep_1(B_124,'#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_pre_topc(B_124,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_394])).

tff(c_460,plain,(
    ! [B_124] :
      ( k6_tmap_1('#skF_2',u1_struct_0(B_124)) != k8_tmap_1('#skF_2','#skF_3')
      | v2_struct_0('#skF_2')
      | ~ v1_tsep_1(B_124,'#skF_2')
      | ~ m1_pre_topc(B_124,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_450])).

tff(c_461,plain,(
    ! [B_124] :
      ( k6_tmap_1('#skF_2',u1_struct_0(B_124)) != k8_tmap_1('#skF_2','#skF_3')
      | ~ v1_tsep_1(B_124,'#skF_2')
      | ~ m1_pre_topc(B_124,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_460])).

tff(c_563,plain,(
    ! [B_141] :
      ( k8_tmap_1('#skF_2',B_141) != k8_tmap_1('#skF_2','#skF_3')
      | ~ v1_tsep_1(B_141,'#skF_2')
      | ~ m1_pre_topc(B_141,'#skF_2')
      | ~ m1_pre_topc(B_141,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_550,c_461])).

tff(c_583,plain,(
    ! [B_141] :
      ( k8_tmap_1('#skF_2',B_141) != k8_tmap_1('#skF_2','#skF_3')
      | ~ v1_tsep_1(B_141,'#skF_2')
      | ~ m1_pre_topc(B_141,'#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_563])).

tff(c_586,plain,(
    ! [B_142] :
      ( k8_tmap_1('#skF_2',B_142) != k8_tmap_1('#skF_2','#skF_3')
      | ~ v1_tsep_1(B_142,'#skF_2')
      | ~ m1_pre_topc(B_142,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_583])).

tff(c_589,plain,(
    ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_393,c_586])).

tff(c_593,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_589])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:46:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.38  
% 2.90/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.39  %$ v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k8_tmap_1 > k6_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 2.90/1.39  
% 2.90/1.39  %Foreground sorts:
% 2.90/1.39  
% 2.90/1.39  
% 2.90/1.39  %Background operators:
% 2.90/1.39  
% 2.90/1.39  
% 2.90/1.39  %Foreground operators:
% 2.90/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.90/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.90/1.39  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.90/1.39  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.90/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.39  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.90/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.90/1.39  tff(k8_tmap_1, type, k8_tmap_1: ($i * $i) > $i).
% 2.90/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.90/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.90/1.39  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.90/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.90/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.39  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 2.90/1.39  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 2.90/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.39  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.90/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.90/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.90/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.90/1.39  
% 2.90/1.40  tff(f_125, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k8_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_tmap_1)).
% 2.90/1.40  tff(f_66, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_pre_topc(k8_tmap_1(A, B)) & v2_pre_topc(k8_tmap_1(A, B))) & l1_pre_topc(k8_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 2.90/1.40  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.90/1.40  tff(f_51, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (((v1_pre_topc(C) & v2_pre_topc(C)) & l1_pre_topc(C)) => ((C = k8_tmap_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((D = u1_struct_0(B)) => (C = k6_tmap_1(A, D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_tmap_1)).
% 2.90/1.40  tff(f_80, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_tmap_1)).
% 2.90/1.40  tff(f_98, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 2.90/1.40  tff(c_28, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.90/1.40  tff(c_36, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.90/1.40  tff(c_34, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.90/1.40  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.90/1.40  tff(c_10, plain, (![A_23, B_24]: (l1_pre_topc(k8_tmap_1(A_23, B_24)) | ~m1_pre_topc(B_24, A_23) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.90/1.40  tff(c_14, plain, (![A_23, B_24]: (v1_pre_topc(k8_tmap_1(A_23, B_24)) | ~m1_pre_topc(B_24, A_23) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.90/1.40  tff(c_12, plain, (![A_23, B_24]: (v2_pre_topc(k8_tmap_1(A_23, B_24)) | ~m1_pre_topc(B_24, A_23) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.90/1.40  tff(c_26, plain, (![B_37, A_35]: (m1_subset_1(u1_struct_0(B_37), k1_zfmisc_1(u1_struct_0(A_35))) | ~m1_pre_topc(B_37, A_35) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.90/1.40  tff(c_311, plain, (![A_83, B_84]: (k6_tmap_1(A_83, u1_struct_0(B_84))=k8_tmap_1(A_83, B_84) | ~m1_subset_1(u1_struct_0(B_84), k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(k8_tmap_1(A_83, B_84)) | ~v2_pre_topc(k8_tmap_1(A_83, B_84)) | ~v1_pre_topc(k8_tmap_1(A_83, B_84)) | ~m1_pre_topc(B_84, A_83) | ~l1_pre_topc(A_83) | ~v2_pre_topc(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.90/1.40  tff(c_316, plain, (![A_85, B_86]: (k6_tmap_1(A_85, u1_struct_0(B_86))=k8_tmap_1(A_85, B_86) | ~l1_pre_topc(k8_tmap_1(A_85, B_86)) | ~v2_pre_topc(k8_tmap_1(A_85, B_86)) | ~v1_pre_topc(k8_tmap_1(A_85, B_86)) | ~v2_pre_topc(A_85) | v2_struct_0(A_85) | ~m1_pre_topc(B_86, A_85) | ~l1_pre_topc(A_85))), inference(resolution, [status(thm)], [c_26, c_311])).
% 2.90/1.40  tff(c_321, plain, (![A_87, B_88]: (k6_tmap_1(A_87, u1_struct_0(B_88))=k8_tmap_1(A_87, B_88) | ~l1_pre_topc(k8_tmap_1(A_87, B_88)) | ~v1_pre_topc(k8_tmap_1(A_87, B_88)) | ~m1_pre_topc(B_88, A_87) | ~l1_pre_topc(A_87) | ~v2_pre_topc(A_87) | v2_struct_0(A_87))), inference(resolution, [status(thm)], [c_12, c_316])).
% 2.90/1.40  tff(c_326, plain, (![A_89, B_90]: (k6_tmap_1(A_89, u1_struct_0(B_90))=k8_tmap_1(A_89, B_90) | ~l1_pre_topc(k8_tmap_1(A_89, B_90)) | ~m1_pre_topc(B_90, A_89) | ~l1_pre_topc(A_89) | ~v2_pre_topc(A_89) | v2_struct_0(A_89))), inference(resolution, [status(thm)], [c_14, c_321])).
% 2.90/1.40  tff(c_331, plain, (![A_91, B_92]: (k6_tmap_1(A_91, u1_struct_0(B_92))=k8_tmap_1(A_91, B_92) | ~m1_pre_topc(B_92, A_91) | ~l1_pre_topc(A_91) | ~v2_pre_topc(A_91) | v2_struct_0(A_91))), inference(resolution, [status(thm)], [c_10, c_326])).
% 2.90/1.40  tff(c_48, plain, (v1_tsep_1('#skF_3', '#skF_2') | g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k8_tmap_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.90/1.40  tff(c_52, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k8_tmap_1('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_48])).
% 2.90/1.40  tff(c_74, plain, (![B_53, A_54]: (v3_pre_topc(B_53, A_54) | k6_tmap_1(A_54, B_53)!=g1_pre_topc(u1_struct_0(A_54), u1_pre_topc(A_54)) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54) | ~v2_pre_topc(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.90/1.40  tff(c_76, plain, (![B_53]: (v3_pre_topc(B_53, '#skF_2') | k8_tmap_1('#skF_2', '#skF_3')!=k6_tmap_1('#skF_2', B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_74])).
% 2.90/1.40  tff(c_78, plain, (![B_53]: (v3_pre_topc(B_53, '#skF_2') | k8_tmap_1('#skF_2', '#skF_3')!=k6_tmap_1('#skF_2', B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_76])).
% 2.90/1.40  tff(c_85, plain, (![B_57]: (v3_pre_topc(B_57, '#skF_2') | k8_tmap_1('#skF_2', '#skF_3')!=k6_tmap_1('#skF_2', B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_36, c_78])).
% 2.90/1.40  tff(c_89, plain, (![B_37]: (v3_pre_topc(u1_struct_0(B_37), '#skF_2') | k6_tmap_1('#skF_2', u1_struct_0(B_37))!=k8_tmap_1('#skF_2', '#skF_3') | ~m1_pre_topc(B_37, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_85])).
% 2.90/1.40  tff(c_93, plain, (![B_58]: (v3_pre_topc(u1_struct_0(B_58), '#skF_2') | k6_tmap_1('#skF_2', u1_struct_0(B_58))!=k8_tmap_1('#skF_2', '#skF_3') | ~m1_pre_topc(B_58, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_89])).
% 2.90/1.40  tff(c_63, plain, (![B_47, A_48]: (v1_tsep_1(B_47, A_48) | ~v3_pre_topc(u1_struct_0(B_47), A_48) | ~m1_subset_1(u1_struct_0(B_47), k1_zfmisc_1(u1_struct_0(A_48))) | ~m1_pre_topc(B_47, A_48) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.90/1.40  tff(c_67, plain, (![B_37, A_35]: (v1_tsep_1(B_37, A_35) | ~v3_pre_topc(u1_struct_0(B_37), A_35) | ~v2_pre_topc(A_35) | ~m1_pre_topc(B_37, A_35) | ~l1_pre_topc(A_35))), inference(resolution, [status(thm)], [c_26, c_63])).
% 2.90/1.40  tff(c_96, plain, (![B_58]: (v1_tsep_1(B_58, '#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2') | k6_tmap_1('#skF_2', u1_struct_0(B_58))!=k8_tmap_1('#skF_2', '#skF_3') | ~m1_pre_topc(B_58, '#skF_2'))), inference(resolution, [status(thm)], [c_93, c_67])).
% 2.90/1.40  tff(c_99, plain, (![B_58]: (v1_tsep_1(B_58, '#skF_2') | k6_tmap_1('#skF_2', u1_struct_0(B_58))!=k8_tmap_1('#skF_2', '#skF_3') | ~m1_pre_topc(B_58, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_96])).
% 2.90/1.40  tff(c_351, plain, (![B_92]: (v1_tsep_1(B_92, '#skF_2') | k8_tmap_1('#skF_2', B_92)!=k8_tmap_1('#skF_2', '#skF_3') | ~m1_pre_topc(B_92, '#skF_2') | ~m1_pre_topc(B_92, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_331, c_99])).
% 2.90/1.40  tff(c_374, plain, (![B_92]: (v1_tsep_1(B_92, '#skF_2') | k8_tmap_1('#skF_2', B_92)!=k8_tmap_1('#skF_2', '#skF_3') | ~m1_pre_topc(B_92, '#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_351])).
% 2.90/1.40  tff(c_381, plain, (![B_94]: (v1_tsep_1(B_94, '#skF_2') | k8_tmap_1('#skF_2', B_94)!=k8_tmap_1('#skF_2', '#skF_3') | ~m1_pre_topc(B_94, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_36, c_374])).
% 2.90/1.40  tff(c_38, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k8_tmap_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~v1_tsep_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.90/1.40  tff(c_51, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k8_tmap_1('#skF_2', '#skF_3') | ~v1_tsep_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_38])).
% 2.90/1.40  tff(c_58, plain, (~v1_tsep_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_51])).
% 2.90/1.40  tff(c_387, plain, (~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_381, c_58])).
% 2.90/1.40  tff(c_392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_387])).
% 2.90/1.40  tff(c_393, plain, (v1_tsep_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 2.90/1.40  tff(c_530, plain, (![A_132, B_133]: (k6_tmap_1(A_132, u1_struct_0(B_133))=k8_tmap_1(A_132, B_133) | ~m1_subset_1(u1_struct_0(B_133), k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(k8_tmap_1(A_132, B_133)) | ~v2_pre_topc(k8_tmap_1(A_132, B_133)) | ~v1_pre_topc(k8_tmap_1(A_132, B_133)) | ~m1_pre_topc(B_133, A_132) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | v2_struct_0(A_132))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.90/1.40  tff(c_535, plain, (![A_134, B_135]: (k6_tmap_1(A_134, u1_struct_0(B_135))=k8_tmap_1(A_134, B_135) | ~l1_pre_topc(k8_tmap_1(A_134, B_135)) | ~v2_pre_topc(k8_tmap_1(A_134, B_135)) | ~v1_pre_topc(k8_tmap_1(A_134, B_135)) | ~v2_pre_topc(A_134) | v2_struct_0(A_134) | ~m1_pre_topc(B_135, A_134) | ~l1_pre_topc(A_134))), inference(resolution, [status(thm)], [c_26, c_530])).
% 2.90/1.40  tff(c_540, plain, (![A_136, B_137]: (k6_tmap_1(A_136, u1_struct_0(B_137))=k8_tmap_1(A_136, B_137) | ~l1_pre_topc(k8_tmap_1(A_136, B_137)) | ~v1_pre_topc(k8_tmap_1(A_136, B_137)) | ~m1_pre_topc(B_137, A_136) | ~l1_pre_topc(A_136) | ~v2_pre_topc(A_136) | v2_struct_0(A_136))), inference(resolution, [status(thm)], [c_12, c_535])).
% 2.90/1.40  tff(c_545, plain, (![A_138, B_139]: (k6_tmap_1(A_138, u1_struct_0(B_139))=k8_tmap_1(A_138, B_139) | ~l1_pre_topc(k8_tmap_1(A_138, B_139)) | ~m1_pre_topc(B_139, A_138) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(resolution, [status(thm)], [c_14, c_540])).
% 2.90/1.40  tff(c_550, plain, (![A_140, B_141]: (k6_tmap_1(A_140, u1_struct_0(B_141))=k8_tmap_1(A_140, B_141) | ~m1_pre_topc(B_141, A_140) | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140))), inference(resolution, [status(thm)], [c_10, c_545])).
% 2.90/1.40  tff(c_407, plain, (![B_107, A_108]: (v3_pre_topc(u1_struct_0(B_107), A_108) | ~v1_tsep_1(B_107, A_108) | ~m1_subset_1(u1_struct_0(B_107), k1_zfmisc_1(u1_struct_0(A_108))) | ~m1_pre_topc(B_107, A_108) | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.90/1.40  tff(c_411, plain, (![B_37, A_35]: (v3_pre_topc(u1_struct_0(B_37), A_35) | ~v1_tsep_1(B_37, A_35) | ~v2_pre_topc(A_35) | ~m1_pre_topc(B_37, A_35) | ~l1_pre_topc(A_35))), inference(resolution, [status(thm)], [c_26, c_407])).
% 2.90/1.40  tff(c_418, plain, (![A_113, B_114]: (k6_tmap_1(A_113, B_114)=g1_pre_topc(u1_struct_0(A_113), u1_pre_topc(A_113)) | ~v3_pre_topc(B_114, A_113) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113) | ~v2_pre_topc(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.90/1.40  tff(c_432, plain, (![A_118, B_119]: (k6_tmap_1(A_118, u1_struct_0(B_119))=g1_pre_topc(u1_struct_0(A_118), u1_pre_topc(A_118)) | ~v3_pre_topc(u1_struct_0(B_119), A_118) | ~v2_pre_topc(A_118) | v2_struct_0(A_118) | ~m1_pre_topc(B_119, A_118) | ~l1_pre_topc(A_118))), inference(resolution, [status(thm)], [c_26, c_418])).
% 2.90/1.40  tff(c_437, plain, (![A_123, B_124]: (k6_tmap_1(A_123, u1_struct_0(B_124))=g1_pre_topc(u1_struct_0(A_123), u1_pre_topc(A_123)) | v2_struct_0(A_123) | ~v1_tsep_1(B_124, A_123) | ~v2_pre_topc(A_123) | ~m1_pre_topc(B_124, A_123) | ~l1_pre_topc(A_123))), inference(resolution, [status(thm)], [c_411, c_432])).
% 2.90/1.40  tff(c_394, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k8_tmap_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 2.90/1.40  tff(c_450, plain, (![B_124]: (k6_tmap_1('#skF_2', u1_struct_0(B_124))!=k8_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_2') | ~v1_tsep_1(B_124, '#skF_2') | ~v2_pre_topc('#skF_2') | ~m1_pre_topc(B_124, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_437, c_394])).
% 2.90/1.40  tff(c_460, plain, (![B_124]: (k6_tmap_1('#skF_2', u1_struct_0(B_124))!=k8_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_2') | ~v1_tsep_1(B_124, '#skF_2') | ~m1_pre_topc(B_124, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_450])).
% 2.90/1.40  tff(c_461, plain, (![B_124]: (k6_tmap_1('#skF_2', u1_struct_0(B_124))!=k8_tmap_1('#skF_2', '#skF_3') | ~v1_tsep_1(B_124, '#skF_2') | ~m1_pre_topc(B_124, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_36, c_460])).
% 2.90/1.40  tff(c_563, plain, (![B_141]: (k8_tmap_1('#skF_2', B_141)!=k8_tmap_1('#skF_2', '#skF_3') | ~v1_tsep_1(B_141, '#skF_2') | ~m1_pre_topc(B_141, '#skF_2') | ~m1_pre_topc(B_141, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_550, c_461])).
% 2.90/1.40  tff(c_583, plain, (![B_141]: (k8_tmap_1('#skF_2', B_141)!=k8_tmap_1('#skF_2', '#skF_3') | ~v1_tsep_1(B_141, '#skF_2') | ~m1_pre_topc(B_141, '#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_563])).
% 2.90/1.40  tff(c_586, plain, (![B_142]: (k8_tmap_1('#skF_2', B_142)!=k8_tmap_1('#skF_2', '#skF_3') | ~v1_tsep_1(B_142, '#skF_2') | ~m1_pre_topc(B_142, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_36, c_583])).
% 2.90/1.40  tff(c_589, plain, (~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_393, c_586])).
% 2.90/1.40  tff(c_593, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_589])).
% 2.90/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.40  
% 2.90/1.40  Inference rules
% 2.90/1.40  ----------------------
% 2.90/1.40  #Ref     : 0
% 2.90/1.40  #Sup     : 118
% 2.90/1.40  #Fact    : 0
% 2.90/1.40  #Define  : 0
% 2.90/1.40  #Split   : 3
% 2.90/1.40  #Chain   : 0
% 2.90/1.40  #Close   : 0
% 2.90/1.40  
% 2.90/1.40  Ordering : KBO
% 2.90/1.40  
% 2.90/1.40  Simplification rules
% 2.90/1.40  ----------------------
% 2.90/1.40  #Subsume      : 55
% 2.90/1.40  #Demod        : 84
% 2.90/1.40  #Tautology    : 28
% 2.90/1.40  #SimpNegUnit  : 24
% 2.90/1.40  #BackRed      : 0
% 2.90/1.40  
% 2.90/1.40  #Partial instantiations: 0
% 2.90/1.40  #Strategies tried      : 1
% 2.90/1.40  
% 2.90/1.40  Timing (in seconds)
% 2.90/1.40  ----------------------
% 2.90/1.41  Preprocessing        : 0.32
% 2.90/1.41  Parsing              : 0.16
% 2.90/1.41  CNF conversion       : 0.02
% 2.90/1.41  Main loop            : 0.32
% 2.90/1.41  Inferencing          : 0.13
% 2.90/1.41  Reduction            : 0.09
% 2.90/1.41  Demodulation         : 0.06
% 2.90/1.41  BG Simplification    : 0.02
% 2.90/1.41  Subsumption          : 0.06
% 2.90/1.41  Abstraction          : 0.02
% 2.90/1.41  MUC search           : 0.00
% 2.90/1.41  Cooper               : 0.00
% 2.90/1.41  Total                : 0.67
% 2.90/1.41  Index Insertion      : 0.00
% 2.90/1.41  Index Deletion       : 0.00
% 2.90/1.41  Index Matching       : 0.00
% 2.90/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
