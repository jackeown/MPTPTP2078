%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:11 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 447 expanded)
%              Number of leaves         :   41 ( 168 expanded)
%              Depth                    :   18
%              Number of atoms          :  226 (1699 expanded)
%              Number of equality atoms :   25 ( 123 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_169,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(C),u1_struct_0(B))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                   => r2_funct_2(u1_struct_0(C),u1_struct_0(B),D,k3_tmap_1(A,B,C,C,D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tmap_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_102,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_138,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_134,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => k3_tmap_1(A,B,C,D,E) = k2_partfun1(u1_struct_0(C),u1_struct_0(B),E,u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_24,plain,(
    ! [A_22] :
      ( l1_struct_0(A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_80,plain,(
    ! [C_76,A_77,B_78] :
      ( v1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_84,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_80])).

tff(c_85,plain,(
    ! [C_79,A_80,B_81] :
      ( v4_relat_1(C_79,A_80)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_89,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_85])).

tff(c_96,plain,(
    ! [B_86,A_87] :
      ( k1_relat_1(B_86) = A_87
      | ~ v1_partfun1(B_86,A_87)
      | ~ v4_relat_1(B_86,A_87)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_99,plain,
    ( u1_struct_0('#skF_3') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_89,c_96])).

tff(c_102,plain,
    ( u1_struct_0('#skF_3') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_99])).

tff(c_103,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_38,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_119,plain,(
    ! [C_93,A_94,B_95] :
      ( v1_partfun1(C_93,A_94)
      | ~ v1_funct_2(C_93,A_94,B_95)
      | ~ v1_funct_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95)))
      | v1_xboole_0(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_122,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_3'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_119])).

tff(c_125,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_122])).

tff(c_126,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_125])).

tff(c_28,plain,(
    ! [A_26] :
      ( ~ v1_xboole_0(u1_struct_0(A_26))
      | ~ l1_struct_0(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_129,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_126,c_28])).

tff(c_132,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_129])).

tff(c_135,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_132])).

tff(c_139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_135])).

tff(c_140,plain,(
    u1_struct_0('#skF_3') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_145,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_38])).

tff(c_144,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_36])).

tff(c_215,plain,(
    ! [A_104,B_105,D_106] :
      ( r2_funct_2(A_104,B_105,D_106,D_106)
      | ~ m1_subset_1(D_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105)))
      | ~ v1_funct_2(D_106,A_104,B_105)
      | ~ v1_funct_1(D_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_217,plain,
    ( r2_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'),'#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_144,c_215])).

tff(c_220,plain,(
    r2_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_145,c_217])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_59,plain,(
    ! [B_72,A_73] :
      ( l1_pre_topc(B_72)
      | ~ m1_pre_topc(B_72,A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_65,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_59])).

tff(c_69,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_65])).

tff(c_32,plain,(
    ! [A_58] :
      ( m1_pre_topc(A_58,A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_18,plain,(
    ! [A_14,B_15,C_16,D_17] :
      ( k2_partfun1(A_14,B_15,C_16,D_17) = k7_relat_1(C_16,D_17)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15)))
      | ~ v1_funct_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_180,plain,(
    ! [D_17] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'),'#skF_4',D_17) = k7_relat_1('#skF_4',D_17)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_144,c_18])).

tff(c_192,plain,(
    ! [D_17] : k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'),'#skF_4',D_17) = k7_relat_1('#skF_4',D_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_180])).

tff(c_228,plain,(
    ! [C_111,A_115,D_114,E_113,B_112] :
      ( k3_tmap_1(A_115,B_112,C_111,D_114,E_113) = k2_partfun1(u1_struct_0(C_111),u1_struct_0(B_112),E_113,u1_struct_0(D_114))
      | ~ m1_pre_topc(D_114,C_111)
      | ~ m1_subset_1(E_113,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_111),u1_struct_0(B_112))))
      | ~ v1_funct_2(E_113,u1_struct_0(C_111),u1_struct_0(B_112))
      | ~ v1_funct_1(E_113)
      | ~ m1_pre_topc(D_114,A_115)
      | ~ m1_pre_topc(C_111,A_115)
      | ~ l1_pre_topc(B_112)
      | ~ v2_pre_topc(B_112)
      | v2_struct_0(B_112)
      | ~ l1_pre_topc(A_115)
      | ~ v2_pre_topc(A_115)
      | v2_struct_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_230,plain,(
    ! [A_115,B_112,D_114,E_113] :
      ( k3_tmap_1(A_115,B_112,'#skF_3',D_114,E_113) = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_112),E_113,u1_struct_0(D_114))
      | ~ m1_pre_topc(D_114,'#skF_3')
      | ~ m1_subset_1(E_113,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_112))))
      | ~ v1_funct_2(E_113,u1_struct_0('#skF_3'),u1_struct_0(B_112))
      | ~ v1_funct_1(E_113)
      | ~ m1_pre_topc(D_114,A_115)
      | ~ m1_pre_topc('#skF_3',A_115)
      | ~ l1_pre_topc(B_112)
      | ~ v2_pre_topc(B_112)
      | v2_struct_0(B_112)
      | ~ l1_pre_topc(A_115)
      | ~ v2_pre_topc(A_115)
      | v2_struct_0(A_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_228])).

tff(c_238,plain,(
    ! [A_116,B_117,D_118,E_119] :
      ( k3_tmap_1(A_116,B_117,'#skF_3',D_118,E_119) = k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0(B_117),E_119,u1_struct_0(D_118))
      | ~ m1_pre_topc(D_118,'#skF_3')
      | ~ m1_subset_1(E_119,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_117))))
      | ~ v1_funct_2(E_119,k1_relat_1('#skF_4'),u1_struct_0(B_117))
      | ~ v1_funct_1(E_119)
      | ~ m1_pre_topc(D_118,A_116)
      | ~ m1_pre_topc('#skF_3',A_116)
      | ~ l1_pre_topc(B_117)
      | ~ v2_pre_topc(B_117)
      | v2_struct_0(B_117)
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116)
      | v2_struct_0(A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_140,c_230])).

tff(c_240,plain,(
    ! [A_116,D_118] :
      ( k3_tmap_1(A_116,'#skF_2','#skF_3',D_118,'#skF_4') = k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_118))
      | ~ m1_pre_topc(D_118,'#skF_3')
      | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc(D_118,A_116)
      | ~ m1_pre_topc('#skF_3',A_116)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116)
      | v2_struct_0(A_116) ) ),
    inference(resolution,[status(thm)],[c_144,c_238])).

tff(c_245,plain,(
    ! [D_118,A_116] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_118)) = k3_tmap_1(A_116,'#skF_2','#skF_3',D_118,'#skF_4')
      | ~ m1_pre_topc(D_118,'#skF_3')
      | ~ m1_pre_topc(D_118,A_116)
      | ~ m1_pre_topc('#skF_3',A_116)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116)
      | v2_struct_0(A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_40,c_145,c_192,c_240])).

tff(c_250,plain,(
    ! [D_120,A_121] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_120)) = k3_tmap_1(A_121,'#skF_2','#skF_3',D_120,'#skF_4')
      | ~ m1_pre_topc(D_120,'#skF_3')
      | ~ m1_pre_topc(D_120,A_121)
      | ~ m1_pre_topc('#skF_3',A_121)
      | ~ l1_pre_topc(A_121)
      | ~ v2_pre_topc(A_121)
      | v2_struct_0(A_121) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_245])).

tff(c_254,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_250])).

tff(c_258,plain,
    ( k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_42,c_140,c_254])).

tff(c_259,plain,
    ( k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_258])).

tff(c_260,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_259])).

tff(c_263,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_260])).

tff(c_267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_263])).

tff(c_268,plain,(
    k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_259])).

tff(c_2,plain,(
    ! [A_1] :
      ( k7_relat_1(A_1,k1_relat_1(A_1)) = A_1
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_285,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_2])).

tff(c_292,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_285])).

tff(c_34,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_143,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'),'#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_34])).

tff(c_297,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_143])).

tff(c_300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_297])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:56:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.37  
% 2.55/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.38  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.55/1.38  
% 2.55/1.38  %Foreground sorts:
% 2.55/1.38  
% 2.55/1.38  
% 2.55/1.38  %Background operators:
% 2.55/1.38  
% 2.55/1.38  
% 2.55/1.38  %Foreground operators:
% 2.55/1.38  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.55/1.38  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.55/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.55/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.38  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.55/1.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.55/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.55/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.55/1.38  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.55/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.55/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.55/1.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.55/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.55/1.38  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.55/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.55/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.55/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.55/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.38  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.55/1.38  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.55/1.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.55/1.38  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.55/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.55/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.55/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.55/1.38  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.55/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.55/1.38  
% 2.71/1.40  tff(f_169, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), D, k3_tmap_1(A, B, C, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tmap_1)).
% 2.71/1.40  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.71/1.40  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.71/1.40  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.71/1.40  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 2.71/1.40  tff(f_53, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.71/1.40  tff(f_102, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.71/1.40  tff(f_83, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 2.71/1.40  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.71/1.40  tff(f_138, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 2.71/1.40  tff(f_67, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.71/1.40  tff(f_134, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.71/1.40  tff(f_29, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 2.71/1.40  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.71/1.40  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.71/1.40  tff(c_24, plain, (![A_22]: (l1_struct_0(A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.71/1.40  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.71/1.40  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.71/1.40  tff(c_80, plain, (![C_76, A_77, B_78]: (v1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.71/1.40  tff(c_84, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_80])).
% 2.71/1.40  tff(c_85, plain, (![C_79, A_80, B_81]: (v4_relat_1(C_79, A_80) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.71/1.40  tff(c_89, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_85])).
% 2.71/1.40  tff(c_96, plain, (![B_86, A_87]: (k1_relat_1(B_86)=A_87 | ~v1_partfun1(B_86, A_87) | ~v4_relat_1(B_86, A_87) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.71/1.40  tff(c_99, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_3')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_89, c_96])).
% 2.71/1.40  tff(c_102, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_99])).
% 2.71/1.40  tff(c_103, plain, (~v1_partfun1('#skF_4', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_102])).
% 2.71/1.40  tff(c_38, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.71/1.40  tff(c_119, plain, (![C_93, A_94, B_95]: (v1_partfun1(C_93, A_94) | ~v1_funct_2(C_93, A_94, B_95) | ~v1_funct_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))) | v1_xboole_0(B_95))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.71/1.40  tff(c_122, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_3')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_119])).
% 2.71/1.40  tff(c_125, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_122])).
% 2.71/1.40  tff(c_126, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_103, c_125])).
% 2.71/1.40  tff(c_28, plain, (![A_26]: (~v1_xboole_0(u1_struct_0(A_26)) | ~l1_struct_0(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.71/1.40  tff(c_129, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_126, c_28])).
% 2.71/1.40  tff(c_132, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_129])).
% 2.71/1.40  tff(c_135, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_132])).
% 2.71/1.40  tff(c_139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_135])).
% 2.71/1.40  tff(c_140, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_102])).
% 2.71/1.40  tff(c_145, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_38])).
% 2.71/1.40  tff(c_144, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_36])).
% 2.71/1.40  tff(c_215, plain, (![A_104, B_105, D_106]: (r2_funct_2(A_104, B_105, D_106, D_106) | ~m1_subset_1(D_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))) | ~v1_funct_2(D_106, A_104, B_105) | ~v1_funct_1(D_106))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.71/1.40  tff(c_217, plain, (r2_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_144, c_215])).
% 2.71/1.40  tff(c_220, plain, (r2_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_145, c_217])).
% 2.71/1.40  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.71/1.40  tff(c_42, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.71/1.40  tff(c_59, plain, (![B_72, A_73]: (l1_pre_topc(B_72) | ~m1_pre_topc(B_72, A_73) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.71/1.40  tff(c_65, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_59])).
% 2.71/1.40  tff(c_69, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_65])).
% 2.71/1.40  tff(c_32, plain, (![A_58]: (m1_pre_topc(A_58, A_58) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.71/1.40  tff(c_56, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.71/1.40  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.71/1.40  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.71/1.40  tff(c_18, plain, (![A_14, B_15, C_16, D_17]: (k2_partfun1(A_14, B_15, C_16, D_17)=k7_relat_1(C_16, D_17) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))) | ~v1_funct_1(C_16))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.71/1.40  tff(c_180, plain, (![D_17]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'), '#skF_4', D_17)=k7_relat_1('#skF_4', D_17) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_144, c_18])).
% 2.71/1.40  tff(c_192, plain, (![D_17]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'), '#skF_4', D_17)=k7_relat_1('#skF_4', D_17))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_180])).
% 2.71/1.40  tff(c_228, plain, (![C_111, A_115, D_114, E_113, B_112]: (k3_tmap_1(A_115, B_112, C_111, D_114, E_113)=k2_partfun1(u1_struct_0(C_111), u1_struct_0(B_112), E_113, u1_struct_0(D_114)) | ~m1_pre_topc(D_114, C_111) | ~m1_subset_1(E_113, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_111), u1_struct_0(B_112)))) | ~v1_funct_2(E_113, u1_struct_0(C_111), u1_struct_0(B_112)) | ~v1_funct_1(E_113) | ~m1_pre_topc(D_114, A_115) | ~m1_pre_topc(C_111, A_115) | ~l1_pre_topc(B_112) | ~v2_pre_topc(B_112) | v2_struct_0(B_112) | ~l1_pre_topc(A_115) | ~v2_pre_topc(A_115) | v2_struct_0(A_115))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.71/1.40  tff(c_230, plain, (![A_115, B_112, D_114, E_113]: (k3_tmap_1(A_115, B_112, '#skF_3', D_114, E_113)=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_112), E_113, u1_struct_0(D_114)) | ~m1_pre_topc(D_114, '#skF_3') | ~m1_subset_1(E_113, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_112)))) | ~v1_funct_2(E_113, u1_struct_0('#skF_3'), u1_struct_0(B_112)) | ~v1_funct_1(E_113) | ~m1_pre_topc(D_114, A_115) | ~m1_pre_topc('#skF_3', A_115) | ~l1_pre_topc(B_112) | ~v2_pre_topc(B_112) | v2_struct_0(B_112) | ~l1_pre_topc(A_115) | ~v2_pre_topc(A_115) | v2_struct_0(A_115))), inference(superposition, [status(thm), theory('equality')], [c_140, c_228])).
% 2.71/1.40  tff(c_238, plain, (![A_116, B_117, D_118, E_119]: (k3_tmap_1(A_116, B_117, '#skF_3', D_118, E_119)=k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0(B_117), E_119, u1_struct_0(D_118)) | ~m1_pre_topc(D_118, '#skF_3') | ~m1_subset_1(E_119, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_117)))) | ~v1_funct_2(E_119, k1_relat_1('#skF_4'), u1_struct_0(B_117)) | ~v1_funct_1(E_119) | ~m1_pre_topc(D_118, A_116) | ~m1_pre_topc('#skF_3', A_116) | ~l1_pre_topc(B_117) | ~v2_pre_topc(B_117) | v2_struct_0(B_117) | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116) | v2_struct_0(A_116))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_140, c_230])).
% 2.71/1.40  tff(c_240, plain, (![A_116, D_118]: (k3_tmap_1(A_116, '#skF_2', '#skF_3', D_118, '#skF_4')=k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_118)) | ~m1_pre_topc(D_118, '#skF_3') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc(D_118, A_116) | ~m1_pre_topc('#skF_3', A_116) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116) | v2_struct_0(A_116))), inference(resolution, [status(thm)], [c_144, c_238])).
% 2.71/1.40  tff(c_245, plain, (![D_118, A_116]: (k7_relat_1('#skF_4', u1_struct_0(D_118))=k3_tmap_1(A_116, '#skF_2', '#skF_3', D_118, '#skF_4') | ~m1_pre_topc(D_118, '#skF_3') | ~m1_pre_topc(D_118, A_116) | ~m1_pre_topc('#skF_3', A_116) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116) | v2_struct_0(A_116))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_40, c_145, c_192, c_240])).
% 2.71/1.40  tff(c_250, plain, (![D_120, A_121]: (k7_relat_1('#skF_4', u1_struct_0(D_120))=k3_tmap_1(A_121, '#skF_2', '#skF_3', D_120, '#skF_4') | ~m1_pre_topc(D_120, '#skF_3') | ~m1_pre_topc(D_120, A_121) | ~m1_pre_topc('#skF_3', A_121) | ~l1_pre_topc(A_121) | ~v2_pre_topc(A_121) | v2_struct_0(A_121))), inference(negUnitSimplification, [status(thm)], [c_50, c_245])).
% 2.71/1.40  tff(c_254, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_250])).
% 2.71/1.40  tff(c_258, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_42, c_140, c_254])).
% 2.71/1.40  tff(c_259, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_258])).
% 2.71/1.40  tff(c_260, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_259])).
% 2.71/1.40  tff(c_263, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_32, c_260])).
% 2.71/1.40  tff(c_267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_263])).
% 2.71/1.40  tff(c_268, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_259])).
% 2.71/1.40  tff(c_2, plain, (![A_1]: (k7_relat_1(A_1, k1_relat_1(A_1))=A_1 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.71/1.40  tff(c_285, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_268, c_2])).
% 2.71/1.40  tff(c_292, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_285])).
% 2.71/1.40  tff(c_34, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_169])).
% 2.71/1.40  tff(c_143, plain, (~r2_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'), '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_34])).
% 2.71/1.40  tff(c_297, plain, (~r2_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_292, c_143])).
% 2.71/1.40  tff(c_300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_220, c_297])).
% 2.71/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.40  
% 2.71/1.40  Inference rules
% 2.71/1.40  ----------------------
% 2.71/1.40  #Ref     : 0
% 2.71/1.40  #Sup     : 42
% 2.71/1.40  #Fact    : 0
% 2.71/1.40  #Define  : 0
% 2.71/1.40  #Split   : 4
% 2.71/1.40  #Chain   : 0
% 2.71/1.40  #Close   : 0
% 2.71/1.40  
% 2.71/1.40  Ordering : KBO
% 2.71/1.40  
% 2.71/1.40  Simplification rules
% 2.71/1.40  ----------------------
% 2.71/1.40  #Subsume      : 2
% 2.71/1.40  #Demod        : 56
% 2.71/1.40  #Tautology    : 20
% 2.71/1.40  #SimpNegUnit  : 8
% 2.71/1.40  #BackRed      : 6
% 2.71/1.40  
% 2.71/1.40  #Partial instantiations: 0
% 2.71/1.40  #Strategies tried      : 1
% 2.71/1.40  
% 2.71/1.40  Timing (in seconds)
% 2.71/1.40  ----------------------
% 2.71/1.40  Preprocessing        : 0.35
% 2.71/1.40  Parsing              : 0.19
% 2.71/1.40  CNF conversion       : 0.03
% 2.71/1.40  Main loop            : 0.22
% 2.71/1.40  Inferencing          : 0.08
% 2.71/1.40  Reduction            : 0.07
% 2.71/1.40  Demodulation         : 0.05
% 2.71/1.40  BG Simplification    : 0.02
% 2.71/1.40  Subsumption          : 0.03
% 2.71/1.40  Abstraction          : 0.01
% 2.71/1.40  MUC search           : 0.00
% 2.71/1.40  Cooper               : 0.00
% 2.71/1.40  Total                : 0.62
% 2.71/1.40  Index Insertion      : 0.00
% 2.71/1.40  Index Deletion       : 0.00
% 2.71/1.40  Index Matching       : 0.00
% 2.71/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
