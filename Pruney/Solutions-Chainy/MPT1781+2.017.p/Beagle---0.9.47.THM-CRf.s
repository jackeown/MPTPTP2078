%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:47 EST 2020

% Result     : Theorem 10.55s
% Output     : CNFRefutation 10.92s
% Verified   : 
% Statistics : Number of formulae       :  300 (426298 expanded)
%              Number of leaves         :   38 (144712 expanded)
%              Depth                    :   44
%              Number of atoms          : 1252 (2293669 expanded)
%              Number of equality atoms :  204 (430900 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k1_relset_1 > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k4_tmap_1,type,(
    k4_tmap_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_181,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
               => ( ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_hidden(D,u1_struct_0(B))
                       => D = k1_funct_1(C,D) ) )
                 => r2_funct_2(u1_struct_0(B),u1_struct_0(A),k4_tmap_1(A,B),C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_tmap_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_82,axiom,(
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

tff(f_131,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_funct_1(k4_tmap_1(A,B))
        & v1_funct_2(k4_tmap_1(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(k4_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_tmap_1)).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_100,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( r1_tarski(A,B)
          <=> ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_grfunc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_116,axiom,(
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

tff(f_151,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,u1_struct_0(B))
               => k1_funct_1(k4_tmap_1(A,B),C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_tmap_1)).

tff(c_56,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_88,plain,(
    ! [A_68,B_69,C_70] :
      ( k1_relset_1(A_68,B_69,C_70) = k1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_92,plain,(
    k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_88])).

tff(c_112,plain,(
    ! [B_85,A_86,C_87] :
      ( k1_xboole_0 = B_85
      | k1_relset_1(A_86,B_85,C_87) = A_86
      | ~ v1_funct_2(C_87,A_86,B_85)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_86,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_115,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4') = u1_struct_0('#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_112])).

tff(c_118,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | u1_struct_0('#skF_3') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_92,c_115])).

tff(c_119,plain,(
    u1_struct_0('#skF_3') = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_106,plain,(
    ! [A_82,B_83,D_84] :
      ( r2_funct_2(A_82,B_83,D_84,D_84)
      | ~ m1_subset_1(D_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83)))
      | ~ v1_funct_2(D_84,A_82,B_83)
      | ~ v1_funct_1(D_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_108,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_106])).

tff(c_111,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_108])).

tff(c_120,plain,(
    r2_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_111])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_66,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_64,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_60,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_46,plain,(
    ! [A_37,B_38] :
      ( v1_funct_1(k4_tmap_1(A_37,B_38))
      | ~ m1_pre_topc(B_38,A_37)
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_12,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_191,plain,(
    ! [A_100,B_101] :
      ( m1_subset_1(k4_tmap_1(A_100,B_101),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_101),u1_struct_0(A_100))))
      | ~ m1_pre_topc(B_101,A_100)
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_10,plain,(
    ! [B_7,A_5] :
      ( v1_relat_1(B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_5))
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_205,plain,(
    ! [A_100,B_101] :
      ( v1_relat_1(k4_tmap_1(A_100,B_101))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(B_101),u1_struct_0(A_100)))
      | ~ m1_pre_topc(B_101,A_100)
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(resolution,[status(thm)],[c_191,c_10])).

tff(c_218,plain,(
    ! [A_100,B_101] :
      ( v1_relat_1(k4_tmap_1(A_100,B_101))
      | ~ m1_pre_topc(B_101,A_100)
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_205])).

tff(c_83,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_54,c_10])).

tff(c_86,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_83])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    ! [A_37,B_38] :
      ( v1_funct_2(k4_tmap_1(A_37,B_38),u1_struct_0(B_38),u1_struct_0(A_37))
      | ~ m1_pre_topc(B_38,A_37)
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_26,plain,(
    ! [B_14,A_13,C_15] :
      ( k1_xboole_0 = B_14
      | k1_relset_1(A_13,B_14,C_15) = A_13
      | ~ v1_funct_2(C_15,A_13,B_14)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_364,plain,(
    ! [A_130,B_131] :
      ( u1_struct_0(A_130) = k1_xboole_0
      | k1_relset_1(u1_struct_0(B_131),u1_struct_0(A_130),k4_tmap_1(A_130,B_131)) = u1_struct_0(B_131)
      | ~ v1_funct_2(k4_tmap_1(A_130,B_131),u1_struct_0(B_131),u1_struct_0(A_130))
      | ~ m1_pre_topc(B_131,A_130)
      | ~ l1_pre_topc(A_130)
      | ~ v2_pre_topc(A_130)
      | v2_struct_0(A_130) ) ),
    inference(resolution,[status(thm)],[c_191,c_26])).

tff(c_379,plain,(
    ! [A_132,B_133] :
      ( u1_struct_0(A_132) = k1_xboole_0
      | k1_relset_1(u1_struct_0(B_133),u1_struct_0(A_132),k4_tmap_1(A_132,B_133)) = u1_struct_0(B_133)
      | ~ m1_pre_topc(B_133,A_132)
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132) ) ),
    inference(resolution,[status(thm)],[c_44,c_364])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] :
      ( k1_relset_1(A_10,B_11,C_12) = k1_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_215,plain,(
    ! [B_101,A_100] :
      ( k1_relset_1(u1_struct_0(B_101),u1_struct_0(A_100),k4_tmap_1(A_100,B_101)) = k1_relat_1(k4_tmap_1(A_100,B_101))
      | ~ m1_pre_topc(B_101,A_100)
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(resolution,[status(thm)],[c_191,c_14])).

tff(c_431,plain,(
    ! [A_139,B_140] :
      ( k1_relat_1(k4_tmap_1(A_139,B_140)) = u1_struct_0(B_140)
      | ~ m1_pre_topc(B_140,A_139)
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139)
      | v2_struct_0(A_139)
      | u1_struct_0(A_139) = k1_xboole_0
      | ~ m1_pre_topc(B_140,A_139)
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139)
      | v2_struct_0(A_139) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_215])).

tff(c_38,plain,(
    ! [A_20,B_26] :
      ( r1_tarski(k1_relat_1(A_20),k1_relat_1(B_26))
      | ~ r1_tarski(A_20,B_26)
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_683,plain,(
    ! [B_165,B_166,A_167] :
      ( r1_tarski(u1_struct_0(B_165),k1_relat_1(B_166))
      | ~ r1_tarski(k4_tmap_1(A_167,B_165),B_166)
      | ~ v1_funct_1(B_166)
      | ~ v1_relat_1(B_166)
      | ~ v1_funct_1(k4_tmap_1(A_167,B_165))
      | ~ v1_relat_1(k4_tmap_1(A_167,B_165))
      | ~ m1_pre_topc(B_165,A_167)
      | ~ l1_pre_topc(A_167)
      | ~ v2_pre_topc(A_167)
      | v2_struct_0(A_167)
      | u1_struct_0(A_167) = k1_xboole_0
      | ~ m1_pre_topc(B_165,A_167)
      | ~ l1_pre_topc(A_167)
      | ~ v2_pre_topc(A_167)
      | v2_struct_0(A_167) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_38])).

tff(c_699,plain,(
    ! [B_171,A_172] :
      ( r1_tarski(u1_struct_0(B_171),k1_relat_1(k4_tmap_1(A_172,B_171)))
      | ~ v1_funct_1(k4_tmap_1(A_172,B_171))
      | ~ v1_relat_1(k4_tmap_1(A_172,B_171))
      | u1_struct_0(A_172) = k1_xboole_0
      | ~ m1_pre_topc(B_171,A_172)
      | ~ l1_pre_topc(A_172)
      | ~ v2_pre_topc(A_172)
      | v2_struct_0(A_172) ) ),
    inference(resolution,[status(thm)],[c_6,c_683])).

tff(c_718,plain,(
    ! [A_176] :
      ( r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(k4_tmap_1(A_176,'#skF_3')))
      | ~ v1_funct_1(k4_tmap_1(A_176,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_176,'#skF_3'))
      | u1_struct_0(A_176) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_176)
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_699])).

tff(c_308,plain,(
    ! [A_118,B_119] :
      ( r2_hidden('#skF_1'(A_118,B_119),k1_relat_1(A_118))
      | r1_tarski(A_118,B_119)
      | ~ r1_tarski(k1_relat_1(A_118),k1_relat_1(B_119))
      | ~ v1_funct_1(B_119)
      | ~ v1_relat_1(B_119)
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,B_4)
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_322,plain,(
    ! [A_118,B_119] :
      ( m1_subset_1('#skF_1'(A_118,B_119),k1_relat_1(A_118))
      | r1_tarski(A_118,B_119)
      | ~ r1_tarski(k1_relat_1(A_118),k1_relat_1(B_119))
      | ~ v1_funct_1(B_119)
      | ~ v1_relat_1(B_119)
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118) ) ),
    inference(resolution,[status(thm)],[c_308,c_8])).

tff(c_730,plain,(
    ! [A_176] :
      ( m1_subset_1('#skF_1'('#skF_4',k4_tmap_1(A_176,'#skF_3')),k1_relat_1('#skF_4'))
      | r1_tarski('#skF_4',k4_tmap_1(A_176,'#skF_3'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_funct_1(k4_tmap_1(A_176,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_176,'#skF_3'))
      | u1_struct_0(A_176) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_176)
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(resolution,[status(thm)],[c_718,c_322])).

tff(c_755,plain,(
    ! [A_176] :
      ( m1_subset_1('#skF_1'('#skF_4',k4_tmap_1(A_176,'#skF_3')),k1_relat_1('#skF_4'))
      | r1_tarski('#skF_4',k4_tmap_1(A_176,'#skF_3'))
      | ~ v1_funct_1(k4_tmap_1(A_176,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_176,'#skF_3'))
      | u1_struct_0(A_176) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_176)
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_58,c_730])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_167,plain,(
    ! [C_91,A_92,B_93] :
      ( m1_subset_1(C_91,u1_struct_0(A_92))
      | ~ m1_subset_1(C_91,u1_struct_0(B_93))
      | ~ m1_pre_topc(B_93,A_92)
      | v2_struct_0(B_93)
      | ~ l1_pre_topc(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_169,plain,(
    ! [C_91,A_92] :
      ( m1_subset_1(C_91,u1_struct_0(A_92))
      | ~ m1_subset_1(C_91,k1_relat_1('#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_92)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_92)
      | v2_struct_0(A_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_167])).

tff(c_170,plain,(
    ! [C_91,A_92] :
      ( m1_subset_1(C_91,u1_struct_0(A_92))
      | ~ m1_subset_1(C_91,k1_relat_1('#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_92)
      | ~ l1_pre_topc(A_92)
      | v2_struct_0(A_92) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_169])).

tff(c_394,plain,(
    ! [A_132] :
      ( u1_struct_0(A_132) = k1_xboole_0
      | k1_relset_1(k1_relat_1('#skF_4'),u1_struct_0(A_132),k4_tmap_1(A_132,'#skF_3')) = u1_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_3',A_132)
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_379])).

tff(c_403,plain,(
    ! [A_134] :
      ( u1_struct_0(A_134) = k1_xboole_0
      | k1_relset_1(k1_relat_1('#skF_4'),u1_struct_0(A_134),k4_tmap_1(A_134,'#skF_3')) = k1_relat_1('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_134)
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134)
      | v2_struct_0(A_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_394])).

tff(c_279,plain,(
    ! [B_115,A_116] :
      ( k1_relset_1(u1_struct_0(B_115),u1_struct_0(A_116),k4_tmap_1(A_116,B_115)) = k1_relat_1(k4_tmap_1(A_116,B_115))
      | ~ m1_pre_topc(B_115,A_116)
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116)
      | v2_struct_0(A_116) ) ),
    inference(resolution,[status(thm)],[c_191,c_14])).

tff(c_288,plain,(
    ! [A_116] :
      ( k1_relset_1(k1_relat_1('#skF_4'),u1_struct_0(A_116),k4_tmap_1(A_116,'#skF_3')) = k1_relat_1(k4_tmap_1(A_116,'#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_116)
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116)
      | v2_struct_0(A_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_279])).

tff(c_464,plain,(
    ! [A_141] :
      ( k1_relat_1(k4_tmap_1(A_141,'#skF_3')) = k1_relat_1('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_141)
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141)
      | v2_struct_0(A_141)
      | u1_struct_0(A_141) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_141)
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141)
      | v2_struct_0(A_141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_288])).

tff(c_52,plain,(
    ! [D_57] :
      ( k1_funct_1('#skF_4',D_57) = D_57
      | ~ r2_hidden(D_57,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_57,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_122,plain,(
    ! [D_57] :
      ( k1_funct_1('#skF_4',D_57) = D_57
      | ~ r2_hidden(D_57,k1_relat_1('#skF_4'))
      | ~ m1_subset_1(D_57,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_52])).

tff(c_314,plain,(
    ! [B_119] :
      ( k1_funct_1('#skF_4','#skF_1'('#skF_4',B_119)) = '#skF_1'('#skF_4',B_119)
      | ~ m1_subset_1('#skF_1'('#skF_4',B_119),u1_struct_0('#skF_2'))
      | r1_tarski('#skF_4',B_119)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_119))
      | ~ v1_funct_1(B_119)
      | ~ v1_relat_1(B_119)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_308,c_122])).

tff(c_321,plain,(
    ! [B_119] :
      ( k1_funct_1('#skF_4','#skF_1'('#skF_4',B_119)) = '#skF_1'('#skF_4',B_119)
      | ~ m1_subset_1('#skF_1'('#skF_4',B_119),u1_struct_0('#skF_2'))
      | r1_tarski('#skF_4',B_119)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_119))
      | ~ v1_funct_1(B_119)
      | ~ v1_relat_1(B_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_58,c_314])).

tff(c_473,plain,(
    ! [A_141] :
      ( k1_funct_1('#skF_4','#skF_1'('#skF_4',k4_tmap_1(A_141,'#skF_3'))) = '#skF_1'('#skF_4',k4_tmap_1(A_141,'#skF_3'))
      | ~ m1_subset_1('#skF_1'('#skF_4',k4_tmap_1(A_141,'#skF_3')),u1_struct_0('#skF_2'))
      | r1_tarski('#skF_4',k4_tmap_1(A_141,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_141,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_141,'#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_141)
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141)
      | v2_struct_0(A_141)
      | u1_struct_0(A_141) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_141)
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141)
      | v2_struct_0(A_141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_464,c_321])).

tff(c_798,plain,(
    ! [A_186] :
      ( k1_funct_1('#skF_4','#skF_1'('#skF_4',k4_tmap_1(A_186,'#skF_3'))) = '#skF_1'('#skF_4',k4_tmap_1(A_186,'#skF_3'))
      | ~ m1_subset_1('#skF_1'('#skF_4',k4_tmap_1(A_186,'#skF_3')),u1_struct_0('#skF_2'))
      | r1_tarski('#skF_4',k4_tmap_1(A_186,'#skF_3'))
      | ~ v1_funct_1(k4_tmap_1(A_186,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_186,'#skF_3'))
      | u1_struct_0(A_186) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_186)
      | ~ l1_pre_topc(A_186)
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_473])).

tff(c_801,plain,(
    ! [A_186] :
      ( k1_funct_1('#skF_4','#skF_1'('#skF_4',k4_tmap_1(A_186,'#skF_3'))) = '#skF_1'('#skF_4',k4_tmap_1(A_186,'#skF_3'))
      | r1_tarski('#skF_4',k4_tmap_1(A_186,'#skF_3'))
      | ~ v1_funct_1(k4_tmap_1(A_186,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_186,'#skF_3'))
      | u1_struct_0(A_186) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_186)
      | ~ l1_pre_topc(A_186)
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186)
      | ~ m1_subset_1('#skF_1'('#skF_4',k4_tmap_1(A_186,'#skF_3')),k1_relat_1('#skF_4'))
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_170,c_798])).

tff(c_804,plain,(
    ! [A_186] :
      ( k1_funct_1('#skF_4','#skF_1'('#skF_4',k4_tmap_1(A_186,'#skF_3'))) = '#skF_1'('#skF_4',k4_tmap_1(A_186,'#skF_3'))
      | r1_tarski('#skF_4',k4_tmap_1(A_186,'#skF_3'))
      | ~ v1_funct_1(k4_tmap_1(A_186,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_186,'#skF_3'))
      | u1_struct_0(A_186) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_186)
      | ~ l1_pre_topc(A_186)
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186)
      | ~ m1_subset_1('#skF_1'('#skF_4',k4_tmap_1(A_186,'#skF_3')),k1_relat_1('#skF_4'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_801])).

tff(c_806,plain,(
    ! [A_187] :
      ( k1_funct_1('#skF_4','#skF_1'('#skF_4',k4_tmap_1(A_187,'#skF_3'))) = '#skF_1'('#skF_4',k4_tmap_1(A_187,'#skF_3'))
      | r1_tarski('#skF_4',k4_tmap_1(A_187,'#skF_3'))
      | ~ v1_funct_1(k4_tmap_1(A_187,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_187,'#skF_3'))
      | u1_struct_0(A_187) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_187)
      | ~ l1_pre_topc(A_187)
      | ~ v2_pre_topc(A_187)
      | v2_struct_0(A_187)
      | ~ m1_subset_1('#skF_1'('#skF_4',k4_tmap_1(A_187,'#skF_3')),k1_relat_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_804])).

tff(c_810,plain,(
    ! [A_176] :
      ( k1_funct_1('#skF_4','#skF_1'('#skF_4',k4_tmap_1(A_176,'#skF_3'))) = '#skF_1'('#skF_4',k4_tmap_1(A_176,'#skF_3'))
      | r1_tarski('#skF_4',k4_tmap_1(A_176,'#skF_3'))
      | ~ v1_funct_1(k4_tmap_1(A_176,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_176,'#skF_3'))
      | u1_struct_0(A_176) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_176)
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(resolution,[status(thm)],[c_755,c_806])).

tff(c_712,plain,(
    ! [A_172] :
      ( r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(k4_tmap_1(A_172,'#skF_3')))
      | ~ v1_funct_1(k4_tmap_1(A_172,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_172,'#skF_3'))
      | u1_struct_0(A_172) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_172)
      | ~ l1_pre_topc(A_172)
      | ~ v2_pre_topc(A_172)
      | v2_struct_0(A_172) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_699])).

tff(c_763,plain,(
    ! [A_177] :
      ( m1_subset_1('#skF_1'('#skF_4',k4_tmap_1(A_177,'#skF_3')),k1_relat_1('#skF_4'))
      | r1_tarski('#skF_4',k4_tmap_1(A_177,'#skF_3'))
      | ~ v1_funct_1(k4_tmap_1(A_177,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_177,'#skF_3'))
      | u1_struct_0(A_177) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_177)
      | ~ l1_pre_topc(A_177)
      | ~ v2_pre_topc(A_177)
      | v2_struct_0(A_177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_58,c_730])).

tff(c_385,plain,(
    ! [A_132,B_133] :
      ( k1_relat_1(k4_tmap_1(A_132,B_133)) = u1_struct_0(B_133)
      | ~ m1_pre_topc(B_133,A_132)
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132)
      | u1_struct_0(A_132) = k1_xboole_0
      | ~ m1_pre_topc(B_133,A_132)
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_215])).

tff(c_34,plain,(
    ! [A_20,B_26] :
      ( r2_hidden('#skF_1'(A_20,B_26),k1_relat_1(A_20))
      | r1_tarski(A_20,B_26)
      | ~ r1_tarski(k1_relat_1(A_20),k1_relat_1(B_26))
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_332,plain,(
    ! [A_122,B_123,C_124] :
      ( k1_funct_1(k4_tmap_1(A_122,B_123),C_124) = C_124
      | ~ r2_hidden(C_124,u1_struct_0(B_123))
      | ~ m1_subset_1(C_124,u1_struct_0(A_122))
      | ~ m1_pre_topc(B_123,A_122)
      | v2_struct_0(B_123)
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_334,plain,(
    ! [A_122,C_124] :
      ( k1_funct_1(k4_tmap_1(A_122,'#skF_3'),C_124) = C_124
      | ~ r2_hidden(C_124,k1_relat_1('#skF_4'))
      | ~ m1_subset_1(C_124,u1_struct_0(A_122))
      | ~ m1_pre_topc('#skF_3',A_122)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122)
      | v2_struct_0(A_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_332])).

tff(c_336,plain,(
    ! [A_125,C_126] :
      ( k1_funct_1(k4_tmap_1(A_125,'#skF_3'),C_126) = C_126
      | ~ r2_hidden(C_126,k1_relat_1('#skF_4'))
      | ~ m1_subset_1(C_126,u1_struct_0(A_125))
      | ~ m1_pre_topc('#skF_3',A_125)
      | ~ l1_pre_topc(A_125)
      | ~ v2_pre_topc(A_125)
      | v2_struct_0(A_125) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_334])).

tff(c_339,plain,(
    ! [A_125,B_26] :
      ( k1_funct_1(k4_tmap_1(A_125,'#skF_3'),'#skF_1'('#skF_4',B_26)) = '#skF_1'('#skF_4',B_26)
      | ~ m1_subset_1('#skF_1'('#skF_4',B_26),u1_struct_0(A_125))
      | ~ m1_pre_topc('#skF_3',A_125)
      | ~ l1_pre_topc(A_125)
      | ~ v2_pre_topc(A_125)
      | v2_struct_0(A_125)
      | r1_tarski('#skF_4',B_26)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_26))
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_336])).

tff(c_508,plain,(
    ! [A_142,B_143] :
      ( k1_funct_1(k4_tmap_1(A_142,'#skF_3'),'#skF_1'('#skF_4',B_143)) = '#skF_1'('#skF_4',B_143)
      | ~ m1_subset_1('#skF_1'('#skF_4',B_143),u1_struct_0(A_142))
      | ~ m1_pre_topc('#skF_3',A_142)
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142)
      | r1_tarski('#skF_4',B_143)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_143))
      | ~ v1_funct_1(B_143)
      | ~ v1_relat_1(B_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_58,c_339])).

tff(c_587,plain,(
    ! [A_154,B_155] :
      ( k1_funct_1(k4_tmap_1(A_154,'#skF_3'),'#skF_1'('#skF_4',B_155)) = '#skF_1'('#skF_4',B_155)
      | ~ v2_pre_topc(A_154)
      | r1_tarski('#skF_4',B_155)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_155))
      | ~ v1_funct_1(B_155)
      | ~ v1_relat_1(B_155)
      | ~ m1_subset_1('#skF_1'('#skF_4',B_155),k1_relat_1('#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_154)
      | ~ l1_pre_topc(A_154)
      | v2_struct_0(A_154) ) ),
    inference(resolution,[status(thm)],[c_170,c_508])).

tff(c_591,plain,(
    ! [A_154,A_132,B_133] :
      ( k1_funct_1(k4_tmap_1(A_154,'#skF_3'),'#skF_1'('#skF_4',k4_tmap_1(A_132,B_133))) = '#skF_1'('#skF_4',k4_tmap_1(A_132,B_133))
      | ~ v2_pre_topc(A_154)
      | r1_tarski('#skF_4',k4_tmap_1(A_132,B_133))
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(B_133))
      | ~ v1_funct_1(k4_tmap_1(A_132,B_133))
      | ~ v1_relat_1(k4_tmap_1(A_132,B_133))
      | ~ m1_subset_1('#skF_1'('#skF_4',k4_tmap_1(A_132,B_133)),k1_relat_1('#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_154)
      | ~ l1_pre_topc(A_154)
      | v2_struct_0(A_154)
      | ~ m1_pre_topc(B_133,A_132)
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132)
      | u1_struct_0(A_132) = k1_xboole_0
      | ~ m1_pre_topc(B_133,A_132)
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_385,c_587])).

tff(c_765,plain,(
    ! [A_154,A_177] :
      ( k1_funct_1(k4_tmap_1(A_154,'#skF_3'),'#skF_1'('#skF_4',k4_tmap_1(A_177,'#skF_3'))) = '#skF_1'('#skF_4',k4_tmap_1(A_177,'#skF_3'))
      | ~ v2_pre_topc(A_154)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_154)
      | ~ l1_pre_topc(A_154)
      | v2_struct_0(A_154)
      | r1_tarski('#skF_4',k4_tmap_1(A_177,'#skF_3'))
      | ~ v1_funct_1(k4_tmap_1(A_177,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_177,'#skF_3'))
      | u1_struct_0(A_177) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_177)
      | ~ l1_pre_topc(A_177)
      | ~ v2_pre_topc(A_177)
      | v2_struct_0(A_177) ) ),
    inference(resolution,[status(thm)],[c_763,c_591])).

tff(c_847,plain,(
    ! [A_191,A_192] :
      ( k1_funct_1(k4_tmap_1(A_191,'#skF_3'),'#skF_1'('#skF_4',k4_tmap_1(A_192,'#skF_3'))) = '#skF_1'('#skF_4',k4_tmap_1(A_192,'#skF_3'))
      | ~ v2_pre_topc(A_191)
      | ~ m1_pre_topc('#skF_3',A_191)
      | ~ l1_pre_topc(A_191)
      | v2_struct_0(A_191)
      | r1_tarski('#skF_4',k4_tmap_1(A_192,'#skF_3'))
      | ~ v1_funct_1(k4_tmap_1(A_192,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_192,'#skF_3'))
      | u1_struct_0(A_192) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_192)
      | ~ l1_pre_topc(A_192)
      | ~ v2_pre_topc(A_192)
      | v2_struct_0(A_192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_119,c_765])).

tff(c_32,plain,(
    ! [B_26,A_20] :
      ( k1_funct_1(B_26,'#skF_1'(A_20,B_26)) != k1_funct_1(A_20,'#skF_1'(A_20,B_26))
      | r1_tarski(A_20,B_26)
      | ~ r1_tarski(k1_relat_1(A_20),k1_relat_1(B_26))
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_856,plain,(
    ! [A_192] :
      ( k1_funct_1('#skF_4','#skF_1'('#skF_4',k4_tmap_1(A_192,'#skF_3'))) != '#skF_1'('#skF_4',k4_tmap_1(A_192,'#skF_3'))
      | r1_tarski('#skF_4',k4_tmap_1(A_192,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(k4_tmap_1(A_192,'#skF_3')))
      | ~ v1_funct_1(k4_tmap_1(A_192,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_192,'#skF_3'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ v2_pre_topc(A_192)
      | ~ m1_pre_topc('#skF_3',A_192)
      | ~ l1_pre_topc(A_192)
      | v2_struct_0(A_192)
      | r1_tarski('#skF_4',k4_tmap_1(A_192,'#skF_3'))
      | ~ v1_funct_1(k4_tmap_1(A_192,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_192,'#skF_3'))
      | u1_struct_0(A_192) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_192)
      | ~ l1_pre_topc(A_192)
      | ~ v2_pre_topc(A_192)
      | v2_struct_0(A_192) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_847,c_32])).

tff(c_868,plain,(
    ! [A_193] :
      ( k1_funct_1('#skF_4','#skF_1'('#skF_4',k4_tmap_1(A_193,'#skF_3'))) != '#skF_1'('#skF_4',k4_tmap_1(A_193,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(k4_tmap_1(A_193,'#skF_3')))
      | r1_tarski('#skF_4',k4_tmap_1(A_193,'#skF_3'))
      | ~ v1_funct_1(k4_tmap_1(A_193,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_193,'#skF_3'))
      | u1_struct_0(A_193) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_193)
      | ~ l1_pre_topc(A_193)
      | ~ v2_pre_topc(A_193)
      | v2_struct_0(A_193) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_58,c_856])).

tff(c_900,plain,(
    ! [A_197] :
      ( k1_funct_1('#skF_4','#skF_1'('#skF_4',k4_tmap_1(A_197,'#skF_3'))) != '#skF_1'('#skF_4',k4_tmap_1(A_197,'#skF_3'))
      | r1_tarski('#skF_4',k4_tmap_1(A_197,'#skF_3'))
      | ~ v1_funct_1(k4_tmap_1(A_197,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_197,'#skF_3'))
      | u1_struct_0(A_197) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_197)
      | ~ l1_pre_topc(A_197)
      | ~ v2_pre_topc(A_197)
      | v2_struct_0(A_197) ) ),
    inference(resolution,[status(thm)],[c_712,c_868])).

tff(c_907,plain,(
    ! [A_176] :
      ( r1_tarski('#skF_4',k4_tmap_1(A_176,'#skF_3'))
      | ~ v1_funct_1(k4_tmap_1(A_176,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_176,'#skF_3'))
      | u1_struct_0(A_176) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_176)
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_810,c_900])).

tff(c_606,plain,(
    ! [A_156,B_157,A_158] :
      ( r1_tarski(k1_relat_1(A_156),u1_struct_0(B_157))
      | ~ r1_tarski(A_156,k4_tmap_1(A_158,B_157))
      | ~ v1_funct_1(k4_tmap_1(A_158,B_157))
      | ~ v1_relat_1(k4_tmap_1(A_158,B_157))
      | ~ v1_funct_1(A_156)
      | ~ v1_relat_1(A_156)
      | ~ m1_pre_topc(B_157,A_158)
      | ~ l1_pre_topc(A_158)
      | ~ v2_pre_topc(A_158)
      | v2_struct_0(A_158)
      | u1_struct_0(A_158) = k1_xboole_0
      | ~ m1_pre_topc(B_157,A_158)
      | ~ l1_pre_topc(A_158)
      | ~ v2_pre_topc(A_158)
      | v2_struct_0(A_158) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_38])).

tff(c_611,plain,(
    ! [A_159,B_160] :
      ( r1_tarski(k1_relat_1(k4_tmap_1(A_159,B_160)),u1_struct_0(B_160))
      | ~ v1_funct_1(k4_tmap_1(A_159,B_160))
      | ~ v1_relat_1(k4_tmap_1(A_159,B_160))
      | u1_struct_0(A_159) = k1_xboole_0
      | ~ m1_pre_topc(B_160,A_159)
      | ~ l1_pre_topc(A_159)
      | ~ v2_pre_topc(A_159)
      | v2_struct_0(A_159) ) ),
    inference(resolution,[status(thm)],[c_6,c_606])).

tff(c_624,plain,(
    ! [A_159] :
      ( r1_tarski(k1_relat_1(k4_tmap_1(A_159,'#skF_3')),k1_relat_1('#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_159,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_159,'#skF_3'))
      | u1_struct_0(A_159) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_159)
      | ~ l1_pre_topc(A_159)
      | ~ v2_pre_topc(A_159)
      | v2_struct_0(A_159) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_611])).

tff(c_1075,plain,(
    ! [A_226,B_227,B_228] :
      ( r2_hidden('#skF_1'(k4_tmap_1(A_226,B_227),B_228),u1_struct_0(B_227))
      | r1_tarski(k4_tmap_1(A_226,B_227),B_228)
      | ~ r1_tarski(k1_relat_1(k4_tmap_1(A_226,B_227)),k1_relat_1(B_228))
      | ~ v1_funct_1(B_228)
      | ~ v1_relat_1(B_228)
      | ~ v1_funct_1(k4_tmap_1(A_226,B_227))
      | ~ v1_relat_1(k4_tmap_1(A_226,B_227))
      | ~ m1_pre_topc(B_227,A_226)
      | ~ l1_pre_topc(A_226)
      | ~ v2_pre_topc(A_226)
      | v2_struct_0(A_226)
      | u1_struct_0(A_226) = k1_xboole_0
      | ~ m1_pre_topc(B_227,A_226)
      | ~ l1_pre_topc(A_226)
      | ~ v2_pre_topc(A_226)
      | v2_struct_0(A_226) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_34])).

tff(c_1122,plain,(
    ! [A_236,B_237] :
      ( r2_hidden('#skF_1'(k4_tmap_1(A_236,'#skF_3'),B_237),k1_relat_1('#skF_4'))
      | r1_tarski(k4_tmap_1(A_236,'#skF_3'),B_237)
      | ~ r1_tarski(k1_relat_1(k4_tmap_1(A_236,'#skF_3')),k1_relat_1(B_237))
      | ~ v1_funct_1(B_237)
      | ~ v1_relat_1(B_237)
      | ~ v1_funct_1(k4_tmap_1(A_236,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_236,'#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_236)
      | ~ l1_pre_topc(A_236)
      | ~ v2_pre_topc(A_236)
      | v2_struct_0(A_236)
      | u1_struct_0(A_236) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_236)
      | ~ l1_pre_topc(A_236)
      | ~ v2_pre_topc(A_236)
      | v2_struct_0(A_236) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_1075])).

tff(c_36,plain,(
    ! [B_26,C_29,A_20] :
      ( k1_funct_1(B_26,C_29) = k1_funct_1(A_20,C_29)
      | ~ r2_hidden(C_29,k1_relat_1(A_20))
      | ~ r1_tarski(A_20,B_26)
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1128,plain,(
    ! [B_26,A_236,B_237] :
      ( k1_funct_1(B_26,'#skF_1'(k4_tmap_1(A_236,'#skF_3'),B_237)) = k1_funct_1('#skF_4','#skF_1'(k4_tmap_1(A_236,'#skF_3'),B_237))
      | ~ r1_tarski('#skF_4',B_26)
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | r1_tarski(k4_tmap_1(A_236,'#skF_3'),B_237)
      | ~ r1_tarski(k1_relat_1(k4_tmap_1(A_236,'#skF_3')),k1_relat_1(B_237))
      | ~ v1_funct_1(B_237)
      | ~ v1_relat_1(B_237)
      | ~ v1_funct_1(k4_tmap_1(A_236,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_236,'#skF_3'))
      | u1_struct_0(A_236) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_236)
      | ~ l1_pre_topc(A_236)
      | ~ v2_pre_topc(A_236)
      | v2_struct_0(A_236) ) ),
    inference(resolution,[status(thm)],[c_1122,c_36])).

tff(c_1324,plain,(
    ! [B_271,A_272,B_273] :
      ( k1_funct_1(B_271,'#skF_1'(k4_tmap_1(A_272,'#skF_3'),B_273)) = k1_funct_1('#skF_4','#skF_1'(k4_tmap_1(A_272,'#skF_3'),B_273))
      | ~ r1_tarski('#skF_4',B_271)
      | ~ v1_funct_1(B_271)
      | ~ v1_relat_1(B_271)
      | r1_tarski(k4_tmap_1(A_272,'#skF_3'),B_273)
      | ~ r1_tarski(k1_relat_1(k4_tmap_1(A_272,'#skF_3')),k1_relat_1(B_273))
      | ~ v1_funct_1(B_273)
      | ~ v1_relat_1(B_273)
      | ~ v1_funct_1(k4_tmap_1(A_272,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_272,'#skF_3'))
      | u1_struct_0(A_272) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_272)
      | ~ l1_pre_topc(A_272)
      | ~ v2_pre_topc(A_272)
      | v2_struct_0(A_272) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_58,c_1128])).

tff(c_1326,plain,(
    ! [B_271,A_159] :
      ( k1_funct_1(B_271,'#skF_1'(k4_tmap_1(A_159,'#skF_3'),'#skF_4')) = k1_funct_1('#skF_4','#skF_1'(k4_tmap_1(A_159,'#skF_3'),'#skF_4'))
      | ~ r1_tarski('#skF_4',B_271)
      | ~ v1_funct_1(B_271)
      | ~ v1_relat_1(B_271)
      | r1_tarski(k4_tmap_1(A_159,'#skF_3'),'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_funct_1(k4_tmap_1(A_159,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_159,'#skF_3'))
      | u1_struct_0(A_159) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_159)
      | ~ l1_pre_topc(A_159)
      | ~ v2_pre_topc(A_159)
      | v2_struct_0(A_159) ) ),
    inference(resolution,[status(thm)],[c_624,c_1324])).

tff(c_1359,plain,(
    ! [B_277,A_278] :
      ( k1_funct_1(B_277,'#skF_1'(k4_tmap_1(A_278,'#skF_3'),'#skF_4')) = k1_funct_1('#skF_4','#skF_1'(k4_tmap_1(A_278,'#skF_3'),'#skF_4'))
      | ~ r1_tarski('#skF_4',B_277)
      | ~ v1_funct_1(B_277)
      | ~ v1_relat_1(B_277)
      | r1_tarski(k4_tmap_1(A_278,'#skF_3'),'#skF_4')
      | ~ v1_funct_1(k4_tmap_1(A_278,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_278,'#skF_3'))
      | u1_struct_0(A_278) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_278)
      | ~ l1_pre_topc(A_278)
      | ~ v2_pre_topc(A_278)
      | v2_struct_0(A_278) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_58,c_1326])).

tff(c_1382,plain,(
    ! [A_278] :
      ( ~ r1_tarski(k1_relat_1(k4_tmap_1(A_278,'#skF_3')),k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_4',k4_tmap_1(A_278,'#skF_3'))
      | r1_tarski(k4_tmap_1(A_278,'#skF_3'),'#skF_4')
      | ~ v1_funct_1(k4_tmap_1(A_278,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_278,'#skF_3'))
      | u1_struct_0(A_278) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_278)
      | ~ l1_pre_topc(A_278)
      | ~ v2_pre_topc(A_278)
      | v2_struct_0(A_278) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1359,c_32])).

tff(c_1404,plain,(
    ! [A_279] :
      ( ~ r1_tarski(k1_relat_1(k4_tmap_1(A_279,'#skF_3')),k1_relat_1('#skF_4'))
      | ~ r1_tarski('#skF_4',k4_tmap_1(A_279,'#skF_3'))
      | r1_tarski(k4_tmap_1(A_279,'#skF_3'),'#skF_4')
      | ~ v1_funct_1(k4_tmap_1(A_279,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_279,'#skF_3'))
      | u1_struct_0(A_279) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_279)
      | ~ l1_pre_topc(A_279)
      | ~ v2_pre_topc(A_279)
      | v2_struct_0(A_279) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_58,c_1382])).

tff(c_1426,plain,(
    ! [A_280] :
      ( ~ r1_tarski('#skF_4',k4_tmap_1(A_280,'#skF_3'))
      | r1_tarski(k4_tmap_1(A_280,'#skF_3'),'#skF_4')
      | ~ v1_funct_1(k4_tmap_1(A_280,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_280,'#skF_3'))
      | u1_struct_0(A_280) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_280)
      | ~ l1_pre_topc(A_280)
      | ~ v2_pre_topc(A_280)
      | v2_struct_0(A_280) ) ),
    inference(resolution,[status(thm)],[c_624,c_1404])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1485,plain,(
    ! [A_284] :
      ( k4_tmap_1(A_284,'#skF_3') = '#skF_4'
      | ~ r1_tarski('#skF_4',k4_tmap_1(A_284,'#skF_3'))
      | ~ v1_funct_1(k4_tmap_1(A_284,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_284,'#skF_3'))
      | u1_struct_0(A_284) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_284)
      | ~ l1_pre_topc(A_284)
      | ~ v2_pre_topc(A_284)
      | v2_struct_0(A_284) ) ),
    inference(resolution,[status(thm)],[c_1426,c_2])).

tff(c_1490,plain,(
    ! [A_285] :
      ( k4_tmap_1(A_285,'#skF_3') = '#skF_4'
      | ~ v1_funct_1(k4_tmap_1(A_285,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_285,'#skF_3'))
      | u1_struct_0(A_285) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_285)
      | ~ l1_pre_topc(A_285)
      | ~ v2_pre_topc(A_285)
      | v2_struct_0(A_285) ) ),
    inference(resolution,[status(thm)],[c_907,c_1485])).

tff(c_1496,plain,(
    ! [A_286] :
      ( k4_tmap_1(A_286,'#skF_3') = '#skF_4'
      | ~ v1_funct_1(k4_tmap_1(A_286,'#skF_3'))
      | u1_struct_0(A_286) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_286)
      | ~ l1_pre_topc(A_286)
      | ~ v2_pre_topc(A_286)
      | v2_struct_0(A_286) ) ),
    inference(resolution,[status(thm)],[c_218,c_1490])).

tff(c_1502,plain,(
    ! [A_287] :
      ( k4_tmap_1(A_287,'#skF_3') = '#skF_4'
      | u1_struct_0(A_287) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_287)
      | ~ l1_pre_topc(A_287)
      | ~ v2_pre_topc(A_287)
      | v2_struct_0(A_287) ) ),
    inference(resolution,[status(thm)],[c_46,c_1496])).

tff(c_1505,plain,
    ( k4_tmap_1('#skF_2','#skF_3') = '#skF_4'
    | u1_struct_0('#skF_2') = k1_xboole_0
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_1502])).

tff(c_1508,plain,
    ( k4_tmap_1('#skF_2','#skF_3') = '#skF_4'
    | u1_struct_0('#skF_2') = k1_xboole_0
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1505])).

tff(c_1509,plain,
    ( k4_tmap_1('#skF_2','#skF_3') = '#skF_4'
    | u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1508])).

tff(c_1510,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1509])).

tff(c_125,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_56])).

tff(c_1528,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1510,c_125])).

tff(c_124,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_54])).

tff(c_1526,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1510,c_124])).

tff(c_18,plain,(
    ! [C_15,A_13] :
      ( k1_xboole_0 = C_15
      | ~ v1_funct_2(C_15,A_13,k1_xboole_0)
      | k1_xboole_0 = A_13
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1671,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k1_xboole_0)
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1526,c_18])).

tff(c_1690,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1528,c_1671])).

tff(c_1695,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1690])).

tff(c_1527,plain,(
    r2_funct_2(k1_relat_1('#skF_4'),k1_xboole_0,'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1510,c_120])).

tff(c_1698,plain,(
    r2_funct_2(k1_xboole_0,k1_xboole_0,'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1695,c_1527])).

tff(c_208,plain,(
    ! [A_100] :
      ( m1_subset_1(k4_tmap_1(A_100,'#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(A_100))))
      | ~ m1_pre_topc('#skF_3',A_100)
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_191])).

tff(c_1588,plain,
    ( m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k1_xboole_0)))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1510,c_208])).

tff(c_1639,plain,
    ( m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k1_xboole_0)))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_1588])).

tff(c_1640,plain,(
    m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k1_xboole_0))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1639])).

tff(c_2070,plain,(
    m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1695,c_1640])).

tff(c_2093,plain,
    ( v1_relat_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2070,c_10])).

tff(c_2116,plain,(
    v1_relat_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2093])).

tff(c_156,plain,(
    ! [A_88,B_89] :
      ( v1_funct_2(k4_tmap_1(A_88,B_89),u1_struct_0(B_89),u1_struct_0(A_88))
      | ~ m1_pre_topc(B_89,A_88)
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_159,plain,(
    ! [A_88] :
      ( v1_funct_2(k4_tmap_1(A_88,'#skF_3'),k1_relat_1('#skF_4'),u1_struct_0(A_88))
      | ~ m1_pre_topc('#skF_3',A_88)
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88)
      | v2_struct_0(A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_156])).

tff(c_1597,plain,
    ( v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),k1_relat_1('#skF_4'),k1_xboole_0)
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1510,c_159])).

tff(c_1645,plain,
    ( v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),k1_relat_1('#skF_4'),k1_xboole_0)
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_1597])).

tff(c_1646,plain,(
    v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1645])).

tff(c_1697,plain,(
    v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1695,c_1646])).

tff(c_28,plain,(
    ! [A_16,B_17,D_19] :
      ( r2_funct_2(A_16,B_17,D_19,D_19)
      | ~ m1_subset_1(D_19,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17)))
      | ~ v1_funct_2(D_19,A_16,B_17)
      | ~ v1_funct_1(D_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2078,plain,
    ( r2_funct_2(k1_xboole_0,k1_xboole_0,k4_tmap_1('#skF_2','#skF_3'),k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2070,c_28])).

tff(c_2103,plain,
    ( r2_funct_2(k1_xboole_0,k1_xboole_0,k4_tmap_1('#skF_2','#skF_3'),k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1697,c_2078])).

tff(c_2374,plain,(
    ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2103])).

tff(c_2377,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_2374])).

tff(c_2380,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_2377])).

tff(c_2382,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2380])).

tff(c_2384,plain,(
    v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2103])).

tff(c_24,plain,(
    ! [B_14,C_15] :
      ( k1_relset_1(k1_xboole_0,B_14,C_15) = k1_xboole_0
      | ~ v1_funct_2(C_15,k1_xboole_0,B_14)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2084,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1('#skF_2','#skF_3')) = k1_xboole_0
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2070,c_24])).

tff(c_2108,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1697,c_2084])).

tff(c_2113,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1('#skF_2','#skF_3')) = k1_relat_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2070,c_14])).

tff(c_2138,plain,(
    k1_relat_1(k4_tmap_1('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2108,c_2113])).

tff(c_1762,plain,(
    ! [B_119] :
      ( m1_subset_1('#skF_1'('#skF_4',B_119),k1_relat_1('#skF_4'))
      | r1_tarski('#skF_4',B_119)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_119))
      | ~ v1_funct_1(B_119)
      | ~ v1_relat_1(B_119)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1695,c_322])).

tff(c_2523,plain,(
    ! [B_317] :
      ( m1_subset_1('#skF_1'('#skF_4',B_317),k1_xboole_0)
      | r1_tarski('#skF_4',B_317)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_317))
      | ~ v1_funct_1(B_317)
      | ~ v1_relat_1(B_317) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_58,c_1695,c_1762])).

tff(c_2529,plain,
    ( m1_subset_1('#skF_1'('#skF_4',k4_tmap_1('#skF_2','#skF_3')),k1_xboole_0)
    | r1_tarski('#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_relat_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2138,c_2523])).

tff(c_2538,plain,
    ( m1_subset_1('#skF_1'('#skF_4',k4_tmap_1('#skF_2','#skF_3')),k1_xboole_0)
    | r1_tarski('#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2116,c_2384,c_6,c_2529])).

tff(c_2541,plain,(
    r1_tarski('#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2538])).

tff(c_2567,plain,
    ( k4_tmap_1('#skF_2','#skF_3') = '#skF_4'
    | ~ r1_tarski(k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2541,c_2])).

tff(c_2568,plain,(
    ~ r1_tarski(k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2567])).

tff(c_2197,plain,(
    ! [B_26] :
      ( r2_hidden('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),B_26),k1_xboole_0)
      | r1_tarski(k4_tmap_1('#skF_2','#skF_3'),B_26)
      | ~ r1_tarski(k1_relat_1(k4_tmap_1('#skF_2','#skF_3')),k1_relat_1(B_26))
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
      | ~ v1_relat_1(k4_tmap_1('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2138,c_34])).

tff(c_2272,plain,(
    ! [B_26] :
      ( r2_hidden('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),B_26),k1_xboole_0)
      | r1_tarski(k4_tmap_1('#skF_2','#skF_3'),B_26)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_26))
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2116,c_2138,c_2197])).

tff(c_3968,plain,(
    ! [B_26] :
      ( r2_hidden('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),B_26),k1_xboole_0)
      | r1_tarski(k4_tmap_1('#skF_2','#skF_3'),B_26)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_26))
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2384,c_2272])).

tff(c_1764,plain,(
    ! [A_118] :
      ( m1_subset_1('#skF_1'(A_118,'#skF_4'),k1_relat_1(A_118))
      | r1_tarski(A_118,'#skF_4')
      | ~ r1_tarski(k1_relat_1(A_118),k1_xboole_0)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1695,c_322])).

tff(c_2643,plain,(
    ! [A_327] :
      ( m1_subset_1('#skF_1'(A_327,'#skF_4'),k1_relat_1(A_327))
      | r1_tarski(A_327,'#skF_4')
      | ~ r1_tarski(k1_relat_1(A_327),k1_xboole_0)
      | ~ v1_funct_1(A_327)
      | ~ v1_relat_1(A_327) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_58,c_1764])).

tff(c_2646,plain,
    ( m1_subset_1('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_xboole_0)
    | r1_tarski(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | ~ r1_tarski(k1_relat_1(k4_tmap_1('#skF_2','#skF_3')),k1_xboole_0)
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_relat_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2138,c_2643])).

tff(c_2654,plain,
    ( m1_subset_1('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_xboole_0)
    | r1_tarski(k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2116,c_2384,c_6,c_2138,c_2646])).

tff(c_2655,plain,(
    m1_subset_1('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_2568,c_2654])).

tff(c_318,plain,(
    ! [B_26,A_118,B_119] :
      ( k1_funct_1(B_26,'#skF_1'(A_118,B_119)) = k1_funct_1(A_118,'#skF_1'(A_118,B_119))
      | ~ r1_tarski(A_118,B_26)
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26)
      | r1_tarski(A_118,B_119)
      | ~ r1_tarski(k1_relat_1(A_118),k1_relat_1(B_119))
      | ~ v1_funct_1(B_119)
      | ~ v1_relat_1(B_119)
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118) ) ),
    inference(resolution,[status(thm)],[c_308,c_36])).

tff(c_1760,plain,(
    ! [B_26,A_118] :
      ( k1_funct_1(B_26,'#skF_1'(A_118,'#skF_4')) = k1_funct_1(A_118,'#skF_1'(A_118,'#skF_4'))
      | ~ r1_tarski(A_118,B_26)
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26)
      | r1_tarski(A_118,'#skF_4')
      | ~ r1_tarski(k1_relat_1(A_118),k1_xboole_0)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1695,c_318])).

tff(c_4706,plain,(
    ! [B_410,A_411] :
      ( k1_funct_1(B_410,'#skF_1'(A_411,'#skF_4')) = k1_funct_1(A_411,'#skF_1'(A_411,'#skF_4'))
      | ~ r1_tarski(A_411,B_410)
      | ~ v1_funct_1(B_410)
      | ~ v1_relat_1(B_410)
      | r1_tarski(A_411,'#skF_4')
      | ~ r1_tarski(k1_relat_1(A_411),k1_xboole_0)
      | ~ v1_funct_1(A_411)
      | ~ v1_relat_1(A_411) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_58,c_1760])).

tff(c_4720,plain,(
    ! [B_410] :
      ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = k1_funct_1(B_410,'#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'))
      | ~ r1_tarski(k4_tmap_1('#skF_2','#skF_3'),B_410)
      | ~ v1_funct_1(B_410)
      | ~ v1_relat_1(B_410)
      | r1_tarski(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
      | ~ v1_relat_1(k4_tmap_1('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2138,c_4706])).

tff(c_4734,plain,(
    ! [B_410] :
      ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = k1_funct_1(B_410,'#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'))
      | ~ r1_tarski(k4_tmap_1('#skF_2','#skF_3'),B_410)
      | ~ v1_funct_1(B_410)
      | ~ v1_relat_1(B_410)
      | r1_tarski(k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2116,c_2384,c_6,c_4720])).

tff(c_4738,plain,(
    ! [B_412] :
      ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = k1_funct_1(B_412,'#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'))
      | ~ r1_tarski(k4_tmap_1('#skF_2','#skF_3'),B_412)
      | ~ v1_funct_1(B_412)
      | ~ v1_relat_1(B_412) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2568,c_4734])).

tff(c_1729,plain,(
    ! [C_91,A_92] :
      ( m1_subset_1(C_91,u1_struct_0(A_92))
      | ~ m1_subset_1(C_91,k1_xboole_0)
      | ~ m1_pre_topc('#skF_3',A_92)
      | ~ l1_pre_topc(A_92)
      | v2_struct_0(A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1695,c_170])).

tff(c_1730,plain,(
    u1_struct_0('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1695,c_119])).

tff(c_48,plain,(
    ! [A_39,B_43,C_45] :
      ( k1_funct_1(k4_tmap_1(A_39,B_43),C_45) = C_45
      | ~ r2_hidden(C_45,u1_struct_0(B_43))
      | ~ m1_subset_1(C_45,u1_struct_0(A_39))
      | ~ m1_pre_topc(B_43,A_39)
      | v2_struct_0(B_43)
      | ~ l1_pre_topc(A_39)
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_1864,plain,(
    ! [A_39,C_45] :
      ( k1_funct_1(k4_tmap_1(A_39,'#skF_3'),C_45) = C_45
      | ~ r2_hidden(C_45,k1_xboole_0)
      | ~ m1_subset_1(C_45,u1_struct_0(A_39))
      | ~ m1_pre_topc('#skF_3',A_39)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_39)
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1730,c_48])).

tff(c_2739,plain,(
    ! [A_332,C_333] :
      ( k1_funct_1(k4_tmap_1(A_332,'#skF_3'),C_333) = C_333
      | ~ r2_hidden(C_333,k1_xboole_0)
      | ~ m1_subset_1(C_333,u1_struct_0(A_332))
      | ~ m1_pre_topc('#skF_3',A_332)
      | ~ l1_pre_topc(A_332)
      | ~ v2_pre_topc(A_332)
      | v2_struct_0(A_332) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1864])).

tff(c_2752,plain,(
    ! [A_92,C_91] :
      ( k1_funct_1(k4_tmap_1(A_92,'#skF_3'),C_91) = C_91
      | ~ r2_hidden(C_91,k1_xboole_0)
      | ~ v2_pre_topc(A_92)
      | ~ m1_subset_1(C_91,k1_xboole_0)
      | ~ m1_pre_topc('#skF_3',A_92)
      | ~ l1_pre_topc(A_92)
      | v2_struct_0(A_92) ) ),
    inference(resolution,[status(thm)],[c_1729,c_2739])).

tff(c_4758,plain,(
    ! [B_412] :
      ( k1_funct_1(B_412,'#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
      | ~ r2_hidden('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_xboole_0)
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_subset_1('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_xboole_0)
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(k4_tmap_1('#skF_2','#skF_3'),B_412)
      | ~ v1_funct_1(B_412)
      | ~ v1_relat_1(B_412) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4738,c_2752])).

tff(c_4849,plain,(
    ! [B_412] :
      ( k1_funct_1(B_412,'#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
      | ~ r2_hidden('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_xboole_0)
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(k4_tmap_1('#skF_2','#skF_3'),B_412)
      | ~ v1_funct_1(B_412)
      | ~ v1_relat_1(B_412) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_2655,c_66,c_4758])).

tff(c_4850,plain,(
    ! [B_412] :
      ( k1_funct_1(B_412,'#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
      | ~ r2_hidden('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_xboole_0)
      | ~ r1_tarski(k4_tmap_1('#skF_2','#skF_3'),B_412)
      | ~ v1_funct_1(B_412)
      | ~ v1_relat_1(B_412) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4849])).

tff(c_5033,plain,(
    ~ r2_hidden('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_4850])).

tff(c_5036,plain,
    ( r1_tarski(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | ~ r1_tarski(k1_xboole_0,k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3968,c_5033])).

tff(c_5039,plain,(
    r1_tarski(k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_58,c_6,c_1695,c_5036])).

tff(c_5041,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2568,c_5039])).

tff(c_5043,plain,(
    r2_hidden('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_4850])).

tff(c_1523,plain,(
    ! [D_57] :
      ( k1_funct_1('#skF_4',D_57) = D_57
      | ~ r2_hidden(D_57,k1_relat_1('#skF_4'))
      | ~ m1_subset_1(D_57,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1510,c_122])).

tff(c_2287,plain,(
    ! [D_57] :
      ( k1_funct_1('#skF_4',D_57) = D_57
      | ~ r2_hidden(D_57,k1_xboole_0)
      | ~ m1_subset_1(D_57,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1695,c_1523])).

tff(c_5048,plain,
    ( k1_funct_1('#skF_4','#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | ~ m1_subset_1('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_5043,c_2287])).

tff(c_5055,plain,(
    k1_funct_1('#skF_4','#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2655,c_5048])).

tff(c_2751,plain,(
    ! [C_333] :
      ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),C_333) = C_333
      | ~ r2_hidden(C_333,k1_xboole_0)
      | ~ m1_subset_1(C_333,k1_xboole_0)
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1510,c_2739])).

tff(c_2756,plain,(
    ! [C_333] :
      ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),C_333) = C_333
      | ~ r2_hidden(C_333,k1_xboole_0)
      | ~ m1_subset_1(C_333,k1_xboole_0)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_2751])).

tff(c_2757,plain,(
    ! [C_333] :
      ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),C_333) = C_333
      | ~ r2_hidden(C_333,k1_xboole_0)
      | ~ m1_subset_1(C_333,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2756])).

tff(c_4785,plain,(
    ! [B_412] :
      ( k1_funct_1(B_412,'#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) != k1_funct_1('#skF_4','#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'))
      | r1_tarski(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
      | ~ r1_tarski(k1_relat_1(k4_tmap_1('#skF_2','#skF_3')),k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
      | ~ v1_relat_1(k4_tmap_1('#skF_2','#skF_3'))
      | ~ r1_tarski(k4_tmap_1('#skF_2','#skF_3'),B_412)
      | ~ v1_funct_1(B_412)
      | ~ v1_relat_1(B_412) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4738,c_32])).

tff(c_4876,plain,(
    ! [B_412] :
      ( k1_funct_1(B_412,'#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) != k1_funct_1('#skF_4','#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'))
      | r1_tarski(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
      | ~ r1_tarski(k4_tmap_1('#skF_2','#skF_3'),B_412)
      | ~ v1_funct_1(B_412)
      | ~ v1_relat_1(B_412) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2116,c_2384,c_86,c_58,c_6,c_1695,c_2138,c_4785])).

tff(c_4923,plain,(
    ! [B_413] :
      ( k1_funct_1(B_413,'#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) != k1_funct_1('#skF_4','#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'))
      | ~ r1_tarski(k4_tmap_1('#skF_2','#skF_3'),B_413)
      | ~ v1_funct_1(B_413)
      | ~ v1_relat_1(B_413) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2568,c_4876])).

tff(c_4961,plain,
    ( k1_funct_1('#skF_4','#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) != '#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | ~ r1_tarski(k4_tmap_1('#skF_2','#skF_3'),k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_relat_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ r2_hidden('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_xboole_0)
    | ~ m1_subset_1('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2757,c_4923])).

tff(c_5010,plain,
    ( k1_funct_1('#skF_4','#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) != '#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | ~ r2_hidden('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2655,c_2116,c_2384,c_6,c_4961])).

tff(c_5090,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5043,c_5055,c_5010])).

tff(c_5091,plain,(
    k4_tmap_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2567])).

tff(c_50,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_123,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_50])).

tff(c_1524,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),k1_xboole_0,k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1510,c_123])).

tff(c_2069,plain,(
    ~ r2_funct_2(k1_xboole_0,k1_xboole_0,k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1695,c_1524])).

tff(c_5100,plain,(
    ~ r2_funct_2(k1_xboole_0,k1_xboole_0,'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5091,c_2069])).

tff(c_5111,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1698,c_5100])).

tff(c_5113,plain,(
    ~ r1_tarski('#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2538])).

tff(c_5112,plain,(
    m1_subset_1('#skF_1'('#skF_4',k4_tmap_1('#skF_2','#skF_3')),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2538])).

tff(c_342,plain,(
    ! [A_125,B_26] :
      ( k1_funct_1(k4_tmap_1(A_125,'#skF_3'),'#skF_1'('#skF_4',B_26)) = '#skF_1'('#skF_4',B_26)
      | ~ m1_subset_1('#skF_1'('#skF_4',B_26),u1_struct_0(A_125))
      | ~ m1_pre_topc('#skF_3',A_125)
      | ~ l1_pre_topc(A_125)
      | ~ v2_pre_topc(A_125)
      | v2_struct_0(A_125)
      | r1_tarski('#skF_4',B_26)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_26))
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_58,c_339])).

tff(c_1565,plain,(
    ! [B_26] :
      ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_4',B_26)) = '#skF_1'('#skF_4',B_26)
      | ~ m1_subset_1('#skF_1'('#skF_4',B_26),k1_xboole_0)
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | r1_tarski('#skF_4',B_26)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_26))
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1510,c_342])).

tff(c_1622,plain,(
    ! [B_26] :
      ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_4',B_26)) = '#skF_1'('#skF_4',B_26)
      | ~ m1_subset_1('#skF_1'('#skF_4',B_26),k1_xboole_0)
      | v2_struct_0('#skF_2')
      | r1_tarski('#skF_4',B_26)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_26))
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_1565])).

tff(c_1623,plain,(
    ! [B_26] :
      ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_4',B_26)) = '#skF_1'('#skF_4',B_26)
      | ~ m1_subset_1('#skF_1'('#skF_4',B_26),k1_xboole_0)
      | r1_tarski('#skF_4',B_26)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_26))
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1622])).

tff(c_5654,plain,(
    ! [B_441] :
      ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_4',B_441)) = '#skF_1'('#skF_4',B_441)
      | ~ m1_subset_1('#skF_1'('#skF_4',B_441),k1_xboole_0)
      | r1_tarski('#skF_4',B_441)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_441))
      | ~ v1_funct_1(B_441)
      | ~ v1_relat_1(B_441) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1695,c_1623])).

tff(c_5667,plain,
    ( k1_funct_1('#skF_4','#skF_1'('#skF_4',k4_tmap_1('#skF_2','#skF_3'))) != '#skF_1'('#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | r1_tarski('#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(k4_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_relat_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_4',k4_tmap_1('#skF_2','#skF_3')),k1_xboole_0)
    | r1_tarski('#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(k4_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_relat_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5654,c_32])).

tff(c_5683,plain,
    ( k1_funct_1('#skF_4','#skF_1'('#skF_4',k4_tmap_1('#skF_2','#skF_3'))) != '#skF_1'('#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | r1_tarski('#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2116,c_2384,c_6,c_2138,c_5112,c_86,c_58,c_2116,c_2384,c_6,c_1695,c_2138,c_5667])).

tff(c_5684,plain,(
    k1_funct_1('#skF_4','#skF_1'('#skF_4',k4_tmap_1('#skF_2','#skF_3'))) != '#skF_1'('#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_5113,c_5683])).

tff(c_1767,plain,(
    ! [B_26] :
      ( r2_hidden('#skF_1'('#skF_4',B_26),k1_xboole_0)
      | r1_tarski('#skF_4',B_26)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_26))
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1695,c_34])).

tff(c_5136,plain,(
    ! [B_416] :
      ( r2_hidden('#skF_1'('#skF_4',B_416),k1_xboole_0)
      | r1_tarski('#skF_4',B_416)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_416))
      | ~ v1_funct_1(B_416)
      | ~ v1_relat_1(B_416) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_58,c_1695,c_1767])).

tff(c_6936,plain,(
    ! [B_482] :
      ( k1_funct_1('#skF_4','#skF_1'('#skF_4',B_482)) = '#skF_1'('#skF_4',B_482)
      | ~ m1_subset_1('#skF_1'('#skF_4',B_482),k1_xboole_0)
      | r1_tarski('#skF_4',B_482)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_482))
      | ~ v1_funct_1(B_482)
      | ~ v1_relat_1(B_482) ) ),
    inference(resolution,[status(thm)],[c_5136,c_2287])).

tff(c_6948,plain,
    ( k1_funct_1('#skF_4','#skF_1'('#skF_4',k4_tmap_1('#skF_2','#skF_3'))) = '#skF_1'('#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_4',k4_tmap_1('#skF_2','#skF_3')),k1_xboole_0)
    | r1_tarski('#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_relat_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2138,c_6936])).

tff(c_6961,plain,
    ( k1_funct_1('#skF_4','#skF_1'('#skF_4',k4_tmap_1('#skF_2','#skF_3'))) = '#skF_1'('#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | r1_tarski('#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2116,c_2384,c_6,c_5112,c_6948])).

tff(c_6963,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5113,c_5684,c_6961])).

tff(c_6964,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1690])).

tff(c_6968,plain,(
    r2_funct_2(k1_relat_1('#skF_4'),'#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6964,c_1527])).

tff(c_6965,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1690])).

tff(c_7031,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6964,c_6965])).

tff(c_6967,plain,(
    v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),k1_relat_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6964,c_1646])).

tff(c_7182,plain,(
    m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6964,c_1640])).

tff(c_7297,plain,(
    ! [C_502,A_503] :
      ( C_502 = '#skF_4'
      | ~ v1_funct_2(C_502,A_503,'#skF_4')
      | A_503 = '#skF_4'
      | ~ m1_subset_1(C_502,k1_zfmisc_1(k2_zfmisc_1(A_503,'#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6964,c_6964,c_6964,c_6964,c_18])).

tff(c_7303,plain,
    ( k4_tmap_1('#skF_2','#skF_3') = '#skF_4'
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),k1_relat_1('#skF_4'),'#skF_4')
    | k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_7182,c_7297])).

tff(c_7310,plain,
    ( k4_tmap_1('#skF_2','#skF_3') = '#skF_4'
    | k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6967,c_7303])).

tff(c_7311,plain,(
    k4_tmap_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_7031,c_7310])).

tff(c_7181,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6964,c_1524])).

tff(c_7320,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),'#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7311,c_7181])).

tff(c_7327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6968,c_7320])).

tff(c_7328,plain,(
    k4_tmap_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1509])).

tff(c_7330,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7328,c_123])).

tff(c_7333,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_7330])).

tff(c_7334,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_7341,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7334,c_56])).

tff(c_7340,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7334,c_54])).

tff(c_7353,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),k1_xboole_0)
    | u1_struct_0('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7340,c_18])).

tff(c_7369,plain,
    ( k1_xboole_0 = '#skF_4'
    | u1_struct_0('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7341,c_7353])).

tff(c_7381,plain,(
    u1_struct_0('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7369])).

tff(c_7335,plain,(
    u1_struct_0('#skF_3') != k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_7385,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7381,c_7335])).

tff(c_7384,plain,(
    v1_funct_2('#skF_4',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7381,c_7341])).

tff(c_7382,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7381,c_7340])).

tff(c_7404,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_4',k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_7382,c_24])).

tff(c_7428,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7384,c_7404])).

tff(c_7433,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_7382,c_14])).

tff(c_7441,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7428,c_7433])).

tff(c_7442,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7385,c_7441])).

tff(c_7443,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_7369])).

tff(c_7336,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),k1_xboole_0,'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7334,c_111])).

tff(c_7451,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),'#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7443,c_7336])).

tff(c_7444,plain,(
    u1_struct_0('#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7369])).

tff(c_7463,plain,(
    u1_struct_0('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7443,c_7444])).

tff(c_7453,plain,(
    u1_struct_0('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7443,c_7334])).

tff(c_7494,plain,(
    ! [A_510,B_511] :
      ( v1_funct_2(k4_tmap_1(A_510,B_511),u1_struct_0(B_511),u1_struct_0(A_510))
      | ~ m1_pre_topc(B_511,A_510)
      | ~ l1_pre_topc(A_510)
      | ~ v2_pre_topc(A_510)
      | v2_struct_0(A_510) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_7500,plain,(
    ! [B_511] :
      ( v1_funct_2(k4_tmap_1('#skF_2',B_511),u1_struct_0(B_511),'#skF_4')
      | ~ m1_pre_topc(B_511,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7453,c_7494])).

tff(c_7502,plain,(
    ! [B_511] :
      ( v1_funct_2(k4_tmap_1('#skF_2',B_511),u1_struct_0(B_511),'#skF_4')
      | ~ m1_pre_topc(B_511,'#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_7500])).

tff(c_7503,plain,(
    ! [B_511] :
      ( v1_funct_2(k4_tmap_1('#skF_2',B_511),u1_struct_0(B_511),'#skF_4')
      | ~ m1_pre_topc(B_511,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_7502])).

tff(c_7539,plain,(
    ! [A_521,B_522] :
      ( m1_subset_1(k4_tmap_1(A_521,B_522),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_522),u1_struct_0(A_521))))
      | ~ m1_pre_topc(B_522,A_521)
      | ~ l1_pre_topc(A_521)
      | ~ v2_pre_topc(A_521)
      | v2_struct_0(A_521) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_7553,plain,(
    ! [B_522] :
      ( m1_subset_1(k4_tmap_1('#skF_2',B_522),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_522),'#skF_4')))
      | ~ m1_pre_topc(B_522,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7453,c_7539])).

tff(c_7560,plain,(
    ! [B_522] :
      ( m1_subset_1(k4_tmap_1('#skF_2',B_522),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_522),'#skF_4')))
      | ~ m1_pre_topc(B_522,'#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_7553])).

tff(c_7562,plain,(
    ! [B_523] :
      ( m1_subset_1(k4_tmap_1('#skF_2',B_523),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_523),'#skF_4')))
      | ~ m1_pre_topc(B_523,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_7560])).

tff(c_7457,plain,(
    ! [C_15,A_13] :
      ( C_15 = '#skF_4'
      | ~ v1_funct_2(C_15,A_13,'#skF_4')
      | A_13 = '#skF_4'
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,'#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7443,c_7443,c_7443,c_7443,c_18])).

tff(c_7637,plain,(
    ! [B_537] :
      ( k4_tmap_1('#skF_2',B_537) = '#skF_4'
      | ~ v1_funct_2(k4_tmap_1('#skF_2',B_537),u1_struct_0(B_537),'#skF_4')
      | u1_struct_0(B_537) = '#skF_4'
      | ~ m1_pre_topc(B_537,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_7562,c_7457])).

tff(c_7647,plain,(
    ! [B_541] :
      ( k4_tmap_1('#skF_2',B_541) = '#skF_4'
      | u1_struct_0(B_541) = '#skF_4'
      | ~ m1_pre_topc(B_541,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_7503,c_7637])).

tff(c_7650,plain,
    ( k4_tmap_1('#skF_2','#skF_3') = '#skF_4'
    | u1_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_60,c_7647])).

tff(c_7653,plain,(
    k4_tmap_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_7463,c_7650])).

tff(c_7339,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),k1_xboole_0,k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7334,c_50])).

tff(c_7471,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7443,c_7339])).

tff(c_7654,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),'#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7653,c_7471])).

tff(c_7657,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7451,c_7654])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:54:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.55/3.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.67/3.70  
% 10.67/3.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.67/3.71  %$ r2_funct_2 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k1_relset_1 > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 10.67/3.71  
% 10.67/3.71  %Foreground sorts:
% 10.67/3.71  
% 10.67/3.71  
% 10.67/3.71  %Background operators:
% 10.67/3.71  
% 10.67/3.71  
% 10.67/3.71  %Foreground operators:
% 10.67/3.71  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.67/3.71  tff(k4_tmap_1, type, k4_tmap_1: ($i * $i) > $i).
% 10.67/3.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.67/3.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.67/3.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.67/3.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.67/3.71  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.67/3.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.67/3.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.67/3.71  tff('#skF_2', type, '#skF_2': $i).
% 10.67/3.71  tff('#skF_3', type, '#skF_3': $i).
% 10.67/3.71  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.67/3.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.67/3.71  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.67/3.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.67/3.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.67/3.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.67/3.71  tff('#skF_4', type, '#skF_4': $i).
% 10.67/3.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.67/3.71  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 10.67/3.71  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.67/3.71  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.67/3.71  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.67/3.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.67/3.71  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 10.67/3.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.67/3.71  
% 10.92/3.75  tff(f_181, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, u1_struct_0(B)) => (D = k1_funct_1(C, D))))) => r2_funct_2(u1_struct_0(B), u1_struct_0(A), k4_tmap_1(A, B), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_tmap_1)).
% 10.92/3.75  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.92/3.75  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 10.92/3.75  tff(f_82, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 10.92/3.75  tff(f_131, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_funct_1(k4_tmap_1(A, B)) & v1_funct_2(k4_tmap_1(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(k4_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_tmap_1)).
% 10.92/3.75  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 10.92/3.75  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 10.92/3.75  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.92/3.75  tff(f_100, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, B) <=> (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_grfunc_1)).
% 10.92/3.75  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 10.92/3.75  tff(f_116, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 10.92/3.75  tff(f_151, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, u1_struct_0(B)) => (k1_funct_1(k4_tmap_1(A, B), C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_tmap_1)).
% 10.92/3.75  tff(c_56, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 10.92/3.75  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_181])).
% 10.92/3.75  tff(c_88, plain, (![A_68, B_69, C_70]: (k1_relset_1(A_68, B_69, C_70)=k1_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.92/3.75  tff(c_92, plain, (k1_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_88])).
% 10.92/3.75  tff(c_112, plain, (![B_85, A_86, C_87]: (k1_xboole_0=B_85 | k1_relset_1(A_86, B_85, C_87)=A_86 | ~v1_funct_2(C_87, A_86, B_85) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_86, B_85))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.92/3.75  tff(c_115, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | k1_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4')=u1_struct_0('#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_112])).
% 10.92/3.75  tff(c_118, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | u1_struct_0('#skF_3')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_92, c_115])).
% 10.92/3.75  tff(c_119, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_118])).
% 10.92/3.75  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_181])).
% 10.92/3.75  tff(c_106, plain, (![A_82, B_83, D_84]: (r2_funct_2(A_82, B_83, D_84, D_84) | ~m1_subset_1(D_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))) | ~v1_funct_2(D_84, A_82, B_83) | ~v1_funct_1(D_84))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.92/3.75  tff(c_108, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_106])).
% 10.92/3.75  tff(c_111, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_108])).
% 10.92/3.75  tff(c_120, plain, (r2_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_111])).
% 10.92/3.75  tff(c_68, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_181])).
% 10.92/3.75  tff(c_66, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_181])).
% 10.92/3.75  tff(c_64, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_181])).
% 10.92/3.75  tff(c_60, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_181])).
% 10.92/3.75  tff(c_46, plain, (![A_37, B_38]: (v1_funct_1(k4_tmap_1(A_37, B_38)) | ~m1_pre_topc(B_38, A_37) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_131])).
% 10.92/3.75  tff(c_12, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.92/3.75  tff(c_191, plain, (![A_100, B_101]: (m1_subset_1(k4_tmap_1(A_100, B_101), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_101), u1_struct_0(A_100)))) | ~m1_pre_topc(B_101, A_100) | ~l1_pre_topc(A_100) | ~v2_pre_topc(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_131])).
% 10.92/3.75  tff(c_10, plain, (![B_7, A_5]: (v1_relat_1(B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_5)) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.92/3.75  tff(c_205, plain, (![A_100, B_101]: (v1_relat_1(k4_tmap_1(A_100, B_101)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(B_101), u1_struct_0(A_100))) | ~m1_pre_topc(B_101, A_100) | ~l1_pre_topc(A_100) | ~v2_pre_topc(A_100) | v2_struct_0(A_100))), inference(resolution, [status(thm)], [c_191, c_10])).
% 10.92/3.75  tff(c_218, plain, (![A_100, B_101]: (v1_relat_1(k4_tmap_1(A_100, B_101)) | ~m1_pre_topc(B_101, A_100) | ~l1_pre_topc(A_100) | ~v2_pre_topc(A_100) | v2_struct_0(A_100))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_205])).
% 10.92/3.75  tff(c_83, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_54, c_10])).
% 10.92/3.75  tff(c_86, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_83])).
% 10.92/3.75  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.92/3.75  tff(c_44, plain, (![A_37, B_38]: (v1_funct_2(k4_tmap_1(A_37, B_38), u1_struct_0(B_38), u1_struct_0(A_37)) | ~m1_pre_topc(B_38, A_37) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_131])).
% 10.92/3.75  tff(c_26, plain, (![B_14, A_13, C_15]: (k1_xboole_0=B_14 | k1_relset_1(A_13, B_14, C_15)=A_13 | ~v1_funct_2(C_15, A_13, B_14) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.92/3.75  tff(c_364, plain, (![A_130, B_131]: (u1_struct_0(A_130)=k1_xboole_0 | k1_relset_1(u1_struct_0(B_131), u1_struct_0(A_130), k4_tmap_1(A_130, B_131))=u1_struct_0(B_131) | ~v1_funct_2(k4_tmap_1(A_130, B_131), u1_struct_0(B_131), u1_struct_0(A_130)) | ~m1_pre_topc(B_131, A_130) | ~l1_pre_topc(A_130) | ~v2_pre_topc(A_130) | v2_struct_0(A_130))), inference(resolution, [status(thm)], [c_191, c_26])).
% 10.92/3.75  tff(c_379, plain, (![A_132, B_133]: (u1_struct_0(A_132)=k1_xboole_0 | k1_relset_1(u1_struct_0(B_133), u1_struct_0(A_132), k4_tmap_1(A_132, B_133))=u1_struct_0(B_133) | ~m1_pre_topc(B_133, A_132) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | v2_struct_0(A_132))), inference(resolution, [status(thm)], [c_44, c_364])).
% 10.92/3.75  tff(c_14, plain, (![A_10, B_11, C_12]: (k1_relset_1(A_10, B_11, C_12)=k1_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.92/3.75  tff(c_215, plain, (![B_101, A_100]: (k1_relset_1(u1_struct_0(B_101), u1_struct_0(A_100), k4_tmap_1(A_100, B_101))=k1_relat_1(k4_tmap_1(A_100, B_101)) | ~m1_pre_topc(B_101, A_100) | ~l1_pre_topc(A_100) | ~v2_pre_topc(A_100) | v2_struct_0(A_100))), inference(resolution, [status(thm)], [c_191, c_14])).
% 10.92/3.75  tff(c_431, plain, (![A_139, B_140]: (k1_relat_1(k4_tmap_1(A_139, B_140))=u1_struct_0(B_140) | ~m1_pre_topc(B_140, A_139) | ~l1_pre_topc(A_139) | ~v2_pre_topc(A_139) | v2_struct_0(A_139) | u1_struct_0(A_139)=k1_xboole_0 | ~m1_pre_topc(B_140, A_139) | ~l1_pre_topc(A_139) | ~v2_pre_topc(A_139) | v2_struct_0(A_139))), inference(superposition, [status(thm), theory('equality')], [c_379, c_215])).
% 10.92/3.75  tff(c_38, plain, (![A_20, B_26]: (r1_tarski(k1_relat_1(A_20), k1_relat_1(B_26)) | ~r1_tarski(A_20, B_26) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.92/3.75  tff(c_683, plain, (![B_165, B_166, A_167]: (r1_tarski(u1_struct_0(B_165), k1_relat_1(B_166)) | ~r1_tarski(k4_tmap_1(A_167, B_165), B_166) | ~v1_funct_1(B_166) | ~v1_relat_1(B_166) | ~v1_funct_1(k4_tmap_1(A_167, B_165)) | ~v1_relat_1(k4_tmap_1(A_167, B_165)) | ~m1_pre_topc(B_165, A_167) | ~l1_pre_topc(A_167) | ~v2_pre_topc(A_167) | v2_struct_0(A_167) | u1_struct_0(A_167)=k1_xboole_0 | ~m1_pre_topc(B_165, A_167) | ~l1_pre_topc(A_167) | ~v2_pre_topc(A_167) | v2_struct_0(A_167))), inference(superposition, [status(thm), theory('equality')], [c_431, c_38])).
% 10.92/3.75  tff(c_699, plain, (![B_171, A_172]: (r1_tarski(u1_struct_0(B_171), k1_relat_1(k4_tmap_1(A_172, B_171))) | ~v1_funct_1(k4_tmap_1(A_172, B_171)) | ~v1_relat_1(k4_tmap_1(A_172, B_171)) | u1_struct_0(A_172)=k1_xboole_0 | ~m1_pre_topc(B_171, A_172) | ~l1_pre_topc(A_172) | ~v2_pre_topc(A_172) | v2_struct_0(A_172))), inference(resolution, [status(thm)], [c_6, c_683])).
% 10.92/3.75  tff(c_718, plain, (![A_176]: (r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(k4_tmap_1(A_176, '#skF_3'))) | ~v1_funct_1(k4_tmap_1(A_176, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_176, '#skF_3')) | u1_struct_0(A_176)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_176) | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176) | v2_struct_0(A_176))), inference(superposition, [status(thm), theory('equality')], [c_119, c_699])).
% 10.92/3.75  tff(c_308, plain, (![A_118, B_119]: (r2_hidden('#skF_1'(A_118, B_119), k1_relat_1(A_118)) | r1_tarski(A_118, B_119) | ~r1_tarski(k1_relat_1(A_118), k1_relat_1(B_119)) | ~v1_funct_1(B_119) | ~v1_relat_1(B_119) | ~v1_funct_1(A_118) | ~v1_relat_1(A_118))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.92/3.75  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(A_3, B_4) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.92/3.75  tff(c_322, plain, (![A_118, B_119]: (m1_subset_1('#skF_1'(A_118, B_119), k1_relat_1(A_118)) | r1_tarski(A_118, B_119) | ~r1_tarski(k1_relat_1(A_118), k1_relat_1(B_119)) | ~v1_funct_1(B_119) | ~v1_relat_1(B_119) | ~v1_funct_1(A_118) | ~v1_relat_1(A_118))), inference(resolution, [status(thm)], [c_308, c_8])).
% 10.92/3.75  tff(c_730, plain, (![A_176]: (m1_subset_1('#skF_1'('#skF_4', k4_tmap_1(A_176, '#skF_3')), k1_relat_1('#skF_4')) | r1_tarski('#skF_4', k4_tmap_1(A_176, '#skF_3')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1(k4_tmap_1(A_176, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_176, '#skF_3')) | u1_struct_0(A_176)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_176) | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176) | v2_struct_0(A_176))), inference(resolution, [status(thm)], [c_718, c_322])).
% 10.92/3.75  tff(c_755, plain, (![A_176]: (m1_subset_1('#skF_1'('#skF_4', k4_tmap_1(A_176, '#skF_3')), k1_relat_1('#skF_4')) | r1_tarski('#skF_4', k4_tmap_1(A_176, '#skF_3')) | ~v1_funct_1(k4_tmap_1(A_176, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_176, '#skF_3')) | u1_struct_0(A_176)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_176) | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176) | v2_struct_0(A_176))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_58, c_730])).
% 10.92/3.75  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_181])).
% 10.92/3.75  tff(c_167, plain, (![C_91, A_92, B_93]: (m1_subset_1(C_91, u1_struct_0(A_92)) | ~m1_subset_1(C_91, u1_struct_0(B_93)) | ~m1_pre_topc(B_93, A_92) | v2_struct_0(B_93) | ~l1_pre_topc(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_116])).
% 10.92/3.75  tff(c_169, plain, (![C_91, A_92]: (m1_subset_1(C_91, u1_struct_0(A_92)) | ~m1_subset_1(C_91, k1_relat_1('#skF_4')) | ~m1_pre_topc('#skF_3', A_92) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_92) | v2_struct_0(A_92))), inference(superposition, [status(thm), theory('equality')], [c_119, c_167])).
% 10.92/3.75  tff(c_170, plain, (![C_91, A_92]: (m1_subset_1(C_91, u1_struct_0(A_92)) | ~m1_subset_1(C_91, k1_relat_1('#skF_4')) | ~m1_pre_topc('#skF_3', A_92) | ~l1_pre_topc(A_92) | v2_struct_0(A_92))), inference(negUnitSimplification, [status(thm)], [c_62, c_169])).
% 10.92/3.75  tff(c_394, plain, (![A_132]: (u1_struct_0(A_132)=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_4'), u1_struct_0(A_132), k4_tmap_1(A_132, '#skF_3'))=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', A_132) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | v2_struct_0(A_132))), inference(superposition, [status(thm), theory('equality')], [c_119, c_379])).
% 10.92/3.75  tff(c_403, plain, (![A_134]: (u1_struct_0(A_134)=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_4'), u1_struct_0(A_134), k4_tmap_1(A_134, '#skF_3'))=k1_relat_1('#skF_4') | ~m1_pre_topc('#skF_3', A_134) | ~l1_pre_topc(A_134) | ~v2_pre_topc(A_134) | v2_struct_0(A_134))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_394])).
% 10.92/3.75  tff(c_279, plain, (![B_115, A_116]: (k1_relset_1(u1_struct_0(B_115), u1_struct_0(A_116), k4_tmap_1(A_116, B_115))=k1_relat_1(k4_tmap_1(A_116, B_115)) | ~m1_pre_topc(B_115, A_116) | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116) | v2_struct_0(A_116))), inference(resolution, [status(thm)], [c_191, c_14])).
% 10.92/3.75  tff(c_288, plain, (![A_116]: (k1_relset_1(k1_relat_1('#skF_4'), u1_struct_0(A_116), k4_tmap_1(A_116, '#skF_3'))=k1_relat_1(k4_tmap_1(A_116, '#skF_3')) | ~m1_pre_topc('#skF_3', A_116) | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116) | v2_struct_0(A_116))), inference(superposition, [status(thm), theory('equality')], [c_119, c_279])).
% 10.92/3.75  tff(c_464, plain, (![A_141]: (k1_relat_1(k4_tmap_1(A_141, '#skF_3'))=k1_relat_1('#skF_4') | ~m1_pre_topc('#skF_3', A_141) | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141) | v2_struct_0(A_141) | u1_struct_0(A_141)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_141) | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141) | v2_struct_0(A_141))), inference(superposition, [status(thm), theory('equality')], [c_403, c_288])).
% 10.92/3.75  tff(c_52, plain, (![D_57]: (k1_funct_1('#skF_4', D_57)=D_57 | ~r2_hidden(D_57, u1_struct_0('#skF_3')) | ~m1_subset_1(D_57, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_181])).
% 10.92/3.75  tff(c_122, plain, (![D_57]: (k1_funct_1('#skF_4', D_57)=D_57 | ~r2_hidden(D_57, k1_relat_1('#skF_4')) | ~m1_subset_1(D_57, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_52])).
% 10.92/3.75  tff(c_314, plain, (![B_119]: (k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_119))='#skF_1'('#skF_4', B_119) | ~m1_subset_1('#skF_1'('#skF_4', B_119), u1_struct_0('#skF_2')) | r1_tarski('#skF_4', B_119) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_119)) | ~v1_funct_1(B_119) | ~v1_relat_1(B_119) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_308, c_122])).
% 10.92/3.75  tff(c_321, plain, (![B_119]: (k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_119))='#skF_1'('#skF_4', B_119) | ~m1_subset_1('#skF_1'('#skF_4', B_119), u1_struct_0('#skF_2')) | r1_tarski('#skF_4', B_119) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_119)) | ~v1_funct_1(B_119) | ~v1_relat_1(B_119))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_58, c_314])).
% 10.92/3.75  tff(c_473, plain, (![A_141]: (k1_funct_1('#skF_4', '#skF_1'('#skF_4', k4_tmap_1(A_141, '#skF_3')))='#skF_1'('#skF_4', k4_tmap_1(A_141, '#skF_3')) | ~m1_subset_1('#skF_1'('#skF_4', k4_tmap_1(A_141, '#skF_3')), u1_struct_0('#skF_2')) | r1_tarski('#skF_4', k4_tmap_1(A_141, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_funct_1(k4_tmap_1(A_141, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_141, '#skF_3')) | ~m1_pre_topc('#skF_3', A_141) | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141) | v2_struct_0(A_141) | u1_struct_0(A_141)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_141) | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141) | v2_struct_0(A_141))), inference(superposition, [status(thm), theory('equality')], [c_464, c_321])).
% 10.92/3.75  tff(c_798, plain, (![A_186]: (k1_funct_1('#skF_4', '#skF_1'('#skF_4', k4_tmap_1(A_186, '#skF_3')))='#skF_1'('#skF_4', k4_tmap_1(A_186, '#skF_3')) | ~m1_subset_1('#skF_1'('#skF_4', k4_tmap_1(A_186, '#skF_3')), u1_struct_0('#skF_2')) | r1_tarski('#skF_4', k4_tmap_1(A_186, '#skF_3')) | ~v1_funct_1(k4_tmap_1(A_186, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_186, '#skF_3')) | u1_struct_0(A_186)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_186) | ~l1_pre_topc(A_186) | ~v2_pre_topc(A_186) | v2_struct_0(A_186))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_473])).
% 10.92/3.75  tff(c_801, plain, (![A_186]: (k1_funct_1('#skF_4', '#skF_1'('#skF_4', k4_tmap_1(A_186, '#skF_3')))='#skF_1'('#skF_4', k4_tmap_1(A_186, '#skF_3')) | r1_tarski('#skF_4', k4_tmap_1(A_186, '#skF_3')) | ~v1_funct_1(k4_tmap_1(A_186, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_186, '#skF_3')) | u1_struct_0(A_186)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_186) | ~l1_pre_topc(A_186) | ~v2_pre_topc(A_186) | v2_struct_0(A_186) | ~m1_subset_1('#skF_1'('#skF_4', k4_tmap_1(A_186, '#skF_3')), k1_relat_1('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_170, c_798])).
% 10.92/3.75  tff(c_804, plain, (![A_186]: (k1_funct_1('#skF_4', '#skF_1'('#skF_4', k4_tmap_1(A_186, '#skF_3')))='#skF_1'('#skF_4', k4_tmap_1(A_186, '#skF_3')) | r1_tarski('#skF_4', k4_tmap_1(A_186, '#skF_3')) | ~v1_funct_1(k4_tmap_1(A_186, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_186, '#skF_3')) | u1_struct_0(A_186)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_186) | ~l1_pre_topc(A_186) | ~v2_pre_topc(A_186) | v2_struct_0(A_186) | ~m1_subset_1('#skF_1'('#skF_4', k4_tmap_1(A_186, '#skF_3')), k1_relat_1('#skF_4')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_801])).
% 10.92/3.75  tff(c_806, plain, (![A_187]: (k1_funct_1('#skF_4', '#skF_1'('#skF_4', k4_tmap_1(A_187, '#skF_3')))='#skF_1'('#skF_4', k4_tmap_1(A_187, '#skF_3')) | r1_tarski('#skF_4', k4_tmap_1(A_187, '#skF_3')) | ~v1_funct_1(k4_tmap_1(A_187, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_187, '#skF_3')) | u1_struct_0(A_187)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_187) | ~l1_pre_topc(A_187) | ~v2_pre_topc(A_187) | v2_struct_0(A_187) | ~m1_subset_1('#skF_1'('#skF_4', k4_tmap_1(A_187, '#skF_3')), k1_relat_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_68, c_804])).
% 10.92/3.75  tff(c_810, plain, (![A_176]: (k1_funct_1('#skF_4', '#skF_1'('#skF_4', k4_tmap_1(A_176, '#skF_3')))='#skF_1'('#skF_4', k4_tmap_1(A_176, '#skF_3')) | r1_tarski('#skF_4', k4_tmap_1(A_176, '#skF_3')) | ~v1_funct_1(k4_tmap_1(A_176, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_176, '#skF_3')) | u1_struct_0(A_176)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_176) | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176) | v2_struct_0(A_176))), inference(resolution, [status(thm)], [c_755, c_806])).
% 10.92/3.75  tff(c_712, plain, (![A_172]: (r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(k4_tmap_1(A_172, '#skF_3'))) | ~v1_funct_1(k4_tmap_1(A_172, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_172, '#skF_3')) | u1_struct_0(A_172)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_172) | ~l1_pre_topc(A_172) | ~v2_pre_topc(A_172) | v2_struct_0(A_172))), inference(superposition, [status(thm), theory('equality')], [c_119, c_699])).
% 10.92/3.75  tff(c_763, plain, (![A_177]: (m1_subset_1('#skF_1'('#skF_4', k4_tmap_1(A_177, '#skF_3')), k1_relat_1('#skF_4')) | r1_tarski('#skF_4', k4_tmap_1(A_177, '#skF_3')) | ~v1_funct_1(k4_tmap_1(A_177, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_177, '#skF_3')) | u1_struct_0(A_177)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_177) | ~l1_pre_topc(A_177) | ~v2_pre_topc(A_177) | v2_struct_0(A_177))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_58, c_730])).
% 10.92/3.75  tff(c_385, plain, (![A_132, B_133]: (k1_relat_1(k4_tmap_1(A_132, B_133))=u1_struct_0(B_133) | ~m1_pre_topc(B_133, A_132) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | v2_struct_0(A_132) | u1_struct_0(A_132)=k1_xboole_0 | ~m1_pre_topc(B_133, A_132) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | v2_struct_0(A_132))), inference(superposition, [status(thm), theory('equality')], [c_379, c_215])).
% 10.92/3.75  tff(c_34, plain, (![A_20, B_26]: (r2_hidden('#skF_1'(A_20, B_26), k1_relat_1(A_20)) | r1_tarski(A_20, B_26) | ~r1_tarski(k1_relat_1(A_20), k1_relat_1(B_26)) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.92/3.75  tff(c_332, plain, (![A_122, B_123, C_124]: (k1_funct_1(k4_tmap_1(A_122, B_123), C_124)=C_124 | ~r2_hidden(C_124, u1_struct_0(B_123)) | ~m1_subset_1(C_124, u1_struct_0(A_122)) | ~m1_pre_topc(B_123, A_122) | v2_struct_0(B_123) | ~l1_pre_topc(A_122) | ~v2_pre_topc(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_151])).
% 10.92/3.75  tff(c_334, plain, (![A_122, C_124]: (k1_funct_1(k4_tmap_1(A_122, '#skF_3'), C_124)=C_124 | ~r2_hidden(C_124, k1_relat_1('#skF_4')) | ~m1_subset_1(C_124, u1_struct_0(A_122)) | ~m1_pre_topc('#skF_3', A_122) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_122) | ~v2_pre_topc(A_122) | v2_struct_0(A_122))), inference(superposition, [status(thm), theory('equality')], [c_119, c_332])).
% 10.92/3.75  tff(c_336, plain, (![A_125, C_126]: (k1_funct_1(k4_tmap_1(A_125, '#skF_3'), C_126)=C_126 | ~r2_hidden(C_126, k1_relat_1('#skF_4')) | ~m1_subset_1(C_126, u1_struct_0(A_125)) | ~m1_pre_topc('#skF_3', A_125) | ~l1_pre_topc(A_125) | ~v2_pre_topc(A_125) | v2_struct_0(A_125))), inference(negUnitSimplification, [status(thm)], [c_62, c_334])).
% 10.92/3.75  tff(c_339, plain, (![A_125, B_26]: (k1_funct_1(k4_tmap_1(A_125, '#skF_3'), '#skF_1'('#skF_4', B_26))='#skF_1'('#skF_4', B_26) | ~m1_subset_1('#skF_1'('#skF_4', B_26), u1_struct_0(A_125)) | ~m1_pre_topc('#skF_3', A_125) | ~l1_pre_topc(A_125) | ~v2_pre_topc(A_125) | v2_struct_0(A_125) | r1_tarski('#skF_4', B_26) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_26)) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_336])).
% 10.92/3.75  tff(c_508, plain, (![A_142, B_143]: (k1_funct_1(k4_tmap_1(A_142, '#skF_3'), '#skF_1'('#skF_4', B_143))='#skF_1'('#skF_4', B_143) | ~m1_subset_1('#skF_1'('#skF_4', B_143), u1_struct_0(A_142)) | ~m1_pre_topc('#skF_3', A_142) | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142) | v2_struct_0(A_142) | r1_tarski('#skF_4', B_143) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_143)) | ~v1_funct_1(B_143) | ~v1_relat_1(B_143))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_58, c_339])).
% 10.92/3.75  tff(c_587, plain, (![A_154, B_155]: (k1_funct_1(k4_tmap_1(A_154, '#skF_3'), '#skF_1'('#skF_4', B_155))='#skF_1'('#skF_4', B_155) | ~v2_pre_topc(A_154) | r1_tarski('#skF_4', B_155) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_155)) | ~v1_funct_1(B_155) | ~v1_relat_1(B_155) | ~m1_subset_1('#skF_1'('#skF_4', B_155), k1_relat_1('#skF_4')) | ~m1_pre_topc('#skF_3', A_154) | ~l1_pre_topc(A_154) | v2_struct_0(A_154))), inference(resolution, [status(thm)], [c_170, c_508])).
% 10.92/3.75  tff(c_591, plain, (![A_154, A_132, B_133]: (k1_funct_1(k4_tmap_1(A_154, '#skF_3'), '#skF_1'('#skF_4', k4_tmap_1(A_132, B_133)))='#skF_1'('#skF_4', k4_tmap_1(A_132, B_133)) | ~v2_pre_topc(A_154) | r1_tarski('#skF_4', k4_tmap_1(A_132, B_133)) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(B_133)) | ~v1_funct_1(k4_tmap_1(A_132, B_133)) | ~v1_relat_1(k4_tmap_1(A_132, B_133)) | ~m1_subset_1('#skF_1'('#skF_4', k4_tmap_1(A_132, B_133)), k1_relat_1('#skF_4')) | ~m1_pre_topc('#skF_3', A_154) | ~l1_pre_topc(A_154) | v2_struct_0(A_154) | ~m1_pre_topc(B_133, A_132) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | v2_struct_0(A_132) | u1_struct_0(A_132)=k1_xboole_0 | ~m1_pre_topc(B_133, A_132) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | v2_struct_0(A_132))), inference(superposition, [status(thm), theory('equality')], [c_385, c_587])).
% 10.92/3.75  tff(c_765, plain, (![A_154, A_177]: (k1_funct_1(k4_tmap_1(A_154, '#skF_3'), '#skF_1'('#skF_4', k4_tmap_1(A_177, '#skF_3')))='#skF_1'('#skF_4', k4_tmap_1(A_177, '#skF_3')) | ~v2_pre_topc(A_154) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', A_154) | ~l1_pre_topc(A_154) | v2_struct_0(A_154) | r1_tarski('#skF_4', k4_tmap_1(A_177, '#skF_3')) | ~v1_funct_1(k4_tmap_1(A_177, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_177, '#skF_3')) | u1_struct_0(A_177)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_177) | ~l1_pre_topc(A_177) | ~v2_pre_topc(A_177) | v2_struct_0(A_177))), inference(resolution, [status(thm)], [c_763, c_591])).
% 10.92/3.75  tff(c_847, plain, (![A_191, A_192]: (k1_funct_1(k4_tmap_1(A_191, '#skF_3'), '#skF_1'('#skF_4', k4_tmap_1(A_192, '#skF_3')))='#skF_1'('#skF_4', k4_tmap_1(A_192, '#skF_3')) | ~v2_pre_topc(A_191) | ~m1_pre_topc('#skF_3', A_191) | ~l1_pre_topc(A_191) | v2_struct_0(A_191) | r1_tarski('#skF_4', k4_tmap_1(A_192, '#skF_3')) | ~v1_funct_1(k4_tmap_1(A_192, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_192, '#skF_3')) | u1_struct_0(A_192)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_192) | ~l1_pre_topc(A_192) | ~v2_pre_topc(A_192) | v2_struct_0(A_192))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_119, c_765])).
% 10.92/3.75  tff(c_32, plain, (![B_26, A_20]: (k1_funct_1(B_26, '#skF_1'(A_20, B_26))!=k1_funct_1(A_20, '#skF_1'(A_20, B_26)) | r1_tarski(A_20, B_26) | ~r1_tarski(k1_relat_1(A_20), k1_relat_1(B_26)) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.92/3.75  tff(c_856, plain, (![A_192]: (k1_funct_1('#skF_4', '#skF_1'('#skF_4', k4_tmap_1(A_192, '#skF_3')))!='#skF_1'('#skF_4', k4_tmap_1(A_192, '#skF_3')) | r1_tarski('#skF_4', k4_tmap_1(A_192, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(k4_tmap_1(A_192, '#skF_3'))) | ~v1_funct_1(k4_tmap_1(A_192, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_192, '#skF_3')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v2_pre_topc(A_192) | ~m1_pre_topc('#skF_3', A_192) | ~l1_pre_topc(A_192) | v2_struct_0(A_192) | r1_tarski('#skF_4', k4_tmap_1(A_192, '#skF_3')) | ~v1_funct_1(k4_tmap_1(A_192, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_192, '#skF_3')) | u1_struct_0(A_192)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_192) | ~l1_pre_topc(A_192) | ~v2_pre_topc(A_192) | v2_struct_0(A_192))), inference(superposition, [status(thm), theory('equality')], [c_847, c_32])).
% 10.92/3.75  tff(c_868, plain, (![A_193]: (k1_funct_1('#skF_4', '#skF_1'('#skF_4', k4_tmap_1(A_193, '#skF_3')))!='#skF_1'('#skF_4', k4_tmap_1(A_193, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(k4_tmap_1(A_193, '#skF_3'))) | r1_tarski('#skF_4', k4_tmap_1(A_193, '#skF_3')) | ~v1_funct_1(k4_tmap_1(A_193, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_193, '#skF_3')) | u1_struct_0(A_193)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_193) | ~l1_pre_topc(A_193) | ~v2_pre_topc(A_193) | v2_struct_0(A_193))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_58, c_856])).
% 10.92/3.75  tff(c_900, plain, (![A_197]: (k1_funct_1('#skF_4', '#skF_1'('#skF_4', k4_tmap_1(A_197, '#skF_3')))!='#skF_1'('#skF_4', k4_tmap_1(A_197, '#skF_3')) | r1_tarski('#skF_4', k4_tmap_1(A_197, '#skF_3')) | ~v1_funct_1(k4_tmap_1(A_197, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_197, '#skF_3')) | u1_struct_0(A_197)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_197) | ~l1_pre_topc(A_197) | ~v2_pre_topc(A_197) | v2_struct_0(A_197))), inference(resolution, [status(thm)], [c_712, c_868])).
% 10.92/3.75  tff(c_907, plain, (![A_176]: (r1_tarski('#skF_4', k4_tmap_1(A_176, '#skF_3')) | ~v1_funct_1(k4_tmap_1(A_176, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_176, '#skF_3')) | u1_struct_0(A_176)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_176) | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176) | v2_struct_0(A_176))), inference(superposition, [status(thm), theory('equality')], [c_810, c_900])).
% 10.92/3.75  tff(c_606, plain, (![A_156, B_157, A_158]: (r1_tarski(k1_relat_1(A_156), u1_struct_0(B_157)) | ~r1_tarski(A_156, k4_tmap_1(A_158, B_157)) | ~v1_funct_1(k4_tmap_1(A_158, B_157)) | ~v1_relat_1(k4_tmap_1(A_158, B_157)) | ~v1_funct_1(A_156) | ~v1_relat_1(A_156) | ~m1_pre_topc(B_157, A_158) | ~l1_pre_topc(A_158) | ~v2_pre_topc(A_158) | v2_struct_0(A_158) | u1_struct_0(A_158)=k1_xboole_0 | ~m1_pre_topc(B_157, A_158) | ~l1_pre_topc(A_158) | ~v2_pre_topc(A_158) | v2_struct_0(A_158))), inference(superposition, [status(thm), theory('equality')], [c_431, c_38])).
% 10.92/3.75  tff(c_611, plain, (![A_159, B_160]: (r1_tarski(k1_relat_1(k4_tmap_1(A_159, B_160)), u1_struct_0(B_160)) | ~v1_funct_1(k4_tmap_1(A_159, B_160)) | ~v1_relat_1(k4_tmap_1(A_159, B_160)) | u1_struct_0(A_159)=k1_xboole_0 | ~m1_pre_topc(B_160, A_159) | ~l1_pre_topc(A_159) | ~v2_pre_topc(A_159) | v2_struct_0(A_159))), inference(resolution, [status(thm)], [c_6, c_606])).
% 10.92/3.75  tff(c_624, plain, (![A_159]: (r1_tarski(k1_relat_1(k4_tmap_1(A_159, '#skF_3')), k1_relat_1('#skF_4')) | ~v1_funct_1(k4_tmap_1(A_159, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_159, '#skF_3')) | u1_struct_0(A_159)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_159) | ~l1_pre_topc(A_159) | ~v2_pre_topc(A_159) | v2_struct_0(A_159))), inference(superposition, [status(thm), theory('equality')], [c_119, c_611])).
% 10.92/3.75  tff(c_1075, plain, (![A_226, B_227, B_228]: (r2_hidden('#skF_1'(k4_tmap_1(A_226, B_227), B_228), u1_struct_0(B_227)) | r1_tarski(k4_tmap_1(A_226, B_227), B_228) | ~r1_tarski(k1_relat_1(k4_tmap_1(A_226, B_227)), k1_relat_1(B_228)) | ~v1_funct_1(B_228) | ~v1_relat_1(B_228) | ~v1_funct_1(k4_tmap_1(A_226, B_227)) | ~v1_relat_1(k4_tmap_1(A_226, B_227)) | ~m1_pre_topc(B_227, A_226) | ~l1_pre_topc(A_226) | ~v2_pre_topc(A_226) | v2_struct_0(A_226) | u1_struct_0(A_226)=k1_xboole_0 | ~m1_pre_topc(B_227, A_226) | ~l1_pre_topc(A_226) | ~v2_pre_topc(A_226) | v2_struct_0(A_226))), inference(superposition, [status(thm), theory('equality')], [c_431, c_34])).
% 10.92/3.75  tff(c_1122, plain, (![A_236, B_237]: (r2_hidden('#skF_1'(k4_tmap_1(A_236, '#skF_3'), B_237), k1_relat_1('#skF_4')) | r1_tarski(k4_tmap_1(A_236, '#skF_3'), B_237) | ~r1_tarski(k1_relat_1(k4_tmap_1(A_236, '#skF_3')), k1_relat_1(B_237)) | ~v1_funct_1(B_237) | ~v1_relat_1(B_237) | ~v1_funct_1(k4_tmap_1(A_236, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_236, '#skF_3')) | ~m1_pre_topc('#skF_3', A_236) | ~l1_pre_topc(A_236) | ~v2_pre_topc(A_236) | v2_struct_0(A_236) | u1_struct_0(A_236)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_236) | ~l1_pre_topc(A_236) | ~v2_pre_topc(A_236) | v2_struct_0(A_236))), inference(superposition, [status(thm), theory('equality')], [c_119, c_1075])).
% 10.92/3.75  tff(c_36, plain, (![B_26, C_29, A_20]: (k1_funct_1(B_26, C_29)=k1_funct_1(A_20, C_29) | ~r2_hidden(C_29, k1_relat_1(A_20)) | ~r1_tarski(A_20, B_26) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.92/3.75  tff(c_1128, plain, (![B_26, A_236, B_237]: (k1_funct_1(B_26, '#skF_1'(k4_tmap_1(A_236, '#skF_3'), B_237))=k1_funct_1('#skF_4', '#skF_1'(k4_tmap_1(A_236, '#skF_3'), B_237)) | ~r1_tarski('#skF_4', B_26) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | r1_tarski(k4_tmap_1(A_236, '#skF_3'), B_237) | ~r1_tarski(k1_relat_1(k4_tmap_1(A_236, '#skF_3')), k1_relat_1(B_237)) | ~v1_funct_1(B_237) | ~v1_relat_1(B_237) | ~v1_funct_1(k4_tmap_1(A_236, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_236, '#skF_3')) | u1_struct_0(A_236)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_236) | ~l1_pre_topc(A_236) | ~v2_pre_topc(A_236) | v2_struct_0(A_236))), inference(resolution, [status(thm)], [c_1122, c_36])).
% 10.92/3.75  tff(c_1324, plain, (![B_271, A_272, B_273]: (k1_funct_1(B_271, '#skF_1'(k4_tmap_1(A_272, '#skF_3'), B_273))=k1_funct_1('#skF_4', '#skF_1'(k4_tmap_1(A_272, '#skF_3'), B_273)) | ~r1_tarski('#skF_4', B_271) | ~v1_funct_1(B_271) | ~v1_relat_1(B_271) | r1_tarski(k4_tmap_1(A_272, '#skF_3'), B_273) | ~r1_tarski(k1_relat_1(k4_tmap_1(A_272, '#skF_3')), k1_relat_1(B_273)) | ~v1_funct_1(B_273) | ~v1_relat_1(B_273) | ~v1_funct_1(k4_tmap_1(A_272, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_272, '#skF_3')) | u1_struct_0(A_272)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_272) | ~l1_pre_topc(A_272) | ~v2_pre_topc(A_272) | v2_struct_0(A_272))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_58, c_1128])).
% 10.92/3.75  tff(c_1326, plain, (![B_271, A_159]: (k1_funct_1(B_271, '#skF_1'(k4_tmap_1(A_159, '#skF_3'), '#skF_4'))=k1_funct_1('#skF_4', '#skF_1'(k4_tmap_1(A_159, '#skF_3'), '#skF_4')) | ~r1_tarski('#skF_4', B_271) | ~v1_funct_1(B_271) | ~v1_relat_1(B_271) | r1_tarski(k4_tmap_1(A_159, '#skF_3'), '#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1(k4_tmap_1(A_159, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_159, '#skF_3')) | u1_struct_0(A_159)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_159) | ~l1_pre_topc(A_159) | ~v2_pre_topc(A_159) | v2_struct_0(A_159))), inference(resolution, [status(thm)], [c_624, c_1324])).
% 10.92/3.75  tff(c_1359, plain, (![B_277, A_278]: (k1_funct_1(B_277, '#skF_1'(k4_tmap_1(A_278, '#skF_3'), '#skF_4'))=k1_funct_1('#skF_4', '#skF_1'(k4_tmap_1(A_278, '#skF_3'), '#skF_4')) | ~r1_tarski('#skF_4', B_277) | ~v1_funct_1(B_277) | ~v1_relat_1(B_277) | r1_tarski(k4_tmap_1(A_278, '#skF_3'), '#skF_4') | ~v1_funct_1(k4_tmap_1(A_278, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_278, '#skF_3')) | u1_struct_0(A_278)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_278) | ~l1_pre_topc(A_278) | ~v2_pre_topc(A_278) | v2_struct_0(A_278))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_58, c_1326])).
% 10.92/3.75  tff(c_1382, plain, (![A_278]: (~r1_tarski(k1_relat_1(k4_tmap_1(A_278, '#skF_3')), k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_4', k4_tmap_1(A_278, '#skF_3')) | r1_tarski(k4_tmap_1(A_278, '#skF_3'), '#skF_4') | ~v1_funct_1(k4_tmap_1(A_278, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_278, '#skF_3')) | u1_struct_0(A_278)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_278) | ~l1_pre_topc(A_278) | ~v2_pre_topc(A_278) | v2_struct_0(A_278))), inference(superposition, [status(thm), theory('equality')], [c_1359, c_32])).
% 10.92/3.75  tff(c_1404, plain, (![A_279]: (~r1_tarski(k1_relat_1(k4_tmap_1(A_279, '#skF_3')), k1_relat_1('#skF_4')) | ~r1_tarski('#skF_4', k4_tmap_1(A_279, '#skF_3')) | r1_tarski(k4_tmap_1(A_279, '#skF_3'), '#skF_4') | ~v1_funct_1(k4_tmap_1(A_279, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_279, '#skF_3')) | u1_struct_0(A_279)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_279) | ~l1_pre_topc(A_279) | ~v2_pre_topc(A_279) | v2_struct_0(A_279))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_58, c_1382])).
% 10.92/3.75  tff(c_1426, plain, (![A_280]: (~r1_tarski('#skF_4', k4_tmap_1(A_280, '#skF_3')) | r1_tarski(k4_tmap_1(A_280, '#skF_3'), '#skF_4') | ~v1_funct_1(k4_tmap_1(A_280, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_280, '#skF_3')) | u1_struct_0(A_280)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_280) | ~l1_pre_topc(A_280) | ~v2_pre_topc(A_280) | v2_struct_0(A_280))), inference(resolution, [status(thm)], [c_624, c_1404])).
% 10.92/3.75  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.92/3.75  tff(c_1485, plain, (![A_284]: (k4_tmap_1(A_284, '#skF_3')='#skF_4' | ~r1_tarski('#skF_4', k4_tmap_1(A_284, '#skF_3')) | ~v1_funct_1(k4_tmap_1(A_284, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_284, '#skF_3')) | u1_struct_0(A_284)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_284) | ~l1_pre_topc(A_284) | ~v2_pre_topc(A_284) | v2_struct_0(A_284))), inference(resolution, [status(thm)], [c_1426, c_2])).
% 10.92/3.75  tff(c_1490, plain, (![A_285]: (k4_tmap_1(A_285, '#skF_3')='#skF_4' | ~v1_funct_1(k4_tmap_1(A_285, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_285, '#skF_3')) | u1_struct_0(A_285)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_285) | ~l1_pre_topc(A_285) | ~v2_pre_topc(A_285) | v2_struct_0(A_285))), inference(resolution, [status(thm)], [c_907, c_1485])).
% 10.92/3.75  tff(c_1496, plain, (![A_286]: (k4_tmap_1(A_286, '#skF_3')='#skF_4' | ~v1_funct_1(k4_tmap_1(A_286, '#skF_3')) | u1_struct_0(A_286)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_286) | ~l1_pre_topc(A_286) | ~v2_pre_topc(A_286) | v2_struct_0(A_286))), inference(resolution, [status(thm)], [c_218, c_1490])).
% 10.92/3.75  tff(c_1502, plain, (![A_287]: (k4_tmap_1(A_287, '#skF_3')='#skF_4' | u1_struct_0(A_287)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_287) | ~l1_pre_topc(A_287) | ~v2_pre_topc(A_287) | v2_struct_0(A_287))), inference(resolution, [status(thm)], [c_46, c_1496])).
% 10.92/3.75  tff(c_1505, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4' | u1_struct_0('#skF_2')=k1_xboole_0 | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_1502])).
% 10.92/3.75  tff(c_1508, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4' | u1_struct_0('#skF_2')=k1_xboole_0 | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1505])).
% 10.92/3.75  tff(c_1509, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4' | u1_struct_0('#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_1508])).
% 10.92/3.75  tff(c_1510, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1509])).
% 10.92/3.75  tff(c_125, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_56])).
% 10.92/3.75  tff(c_1528, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1510, c_125])).
% 10.92/3.75  tff(c_124, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_54])).
% 10.92/3.75  tff(c_1526, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1510, c_124])).
% 10.92/3.75  tff(c_18, plain, (![C_15, A_13]: (k1_xboole_0=C_15 | ~v1_funct_2(C_15, A_13, k1_xboole_0) | k1_xboole_0=A_13 | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.92/3.75  tff(c_1671, plain, (k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k1_xboole_0) | k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1526, c_18])).
% 10.92/3.75  tff(c_1690, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1528, c_1671])).
% 10.92/3.75  tff(c_1695, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1690])).
% 10.92/3.75  tff(c_1527, plain, (r2_funct_2(k1_relat_1('#skF_4'), k1_xboole_0, '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1510, c_120])).
% 10.92/3.75  tff(c_1698, plain, (r2_funct_2(k1_xboole_0, k1_xboole_0, '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1695, c_1527])).
% 10.92/3.75  tff(c_208, plain, (![A_100]: (m1_subset_1(k4_tmap_1(A_100, '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(A_100)))) | ~m1_pre_topc('#skF_3', A_100) | ~l1_pre_topc(A_100) | ~v2_pre_topc(A_100) | v2_struct_0(A_100))), inference(superposition, [status(thm), theory('equality')], [c_119, c_191])).
% 10.92/3.75  tff(c_1588, plain, (m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k1_xboole_0))) | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1510, c_208])).
% 10.92/3.75  tff(c_1639, plain, (m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k1_xboole_0))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_1588])).
% 10.92/3.75  tff(c_1640, plain, (m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_68, c_1639])).
% 10.92/3.75  tff(c_2070, plain, (m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1695, c_1640])).
% 10.92/3.75  tff(c_2093, plain, (v1_relat_1(k4_tmap_1('#skF_2', '#skF_3')) | ~v1_relat_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_2070, c_10])).
% 10.92/3.75  tff(c_2116, plain, (v1_relat_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2093])).
% 10.92/3.75  tff(c_156, plain, (![A_88, B_89]: (v1_funct_2(k4_tmap_1(A_88, B_89), u1_struct_0(B_89), u1_struct_0(A_88)) | ~m1_pre_topc(B_89, A_88) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_131])).
% 10.92/3.75  tff(c_159, plain, (![A_88]: (v1_funct_2(k4_tmap_1(A_88, '#skF_3'), k1_relat_1('#skF_4'), u1_struct_0(A_88)) | ~m1_pre_topc('#skF_3', A_88) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88) | v2_struct_0(A_88))), inference(superposition, [status(thm), theory('equality')], [c_119, c_156])).
% 10.92/3.75  tff(c_1597, plain, (v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), k1_relat_1('#skF_4'), k1_xboole_0) | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1510, c_159])).
% 10.92/3.75  tff(c_1645, plain, (v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), k1_relat_1('#skF_4'), k1_xboole_0) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_1597])).
% 10.92/3.75  tff(c_1646, plain, (v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), k1_relat_1('#skF_4'), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_68, c_1645])).
% 10.92/3.75  tff(c_1697, plain, (v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1695, c_1646])).
% 10.92/3.75  tff(c_28, plain, (![A_16, B_17, D_19]: (r2_funct_2(A_16, B_17, D_19, D_19) | ~m1_subset_1(D_19, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))) | ~v1_funct_2(D_19, A_16, B_17) | ~v1_funct_1(D_19))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.92/3.75  tff(c_2078, plain, (r2_funct_2(k1_xboole_0, k1_xboole_0, k4_tmap_1('#skF_2', '#skF_3'), k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_2070, c_28])).
% 10.92/3.75  tff(c_2103, plain, (r2_funct_2(k1_xboole_0, k1_xboole_0, k4_tmap_1('#skF_2', '#skF_3'), k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1697, c_2078])).
% 10.92/3.75  tff(c_2374, plain, (~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_2103])).
% 10.92/3.75  tff(c_2377, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_2374])).
% 10.92/3.75  tff(c_2380, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_2377])).
% 10.92/3.75  tff(c_2382, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_2380])).
% 10.92/3.75  tff(c_2384, plain, (v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_2103])).
% 10.92/3.75  tff(c_24, plain, (![B_14, C_15]: (k1_relset_1(k1_xboole_0, B_14, C_15)=k1_xboole_0 | ~v1_funct_2(C_15, k1_xboole_0, B_14) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_14))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.92/3.75  tff(c_2084, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, k4_tmap_1('#skF_2', '#skF_3'))=k1_xboole_0 | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_2070, c_24])).
% 10.92/3.75  tff(c_2108, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, k4_tmap_1('#skF_2', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1697, c_2084])).
% 10.92/3.75  tff(c_2113, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, k4_tmap_1('#skF_2', '#skF_3'))=k1_relat_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_2070, c_14])).
% 10.92/3.75  tff(c_2138, plain, (k1_relat_1(k4_tmap_1('#skF_2', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2108, c_2113])).
% 10.92/3.75  tff(c_1762, plain, (![B_119]: (m1_subset_1('#skF_1'('#skF_4', B_119), k1_relat_1('#skF_4')) | r1_tarski('#skF_4', B_119) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_119)) | ~v1_funct_1(B_119) | ~v1_relat_1(B_119) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1695, c_322])).
% 10.92/3.75  tff(c_2523, plain, (![B_317]: (m1_subset_1('#skF_1'('#skF_4', B_317), k1_xboole_0) | r1_tarski('#skF_4', B_317) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_317)) | ~v1_funct_1(B_317) | ~v1_relat_1(B_317))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_58, c_1695, c_1762])).
% 10.92/3.75  tff(c_2529, plain, (m1_subset_1('#skF_1'('#skF_4', k4_tmap_1('#skF_2', '#skF_3')), k1_xboole_0) | r1_tarski('#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~v1_relat_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2138, c_2523])).
% 10.92/3.75  tff(c_2538, plain, (m1_subset_1('#skF_1'('#skF_4', k4_tmap_1('#skF_2', '#skF_3')), k1_xboole_0) | r1_tarski('#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2116, c_2384, c_6, c_2529])).
% 10.92/3.75  tff(c_2541, plain, (r1_tarski('#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_2538])).
% 10.92/3.75  tff(c_2567, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4' | ~r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_2541, c_2])).
% 10.92/3.75  tff(c_2568, plain, (~r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_2567])).
% 10.92/3.75  tff(c_2197, plain, (![B_26]: (r2_hidden('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), B_26), k1_xboole_0) | r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), B_26) | ~r1_tarski(k1_relat_1(k4_tmap_1('#skF_2', '#skF_3')), k1_relat_1(B_26)) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~v1_relat_1(k4_tmap_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2138, c_34])).
% 10.92/3.75  tff(c_2272, plain, (![B_26]: (r2_hidden('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), B_26), k1_xboole_0) | r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), B_26) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_26)) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2116, c_2138, c_2197])).
% 10.92/3.75  tff(c_3968, plain, (![B_26]: (r2_hidden('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), B_26), k1_xboole_0) | r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), B_26) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_26)) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26))), inference(demodulation, [status(thm), theory('equality')], [c_2384, c_2272])).
% 10.92/3.75  tff(c_1764, plain, (![A_118]: (m1_subset_1('#skF_1'(A_118, '#skF_4'), k1_relat_1(A_118)) | r1_tarski(A_118, '#skF_4') | ~r1_tarski(k1_relat_1(A_118), k1_xboole_0) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1(A_118) | ~v1_relat_1(A_118))), inference(superposition, [status(thm), theory('equality')], [c_1695, c_322])).
% 10.92/3.75  tff(c_2643, plain, (![A_327]: (m1_subset_1('#skF_1'(A_327, '#skF_4'), k1_relat_1(A_327)) | r1_tarski(A_327, '#skF_4') | ~r1_tarski(k1_relat_1(A_327), k1_xboole_0) | ~v1_funct_1(A_327) | ~v1_relat_1(A_327))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_58, c_1764])).
% 10.92/3.75  tff(c_2646, plain, (m1_subset_1('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), k1_xboole_0) | r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~r1_tarski(k1_relat_1(k4_tmap_1('#skF_2', '#skF_3')), k1_xboole_0) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~v1_relat_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2138, c_2643])).
% 10.92/3.75  tff(c_2654, plain, (m1_subset_1('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), k1_xboole_0) | r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2116, c_2384, c_6, c_2138, c_2646])).
% 10.92/3.75  tff(c_2655, plain, (m1_subset_1('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_2568, c_2654])).
% 10.92/3.75  tff(c_318, plain, (![B_26, A_118, B_119]: (k1_funct_1(B_26, '#skF_1'(A_118, B_119))=k1_funct_1(A_118, '#skF_1'(A_118, B_119)) | ~r1_tarski(A_118, B_26) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26) | r1_tarski(A_118, B_119) | ~r1_tarski(k1_relat_1(A_118), k1_relat_1(B_119)) | ~v1_funct_1(B_119) | ~v1_relat_1(B_119) | ~v1_funct_1(A_118) | ~v1_relat_1(A_118))), inference(resolution, [status(thm)], [c_308, c_36])).
% 10.92/3.75  tff(c_1760, plain, (![B_26, A_118]: (k1_funct_1(B_26, '#skF_1'(A_118, '#skF_4'))=k1_funct_1(A_118, '#skF_1'(A_118, '#skF_4')) | ~r1_tarski(A_118, B_26) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26) | r1_tarski(A_118, '#skF_4') | ~r1_tarski(k1_relat_1(A_118), k1_xboole_0) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1(A_118) | ~v1_relat_1(A_118))), inference(superposition, [status(thm), theory('equality')], [c_1695, c_318])).
% 10.92/3.75  tff(c_4706, plain, (![B_410, A_411]: (k1_funct_1(B_410, '#skF_1'(A_411, '#skF_4'))=k1_funct_1(A_411, '#skF_1'(A_411, '#skF_4')) | ~r1_tarski(A_411, B_410) | ~v1_funct_1(B_410) | ~v1_relat_1(B_410) | r1_tarski(A_411, '#skF_4') | ~r1_tarski(k1_relat_1(A_411), k1_xboole_0) | ~v1_funct_1(A_411) | ~v1_relat_1(A_411))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_58, c_1760])).
% 10.92/3.75  tff(c_4720, plain, (![B_410]: (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))=k1_funct_1(B_410, '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')) | ~r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), B_410) | ~v1_funct_1(B_410) | ~v1_relat_1(B_410) | r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~v1_relat_1(k4_tmap_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2138, c_4706])).
% 10.92/3.75  tff(c_4734, plain, (![B_410]: (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))=k1_funct_1(B_410, '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')) | ~r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), B_410) | ~v1_funct_1(B_410) | ~v1_relat_1(B_410) | r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2116, c_2384, c_6, c_4720])).
% 10.92/3.75  tff(c_4738, plain, (![B_412]: (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))=k1_funct_1(B_412, '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')) | ~r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), B_412) | ~v1_funct_1(B_412) | ~v1_relat_1(B_412))), inference(negUnitSimplification, [status(thm)], [c_2568, c_4734])).
% 10.92/3.75  tff(c_1729, plain, (![C_91, A_92]: (m1_subset_1(C_91, u1_struct_0(A_92)) | ~m1_subset_1(C_91, k1_xboole_0) | ~m1_pre_topc('#skF_3', A_92) | ~l1_pre_topc(A_92) | v2_struct_0(A_92))), inference(demodulation, [status(thm), theory('equality')], [c_1695, c_170])).
% 10.92/3.75  tff(c_1730, plain, (u1_struct_0('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1695, c_119])).
% 10.92/3.75  tff(c_48, plain, (![A_39, B_43, C_45]: (k1_funct_1(k4_tmap_1(A_39, B_43), C_45)=C_45 | ~r2_hidden(C_45, u1_struct_0(B_43)) | ~m1_subset_1(C_45, u1_struct_0(A_39)) | ~m1_pre_topc(B_43, A_39) | v2_struct_0(B_43) | ~l1_pre_topc(A_39) | ~v2_pre_topc(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_151])).
% 10.92/3.75  tff(c_1864, plain, (![A_39, C_45]: (k1_funct_1(k4_tmap_1(A_39, '#skF_3'), C_45)=C_45 | ~r2_hidden(C_45, k1_xboole_0) | ~m1_subset_1(C_45, u1_struct_0(A_39)) | ~m1_pre_topc('#skF_3', A_39) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_39) | ~v2_pre_topc(A_39) | v2_struct_0(A_39))), inference(superposition, [status(thm), theory('equality')], [c_1730, c_48])).
% 10.92/3.75  tff(c_2739, plain, (![A_332, C_333]: (k1_funct_1(k4_tmap_1(A_332, '#skF_3'), C_333)=C_333 | ~r2_hidden(C_333, k1_xboole_0) | ~m1_subset_1(C_333, u1_struct_0(A_332)) | ~m1_pre_topc('#skF_3', A_332) | ~l1_pre_topc(A_332) | ~v2_pre_topc(A_332) | v2_struct_0(A_332))), inference(negUnitSimplification, [status(thm)], [c_62, c_1864])).
% 10.92/3.75  tff(c_2752, plain, (![A_92, C_91]: (k1_funct_1(k4_tmap_1(A_92, '#skF_3'), C_91)=C_91 | ~r2_hidden(C_91, k1_xboole_0) | ~v2_pre_topc(A_92) | ~m1_subset_1(C_91, k1_xboole_0) | ~m1_pre_topc('#skF_3', A_92) | ~l1_pre_topc(A_92) | v2_struct_0(A_92))), inference(resolution, [status(thm)], [c_1729, c_2739])).
% 10.92/3.75  tff(c_4758, plain, (![B_412]: (k1_funct_1(B_412, '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~r2_hidden('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), k1_xboole_0) | ~v2_pre_topc('#skF_2') | ~m1_subset_1('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), k1_xboole_0) | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), B_412) | ~v1_funct_1(B_412) | ~v1_relat_1(B_412))), inference(superposition, [status(thm), theory('equality')], [c_4738, c_2752])).
% 10.92/3.75  tff(c_4849, plain, (![B_412]: (k1_funct_1(B_412, '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~r2_hidden('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), k1_xboole_0) | v2_struct_0('#skF_2') | ~r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), B_412) | ~v1_funct_1(B_412) | ~v1_relat_1(B_412))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_2655, c_66, c_4758])).
% 10.92/3.75  tff(c_4850, plain, (![B_412]: (k1_funct_1(B_412, '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~r2_hidden('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), k1_xboole_0) | ~r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), B_412) | ~v1_funct_1(B_412) | ~v1_relat_1(B_412))), inference(negUnitSimplification, [status(thm)], [c_68, c_4849])).
% 10.92/3.75  tff(c_5033, plain, (~r2_hidden('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_4850])).
% 10.92/3.75  tff(c_5036, plain, (r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~r1_tarski(k1_xboole_0, k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_3968, c_5033])).
% 10.92/3.75  tff(c_5039, plain, (r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_58, c_6, c_1695, c_5036])).
% 10.92/3.75  tff(c_5041, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2568, c_5039])).
% 10.92/3.75  tff(c_5043, plain, (r2_hidden('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_4850])).
% 10.92/3.75  tff(c_1523, plain, (![D_57]: (k1_funct_1('#skF_4', D_57)=D_57 | ~r2_hidden(D_57, k1_relat_1('#skF_4')) | ~m1_subset_1(D_57, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1510, c_122])).
% 10.92/3.75  tff(c_2287, plain, (![D_57]: (k1_funct_1('#skF_4', D_57)=D_57 | ~r2_hidden(D_57, k1_xboole_0) | ~m1_subset_1(D_57, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1695, c_1523])).
% 10.92/3.75  tff(c_5048, plain, (k1_funct_1('#skF_4', '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~m1_subset_1('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), k1_xboole_0)), inference(resolution, [status(thm)], [c_5043, c_2287])).
% 10.92/3.75  tff(c_5055, plain, (k1_funct_1('#skF_4', '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2655, c_5048])).
% 10.92/3.75  tff(c_2751, plain, (![C_333]: (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), C_333)=C_333 | ~r2_hidden(C_333, k1_xboole_0) | ~m1_subset_1(C_333, k1_xboole_0) | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1510, c_2739])).
% 10.92/3.75  tff(c_2756, plain, (![C_333]: (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), C_333)=C_333 | ~r2_hidden(C_333, k1_xboole_0) | ~m1_subset_1(C_333, k1_xboole_0) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_2751])).
% 10.92/3.75  tff(c_2757, plain, (![C_333]: (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), C_333)=C_333 | ~r2_hidden(C_333, k1_xboole_0) | ~m1_subset_1(C_333, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_68, c_2756])).
% 10.92/3.75  tff(c_4785, plain, (![B_412]: (k1_funct_1(B_412, '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))!=k1_funct_1('#skF_4', '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')) | r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~r1_tarski(k1_relat_1(k4_tmap_1('#skF_2', '#skF_3')), k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~v1_relat_1(k4_tmap_1('#skF_2', '#skF_3')) | ~r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), B_412) | ~v1_funct_1(B_412) | ~v1_relat_1(B_412))), inference(superposition, [status(thm), theory('equality')], [c_4738, c_32])).
% 10.92/3.75  tff(c_4876, plain, (![B_412]: (k1_funct_1(B_412, '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))!=k1_funct_1('#skF_4', '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')) | r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), B_412) | ~v1_funct_1(B_412) | ~v1_relat_1(B_412))), inference(demodulation, [status(thm), theory('equality')], [c_2116, c_2384, c_86, c_58, c_6, c_1695, c_2138, c_4785])).
% 10.92/3.75  tff(c_4923, plain, (![B_413]: (k1_funct_1(B_413, '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))!=k1_funct_1('#skF_4', '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')) | ~r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), B_413) | ~v1_funct_1(B_413) | ~v1_relat_1(B_413))), inference(negUnitSimplification, [status(thm)], [c_2568, c_4876])).
% 10.92/3.75  tff(c_4961, plain, (k1_funct_1('#skF_4', '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))!='#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~v1_relat_1(k4_tmap_1('#skF_2', '#skF_3')) | ~r2_hidden('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), k1_xboole_0) | ~m1_subset_1('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2757, c_4923])).
% 10.92/3.75  tff(c_5010, plain, (k1_funct_1('#skF_4', '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))!='#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~r2_hidden('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2655, c_2116, c_2384, c_6, c_4961])).
% 10.92/3.75  tff(c_5090, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5043, c_5055, c_5010])).
% 10.92/3.75  tff(c_5091, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_2567])).
% 10.92/3.75  tff(c_50, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_181])).
% 10.92/3.75  tff(c_123, plain, (~r2_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_50])).
% 10.92/3.75  tff(c_1524, plain, (~r2_funct_2(k1_relat_1('#skF_4'), k1_xboole_0, k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1510, c_123])).
% 10.92/3.75  tff(c_2069, plain, (~r2_funct_2(k1_xboole_0, k1_xboole_0, k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1695, c_1524])).
% 10.92/3.75  tff(c_5100, plain, (~r2_funct_2(k1_xboole_0, k1_xboole_0, '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5091, c_2069])).
% 10.92/3.75  tff(c_5111, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1698, c_5100])).
% 10.92/3.75  tff(c_5113, plain, (~r1_tarski('#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_2538])).
% 10.92/3.75  tff(c_5112, plain, (m1_subset_1('#skF_1'('#skF_4', k4_tmap_1('#skF_2', '#skF_3')), k1_xboole_0)), inference(splitRight, [status(thm)], [c_2538])).
% 10.92/3.75  tff(c_342, plain, (![A_125, B_26]: (k1_funct_1(k4_tmap_1(A_125, '#skF_3'), '#skF_1'('#skF_4', B_26))='#skF_1'('#skF_4', B_26) | ~m1_subset_1('#skF_1'('#skF_4', B_26), u1_struct_0(A_125)) | ~m1_pre_topc('#skF_3', A_125) | ~l1_pre_topc(A_125) | ~v2_pre_topc(A_125) | v2_struct_0(A_125) | r1_tarski('#skF_4', B_26) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_26)) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_58, c_339])).
% 10.92/3.75  tff(c_1565, plain, (![B_26]: (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_4', B_26))='#skF_1'('#skF_4', B_26) | ~m1_subset_1('#skF_1'('#skF_4', B_26), k1_xboole_0) | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | r1_tarski('#skF_4', B_26) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_26)) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26))), inference(superposition, [status(thm), theory('equality')], [c_1510, c_342])).
% 10.92/3.75  tff(c_1622, plain, (![B_26]: (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_4', B_26))='#skF_1'('#skF_4', B_26) | ~m1_subset_1('#skF_1'('#skF_4', B_26), k1_xboole_0) | v2_struct_0('#skF_2') | r1_tarski('#skF_4', B_26) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_26)) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_1565])).
% 10.92/3.75  tff(c_1623, plain, (![B_26]: (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_4', B_26))='#skF_1'('#skF_4', B_26) | ~m1_subset_1('#skF_1'('#skF_4', B_26), k1_xboole_0) | r1_tarski('#skF_4', B_26) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_26)) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26))), inference(negUnitSimplification, [status(thm)], [c_68, c_1622])).
% 10.92/3.75  tff(c_5654, plain, (![B_441]: (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_4', B_441))='#skF_1'('#skF_4', B_441) | ~m1_subset_1('#skF_1'('#skF_4', B_441), k1_xboole_0) | r1_tarski('#skF_4', B_441) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_441)) | ~v1_funct_1(B_441) | ~v1_relat_1(B_441))), inference(demodulation, [status(thm), theory('equality')], [c_1695, c_1623])).
% 10.92/3.75  tff(c_5667, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_4', k4_tmap_1('#skF_2', '#skF_3')))!='#skF_1'('#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | r1_tarski('#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(k4_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~v1_relat_1(k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~m1_subset_1('#skF_1'('#skF_4', k4_tmap_1('#skF_2', '#skF_3')), k1_xboole_0) | r1_tarski('#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~r1_tarski(k1_xboole_0, k1_relat_1(k4_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~v1_relat_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5654, c_32])).
% 10.92/3.75  tff(c_5683, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_4', k4_tmap_1('#skF_2', '#skF_3')))!='#skF_1'('#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | r1_tarski('#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2116, c_2384, c_6, c_2138, c_5112, c_86, c_58, c_2116, c_2384, c_6, c_1695, c_2138, c_5667])).
% 10.92/3.75  tff(c_5684, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_4', k4_tmap_1('#skF_2', '#skF_3')))!='#skF_1'('#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_5113, c_5683])).
% 10.92/3.75  tff(c_1767, plain, (![B_26]: (r2_hidden('#skF_1'('#skF_4', B_26), k1_xboole_0) | r1_tarski('#skF_4', B_26) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_26)) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1695, c_34])).
% 10.92/3.75  tff(c_5136, plain, (![B_416]: (r2_hidden('#skF_1'('#skF_4', B_416), k1_xboole_0) | r1_tarski('#skF_4', B_416) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_416)) | ~v1_funct_1(B_416) | ~v1_relat_1(B_416))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_58, c_1695, c_1767])).
% 10.92/3.75  tff(c_6936, plain, (![B_482]: (k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_482))='#skF_1'('#skF_4', B_482) | ~m1_subset_1('#skF_1'('#skF_4', B_482), k1_xboole_0) | r1_tarski('#skF_4', B_482) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_482)) | ~v1_funct_1(B_482) | ~v1_relat_1(B_482))), inference(resolution, [status(thm)], [c_5136, c_2287])).
% 10.92/3.75  tff(c_6948, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_4', k4_tmap_1('#skF_2', '#skF_3')))='#skF_1'('#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_1'('#skF_4', k4_tmap_1('#skF_2', '#skF_3')), k1_xboole_0) | r1_tarski('#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~v1_relat_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2138, c_6936])).
% 10.92/3.75  tff(c_6961, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_4', k4_tmap_1('#skF_2', '#skF_3')))='#skF_1'('#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | r1_tarski('#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2116, c_2384, c_6, c_5112, c_6948])).
% 10.92/3.75  tff(c_6963, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5113, c_5684, c_6961])).
% 10.92/3.75  tff(c_6964, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1690])).
% 10.92/3.75  tff(c_6968, plain, (r2_funct_2(k1_relat_1('#skF_4'), '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6964, c_1527])).
% 10.92/3.75  tff(c_6965, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1690])).
% 10.92/3.75  tff(c_7031, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6964, c_6965])).
% 10.92/3.75  tff(c_6967, plain, (v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), k1_relat_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6964, c_1646])).
% 10.92/3.75  tff(c_7182, plain, (m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_6964, c_1640])).
% 10.92/3.75  tff(c_7297, plain, (![C_502, A_503]: (C_502='#skF_4' | ~v1_funct_2(C_502, A_503, '#skF_4') | A_503='#skF_4' | ~m1_subset_1(C_502, k1_zfmisc_1(k2_zfmisc_1(A_503, '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_6964, c_6964, c_6964, c_6964, c_18])).
% 10.92/3.75  tff(c_7303, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4' | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), k1_relat_1('#skF_4'), '#skF_4') | k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_7182, c_7297])).
% 10.92/3.75  tff(c_7310, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4' | k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6967, c_7303])).
% 10.92/3.75  tff(c_7311, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_7031, c_7310])).
% 10.92/3.75  tff(c_7181, plain, (~r2_funct_2(k1_relat_1('#skF_4'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6964, c_1524])).
% 10.92/3.75  tff(c_7320, plain, (~r2_funct_2(k1_relat_1('#skF_4'), '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7311, c_7181])).
% 10.92/3.75  tff(c_7327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6968, c_7320])).
% 10.92/3.75  tff(c_7328, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_1509])).
% 10.92/3.75  tff(c_7330, plain, (~r2_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7328, c_123])).
% 10.92/3.75  tff(c_7333, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_120, c_7330])).
% 10.92/3.75  tff(c_7334, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_118])).
% 10.92/3.75  tff(c_7341, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7334, c_56])).
% 10.92/3.75  tff(c_7340, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_7334, c_54])).
% 10.92/3.75  tff(c_7353, plain, (k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), k1_xboole_0) | u1_struct_0('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_7340, c_18])).
% 10.92/3.75  tff(c_7369, plain, (k1_xboole_0='#skF_4' | u1_struct_0('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7341, c_7353])).
% 10.92/3.75  tff(c_7381, plain, (u1_struct_0('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7369])).
% 10.92/3.75  tff(c_7335, plain, (u1_struct_0('#skF_3')!=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_118])).
% 10.92/3.75  tff(c_7385, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7381, c_7335])).
% 10.92/3.75  tff(c_7384, plain, (v1_funct_2('#skF_4', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7381, c_7341])).
% 10.92/3.75  tff(c_7382, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_7381, c_7340])).
% 10.92/3.75  tff(c_7404, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_4', k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_7382, c_24])).
% 10.92/3.75  tff(c_7428, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7384, c_7404])).
% 10.92/3.75  tff(c_7433, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_7382, c_14])).
% 10.92/3.75  tff(c_7441, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7428, c_7433])).
% 10.92/3.75  tff(c_7442, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7385, c_7441])).
% 10.92/3.75  tff(c_7443, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_7369])).
% 10.92/3.75  tff(c_7336, plain, (r2_funct_2(u1_struct_0('#skF_3'), k1_xboole_0, '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7334, c_111])).
% 10.92/3.75  tff(c_7451, plain, (r2_funct_2(u1_struct_0('#skF_3'), '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7443, c_7336])).
% 10.92/3.75  tff(c_7444, plain, (u1_struct_0('#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_7369])).
% 10.92/3.75  tff(c_7463, plain, (u1_struct_0('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7443, c_7444])).
% 10.92/3.75  tff(c_7453, plain, (u1_struct_0('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7443, c_7334])).
% 10.92/3.75  tff(c_7494, plain, (![A_510, B_511]: (v1_funct_2(k4_tmap_1(A_510, B_511), u1_struct_0(B_511), u1_struct_0(A_510)) | ~m1_pre_topc(B_511, A_510) | ~l1_pre_topc(A_510) | ~v2_pre_topc(A_510) | v2_struct_0(A_510))), inference(cnfTransformation, [status(thm)], [f_131])).
% 10.92/3.75  tff(c_7500, plain, (![B_511]: (v1_funct_2(k4_tmap_1('#skF_2', B_511), u1_struct_0(B_511), '#skF_4') | ~m1_pre_topc(B_511, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_7453, c_7494])).
% 10.92/3.75  tff(c_7502, plain, (![B_511]: (v1_funct_2(k4_tmap_1('#skF_2', B_511), u1_struct_0(B_511), '#skF_4') | ~m1_pre_topc(B_511, '#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_7500])).
% 10.92/3.75  tff(c_7503, plain, (![B_511]: (v1_funct_2(k4_tmap_1('#skF_2', B_511), u1_struct_0(B_511), '#skF_4') | ~m1_pre_topc(B_511, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_68, c_7502])).
% 10.92/3.75  tff(c_7539, plain, (![A_521, B_522]: (m1_subset_1(k4_tmap_1(A_521, B_522), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_522), u1_struct_0(A_521)))) | ~m1_pre_topc(B_522, A_521) | ~l1_pre_topc(A_521) | ~v2_pre_topc(A_521) | v2_struct_0(A_521))), inference(cnfTransformation, [status(thm)], [f_131])).
% 10.92/3.75  tff(c_7553, plain, (![B_522]: (m1_subset_1(k4_tmap_1('#skF_2', B_522), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_522), '#skF_4'))) | ~m1_pre_topc(B_522, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_7453, c_7539])).
% 10.92/3.75  tff(c_7560, plain, (![B_522]: (m1_subset_1(k4_tmap_1('#skF_2', B_522), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_522), '#skF_4'))) | ~m1_pre_topc(B_522, '#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_7553])).
% 10.92/3.75  tff(c_7562, plain, (![B_523]: (m1_subset_1(k4_tmap_1('#skF_2', B_523), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_523), '#skF_4'))) | ~m1_pre_topc(B_523, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_68, c_7560])).
% 10.92/3.75  tff(c_7457, plain, (![C_15, A_13]: (C_15='#skF_4' | ~v1_funct_2(C_15, A_13, '#skF_4') | A_13='#skF_4' | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_7443, c_7443, c_7443, c_7443, c_18])).
% 10.92/3.75  tff(c_7637, plain, (![B_537]: (k4_tmap_1('#skF_2', B_537)='#skF_4' | ~v1_funct_2(k4_tmap_1('#skF_2', B_537), u1_struct_0(B_537), '#skF_4') | u1_struct_0(B_537)='#skF_4' | ~m1_pre_topc(B_537, '#skF_2'))), inference(resolution, [status(thm)], [c_7562, c_7457])).
% 10.92/3.75  tff(c_7647, plain, (![B_541]: (k4_tmap_1('#skF_2', B_541)='#skF_4' | u1_struct_0(B_541)='#skF_4' | ~m1_pre_topc(B_541, '#skF_2'))), inference(resolution, [status(thm)], [c_7503, c_7637])).
% 10.92/3.75  tff(c_7650, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4' | u1_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_60, c_7647])).
% 10.92/3.75  tff(c_7653, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_7463, c_7650])).
% 10.92/3.75  tff(c_7339, plain, (~r2_funct_2(u1_struct_0('#skF_3'), k1_xboole_0, k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7334, c_50])).
% 10.92/3.75  tff(c_7471, plain, (~r2_funct_2(u1_struct_0('#skF_3'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7443, c_7339])).
% 10.92/3.75  tff(c_7654, plain, (~r2_funct_2(u1_struct_0('#skF_3'), '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7653, c_7471])).
% 10.92/3.75  tff(c_7657, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7451, c_7654])).
% 10.92/3.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.92/3.75  
% 10.92/3.75  Inference rules
% 10.92/3.75  ----------------------
% 10.92/3.75  #Ref     : 3
% 10.92/3.75  #Sup     : 1616
% 10.92/3.75  #Fact    : 0
% 10.92/3.75  #Define  : 0
% 10.92/3.75  #Split   : 15
% 10.92/3.75  #Chain   : 0
% 10.92/3.75  #Close   : 0
% 10.92/3.75  
% 10.92/3.75  Ordering : KBO
% 10.92/3.75  
% 10.92/3.75  Simplification rules
% 10.92/3.75  ----------------------
% 10.92/3.75  #Subsume      : 399
% 10.92/3.75  #Demod        : 2974
% 10.92/3.75  #Tautology    : 528
% 10.92/3.75  #SimpNegUnit  : 305
% 10.92/3.75  #BackRed      : 147
% 10.92/3.75  
% 10.92/3.75  #Partial instantiations: 0
% 10.92/3.75  #Strategies tried      : 1
% 10.92/3.75  
% 10.92/3.75  Timing (in seconds)
% 10.92/3.75  ----------------------
% 10.92/3.75  Preprocessing        : 0.38
% 10.92/3.75  Parsing              : 0.20
% 10.92/3.75  CNF conversion       : 0.03
% 10.92/3.75  Main loop            : 2.60
% 10.92/3.75  Inferencing          : 0.70
% 10.92/3.75  Reduction            : 0.75
% 10.92/3.75  Demodulation         : 0.53
% 10.92/3.75  BG Simplification    : 0.08
% 10.92/3.75  Subsumption          : 0.95
% 10.92/3.75  Abstraction          : 0.11
% 10.92/3.75  MUC search           : 0.00
% 10.92/3.75  Cooper               : 0.00
% 10.92/3.75  Total                : 3.07
% 10.92/3.75  Index Insertion      : 0.00
% 10.92/3.75  Index Deletion       : 0.00
% 10.92/3.75  Index Matching       : 0.00
% 10.92/3.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
