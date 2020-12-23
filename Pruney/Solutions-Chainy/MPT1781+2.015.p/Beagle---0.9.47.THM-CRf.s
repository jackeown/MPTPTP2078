%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:47 EST 2020

% Result     : Theorem 5.96s
% Output     : CNFRefutation 5.96s
% Verified   : 
% Statistics : Number of formulae       :  179 (1984 expanded)
%              Number of leaves         :   44 ( 692 expanded)
%              Depth                    :   29
%              Number of atoms          :  963 (10431 expanded)
%              Number of equality atoms :  143 (2068 expanded)
%              Maximal formula depth    :   23 (   8 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k1_relset_1 > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

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

tff(f_198,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tmap_1)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_67,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( r2_funct_2(A,B,C,D)
          <=> ! [E] :
                ( m1_subset_1(E,A)
               => k1_funct_1(C,E) = k1_funct_1(D,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_2)).

tff(f_148,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_funct_1(k4_tmap_1(A,B))
        & v1_funct_2(k4_tmap_1(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(k4_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_tmap_1)).

tff(f_45,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_105,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_grfunc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_133,axiom,(
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

tff(f_168,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tmap_1)).

tff(f_117,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_72,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_44,plain,(
    ! [A_38] :
      ( l1_struct_0(A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_66,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_64,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_99,plain,(
    ! [A_81,B_82,C_83] :
      ( k1_relset_1(A_81,B_82,C_83) = k1_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_103,plain,(
    k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_99])).

tff(c_122,plain,(
    ! [B_97,A_98,C_99] :
      ( k1_xboole_0 = B_97
      | k1_relset_1(A_98,B_97,C_99) = A_98
      | ~ v1_funct_2(C_99,A_98,B_97)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_98,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_125,plain,
    ( u1_struct_0('#skF_3') = k1_xboole_0
    | k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5') = u1_struct_0('#skF_4')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_62,c_122])).

tff(c_128,plain,
    ( u1_struct_0('#skF_3') = k1_xboole_0
    | u1_struct_0('#skF_4') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_103,c_125])).

tff(c_129,plain,(
    u1_struct_0('#skF_4') = k1_relat_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_134,plain,(
    v1_funct_2('#skF_5',k1_relat_1('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_64])).

tff(c_133,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_62])).

tff(c_32,plain,(
    ! [D_24,A_16,B_17,C_18] :
      ( k1_funct_1(D_24,'#skF_1'(A_16,B_17,C_18,D_24)) != k1_funct_1(C_18,'#skF_1'(A_16,B_17,C_18,D_24))
      | r2_funct_2(A_16,B_17,C_18,D_24)
      | ~ m1_subset_1(D_24,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17)))
      | ~ v1_funct_2(D_24,A_16,B_17)
      | ~ v1_funct_1(D_24)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17)))
      | ~ v1_funct_2(C_18,A_16,B_17)
      | ~ v1_funct_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_611,plain,(
    ! [A_172,B_173,C_174] :
      ( r2_funct_2(A_172,B_173,C_174,C_174)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173)))
      | ~ v1_funct_2(C_174,A_172,B_173)
      | ~ v1_funct_1(C_174)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173)))
      | ~ v1_funct_2(C_174,A_172,B_173)
      | ~ v1_funct_1(C_174) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_32])).

tff(c_617,plain,
    ( r2_funct_2(k1_relat_1('#skF_5'),u1_struct_0('#skF_3'),'#skF_5','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_133,c_611])).

tff(c_622,plain,(
    r2_funct_2(k1_relat_1('#skF_5'),u1_struct_0('#skF_3'),'#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_134,c_133,c_617])).

tff(c_74,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_68,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_54,plain,(
    ! [A_47,B_48] :
      ( v1_funct_1(k4_tmap_1(A_47,B_48))
      | ~ m1_pre_topc(B_48,A_47)
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_201,plain,(
    ! [A_109,B_110] :
      ( m1_subset_1(k4_tmap_1(A_109,B_110),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_110),u1_struct_0(A_109))))
      | ~ m1_pre_topc(B_110,A_109)
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_12,plain,(
    ! [B_7,A_5] :
      ( v1_relat_1(B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_5))
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_213,plain,(
    ! [A_109,B_110] :
      ( v1_relat_1(k4_tmap_1(A_109,B_110))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(B_110),u1_struct_0(A_109)))
      | ~ m1_pre_topc(B_110,A_109)
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109)
      | v2_struct_0(A_109) ) ),
    inference(resolution,[status(thm)],[c_201,c_12])).

tff(c_225,plain,(
    ! [A_109,B_110] :
      ( v1_relat_1(k4_tmap_1(A_109,B_110))
      | ~ m1_pre_topc(B_110,A_109)
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109)
      | v2_struct_0(A_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_213])).

tff(c_90,plain,(
    ! [B_77,A_78] :
      ( v1_relat_1(B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_78))
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_93,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_62,c_90])).

tff(c_96,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_93])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ! [A_47,B_48] :
      ( v1_funct_2(k4_tmap_1(A_47,B_48),u1_struct_0(B_48),u1_struct_0(A_47))
      | ~ m1_pre_topc(B_48,A_47)
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_28,plain,(
    ! [B_14,A_13,C_15] :
      ( k1_xboole_0 = B_14
      | k1_relset_1(A_13,B_14,C_15) = A_13
      | ~ v1_funct_2(C_15,A_13,B_14)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_375,plain,(
    ! [A_141,B_142] :
      ( u1_struct_0(A_141) = k1_xboole_0
      | k1_relset_1(u1_struct_0(B_142),u1_struct_0(A_141),k4_tmap_1(A_141,B_142)) = u1_struct_0(B_142)
      | ~ v1_funct_2(k4_tmap_1(A_141,B_142),u1_struct_0(B_142),u1_struct_0(A_141))
      | ~ m1_pre_topc(B_142,A_141)
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141)
      | v2_struct_0(A_141) ) ),
    inference(resolution,[status(thm)],[c_201,c_28])).

tff(c_390,plain,(
    ! [A_143,B_144] :
      ( u1_struct_0(A_143) = k1_xboole_0
      | k1_relset_1(u1_struct_0(B_144),u1_struct_0(A_143),k4_tmap_1(A_143,B_144)) = u1_struct_0(B_144)
      | ~ m1_pre_topc(B_144,A_143)
      | ~ l1_pre_topc(A_143)
      | ~ v2_pre_topc(A_143)
      | v2_struct_0(A_143) ) ),
    inference(resolution,[status(thm)],[c_52,c_375])).

tff(c_16,plain,(
    ! [A_10,B_11,C_12] :
      ( k1_relset_1(A_10,B_11,C_12) = k1_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_222,plain,(
    ! [B_110,A_109] :
      ( k1_relset_1(u1_struct_0(B_110),u1_struct_0(A_109),k4_tmap_1(A_109,B_110)) = k1_relat_1(k4_tmap_1(A_109,B_110))
      | ~ m1_pre_topc(B_110,A_109)
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109)
      | v2_struct_0(A_109) ) ),
    inference(resolution,[status(thm)],[c_201,c_16])).

tff(c_435,plain,(
    ! [A_146,B_147] :
      ( k1_relat_1(k4_tmap_1(A_146,B_147)) = u1_struct_0(B_147)
      | ~ m1_pre_topc(B_147,A_146)
      | ~ l1_pre_topc(A_146)
      | ~ v2_pre_topc(A_146)
      | v2_struct_0(A_146)
      | u1_struct_0(A_146) = k1_xboole_0
      | ~ m1_pre_topc(B_147,A_146)
      | ~ l1_pre_topc(A_146)
      | ~ v2_pre_topc(A_146)
      | v2_struct_0(A_146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_222])).

tff(c_42,plain,(
    ! [A_28,B_34] :
      ( r1_tarski(k1_relat_1(A_28),k1_relat_1(B_34))
      | ~ r1_tarski(A_28,B_34)
      | ~ v1_funct_1(B_34)
      | ~ v1_relat_1(B_34)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_679,plain,(
    ! [A_188,B_189,A_190] :
      ( r1_tarski(k1_relat_1(A_188),u1_struct_0(B_189))
      | ~ r1_tarski(A_188,k4_tmap_1(A_190,B_189))
      | ~ v1_funct_1(k4_tmap_1(A_190,B_189))
      | ~ v1_relat_1(k4_tmap_1(A_190,B_189))
      | ~ v1_funct_1(A_188)
      | ~ v1_relat_1(A_188)
      | ~ m1_pre_topc(B_189,A_190)
      | ~ l1_pre_topc(A_190)
      | ~ v2_pre_topc(A_190)
      | v2_struct_0(A_190)
      | u1_struct_0(A_190) = k1_xboole_0
      | ~ m1_pre_topc(B_189,A_190)
      | ~ l1_pre_topc(A_190)
      | ~ v2_pre_topc(A_190)
      | v2_struct_0(A_190) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_42])).

tff(c_684,plain,(
    ! [A_191,B_192] :
      ( r1_tarski(k1_relat_1(k4_tmap_1(A_191,B_192)),u1_struct_0(B_192))
      | ~ v1_funct_1(k4_tmap_1(A_191,B_192))
      | ~ v1_relat_1(k4_tmap_1(A_191,B_192))
      | u1_struct_0(A_191) = k1_xboole_0
      | ~ m1_pre_topc(B_192,A_191)
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(resolution,[status(thm)],[c_8,c_679])).

tff(c_697,plain,(
    ! [A_191] :
      ( r1_tarski(k1_relat_1(k4_tmap_1(A_191,'#skF_4')),k1_relat_1('#skF_5'))
      | ~ v1_funct_1(k4_tmap_1(A_191,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_191,'#skF_4'))
      | u1_struct_0(A_191) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_191)
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_684])).

tff(c_38,plain,(
    ! [A_28,B_34] :
      ( r2_hidden('#skF_2'(A_28,B_34),k1_relat_1(A_28))
      | r1_tarski(A_28,B_34)
      | ~ r1_tarski(k1_relat_1(A_28),k1_relat_1(B_34))
      | ~ v1_funct_1(B_34)
      | ~ v1_relat_1(B_34)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1248,plain,(
    ! [A_297,B_298,B_299] :
      ( r2_hidden('#skF_2'(k4_tmap_1(A_297,B_298),B_299),u1_struct_0(B_298))
      | r1_tarski(k4_tmap_1(A_297,B_298),B_299)
      | ~ r1_tarski(k1_relat_1(k4_tmap_1(A_297,B_298)),k1_relat_1(B_299))
      | ~ v1_funct_1(B_299)
      | ~ v1_relat_1(B_299)
      | ~ v1_funct_1(k4_tmap_1(A_297,B_298))
      | ~ v1_relat_1(k4_tmap_1(A_297,B_298))
      | ~ m1_pre_topc(B_298,A_297)
      | ~ l1_pre_topc(A_297)
      | ~ v2_pre_topc(A_297)
      | v2_struct_0(A_297)
      | u1_struct_0(A_297) = k1_xboole_0
      | ~ m1_pre_topc(B_298,A_297)
      | ~ l1_pre_topc(A_297)
      | ~ v2_pre_topc(A_297)
      | v2_struct_0(A_297) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_38])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,B_4)
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1262,plain,(
    ! [A_300,B_301,B_302] :
      ( m1_subset_1('#skF_2'(k4_tmap_1(A_300,B_301),B_302),u1_struct_0(B_301))
      | r1_tarski(k4_tmap_1(A_300,B_301),B_302)
      | ~ r1_tarski(k1_relat_1(k4_tmap_1(A_300,B_301)),k1_relat_1(B_302))
      | ~ v1_funct_1(B_302)
      | ~ v1_relat_1(B_302)
      | ~ v1_funct_1(k4_tmap_1(A_300,B_301))
      | ~ v1_relat_1(k4_tmap_1(A_300,B_301))
      | u1_struct_0(A_300) = k1_xboole_0
      | ~ m1_pre_topc(B_301,A_300)
      | ~ l1_pre_topc(A_300)
      | ~ v2_pre_topc(A_300)
      | v2_struct_0(A_300) ) ),
    inference(resolution,[status(thm)],[c_1248,c_10])).

tff(c_1264,plain,(
    ! [A_191] :
      ( m1_subset_1('#skF_2'(k4_tmap_1(A_191,'#skF_4'),'#skF_5'),u1_struct_0('#skF_4'))
      | r1_tarski(k4_tmap_1(A_191,'#skF_4'),'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_funct_1(k4_tmap_1(A_191,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_191,'#skF_4'))
      | u1_struct_0(A_191) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_191)
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(resolution,[status(thm)],[c_697,c_1262])).

tff(c_1281,plain,(
    ! [A_191] :
      ( m1_subset_1('#skF_2'(k4_tmap_1(A_191,'#skF_4'),'#skF_5'),k1_relat_1('#skF_5'))
      | r1_tarski(k4_tmap_1(A_191,'#skF_4'),'#skF_5')
      | ~ v1_funct_1(k4_tmap_1(A_191,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_191,'#skF_4'))
      | u1_struct_0(A_191) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_191)
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_66,c_129,c_1264])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_148,plain,(
    ! [C_100,A_101,B_102] :
      ( m1_subset_1(C_100,u1_struct_0(A_101))
      | ~ m1_subset_1(C_100,u1_struct_0(B_102))
      | ~ m1_pre_topc(B_102,A_101)
      | v2_struct_0(B_102)
      | ~ l1_pre_topc(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_150,plain,(
    ! [C_100,A_101] :
      ( m1_subset_1(C_100,u1_struct_0(A_101))
      | ~ m1_subset_1(C_100,k1_relat_1('#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_101)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_101)
      | v2_struct_0(A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_148])).

tff(c_151,plain,(
    ! [C_100,A_101] :
      ( m1_subset_1(C_100,u1_struct_0(A_101))
      | ~ m1_subset_1(C_100,k1_relat_1('#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_101)
      | ~ l1_pre_topc(A_101)
      | v2_struct_0(A_101) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_150])).

tff(c_405,plain,(
    ! [A_143] :
      ( u1_struct_0(A_143) = k1_xboole_0
      | k1_relset_1(k1_relat_1('#skF_5'),u1_struct_0(A_143),k4_tmap_1(A_143,'#skF_4')) = u1_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_4',A_143)
      | ~ l1_pre_topc(A_143)
      | ~ v2_pre_topc(A_143)
      | v2_struct_0(A_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_390])).

tff(c_414,plain,(
    ! [A_145] :
      ( u1_struct_0(A_145) = k1_xboole_0
      | k1_relset_1(k1_relat_1('#skF_5'),u1_struct_0(A_145),k4_tmap_1(A_145,'#skF_4')) = k1_relat_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_145)
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145)
      | v2_struct_0(A_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_405])).

tff(c_282,plain,(
    ! [B_124,A_125] :
      ( k1_relset_1(u1_struct_0(B_124),u1_struct_0(A_125),k4_tmap_1(A_125,B_124)) = k1_relat_1(k4_tmap_1(A_125,B_124))
      | ~ m1_pre_topc(B_124,A_125)
      | ~ l1_pre_topc(A_125)
      | ~ v2_pre_topc(A_125)
      | v2_struct_0(A_125) ) ),
    inference(resolution,[status(thm)],[c_201,c_16])).

tff(c_291,plain,(
    ! [A_125] :
      ( k1_relset_1(k1_relat_1('#skF_5'),u1_struct_0(A_125),k4_tmap_1(A_125,'#skF_4')) = k1_relat_1(k4_tmap_1(A_125,'#skF_4'))
      | ~ m1_pre_topc('#skF_4',A_125)
      | ~ l1_pre_topc(A_125)
      | ~ v2_pre_topc(A_125)
      | v2_struct_0(A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_282])).

tff(c_480,plain,(
    ! [A_152] :
      ( k1_relat_1(k4_tmap_1(A_152,'#skF_4')) = k1_relat_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_152)
      | ~ l1_pre_topc(A_152)
      | ~ v2_pre_topc(A_152)
      | v2_struct_0(A_152)
      | u1_struct_0(A_152) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_152)
      | ~ l1_pre_topc(A_152)
      | ~ v2_pre_topc(A_152)
      | v2_struct_0(A_152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_291])).

tff(c_1301,plain,(
    ! [A_307,B_308] :
      ( r2_hidden('#skF_2'(k4_tmap_1(A_307,'#skF_4'),B_308),k1_relat_1('#skF_5'))
      | r1_tarski(k4_tmap_1(A_307,'#skF_4'),B_308)
      | ~ r1_tarski(k1_relat_1(k4_tmap_1(A_307,'#skF_4')),k1_relat_1(B_308))
      | ~ v1_funct_1(B_308)
      | ~ v1_relat_1(B_308)
      | ~ v1_funct_1(k4_tmap_1(A_307,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_307,'#skF_4'))
      | ~ m1_pre_topc('#skF_4',A_307)
      | ~ l1_pre_topc(A_307)
      | ~ v2_pre_topc(A_307)
      | v2_struct_0(A_307)
      | u1_struct_0(A_307) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_307)
      | ~ l1_pre_topc(A_307)
      | ~ v2_pre_topc(A_307)
      | v2_struct_0(A_307) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_38])).

tff(c_60,plain,(
    ! [D_67] :
      ( k1_funct_1('#skF_5',D_67) = D_67
      | ~ r2_hidden(D_67,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(D_67,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_131,plain,(
    ! [D_67] :
      ( k1_funct_1('#skF_5',D_67) = D_67
      | ~ r2_hidden(D_67,k1_relat_1('#skF_5'))
      | ~ m1_subset_1(D_67,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_60])).

tff(c_1353,plain,(
    ! [A_311,B_312] :
      ( k1_funct_1('#skF_5','#skF_2'(k4_tmap_1(A_311,'#skF_4'),B_312)) = '#skF_2'(k4_tmap_1(A_311,'#skF_4'),B_312)
      | ~ m1_subset_1('#skF_2'(k4_tmap_1(A_311,'#skF_4'),B_312),u1_struct_0('#skF_3'))
      | r1_tarski(k4_tmap_1(A_311,'#skF_4'),B_312)
      | ~ r1_tarski(k1_relat_1(k4_tmap_1(A_311,'#skF_4')),k1_relat_1(B_312))
      | ~ v1_funct_1(B_312)
      | ~ v1_relat_1(B_312)
      | ~ v1_funct_1(k4_tmap_1(A_311,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_311,'#skF_4'))
      | u1_struct_0(A_311) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_311)
      | ~ l1_pre_topc(A_311)
      | ~ v2_pre_topc(A_311)
      | v2_struct_0(A_311) ) ),
    inference(resolution,[status(thm)],[c_1301,c_131])).

tff(c_1356,plain,(
    ! [A_191] :
      ( k1_funct_1('#skF_5','#skF_2'(k4_tmap_1(A_191,'#skF_4'),'#skF_5')) = '#skF_2'(k4_tmap_1(A_191,'#skF_4'),'#skF_5')
      | ~ m1_subset_1('#skF_2'(k4_tmap_1(A_191,'#skF_4'),'#skF_5'),u1_struct_0('#skF_3'))
      | r1_tarski(k4_tmap_1(A_191,'#skF_4'),'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_funct_1(k4_tmap_1(A_191,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_191,'#skF_4'))
      | u1_struct_0(A_191) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_191)
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(resolution,[status(thm)],[c_697,c_1353])).

tff(c_1385,plain,(
    ! [A_313] :
      ( k1_funct_1('#skF_5','#skF_2'(k4_tmap_1(A_313,'#skF_4'),'#skF_5')) = '#skF_2'(k4_tmap_1(A_313,'#skF_4'),'#skF_5')
      | ~ m1_subset_1('#skF_2'(k4_tmap_1(A_313,'#skF_4'),'#skF_5'),u1_struct_0('#skF_3'))
      | r1_tarski(k4_tmap_1(A_313,'#skF_4'),'#skF_5')
      | ~ v1_funct_1(k4_tmap_1(A_313,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_313,'#skF_4'))
      | u1_struct_0(A_313) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_313)
      | ~ l1_pre_topc(A_313)
      | ~ v2_pre_topc(A_313)
      | v2_struct_0(A_313) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_66,c_1356])).

tff(c_1388,plain,(
    ! [A_313] :
      ( k1_funct_1('#skF_5','#skF_2'(k4_tmap_1(A_313,'#skF_4'),'#skF_5')) = '#skF_2'(k4_tmap_1(A_313,'#skF_4'),'#skF_5')
      | r1_tarski(k4_tmap_1(A_313,'#skF_4'),'#skF_5')
      | ~ v1_funct_1(k4_tmap_1(A_313,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_313,'#skF_4'))
      | u1_struct_0(A_313) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_313)
      | ~ l1_pre_topc(A_313)
      | ~ v2_pre_topc(A_313)
      | v2_struct_0(A_313)
      | ~ m1_subset_1('#skF_2'(k4_tmap_1(A_313,'#skF_4'),'#skF_5'),k1_relat_1('#skF_5'))
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_151,c_1385])).

tff(c_1391,plain,(
    ! [A_313] :
      ( k1_funct_1('#skF_5','#skF_2'(k4_tmap_1(A_313,'#skF_4'),'#skF_5')) = '#skF_2'(k4_tmap_1(A_313,'#skF_4'),'#skF_5')
      | r1_tarski(k4_tmap_1(A_313,'#skF_4'),'#skF_5')
      | ~ v1_funct_1(k4_tmap_1(A_313,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_313,'#skF_4'))
      | u1_struct_0(A_313) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_313)
      | ~ l1_pre_topc(A_313)
      | ~ v2_pre_topc(A_313)
      | v2_struct_0(A_313)
      | ~ m1_subset_1('#skF_2'(k4_tmap_1(A_313,'#skF_4'),'#skF_5'),k1_relat_1('#skF_5'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_1388])).

tff(c_1393,plain,(
    ! [A_314] :
      ( k1_funct_1('#skF_5','#skF_2'(k4_tmap_1(A_314,'#skF_4'),'#skF_5')) = '#skF_2'(k4_tmap_1(A_314,'#skF_4'),'#skF_5')
      | r1_tarski(k4_tmap_1(A_314,'#skF_4'),'#skF_5')
      | ~ v1_funct_1(k4_tmap_1(A_314,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_314,'#skF_4'))
      | u1_struct_0(A_314) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_314)
      | ~ l1_pre_topc(A_314)
      | ~ v2_pre_topc(A_314)
      | v2_struct_0(A_314)
      | ~ m1_subset_1('#skF_2'(k4_tmap_1(A_314,'#skF_4'),'#skF_5'),k1_relat_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1391])).

tff(c_1397,plain,(
    ! [A_191] :
      ( k1_funct_1('#skF_5','#skF_2'(k4_tmap_1(A_191,'#skF_4'),'#skF_5')) = '#skF_2'(k4_tmap_1(A_191,'#skF_4'),'#skF_5')
      | r1_tarski(k4_tmap_1(A_191,'#skF_4'),'#skF_5')
      | ~ v1_funct_1(k4_tmap_1(A_191,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_191,'#skF_4'))
      | u1_struct_0(A_191) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_191)
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(resolution,[status(thm)],[c_1281,c_1393])).

tff(c_335,plain,(
    ! [A_131,B_132,C_133] :
      ( k1_funct_1(k4_tmap_1(A_131,B_132),C_133) = C_133
      | ~ r2_hidden(C_133,u1_struct_0(B_132))
      | ~ m1_subset_1(C_133,u1_struct_0(A_131))
      | ~ m1_pre_topc(B_132,A_131)
      | v2_struct_0(B_132)
      | ~ l1_pre_topc(A_131)
      | ~ v2_pre_topc(A_131)
      | v2_struct_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_337,plain,(
    ! [A_131,C_133] :
      ( k1_funct_1(k4_tmap_1(A_131,'#skF_4'),C_133) = C_133
      | ~ r2_hidden(C_133,k1_relat_1('#skF_5'))
      | ~ m1_subset_1(C_133,u1_struct_0(A_131))
      | ~ m1_pre_topc('#skF_4',A_131)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_131)
      | ~ v2_pre_topc(A_131)
      | v2_struct_0(A_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_335])).

tff(c_338,plain,(
    ! [A_131,C_133] :
      ( k1_funct_1(k4_tmap_1(A_131,'#skF_4'),C_133) = C_133
      | ~ r2_hidden(C_133,k1_relat_1('#skF_5'))
      | ~ m1_subset_1(C_133,u1_struct_0(A_131))
      | ~ m1_pre_topc('#skF_4',A_131)
      | ~ l1_pre_topc(A_131)
      | ~ v2_pre_topc(A_131)
      | v2_struct_0(A_131) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_337])).

tff(c_1439,plain,(
    ! [A_324,A_325,B_326] :
      ( k1_funct_1(k4_tmap_1(A_324,'#skF_4'),'#skF_2'(k4_tmap_1(A_325,'#skF_4'),B_326)) = '#skF_2'(k4_tmap_1(A_325,'#skF_4'),B_326)
      | ~ m1_subset_1('#skF_2'(k4_tmap_1(A_325,'#skF_4'),B_326),u1_struct_0(A_324))
      | ~ m1_pre_topc('#skF_4',A_324)
      | ~ l1_pre_topc(A_324)
      | ~ v2_pre_topc(A_324)
      | v2_struct_0(A_324)
      | r1_tarski(k4_tmap_1(A_325,'#skF_4'),B_326)
      | ~ r1_tarski(k1_relat_1(k4_tmap_1(A_325,'#skF_4')),k1_relat_1(B_326))
      | ~ v1_funct_1(B_326)
      | ~ v1_relat_1(B_326)
      | ~ v1_funct_1(k4_tmap_1(A_325,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_325,'#skF_4'))
      | u1_struct_0(A_325) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_325)
      | ~ l1_pre_topc(A_325)
      | ~ v2_pre_topc(A_325)
      | v2_struct_0(A_325) ) ),
    inference(resolution,[status(thm)],[c_1301,c_338])).

tff(c_1475,plain,(
    ! [A_337,A_338,B_339] :
      ( k1_funct_1(k4_tmap_1(A_337,'#skF_4'),'#skF_2'(k4_tmap_1(A_338,'#skF_4'),B_339)) = '#skF_2'(k4_tmap_1(A_338,'#skF_4'),B_339)
      | ~ v2_pre_topc(A_337)
      | r1_tarski(k4_tmap_1(A_338,'#skF_4'),B_339)
      | ~ r1_tarski(k1_relat_1(k4_tmap_1(A_338,'#skF_4')),k1_relat_1(B_339))
      | ~ v1_funct_1(B_339)
      | ~ v1_relat_1(B_339)
      | ~ v1_funct_1(k4_tmap_1(A_338,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_338,'#skF_4'))
      | u1_struct_0(A_338) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_338)
      | ~ l1_pre_topc(A_338)
      | ~ v2_pre_topc(A_338)
      | v2_struct_0(A_338)
      | ~ m1_subset_1('#skF_2'(k4_tmap_1(A_338,'#skF_4'),B_339),k1_relat_1('#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_337)
      | ~ l1_pre_topc(A_337)
      | v2_struct_0(A_337) ) ),
    inference(resolution,[status(thm)],[c_151,c_1439])).

tff(c_1477,plain,(
    ! [A_337,A_191] :
      ( k1_funct_1(k4_tmap_1(A_337,'#skF_4'),'#skF_2'(k4_tmap_1(A_191,'#skF_4'),'#skF_5')) = '#skF_2'(k4_tmap_1(A_191,'#skF_4'),'#skF_5')
      | ~ v2_pre_topc(A_337)
      | r1_tarski(k4_tmap_1(A_191,'#skF_4'),'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ m1_subset_1('#skF_2'(k4_tmap_1(A_191,'#skF_4'),'#skF_5'),k1_relat_1('#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_337)
      | ~ l1_pre_topc(A_337)
      | v2_struct_0(A_337)
      | ~ v1_funct_1(k4_tmap_1(A_191,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_191,'#skF_4'))
      | u1_struct_0(A_191) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_191)
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(resolution,[status(thm)],[c_697,c_1475])).

tff(c_1500,plain,(
    ! [A_340,A_341] :
      ( k1_funct_1(k4_tmap_1(A_340,'#skF_4'),'#skF_2'(k4_tmap_1(A_341,'#skF_4'),'#skF_5')) = '#skF_2'(k4_tmap_1(A_341,'#skF_4'),'#skF_5')
      | ~ v2_pre_topc(A_340)
      | r1_tarski(k4_tmap_1(A_341,'#skF_4'),'#skF_5')
      | ~ m1_subset_1('#skF_2'(k4_tmap_1(A_341,'#skF_4'),'#skF_5'),k1_relat_1('#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_340)
      | ~ l1_pre_topc(A_340)
      | v2_struct_0(A_340)
      | ~ v1_funct_1(k4_tmap_1(A_341,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_341,'#skF_4'))
      | u1_struct_0(A_341) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_341)
      | ~ l1_pre_topc(A_341)
      | ~ v2_pre_topc(A_341)
      | v2_struct_0(A_341) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_66,c_1477])).

tff(c_1504,plain,(
    ! [A_342,A_343] :
      ( k1_funct_1(k4_tmap_1(A_342,'#skF_4'),'#skF_2'(k4_tmap_1(A_343,'#skF_4'),'#skF_5')) = '#skF_2'(k4_tmap_1(A_343,'#skF_4'),'#skF_5')
      | ~ v2_pre_topc(A_342)
      | ~ m1_pre_topc('#skF_4',A_342)
      | ~ l1_pre_topc(A_342)
      | v2_struct_0(A_342)
      | r1_tarski(k4_tmap_1(A_343,'#skF_4'),'#skF_5')
      | ~ v1_funct_1(k4_tmap_1(A_343,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_343,'#skF_4'))
      | u1_struct_0(A_343) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_343)
      | ~ l1_pre_topc(A_343)
      | ~ v2_pre_topc(A_343)
      | v2_struct_0(A_343) ) ),
    inference(resolution,[status(thm)],[c_1281,c_1500])).

tff(c_36,plain,(
    ! [B_34,A_28] :
      ( k1_funct_1(B_34,'#skF_2'(A_28,B_34)) != k1_funct_1(A_28,'#skF_2'(A_28,B_34))
      | r1_tarski(A_28,B_34)
      | ~ r1_tarski(k1_relat_1(A_28),k1_relat_1(B_34))
      | ~ v1_funct_1(B_34)
      | ~ v1_relat_1(B_34)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1519,plain,(
    ! [A_343] :
      ( k1_funct_1('#skF_5','#skF_2'(k4_tmap_1(A_343,'#skF_4'),'#skF_5')) != '#skF_2'(k4_tmap_1(A_343,'#skF_4'),'#skF_5')
      | r1_tarski(k4_tmap_1(A_343,'#skF_4'),'#skF_5')
      | ~ r1_tarski(k1_relat_1(k4_tmap_1(A_343,'#skF_4')),k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_funct_1(k4_tmap_1(A_343,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_343,'#skF_4'))
      | ~ v2_pre_topc(A_343)
      | ~ m1_pre_topc('#skF_4',A_343)
      | ~ l1_pre_topc(A_343)
      | v2_struct_0(A_343)
      | r1_tarski(k4_tmap_1(A_343,'#skF_4'),'#skF_5')
      | ~ v1_funct_1(k4_tmap_1(A_343,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_343,'#skF_4'))
      | u1_struct_0(A_343) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_343)
      | ~ l1_pre_topc(A_343)
      | ~ v2_pre_topc(A_343)
      | v2_struct_0(A_343) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1504,c_36])).

tff(c_1534,plain,(
    ! [A_344] :
      ( k1_funct_1('#skF_5','#skF_2'(k4_tmap_1(A_344,'#skF_4'),'#skF_5')) != '#skF_2'(k4_tmap_1(A_344,'#skF_4'),'#skF_5')
      | ~ r1_tarski(k1_relat_1(k4_tmap_1(A_344,'#skF_4')),k1_relat_1('#skF_5'))
      | r1_tarski(k4_tmap_1(A_344,'#skF_4'),'#skF_5')
      | ~ v1_funct_1(k4_tmap_1(A_344,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_344,'#skF_4'))
      | u1_struct_0(A_344) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_344)
      | ~ l1_pre_topc(A_344)
      | ~ v2_pre_topc(A_344)
      | v2_struct_0(A_344) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_66,c_1519])).

tff(c_1556,plain,(
    ! [A_345] :
      ( k1_funct_1('#skF_5','#skF_2'(k4_tmap_1(A_345,'#skF_4'),'#skF_5')) != '#skF_2'(k4_tmap_1(A_345,'#skF_4'),'#skF_5')
      | r1_tarski(k4_tmap_1(A_345,'#skF_4'),'#skF_5')
      | ~ v1_funct_1(k4_tmap_1(A_345,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_345,'#skF_4'))
      | u1_struct_0(A_345) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_345)
      | ~ l1_pre_topc(A_345)
      | ~ v2_pre_topc(A_345)
      | v2_struct_0(A_345) ) ),
    inference(resolution,[status(thm)],[c_697,c_1534])).

tff(c_1561,plain,(
    ! [A_346] :
      ( r1_tarski(k4_tmap_1(A_346,'#skF_4'),'#skF_5')
      | ~ v1_funct_1(k4_tmap_1(A_346,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_346,'#skF_4'))
      | u1_struct_0(A_346) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_346)
      | ~ l1_pre_topc(A_346)
      | ~ v2_pre_topc(A_346)
      | v2_struct_0(A_346) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1397,c_1556])).

tff(c_788,plain,(
    ! [B_209,B_210,A_211] :
      ( r1_tarski(u1_struct_0(B_209),k1_relat_1(B_210))
      | ~ r1_tarski(k4_tmap_1(A_211,B_209),B_210)
      | ~ v1_funct_1(B_210)
      | ~ v1_relat_1(B_210)
      | ~ v1_funct_1(k4_tmap_1(A_211,B_209))
      | ~ v1_relat_1(k4_tmap_1(A_211,B_209))
      | ~ m1_pre_topc(B_209,A_211)
      | ~ l1_pre_topc(A_211)
      | ~ v2_pre_topc(A_211)
      | v2_struct_0(A_211)
      | u1_struct_0(A_211) = k1_xboole_0
      | ~ m1_pre_topc(B_209,A_211)
      | ~ l1_pre_topc(A_211)
      | ~ v2_pre_topc(A_211)
      | v2_struct_0(A_211) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_42])).

tff(c_794,plain,(
    ! [B_215,A_216] :
      ( r1_tarski(u1_struct_0(B_215),k1_relat_1(k4_tmap_1(A_216,B_215)))
      | ~ v1_funct_1(k4_tmap_1(A_216,B_215))
      | ~ v1_relat_1(k4_tmap_1(A_216,B_215))
      | u1_struct_0(A_216) = k1_xboole_0
      | ~ m1_pre_topc(B_215,A_216)
      | ~ l1_pre_topc(A_216)
      | ~ v2_pre_topc(A_216)
      | v2_struct_0(A_216) ) ),
    inference(resolution,[status(thm)],[c_8,c_788])).

tff(c_812,plain,(
    ! [A_217] :
      ( r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(k4_tmap_1(A_217,'#skF_4')))
      | ~ v1_funct_1(k4_tmap_1(A_217,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_217,'#skF_4'))
      | u1_struct_0(A_217) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_217)
      | ~ l1_pre_topc(A_217)
      | ~ v2_pre_topc(A_217)
      | v2_struct_0(A_217) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_794])).

tff(c_311,plain,(
    ! [A_127,B_128] :
      ( r2_hidden('#skF_2'(A_127,B_128),k1_relat_1(A_127))
      | r1_tarski(A_127,B_128)
      | ~ r1_tarski(k1_relat_1(A_127),k1_relat_1(B_128))
      | ~ v1_funct_1(B_128)
      | ~ v1_relat_1(B_128)
      | ~ v1_funct_1(A_127)
      | ~ v1_relat_1(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_325,plain,(
    ! [A_127,B_128] :
      ( m1_subset_1('#skF_2'(A_127,B_128),k1_relat_1(A_127))
      | r1_tarski(A_127,B_128)
      | ~ r1_tarski(k1_relat_1(A_127),k1_relat_1(B_128))
      | ~ v1_funct_1(B_128)
      | ~ v1_relat_1(B_128)
      | ~ v1_funct_1(A_127)
      | ~ v1_relat_1(A_127) ) ),
    inference(resolution,[status(thm)],[c_311,c_10])).

tff(c_824,plain,(
    ! [A_217] :
      ( m1_subset_1('#skF_2'('#skF_5',k4_tmap_1(A_217,'#skF_4')),k1_relat_1('#skF_5'))
      | r1_tarski('#skF_5',k4_tmap_1(A_217,'#skF_4'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_funct_1(k4_tmap_1(A_217,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_217,'#skF_4'))
      | u1_struct_0(A_217) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_217)
      | ~ l1_pre_topc(A_217)
      | ~ v2_pre_topc(A_217)
      | v2_struct_0(A_217) ) ),
    inference(resolution,[status(thm)],[c_812,c_325])).

tff(c_849,plain,(
    ! [A_217] :
      ( m1_subset_1('#skF_2'('#skF_5',k4_tmap_1(A_217,'#skF_4')),k1_relat_1('#skF_5'))
      | r1_tarski('#skF_5',k4_tmap_1(A_217,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_217,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_217,'#skF_4'))
      | u1_struct_0(A_217) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_217)
      | ~ l1_pre_topc(A_217)
      | ~ v2_pre_topc(A_217)
      | v2_struct_0(A_217) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_66,c_824])).

tff(c_317,plain,(
    ! [B_128] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',B_128)) = '#skF_2'('#skF_5',B_128)
      | ~ m1_subset_1('#skF_2'('#skF_5',B_128),u1_struct_0('#skF_3'))
      | r1_tarski('#skF_5',B_128)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(B_128))
      | ~ v1_funct_1(B_128)
      | ~ v1_relat_1(B_128)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_311,c_131])).

tff(c_324,plain,(
    ! [B_128] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',B_128)) = '#skF_2'('#skF_5',B_128)
      | ~ m1_subset_1('#skF_2'('#skF_5',B_128),u1_struct_0('#skF_3'))
      | r1_tarski('#skF_5',B_128)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(B_128))
      | ~ v1_funct_1(B_128)
      | ~ v1_relat_1(B_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_66,c_317])).

tff(c_489,plain,(
    ! [A_152] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',k4_tmap_1(A_152,'#skF_4'))) = '#skF_2'('#skF_5',k4_tmap_1(A_152,'#skF_4'))
      | ~ m1_subset_1('#skF_2'('#skF_5',k4_tmap_1(A_152,'#skF_4')),u1_struct_0('#skF_3'))
      | r1_tarski('#skF_5',k4_tmap_1(A_152,'#skF_4'))
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1('#skF_5'))
      | ~ v1_funct_1(k4_tmap_1(A_152,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_152,'#skF_4'))
      | ~ m1_pre_topc('#skF_4',A_152)
      | ~ l1_pre_topc(A_152)
      | ~ v2_pre_topc(A_152)
      | v2_struct_0(A_152)
      | u1_struct_0(A_152) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_152)
      | ~ l1_pre_topc(A_152)
      | ~ v2_pre_topc(A_152)
      | v2_struct_0(A_152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_324])).

tff(c_885,plain,(
    ! [A_225] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',k4_tmap_1(A_225,'#skF_4'))) = '#skF_2'('#skF_5',k4_tmap_1(A_225,'#skF_4'))
      | ~ m1_subset_1('#skF_2'('#skF_5',k4_tmap_1(A_225,'#skF_4')),u1_struct_0('#skF_3'))
      | r1_tarski('#skF_5',k4_tmap_1(A_225,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_225,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_225,'#skF_4'))
      | u1_struct_0(A_225) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_225)
      | ~ l1_pre_topc(A_225)
      | ~ v2_pre_topc(A_225)
      | v2_struct_0(A_225) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_489])).

tff(c_888,plain,(
    ! [A_225] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',k4_tmap_1(A_225,'#skF_4'))) = '#skF_2'('#skF_5',k4_tmap_1(A_225,'#skF_4'))
      | r1_tarski('#skF_5',k4_tmap_1(A_225,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_225,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_225,'#skF_4'))
      | u1_struct_0(A_225) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_225)
      | ~ l1_pre_topc(A_225)
      | ~ v2_pre_topc(A_225)
      | v2_struct_0(A_225)
      | ~ m1_subset_1('#skF_2'('#skF_5',k4_tmap_1(A_225,'#skF_4')),k1_relat_1('#skF_5'))
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_151,c_885])).

tff(c_891,plain,(
    ! [A_225] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',k4_tmap_1(A_225,'#skF_4'))) = '#skF_2'('#skF_5',k4_tmap_1(A_225,'#skF_4'))
      | r1_tarski('#skF_5',k4_tmap_1(A_225,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_225,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_225,'#skF_4'))
      | u1_struct_0(A_225) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_225)
      | ~ l1_pre_topc(A_225)
      | ~ v2_pre_topc(A_225)
      | v2_struct_0(A_225)
      | ~ m1_subset_1('#skF_2'('#skF_5',k4_tmap_1(A_225,'#skF_4')),k1_relat_1('#skF_5'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_888])).

tff(c_893,plain,(
    ! [A_226] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',k4_tmap_1(A_226,'#skF_4'))) = '#skF_2'('#skF_5',k4_tmap_1(A_226,'#skF_4'))
      | r1_tarski('#skF_5',k4_tmap_1(A_226,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_226,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_226,'#skF_4'))
      | u1_struct_0(A_226) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_226)
      | ~ l1_pre_topc(A_226)
      | ~ v2_pre_topc(A_226)
      | v2_struct_0(A_226)
      | ~ m1_subset_1('#skF_2'('#skF_5',k4_tmap_1(A_226,'#skF_4')),k1_relat_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_891])).

tff(c_897,plain,(
    ! [A_217] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',k4_tmap_1(A_217,'#skF_4'))) = '#skF_2'('#skF_5',k4_tmap_1(A_217,'#skF_4'))
      | r1_tarski('#skF_5',k4_tmap_1(A_217,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_217,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_217,'#skF_4'))
      | u1_struct_0(A_217) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_217)
      | ~ l1_pre_topc(A_217)
      | ~ v2_pre_topc(A_217)
      | v2_struct_0(A_217) ) ),
    inference(resolution,[status(thm)],[c_849,c_893])).

tff(c_807,plain,(
    ! [A_216] :
      ( r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(k4_tmap_1(A_216,'#skF_4')))
      | ~ v1_funct_1(k4_tmap_1(A_216,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_216,'#skF_4'))
      | u1_struct_0(A_216) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_216)
      | ~ l1_pre_topc(A_216)
      | ~ v2_pre_topc(A_216)
      | v2_struct_0(A_216) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_794])).

tff(c_857,plain,(
    ! [A_218] :
      ( m1_subset_1('#skF_2'('#skF_5',k4_tmap_1(A_218,'#skF_4')),k1_relat_1('#skF_5'))
      | r1_tarski('#skF_5',k4_tmap_1(A_218,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_218,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_218,'#skF_4'))
      | u1_struct_0(A_218) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_218)
      | ~ l1_pre_topc(A_218)
      | ~ v2_pre_topc(A_218)
      | v2_struct_0(A_218) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_66,c_824])).

tff(c_396,plain,(
    ! [A_143,B_144] :
      ( k1_relat_1(k4_tmap_1(A_143,B_144)) = u1_struct_0(B_144)
      | ~ m1_pre_topc(B_144,A_143)
      | ~ l1_pre_topc(A_143)
      | ~ v2_pre_topc(A_143)
      | v2_struct_0(A_143)
      | u1_struct_0(A_143) = k1_xboole_0
      | ~ m1_pre_topc(B_144,A_143)
      | ~ l1_pre_topc(A_143)
      | ~ v2_pre_topc(A_143)
      | v2_struct_0(A_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_222])).

tff(c_339,plain,(
    ! [A_134,C_135] :
      ( k1_funct_1(k4_tmap_1(A_134,'#skF_4'),C_135) = C_135
      | ~ r2_hidden(C_135,k1_relat_1('#skF_5'))
      | ~ m1_subset_1(C_135,u1_struct_0(A_134))
      | ~ m1_pre_topc('#skF_4',A_134)
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134)
      | v2_struct_0(A_134) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_337])).

tff(c_342,plain,(
    ! [A_134,B_34] :
      ( k1_funct_1(k4_tmap_1(A_134,'#skF_4'),'#skF_2'('#skF_5',B_34)) = '#skF_2'('#skF_5',B_34)
      | ~ m1_subset_1('#skF_2'('#skF_5',B_34),u1_struct_0(A_134))
      | ~ m1_pre_topc('#skF_4',A_134)
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134)
      | v2_struct_0(A_134)
      | r1_tarski('#skF_5',B_34)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(B_34))
      | ~ v1_funct_1(B_34)
      | ~ v1_relat_1(B_34)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_38,c_339])).

tff(c_367,plain,(
    ! [A_139,B_140] :
      ( k1_funct_1(k4_tmap_1(A_139,'#skF_4'),'#skF_2'('#skF_5',B_140)) = '#skF_2'('#skF_5',B_140)
      | ~ m1_subset_1('#skF_2'('#skF_5',B_140),u1_struct_0(A_139))
      | ~ m1_pre_topc('#skF_4',A_139)
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139)
      | v2_struct_0(A_139)
      | r1_tarski('#skF_5',B_140)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(B_140))
      | ~ v1_funct_1(B_140)
      | ~ v1_relat_1(B_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_66,c_342])).

tff(c_524,plain,(
    ! [A_153,B_154] :
      ( k1_funct_1(k4_tmap_1(A_153,'#skF_4'),'#skF_2'('#skF_5',B_154)) = '#skF_2'('#skF_5',B_154)
      | ~ v2_pre_topc(A_153)
      | r1_tarski('#skF_5',B_154)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(B_154))
      | ~ v1_funct_1(B_154)
      | ~ v1_relat_1(B_154)
      | ~ m1_subset_1('#skF_2'('#skF_5',B_154),k1_relat_1('#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_153)
      | ~ l1_pre_topc(A_153)
      | v2_struct_0(A_153) ) ),
    inference(resolution,[status(thm)],[c_151,c_367])).

tff(c_528,plain,(
    ! [A_153,A_143,B_144] :
      ( k1_funct_1(k4_tmap_1(A_153,'#skF_4'),'#skF_2'('#skF_5',k4_tmap_1(A_143,B_144))) = '#skF_2'('#skF_5',k4_tmap_1(A_143,B_144))
      | ~ v2_pre_topc(A_153)
      | r1_tarski('#skF_5',k4_tmap_1(A_143,B_144))
      | ~ r1_tarski(k1_relat_1('#skF_5'),u1_struct_0(B_144))
      | ~ v1_funct_1(k4_tmap_1(A_143,B_144))
      | ~ v1_relat_1(k4_tmap_1(A_143,B_144))
      | ~ m1_subset_1('#skF_2'('#skF_5',k4_tmap_1(A_143,B_144)),k1_relat_1('#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_153)
      | ~ l1_pre_topc(A_153)
      | v2_struct_0(A_153)
      | ~ m1_pre_topc(B_144,A_143)
      | ~ l1_pre_topc(A_143)
      | ~ v2_pre_topc(A_143)
      | v2_struct_0(A_143)
      | u1_struct_0(A_143) = k1_xboole_0
      | ~ m1_pre_topc(B_144,A_143)
      | ~ l1_pre_topc(A_143)
      | ~ v2_pre_topc(A_143)
      | v2_struct_0(A_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_524])).

tff(c_859,plain,(
    ! [A_153,A_218] :
      ( k1_funct_1(k4_tmap_1(A_153,'#skF_4'),'#skF_2'('#skF_5',k4_tmap_1(A_218,'#skF_4'))) = '#skF_2'('#skF_5',k4_tmap_1(A_218,'#skF_4'))
      | ~ v2_pre_topc(A_153)
      | ~ r1_tarski(k1_relat_1('#skF_5'),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc('#skF_4',A_153)
      | ~ l1_pre_topc(A_153)
      | v2_struct_0(A_153)
      | r1_tarski('#skF_5',k4_tmap_1(A_218,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_218,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_218,'#skF_4'))
      | u1_struct_0(A_218) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_218)
      | ~ l1_pre_topc(A_218)
      | ~ v2_pre_topc(A_218)
      | v2_struct_0(A_218) ) ),
    inference(resolution,[status(thm)],[c_857,c_528])).

tff(c_938,plain,(
    ! [A_232,A_233] :
      ( k1_funct_1(k4_tmap_1(A_232,'#skF_4'),'#skF_2'('#skF_5',k4_tmap_1(A_233,'#skF_4'))) = '#skF_2'('#skF_5',k4_tmap_1(A_233,'#skF_4'))
      | ~ v2_pre_topc(A_232)
      | ~ m1_pre_topc('#skF_4',A_232)
      | ~ l1_pre_topc(A_232)
      | v2_struct_0(A_232)
      | r1_tarski('#skF_5',k4_tmap_1(A_233,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_233,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_233,'#skF_4'))
      | u1_struct_0(A_233) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_233)
      | ~ l1_pre_topc(A_233)
      | ~ v2_pre_topc(A_233)
      | v2_struct_0(A_233) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_129,c_859])).

tff(c_947,plain,(
    ! [A_233] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',k4_tmap_1(A_233,'#skF_4'))) != '#skF_2'('#skF_5',k4_tmap_1(A_233,'#skF_4'))
      | r1_tarski('#skF_5',k4_tmap_1(A_233,'#skF_4'))
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(k4_tmap_1(A_233,'#skF_4')))
      | ~ v1_funct_1(k4_tmap_1(A_233,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_233,'#skF_4'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ v2_pre_topc(A_233)
      | ~ m1_pre_topc('#skF_4',A_233)
      | ~ l1_pre_topc(A_233)
      | v2_struct_0(A_233)
      | r1_tarski('#skF_5',k4_tmap_1(A_233,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_233,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_233,'#skF_4'))
      | u1_struct_0(A_233) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_233)
      | ~ l1_pre_topc(A_233)
      | ~ v2_pre_topc(A_233)
      | v2_struct_0(A_233) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_938,c_36])).

tff(c_959,plain,(
    ! [A_234] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',k4_tmap_1(A_234,'#skF_4'))) != '#skF_2'('#skF_5',k4_tmap_1(A_234,'#skF_4'))
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(k4_tmap_1(A_234,'#skF_4')))
      | r1_tarski('#skF_5',k4_tmap_1(A_234,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_234,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_234,'#skF_4'))
      | u1_struct_0(A_234) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_234)
      | ~ l1_pre_topc(A_234)
      | ~ v2_pre_topc(A_234)
      | v2_struct_0(A_234) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_66,c_947])).

tff(c_981,plain,(
    ! [A_235] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',k4_tmap_1(A_235,'#skF_4'))) != '#skF_2'('#skF_5',k4_tmap_1(A_235,'#skF_4'))
      | r1_tarski('#skF_5',k4_tmap_1(A_235,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_235,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_235,'#skF_4'))
      | u1_struct_0(A_235) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_235)
      | ~ l1_pre_topc(A_235)
      | ~ v2_pre_topc(A_235)
      | v2_struct_0(A_235) ) ),
    inference(resolution,[status(thm)],[c_807,c_959])).

tff(c_989,plain,(
    ! [A_236] :
      ( r1_tarski('#skF_5',k4_tmap_1(A_236,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_236,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_236,'#skF_4'))
      | u1_struct_0(A_236) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_236)
      | ~ l1_pre_topc(A_236)
      | ~ v2_pre_topc(A_236)
      | v2_struct_0(A_236) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_897,c_981])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1007,plain,(
    ! [A_236] :
      ( k4_tmap_1(A_236,'#skF_4') = '#skF_5'
      | ~ r1_tarski(k4_tmap_1(A_236,'#skF_4'),'#skF_5')
      | ~ v1_funct_1(k4_tmap_1(A_236,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_236,'#skF_4'))
      | u1_struct_0(A_236) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_236)
      | ~ l1_pre_topc(A_236)
      | ~ v2_pre_topc(A_236)
      | v2_struct_0(A_236) ) ),
    inference(resolution,[status(thm)],[c_989,c_4])).

tff(c_1606,plain,(
    ! [A_351] :
      ( k4_tmap_1(A_351,'#skF_4') = '#skF_5'
      | ~ v1_funct_1(k4_tmap_1(A_351,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_351,'#skF_4'))
      | u1_struct_0(A_351) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_351)
      | ~ l1_pre_topc(A_351)
      | ~ v2_pre_topc(A_351)
      | v2_struct_0(A_351) ) ),
    inference(resolution,[status(thm)],[c_1561,c_1007])).

tff(c_1612,plain,(
    ! [A_352] :
      ( k4_tmap_1(A_352,'#skF_4') = '#skF_5'
      | ~ v1_funct_1(k4_tmap_1(A_352,'#skF_4'))
      | u1_struct_0(A_352) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_352)
      | ~ l1_pre_topc(A_352)
      | ~ v2_pre_topc(A_352)
      | v2_struct_0(A_352) ) ),
    inference(resolution,[status(thm)],[c_225,c_1606])).

tff(c_1618,plain,(
    ! [A_353] :
      ( k4_tmap_1(A_353,'#skF_4') = '#skF_5'
      | u1_struct_0(A_353) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_353)
      | ~ l1_pre_topc(A_353)
      | ~ v2_pre_topc(A_353)
      | v2_struct_0(A_353) ) ),
    inference(resolution,[status(thm)],[c_54,c_1612])).

tff(c_1621,plain,
    ( k4_tmap_1('#skF_3','#skF_4') = '#skF_5'
    | u1_struct_0('#skF_3') = k1_xboole_0
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1618])).

tff(c_1624,plain,
    ( k4_tmap_1('#skF_3','#skF_4') = '#skF_5'
    | u1_struct_0('#skF_3') = k1_xboole_0
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_1621])).

tff(c_1625,plain,
    ( k4_tmap_1('#skF_3','#skF_4') = '#skF_5'
    | u1_struct_0('#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1624])).

tff(c_1626,plain,(
    u1_struct_0('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1625])).

tff(c_46,plain,(
    ! [A_39] :
      ( ~ v1_xboole_0(u1_struct_0(A_39))
      | ~ l1_struct_0(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1751,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1626,c_46])).

tff(c_1834,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1751])).

tff(c_1835,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1834])).

tff(c_1839,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_1835])).

tff(c_1843,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1839])).

tff(c_1844,plain,(
    k4_tmap_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1625])).

tff(c_58,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_132,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_5'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_58])).

tff(c_1846,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_5'),u1_struct_0('#skF_3'),'#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1844,c_132])).

tff(c_1849,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_1846])).

tff(c_1850,plain,(
    u1_struct_0('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_1860,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1850,c_46])).

tff(c_1864,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1860])).

tff(c_1865,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1864])).

tff(c_1879,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_1865])).

tff(c_1883,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1879])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:36:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.96/2.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.96/2.17  
% 5.96/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.96/2.17  %$ r2_funct_2 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k1_relset_1 > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 5.96/2.17  
% 5.96/2.17  %Foreground sorts:
% 5.96/2.17  
% 5.96/2.17  
% 5.96/2.17  %Background operators:
% 5.96/2.17  
% 5.96/2.17  
% 5.96/2.17  %Foreground operators:
% 5.96/2.17  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.96/2.17  tff(k4_tmap_1, type, k4_tmap_1: ($i * $i) > $i).
% 5.96/2.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.96/2.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.96/2.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.96/2.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.96/2.17  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.96/2.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.96/2.17  tff('#skF_5', type, '#skF_5': $i).
% 5.96/2.17  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.96/2.17  tff('#skF_3', type, '#skF_3': $i).
% 5.96/2.17  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.96/2.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.96/2.17  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.96/2.17  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.96/2.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.96/2.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.96/2.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.96/2.17  tff('#skF_4', type, '#skF_4': $i).
% 5.96/2.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.96/2.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.96/2.17  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.96/2.17  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.96/2.17  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 5.96/2.17  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.96/2.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.96/2.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.96/2.17  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 5.96/2.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.96/2.17  
% 5.96/2.20  tff(f_198, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, u1_struct_0(B)) => (D = k1_funct_1(C, D))))) => r2_funct_2(u1_struct_0(B), u1_struct_0(A), k4_tmap_1(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_tmap_1)).
% 5.96/2.20  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.96/2.20  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.96/2.20  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.96/2.20  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.96/2.20  tff(f_87, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_2)).
% 5.96/2.20  tff(f_148, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_funct_1(k4_tmap_1(A, B)) & v1_funct_2(k4_tmap_1(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(k4_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_tmap_1)).
% 5.96/2.20  tff(f_45, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.96/2.20  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.96/2.20  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.96/2.20  tff(f_105, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, B) <=> (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_grfunc_1)).
% 5.96/2.20  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 5.96/2.20  tff(f_133, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 5.96/2.20  tff(f_168, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, u1_struct_0(B)) => (k1_funct_1(k4_tmap_1(A, B), C) = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_tmap_1)).
% 5.96/2.20  tff(f_117, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.96/2.20  tff(c_72, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_198])).
% 5.96/2.20  tff(c_44, plain, (![A_38]: (l1_struct_0(A_38) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.96/2.20  tff(c_76, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_198])).
% 5.96/2.20  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.96/2.20  tff(c_66, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_198])).
% 5.96/2.20  tff(c_64, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_198])).
% 5.96/2.20  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_198])).
% 5.96/2.20  tff(c_99, plain, (![A_81, B_82, C_83]: (k1_relset_1(A_81, B_82, C_83)=k1_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.96/2.20  tff(c_103, plain, (k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_99])).
% 5.96/2.20  tff(c_122, plain, (![B_97, A_98, C_99]: (k1_xboole_0=B_97 | k1_relset_1(A_98, B_97, C_99)=A_98 | ~v1_funct_2(C_99, A_98, B_97) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_98, B_97))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.96/2.20  tff(c_125, plain, (u1_struct_0('#skF_3')=k1_xboole_0 | k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5')=u1_struct_0('#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_62, c_122])).
% 5.96/2.20  tff(c_128, plain, (u1_struct_0('#skF_3')=k1_xboole_0 | u1_struct_0('#skF_4')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_103, c_125])).
% 5.96/2.20  tff(c_129, plain, (u1_struct_0('#skF_4')=k1_relat_1('#skF_5')), inference(splitLeft, [status(thm)], [c_128])).
% 5.96/2.20  tff(c_134, plain, (v1_funct_2('#skF_5', k1_relat_1('#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_64])).
% 5.96/2.20  tff(c_133, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_62])).
% 5.96/2.20  tff(c_32, plain, (![D_24, A_16, B_17, C_18]: (k1_funct_1(D_24, '#skF_1'(A_16, B_17, C_18, D_24))!=k1_funct_1(C_18, '#skF_1'(A_16, B_17, C_18, D_24)) | r2_funct_2(A_16, B_17, C_18, D_24) | ~m1_subset_1(D_24, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))) | ~v1_funct_2(D_24, A_16, B_17) | ~v1_funct_1(D_24) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))) | ~v1_funct_2(C_18, A_16, B_17) | ~v1_funct_1(C_18))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.96/2.20  tff(c_611, plain, (![A_172, B_173, C_174]: (r2_funct_2(A_172, B_173, C_174, C_174) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))) | ~v1_funct_2(C_174, A_172, B_173) | ~v1_funct_1(C_174) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))) | ~v1_funct_2(C_174, A_172, B_173) | ~v1_funct_1(C_174))), inference(reflexivity, [status(thm), theory('equality')], [c_32])).
% 5.96/2.20  tff(c_617, plain, (r2_funct_2(k1_relat_1('#skF_5'), u1_struct_0('#skF_3'), '#skF_5', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_133, c_611])).
% 5.96/2.20  tff(c_622, plain, (r2_funct_2(k1_relat_1('#skF_5'), u1_struct_0('#skF_3'), '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_134, c_133, c_617])).
% 5.96/2.20  tff(c_74, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_198])).
% 5.96/2.20  tff(c_68, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_198])).
% 5.96/2.20  tff(c_54, plain, (![A_47, B_48]: (v1_funct_1(k4_tmap_1(A_47, B_48)) | ~m1_pre_topc(B_48, A_47) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.96/2.20  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.96/2.20  tff(c_201, plain, (![A_109, B_110]: (m1_subset_1(k4_tmap_1(A_109, B_110), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_110), u1_struct_0(A_109)))) | ~m1_pre_topc(B_110, A_109) | ~l1_pre_topc(A_109) | ~v2_pre_topc(A_109) | v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.96/2.20  tff(c_12, plain, (![B_7, A_5]: (v1_relat_1(B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_5)) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.96/2.20  tff(c_213, plain, (![A_109, B_110]: (v1_relat_1(k4_tmap_1(A_109, B_110)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(B_110), u1_struct_0(A_109))) | ~m1_pre_topc(B_110, A_109) | ~l1_pre_topc(A_109) | ~v2_pre_topc(A_109) | v2_struct_0(A_109))), inference(resolution, [status(thm)], [c_201, c_12])).
% 5.96/2.20  tff(c_225, plain, (![A_109, B_110]: (v1_relat_1(k4_tmap_1(A_109, B_110)) | ~m1_pre_topc(B_110, A_109) | ~l1_pre_topc(A_109) | ~v2_pre_topc(A_109) | v2_struct_0(A_109))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_213])).
% 5.96/2.20  tff(c_90, plain, (![B_77, A_78]: (v1_relat_1(B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(A_78)) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.96/2.20  tff(c_93, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_62, c_90])).
% 5.96/2.20  tff(c_96, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_93])).
% 5.96/2.20  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.96/2.20  tff(c_52, plain, (![A_47, B_48]: (v1_funct_2(k4_tmap_1(A_47, B_48), u1_struct_0(B_48), u1_struct_0(A_47)) | ~m1_pre_topc(B_48, A_47) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.96/2.20  tff(c_28, plain, (![B_14, A_13, C_15]: (k1_xboole_0=B_14 | k1_relset_1(A_13, B_14, C_15)=A_13 | ~v1_funct_2(C_15, A_13, B_14) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.96/2.20  tff(c_375, plain, (![A_141, B_142]: (u1_struct_0(A_141)=k1_xboole_0 | k1_relset_1(u1_struct_0(B_142), u1_struct_0(A_141), k4_tmap_1(A_141, B_142))=u1_struct_0(B_142) | ~v1_funct_2(k4_tmap_1(A_141, B_142), u1_struct_0(B_142), u1_struct_0(A_141)) | ~m1_pre_topc(B_142, A_141) | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141) | v2_struct_0(A_141))), inference(resolution, [status(thm)], [c_201, c_28])).
% 5.96/2.20  tff(c_390, plain, (![A_143, B_144]: (u1_struct_0(A_143)=k1_xboole_0 | k1_relset_1(u1_struct_0(B_144), u1_struct_0(A_143), k4_tmap_1(A_143, B_144))=u1_struct_0(B_144) | ~m1_pre_topc(B_144, A_143) | ~l1_pre_topc(A_143) | ~v2_pre_topc(A_143) | v2_struct_0(A_143))), inference(resolution, [status(thm)], [c_52, c_375])).
% 5.96/2.20  tff(c_16, plain, (![A_10, B_11, C_12]: (k1_relset_1(A_10, B_11, C_12)=k1_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.96/2.20  tff(c_222, plain, (![B_110, A_109]: (k1_relset_1(u1_struct_0(B_110), u1_struct_0(A_109), k4_tmap_1(A_109, B_110))=k1_relat_1(k4_tmap_1(A_109, B_110)) | ~m1_pre_topc(B_110, A_109) | ~l1_pre_topc(A_109) | ~v2_pre_topc(A_109) | v2_struct_0(A_109))), inference(resolution, [status(thm)], [c_201, c_16])).
% 5.96/2.20  tff(c_435, plain, (![A_146, B_147]: (k1_relat_1(k4_tmap_1(A_146, B_147))=u1_struct_0(B_147) | ~m1_pre_topc(B_147, A_146) | ~l1_pre_topc(A_146) | ~v2_pre_topc(A_146) | v2_struct_0(A_146) | u1_struct_0(A_146)=k1_xboole_0 | ~m1_pre_topc(B_147, A_146) | ~l1_pre_topc(A_146) | ~v2_pre_topc(A_146) | v2_struct_0(A_146))), inference(superposition, [status(thm), theory('equality')], [c_390, c_222])).
% 5.96/2.20  tff(c_42, plain, (![A_28, B_34]: (r1_tarski(k1_relat_1(A_28), k1_relat_1(B_34)) | ~r1_tarski(A_28, B_34) | ~v1_funct_1(B_34) | ~v1_relat_1(B_34) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.96/2.20  tff(c_679, plain, (![A_188, B_189, A_190]: (r1_tarski(k1_relat_1(A_188), u1_struct_0(B_189)) | ~r1_tarski(A_188, k4_tmap_1(A_190, B_189)) | ~v1_funct_1(k4_tmap_1(A_190, B_189)) | ~v1_relat_1(k4_tmap_1(A_190, B_189)) | ~v1_funct_1(A_188) | ~v1_relat_1(A_188) | ~m1_pre_topc(B_189, A_190) | ~l1_pre_topc(A_190) | ~v2_pre_topc(A_190) | v2_struct_0(A_190) | u1_struct_0(A_190)=k1_xboole_0 | ~m1_pre_topc(B_189, A_190) | ~l1_pre_topc(A_190) | ~v2_pre_topc(A_190) | v2_struct_0(A_190))), inference(superposition, [status(thm), theory('equality')], [c_435, c_42])).
% 5.96/2.20  tff(c_684, plain, (![A_191, B_192]: (r1_tarski(k1_relat_1(k4_tmap_1(A_191, B_192)), u1_struct_0(B_192)) | ~v1_funct_1(k4_tmap_1(A_191, B_192)) | ~v1_relat_1(k4_tmap_1(A_191, B_192)) | u1_struct_0(A_191)=k1_xboole_0 | ~m1_pre_topc(B_192, A_191) | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191) | v2_struct_0(A_191))), inference(resolution, [status(thm)], [c_8, c_679])).
% 5.96/2.20  tff(c_697, plain, (![A_191]: (r1_tarski(k1_relat_1(k4_tmap_1(A_191, '#skF_4')), k1_relat_1('#skF_5')) | ~v1_funct_1(k4_tmap_1(A_191, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_191, '#skF_4')) | u1_struct_0(A_191)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_191) | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191) | v2_struct_0(A_191))), inference(superposition, [status(thm), theory('equality')], [c_129, c_684])).
% 5.96/2.20  tff(c_38, plain, (![A_28, B_34]: (r2_hidden('#skF_2'(A_28, B_34), k1_relat_1(A_28)) | r1_tarski(A_28, B_34) | ~r1_tarski(k1_relat_1(A_28), k1_relat_1(B_34)) | ~v1_funct_1(B_34) | ~v1_relat_1(B_34) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.96/2.20  tff(c_1248, plain, (![A_297, B_298, B_299]: (r2_hidden('#skF_2'(k4_tmap_1(A_297, B_298), B_299), u1_struct_0(B_298)) | r1_tarski(k4_tmap_1(A_297, B_298), B_299) | ~r1_tarski(k1_relat_1(k4_tmap_1(A_297, B_298)), k1_relat_1(B_299)) | ~v1_funct_1(B_299) | ~v1_relat_1(B_299) | ~v1_funct_1(k4_tmap_1(A_297, B_298)) | ~v1_relat_1(k4_tmap_1(A_297, B_298)) | ~m1_pre_topc(B_298, A_297) | ~l1_pre_topc(A_297) | ~v2_pre_topc(A_297) | v2_struct_0(A_297) | u1_struct_0(A_297)=k1_xboole_0 | ~m1_pre_topc(B_298, A_297) | ~l1_pre_topc(A_297) | ~v2_pre_topc(A_297) | v2_struct_0(A_297))), inference(superposition, [status(thm), theory('equality')], [c_435, c_38])).
% 5.96/2.20  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, B_4) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.96/2.20  tff(c_1262, plain, (![A_300, B_301, B_302]: (m1_subset_1('#skF_2'(k4_tmap_1(A_300, B_301), B_302), u1_struct_0(B_301)) | r1_tarski(k4_tmap_1(A_300, B_301), B_302) | ~r1_tarski(k1_relat_1(k4_tmap_1(A_300, B_301)), k1_relat_1(B_302)) | ~v1_funct_1(B_302) | ~v1_relat_1(B_302) | ~v1_funct_1(k4_tmap_1(A_300, B_301)) | ~v1_relat_1(k4_tmap_1(A_300, B_301)) | u1_struct_0(A_300)=k1_xboole_0 | ~m1_pre_topc(B_301, A_300) | ~l1_pre_topc(A_300) | ~v2_pre_topc(A_300) | v2_struct_0(A_300))), inference(resolution, [status(thm)], [c_1248, c_10])).
% 5.96/2.20  tff(c_1264, plain, (![A_191]: (m1_subset_1('#skF_2'(k4_tmap_1(A_191, '#skF_4'), '#skF_5'), u1_struct_0('#skF_4')) | r1_tarski(k4_tmap_1(A_191, '#skF_4'), '#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1(k4_tmap_1(A_191, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_191, '#skF_4')) | u1_struct_0(A_191)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_191) | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191) | v2_struct_0(A_191))), inference(resolution, [status(thm)], [c_697, c_1262])).
% 5.96/2.20  tff(c_1281, plain, (![A_191]: (m1_subset_1('#skF_2'(k4_tmap_1(A_191, '#skF_4'), '#skF_5'), k1_relat_1('#skF_5')) | r1_tarski(k4_tmap_1(A_191, '#skF_4'), '#skF_5') | ~v1_funct_1(k4_tmap_1(A_191, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_191, '#skF_4')) | u1_struct_0(A_191)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_191) | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191) | v2_struct_0(A_191))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_66, c_129, c_1264])).
% 5.96/2.20  tff(c_70, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_198])).
% 5.96/2.20  tff(c_148, plain, (![C_100, A_101, B_102]: (m1_subset_1(C_100, u1_struct_0(A_101)) | ~m1_subset_1(C_100, u1_struct_0(B_102)) | ~m1_pre_topc(B_102, A_101) | v2_struct_0(B_102) | ~l1_pre_topc(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.96/2.20  tff(c_150, plain, (![C_100, A_101]: (m1_subset_1(C_100, u1_struct_0(A_101)) | ~m1_subset_1(C_100, k1_relat_1('#skF_5')) | ~m1_pre_topc('#skF_4', A_101) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_101) | v2_struct_0(A_101))), inference(superposition, [status(thm), theory('equality')], [c_129, c_148])).
% 5.96/2.20  tff(c_151, plain, (![C_100, A_101]: (m1_subset_1(C_100, u1_struct_0(A_101)) | ~m1_subset_1(C_100, k1_relat_1('#skF_5')) | ~m1_pre_topc('#skF_4', A_101) | ~l1_pre_topc(A_101) | v2_struct_0(A_101))), inference(negUnitSimplification, [status(thm)], [c_70, c_150])).
% 5.96/2.20  tff(c_405, plain, (![A_143]: (u1_struct_0(A_143)=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_5'), u1_struct_0(A_143), k4_tmap_1(A_143, '#skF_4'))=u1_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', A_143) | ~l1_pre_topc(A_143) | ~v2_pre_topc(A_143) | v2_struct_0(A_143))), inference(superposition, [status(thm), theory('equality')], [c_129, c_390])).
% 5.96/2.20  tff(c_414, plain, (![A_145]: (u1_struct_0(A_145)=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_5'), u1_struct_0(A_145), k4_tmap_1(A_145, '#skF_4'))=k1_relat_1('#skF_5') | ~m1_pre_topc('#skF_4', A_145) | ~l1_pre_topc(A_145) | ~v2_pre_topc(A_145) | v2_struct_0(A_145))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_405])).
% 5.96/2.20  tff(c_282, plain, (![B_124, A_125]: (k1_relset_1(u1_struct_0(B_124), u1_struct_0(A_125), k4_tmap_1(A_125, B_124))=k1_relat_1(k4_tmap_1(A_125, B_124)) | ~m1_pre_topc(B_124, A_125) | ~l1_pre_topc(A_125) | ~v2_pre_topc(A_125) | v2_struct_0(A_125))), inference(resolution, [status(thm)], [c_201, c_16])).
% 5.96/2.20  tff(c_291, plain, (![A_125]: (k1_relset_1(k1_relat_1('#skF_5'), u1_struct_0(A_125), k4_tmap_1(A_125, '#skF_4'))=k1_relat_1(k4_tmap_1(A_125, '#skF_4')) | ~m1_pre_topc('#skF_4', A_125) | ~l1_pre_topc(A_125) | ~v2_pre_topc(A_125) | v2_struct_0(A_125))), inference(superposition, [status(thm), theory('equality')], [c_129, c_282])).
% 5.96/2.20  tff(c_480, plain, (![A_152]: (k1_relat_1(k4_tmap_1(A_152, '#skF_4'))=k1_relat_1('#skF_5') | ~m1_pre_topc('#skF_4', A_152) | ~l1_pre_topc(A_152) | ~v2_pre_topc(A_152) | v2_struct_0(A_152) | u1_struct_0(A_152)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_152) | ~l1_pre_topc(A_152) | ~v2_pre_topc(A_152) | v2_struct_0(A_152))), inference(superposition, [status(thm), theory('equality')], [c_414, c_291])).
% 5.96/2.20  tff(c_1301, plain, (![A_307, B_308]: (r2_hidden('#skF_2'(k4_tmap_1(A_307, '#skF_4'), B_308), k1_relat_1('#skF_5')) | r1_tarski(k4_tmap_1(A_307, '#skF_4'), B_308) | ~r1_tarski(k1_relat_1(k4_tmap_1(A_307, '#skF_4')), k1_relat_1(B_308)) | ~v1_funct_1(B_308) | ~v1_relat_1(B_308) | ~v1_funct_1(k4_tmap_1(A_307, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_307, '#skF_4')) | ~m1_pre_topc('#skF_4', A_307) | ~l1_pre_topc(A_307) | ~v2_pre_topc(A_307) | v2_struct_0(A_307) | u1_struct_0(A_307)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_307) | ~l1_pre_topc(A_307) | ~v2_pre_topc(A_307) | v2_struct_0(A_307))), inference(superposition, [status(thm), theory('equality')], [c_480, c_38])).
% 5.96/2.20  tff(c_60, plain, (![D_67]: (k1_funct_1('#skF_5', D_67)=D_67 | ~r2_hidden(D_67, u1_struct_0('#skF_4')) | ~m1_subset_1(D_67, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_198])).
% 5.96/2.20  tff(c_131, plain, (![D_67]: (k1_funct_1('#skF_5', D_67)=D_67 | ~r2_hidden(D_67, k1_relat_1('#skF_5')) | ~m1_subset_1(D_67, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_60])).
% 5.96/2.20  tff(c_1353, plain, (![A_311, B_312]: (k1_funct_1('#skF_5', '#skF_2'(k4_tmap_1(A_311, '#skF_4'), B_312))='#skF_2'(k4_tmap_1(A_311, '#skF_4'), B_312) | ~m1_subset_1('#skF_2'(k4_tmap_1(A_311, '#skF_4'), B_312), u1_struct_0('#skF_3')) | r1_tarski(k4_tmap_1(A_311, '#skF_4'), B_312) | ~r1_tarski(k1_relat_1(k4_tmap_1(A_311, '#skF_4')), k1_relat_1(B_312)) | ~v1_funct_1(B_312) | ~v1_relat_1(B_312) | ~v1_funct_1(k4_tmap_1(A_311, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_311, '#skF_4')) | u1_struct_0(A_311)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_311) | ~l1_pre_topc(A_311) | ~v2_pre_topc(A_311) | v2_struct_0(A_311))), inference(resolution, [status(thm)], [c_1301, c_131])).
% 5.96/2.20  tff(c_1356, plain, (![A_191]: (k1_funct_1('#skF_5', '#skF_2'(k4_tmap_1(A_191, '#skF_4'), '#skF_5'))='#skF_2'(k4_tmap_1(A_191, '#skF_4'), '#skF_5') | ~m1_subset_1('#skF_2'(k4_tmap_1(A_191, '#skF_4'), '#skF_5'), u1_struct_0('#skF_3')) | r1_tarski(k4_tmap_1(A_191, '#skF_4'), '#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1(k4_tmap_1(A_191, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_191, '#skF_4')) | u1_struct_0(A_191)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_191) | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191) | v2_struct_0(A_191))), inference(resolution, [status(thm)], [c_697, c_1353])).
% 5.96/2.20  tff(c_1385, plain, (![A_313]: (k1_funct_1('#skF_5', '#skF_2'(k4_tmap_1(A_313, '#skF_4'), '#skF_5'))='#skF_2'(k4_tmap_1(A_313, '#skF_4'), '#skF_5') | ~m1_subset_1('#skF_2'(k4_tmap_1(A_313, '#skF_4'), '#skF_5'), u1_struct_0('#skF_3')) | r1_tarski(k4_tmap_1(A_313, '#skF_4'), '#skF_5') | ~v1_funct_1(k4_tmap_1(A_313, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_313, '#skF_4')) | u1_struct_0(A_313)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_313) | ~l1_pre_topc(A_313) | ~v2_pre_topc(A_313) | v2_struct_0(A_313))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_66, c_1356])).
% 5.96/2.20  tff(c_1388, plain, (![A_313]: (k1_funct_1('#skF_5', '#skF_2'(k4_tmap_1(A_313, '#skF_4'), '#skF_5'))='#skF_2'(k4_tmap_1(A_313, '#skF_4'), '#skF_5') | r1_tarski(k4_tmap_1(A_313, '#skF_4'), '#skF_5') | ~v1_funct_1(k4_tmap_1(A_313, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_313, '#skF_4')) | u1_struct_0(A_313)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_313) | ~l1_pre_topc(A_313) | ~v2_pre_topc(A_313) | v2_struct_0(A_313) | ~m1_subset_1('#skF_2'(k4_tmap_1(A_313, '#skF_4'), '#skF_5'), k1_relat_1('#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_151, c_1385])).
% 5.96/2.20  tff(c_1391, plain, (![A_313]: (k1_funct_1('#skF_5', '#skF_2'(k4_tmap_1(A_313, '#skF_4'), '#skF_5'))='#skF_2'(k4_tmap_1(A_313, '#skF_4'), '#skF_5') | r1_tarski(k4_tmap_1(A_313, '#skF_4'), '#skF_5') | ~v1_funct_1(k4_tmap_1(A_313, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_313, '#skF_4')) | u1_struct_0(A_313)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_313) | ~l1_pre_topc(A_313) | ~v2_pre_topc(A_313) | v2_struct_0(A_313) | ~m1_subset_1('#skF_2'(k4_tmap_1(A_313, '#skF_4'), '#skF_5'), k1_relat_1('#skF_5')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_1388])).
% 5.96/2.20  tff(c_1393, plain, (![A_314]: (k1_funct_1('#skF_5', '#skF_2'(k4_tmap_1(A_314, '#skF_4'), '#skF_5'))='#skF_2'(k4_tmap_1(A_314, '#skF_4'), '#skF_5') | r1_tarski(k4_tmap_1(A_314, '#skF_4'), '#skF_5') | ~v1_funct_1(k4_tmap_1(A_314, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_314, '#skF_4')) | u1_struct_0(A_314)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_314) | ~l1_pre_topc(A_314) | ~v2_pre_topc(A_314) | v2_struct_0(A_314) | ~m1_subset_1('#skF_2'(k4_tmap_1(A_314, '#skF_4'), '#skF_5'), k1_relat_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_76, c_1391])).
% 5.96/2.20  tff(c_1397, plain, (![A_191]: (k1_funct_1('#skF_5', '#skF_2'(k4_tmap_1(A_191, '#skF_4'), '#skF_5'))='#skF_2'(k4_tmap_1(A_191, '#skF_4'), '#skF_5') | r1_tarski(k4_tmap_1(A_191, '#skF_4'), '#skF_5') | ~v1_funct_1(k4_tmap_1(A_191, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_191, '#skF_4')) | u1_struct_0(A_191)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_191) | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191) | v2_struct_0(A_191))), inference(resolution, [status(thm)], [c_1281, c_1393])).
% 5.96/2.20  tff(c_335, plain, (![A_131, B_132, C_133]: (k1_funct_1(k4_tmap_1(A_131, B_132), C_133)=C_133 | ~r2_hidden(C_133, u1_struct_0(B_132)) | ~m1_subset_1(C_133, u1_struct_0(A_131)) | ~m1_pre_topc(B_132, A_131) | v2_struct_0(B_132) | ~l1_pre_topc(A_131) | ~v2_pre_topc(A_131) | v2_struct_0(A_131))), inference(cnfTransformation, [status(thm)], [f_168])).
% 5.96/2.20  tff(c_337, plain, (![A_131, C_133]: (k1_funct_1(k4_tmap_1(A_131, '#skF_4'), C_133)=C_133 | ~r2_hidden(C_133, k1_relat_1('#skF_5')) | ~m1_subset_1(C_133, u1_struct_0(A_131)) | ~m1_pre_topc('#skF_4', A_131) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_131) | ~v2_pre_topc(A_131) | v2_struct_0(A_131))), inference(superposition, [status(thm), theory('equality')], [c_129, c_335])).
% 5.96/2.20  tff(c_338, plain, (![A_131, C_133]: (k1_funct_1(k4_tmap_1(A_131, '#skF_4'), C_133)=C_133 | ~r2_hidden(C_133, k1_relat_1('#skF_5')) | ~m1_subset_1(C_133, u1_struct_0(A_131)) | ~m1_pre_topc('#skF_4', A_131) | ~l1_pre_topc(A_131) | ~v2_pre_topc(A_131) | v2_struct_0(A_131))), inference(negUnitSimplification, [status(thm)], [c_70, c_337])).
% 5.96/2.20  tff(c_1439, plain, (![A_324, A_325, B_326]: (k1_funct_1(k4_tmap_1(A_324, '#skF_4'), '#skF_2'(k4_tmap_1(A_325, '#skF_4'), B_326))='#skF_2'(k4_tmap_1(A_325, '#skF_4'), B_326) | ~m1_subset_1('#skF_2'(k4_tmap_1(A_325, '#skF_4'), B_326), u1_struct_0(A_324)) | ~m1_pre_topc('#skF_4', A_324) | ~l1_pre_topc(A_324) | ~v2_pre_topc(A_324) | v2_struct_0(A_324) | r1_tarski(k4_tmap_1(A_325, '#skF_4'), B_326) | ~r1_tarski(k1_relat_1(k4_tmap_1(A_325, '#skF_4')), k1_relat_1(B_326)) | ~v1_funct_1(B_326) | ~v1_relat_1(B_326) | ~v1_funct_1(k4_tmap_1(A_325, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_325, '#skF_4')) | u1_struct_0(A_325)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_325) | ~l1_pre_topc(A_325) | ~v2_pre_topc(A_325) | v2_struct_0(A_325))), inference(resolution, [status(thm)], [c_1301, c_338])).
% 5.96/2.20  tff(c_1475, plain, (![A_337, A_338, B_339]: (k1_funct_1(k4_tmap_1(A_337, '#skF_4'), '#skF_2'(k4_tmap_1(A_338, '#skF_4'), B_339))='#skF_2'(k4_tmap_1(A_338, '#skF_4'), B_339) | ~v2_pre_topc(A_337) | r1_tarski(k4_tmap_1(A_338, '#skF_4'), B_339) | ~r1_tarski(k1_relat_1(k4_tmap_1(A_338, '#skF_4')), k1_relat_1(B_339)) | ~v1_funct_1(B_339) | ~v1_relat_1(B_339) | ~v1_funct_1(k4_tmap_1(A_338, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_338, '#skF_4')) | u1_struct_0(A_338)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_338) | ~l1_pre_topc(A_338) | ~v2_pre_topc(A_338) | v2_struct_0(A_338) | ~m1_subset_1('#skF_2'(k4_tmap_1(A_338, '#skF_4'), B_339), k1_relat_1('#skF_5')) | ~m1_pre_topc('#skF_4', A_337) | ~l1_pre_topc(A_337) | v2_struct_0(A_337))), inference(resolution, [status(thm)], [c_151, c_1439])).
% 5.96/2.20  tff(c_1477, plain, (![A_337, A_191]: (k1_funct_1(k4_tmap_1(A_337, '#skF_4'), '#skF_2'(k4_tmap_1(A_191, '#skF_4'), '#skF_5'))='#skF_2'(k4_tmap_1(A_191, '#skF_4'), '#skF_5') | ~v2_pre_topc(A_337) | r1_tarski(k4_tmap_1(A_191, '#skF_4'), '#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~m1_subset_1('#skF_2'(k4_tmap_1(A_191, '#skF_4'), '#skF_5'), k1_relat_1('#skF_5')) | ~m1_pre_topc('#skF_4', A_337) | ~l1_pre_topc(A_337) | v2_struct_0(A_337) | ~v1_funct_1(k4_tmap_1(A_191, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_191, '#skF_4')) | u1_struct_0(A_191)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_191) | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191) | v2_struct_0(A_191))), inference(resolution, [status(thm)], [c_697, c_1475])).
% 5.96/2.20  tff(c_1500, plain, (![A_340, A_341]: (k1_funct_1(k4_tmap_1(A_340, '#skF_4'), '#skF_2'(k4_tmap_1(A_341, '#skF_4'), '#skF_5'))='#skF_2'(k4_tmap_1(A_341, '#skF_4'), '#skF_5') | ~v2_pre_topc(A_340) | r1_tarski(k4_tmap_1(A_341, '#skF_4'), '#skF_5') | ~m1_subset_1('#skF_2'(k4_tmap_1(A_341, '#skF_4'), '#skF_5'), k1_relat_1('#skF_5')) | ~m1_pre_topc('#skF_4', A_340) | ~l1_pre_topc(A_340) | v2_struct_0(A_340) | ~v1_funct_1(k4_tmap_1(A_341, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_341, '#skF_4')) | u1_struct_0(A_341)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_341) | ~l1_pre_topc(A_341) | ~v2_pre_topc(A_341) | v2_struct_0(A_341))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_66, c_1477])).
% 5.96/2.20  tff(c_1504, plain, (![A_342, A_343]: (k1_funct_1(k4_tmap_1(A_342, '#skF_4'), '#skF_2'(k4_tmap_1(A_343, '#skF_4'), '#skF_5'))='#skF_2'(k4_tmap_1(A_343, '#skF_4'), '#skF_5') | ~v2_pre_topc(A_342) | ~m1_pre_topc('#skF_4', A_342) | ~l1_pre_topc(A_342) | v2_struct_0(A_342) | r1_tarski(k4_tmap_1(A_343, '#skF_4'), '#skF_5') | ~v1_funct_1(k4_tmap_1(A_343, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_343, '#skF_4')) | u1_struct_0(A_343)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_343) | ~l1_pre_topc(A_343) | ~v2_pre_topc(A_343) | v2_struct_0(A_343))), inference(resolution, [status(thm)], [c_1281, c_1500])).
% 5.96/2.20  tff(c_36, plain, (![B_34, A_28]: (k1_funct_1(B_34, '#skF_2'(A_28, B_34))!=k1_funct_1(A_28, '#skF_2'(A_28, B_34)) | r1_tarski(A_28, B_34) | ~r1_tarski(k1_relat_1(A_28), k1_relat_1(B_34)) | ~v1_funct_1(B_34) | ~v1_relat_1(B_34) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.96/2.20  tff(c_1519, plain, (![A_343]: (k1_funct_1('#skF_5', '#skF_2'(k4_tmap_1(A_343, '#skF_4'), '#skF_5'))!='#skF_2'(k4_tmap_1(A_343, '#skF_4'), '#skF_5') | r1_tarski(k4_tmap_1(A_343, '#skF_4'), '#skF_5') | ~r1_tarski(k1_relat_1(k4_tmap_1(A_343, '#skF_4')), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1(k4_tmap_1(A_343, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_343, '#skF_4')) | ~v2_pre_topc(A_343) | ~m1_pre_topc('#skF_4', A_343) | ~l1_pre_topc(A_343) | v2_struct_0(A_343) | r1_tarski(k4_tmap_1(A_343, '#skF_4'), '#skF_5') | ~v1_funct_1(k4_tmap_1(A_343, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_343, '#skF_4')) | u1_struct_0(A_343)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_343) | ~l1_pre_topc(A_343) | ~v2_pre_topc(A_343) | v2_struct_0(A_343))), inference(superposition, [status(thm), theory('equality')], [c_1504, c_36])).
% 5.96/2.20  tff(c_1534, plain, (![A_344]: (k1_funct_1('#skF_5', '#skF_2'(k4_tmap_1(A_344, '#skF_4'), '#skF_5'))!='#skF_2'(k4_tmap_1(A_344, '#skF_4'), '#skF_5') | ~r1_tarski(k1_relat_1(k4_tmap_1(A_344, '#skF_4')), k1_relat_1('#skF_5')) | r1_tarski(k4_tmap_1(A_344, '#skF_4'), '#skF_5') | ~v1_funct_1(k4_tmap_1(A_344, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_344, '#skF_4')) | u1_struct_0(A_344)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_344) | ~l1_pre_topc(A_344) | ~v2_pre_topc(A_344) | v2_struct_0(A_344))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_66, c_1519])).
% 5.96/2.20  tff(c_1556, plain, (![A_345]: (k1_funct_1('#skF_5', '#skF_2'(k4_tmap_1(A_345, '#skF_4'), '#skF_5'))!='#skF_2'(k4_tmap_1(A_345, '#skF_4'), '#skF_5') | r1_tarski(k4_tmap_1(A_345, '#skF_4'), '#skF_5') | ~v1_funct_1(k4_tmap_1(A_345, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_345, '#skF_4')) | u1_struct_0(A_345)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_345) | ~l1_pre_topc(A_345) | ~v2_pre_topc(A_345) | v2_struct_0(A_345))), inference(resolution, [status(thm)], [c_697, c_1534])).
% 5.96/2.20  tff(c_1561, plain, (![A_346]: (r1_tarski(k4_tmap_1(A_346, '#skF_4'), '#skF_5') | ~v1_funct_1(k4_tmap_1(A_346, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_346, '#skF_4')) | u1_struct_0(A_346)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_346) | ~l1_pre_topc(A_346) | ~v2_pre_topc(A_346) | v2_struct_0(A_346))), inference(superposition, [status(thm), theory('equality')], [c_1397, c_1556])).
% 5.96/2.20  tff(c_788, plain, (![B_209, B_210, A_211]: (r1_tarski(u1_struct_0(B_209), k1_relat_1(B_210)) | ~r1_tarski(k4_tmap_1(A_211, B_209), B_210) | ~v1_funct_1(B_210) | ~v1_relat_1(B_210) | ~v1_funct_1(k4_tmap_1(A_211, B_209)) | ~v1_relat_1(k4_tmap_1(A_211, B_209)) | ~m1_pre_topc(B_209, A_211) | ~l1_pre_topc(A_211) | ~v2_pre_topc(A_211) | v2_struct_0(A_211) | u1_struct_0(A_211)=k1_xboole_0 | ~m1_pre_topc(B_209, A_211) | ~l1_pre_topc(A_211) | ~v2_pre_topc(A_211) | v2_struct_0(A_211))), inference(superposition, [status(thm), theory('equality')], [c_435, c_42])).
% 5.96/2.20  tff(c_794, plain, (![B_215, A_216]: (r1_tarski(u1_struct_0(B_215), k1_relat_1(k4_tmap_1(A_216, B_215))) | ~v1_funct_1(k4_tmap_1(A_216, B_215)) | ~v1_relat_1(k4_tmap_1(A_216, B_215)) | u1_struct_0(A_216)=k1_xboole_0 | ~m1_pre_topc(B_215, A_216) | ~l1_pre_topc(A_216) | ~v2_pre_topc(A_216) | v2_struct_0(A_216))), inference(resolution, [status(thm)], [c_8, c_788])).
% 5.96/2.20  tff(c_812, plain, (![A_217]: (r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(k4_tmap_1(A_217, '#skF_4'))) | ~v1_funct_1(k4_tmap_1(A_217, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_217, '#skF_4')) | u1_struct_0(A_217)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_217) | ~l1_pre_topc(A_217) | ~v2_pre_topc(A_217) | v2_struct_0(A_217))), inference(superposition, [status(thm), theory('equality')], [c_129, c_794])).
% 5.96/2.20  tff(c_311, plain, (![A_127, B_128]: (r2_hidden('#skF_2'(A_127, B_128), k1_relat_1(A_127)) | r1_tarski(A_127, B_128) | ~r1_tarski(k1_relat_1(A_127), k1_relat_1(B_128)) | ~v1_funct_1(B_128) | ~v1_relat_1(B_128) | ~v1_funct_1(A_127) | ~v1_relat_1(A_127))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.96/2.20  tff(c_325, plain, (![A_127, B_128]: (m1_subset_1('#skF_2'(A_127, B_128), k1_relat_1(A_127)) | r1_tarski(A_127, B_128) | ~r1_tarski(k1_relat_1(A_127), k1_relat_1(B_128)) | ~v1_funct_1(B_128) | ~v1_relat_1(B_128) | ~v1_funct_1(A_127) | ~v1_relat_1(A_127))), inference(resolution, [status(thm)], [c_311, c_10])).
% 5.96/2.20  tff(c_824, plain, (![A_217]: (m1_subset_1('#skF_2'('#skF_5', k4_tmap_1(A_217, '#skF_4')), k1_relat_1('#skF_5')) | r1_tarski('#skF_5', k4_tmap_1(A_217, '#skF_4')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1(k4_tmap_1(A_217, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_217, '#skF_4')) | u1_struct_0(A_217)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_217) | ~l1_pre_topc(A_217) | ~v2_pre_topc(A_217) | v2_struct_0(A_217))), inference(resolution, [status(thm)], [c_812, c_325])).
% 5.96/2.20  tff(c_849, plain, (![A_217]: (m1_subset_1('#skF_2'('#skF_5', k4_tmap_1(A_217, '#skF_4')), k1_relat_1('#skF_5')) | r1_tarski('#skF_5', k4_tmap_1(A_217, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_217, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_217, '#skF_4')) | u1_struct_0(A_217)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_217) | ~l1_pre_topc(A_217) | ~v2_pre_topc(A_217) | v2_struct_0(A_217))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_66, c_824])).
% 5.96/2.20  tff(c_317, plain, (![B_128]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', B_128))='#skF_2'('#skF_5', B_128) | ~m1_subset_1('#skF_2'('#skF_5', B_128), u1_struct_0('#skF_3')) | r1_tarski('#skF_5', B_128) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(B_128)) | ~v1_funct_1(B_128) | ~v1_relat_1(B_128) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_311, c_131])).
% 5.96/2.20  tff(c_324, plain, (![B_128]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', B_128))='#skF_2'('#skF_5', B_128) | ~m1_subset_1('#skF_2'('#skF_5', B_128), u1_struct_0('#skF_3')) | r1_tarski('#skF_5', B_128) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(B_128)) | ~v1_funct_1(B_128) | ~v1_relat_1(B_128))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_66, c_317])).
% 5.96/2.20  tff(c_489, plain, (![A_152]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', k4_tmap_1(A_152, '#skF_4')))='#skF_2'('#skF_5', k4_tmap_1(A_152, '#skF_4')) | ~m1_subset_1('#skF_2'('#skF_5', k4_tmap_1(A_152, '#skF_4')), u1_struct_0('#skF_3')) | r1_tarski('#skF_5', k4_tmap_1(A_152, '#skF_4')) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1('#skF_5')) | ~v1_funct_1(k4_tmap_1(A_152, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_152, '#skF_4')) | ~m1_pre_topc('#skF_4', A_152) | ~l1_pre_topc(A_152) | ~v2_pre_topc(A_152) | v2_struct_0(A_152) | u1_struct_0(A_152)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_152) | ~l1_pre_topc(A_152) | ~v2_pre_topc(A_152) | v2_struct_0(A_152))), inference(superposition, [status(thm), theory('equality')], [c_480, c_324])).
% 5.96/2.20  tff(c_885, plain, (![A_225]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', k4_tmap_1(A_225, '#skF_4')))='#skF_2'('#skF_5', k4_tmap_1(A_225, '#skF_4')) | ~m1_subset_1('#skF_2'('#skF_5', k4_tmap_1(A_225, '#skF_4')), u1_struct_0('#skF_3')) | r1_tarski('#skF_5', k4_tmap_1(A_225, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_225, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_225, '#skF_4')) | u1_struct_0(A_225)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_225) | ~l1_pre_topc(A_225) | ~v2_pre_topc(A_225) | v2_struct_0(A_225))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_489])).
% 5.96/2.20  tff(c_888, plain, (![A_225]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', k4_tmap_1(A_225, '#skF_4')))='#skF_2'('#skF_5', k4_tmap_1(A_225, '#skF_4')) | r1_tarski('#skF_5', k4_tmap_1(A_225, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_225, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_225, '#skF_4')) | u1_struct_0(A_225)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_225) | ~l1_pre_topc(A_225) | ~v2_pre_topc(A_225) | v2_struct_0(A_225) | ~m1_subset_1('#skF_2'('#skF_5', k4_tmap_1(A_225, '#skF_4')), k1_relat_1('#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_151, c_885])).
% 5.96/2.20  tff(c_891, plain, (![A_225]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', k4_tmap_1(A_225, '#skF_4')))='#skF_2'('#skF_5', k4_tmap_1(A_225, '#skF_4')) | r1_tarski('#skF_5', k4_tmap_1(A_225, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_225, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_225, '#skF_4')) | u1_struct_0(A_225)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_225) | ~l1_pre_topc(A_225) | ~v2_pre_topc(A_225) | v2_struct_0(A_225) | ~m1_subset_1('#skF_2'('#skF_5', k4_tmap_1(A_225, '#skF_4')), k1_relat_1('#skF_5')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_888])).
% 5.96/2.20  tff(c_893, plain, (![A_226]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', k4_tmap_1(A_226, '#skF_4')))='#skF_2'('#skF_5', k4_tmap_1(A_226, '#skF_4')) | r1_tarski('#skF_5', k4_tmap_1(A_226, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_226, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_226, '#skF_4')) | u1_struct_0(A_226)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_226) | ~l1_pre_topc(A_226) | ~v2_pre_topc(A_226) | v2_struct_0(A_226) | ~m1_subset_1('#skF_2'('#skF_5', k4_tmap_1(A_226, '#skF_4')), k1_relat_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_76, c_891])).
% 5.96/2.20  tff(c_897, plain, (![A_217]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', k4_tmap_1(A_217, '#skF_4')))='#skF_2'('#skF_5', k4_tmap_1(A_217, '#skF_4')) | r1_tarski('#skF_5', k4_tmap_1(A_217, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_217, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_217, '#skF_4')) | u1_struct_0(A_217)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_217) | ~l1_pre_topc(A_217) | ~v2_pre_topc(A_217) | v2_struct_0(A_217))), inference(resolution, [status(thm)], [c_849, c_893])).
% 5.96/2.20  tff(c_807, plain, (![A_216]: (r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(k4_tmap_1(A_216, '#skF_4'))) | ~v1_funct_1(k4_tmap_1(A_216, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_216, '#skF_4')) | u1_struct_0(A_216)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_216) | ~l1_pre_topc(A_216) | ~v2_pre_topc(A_216) | v2_struct_0(A_216))), inference(superposition, [status(thm), theory('equality')], [c_129, c_794])).
% 5.96/2.20  tff(c_857, plain, (![A_218]: (m1_subset_1('#skF_2'('#skF_5', k4_tmap_1(A_218, '#skF_4')), k1_relat_1('#skF_5')) | r1_tarski('#skF_5', k4_tmap_1(A_218, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_218, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_218, '#skF_4')) | u1_struct_0(A_218)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_218) | ~l1_pre_topc(A_218) | ~v2_pre_topc(A_218) | v2_struct_0(A_218))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_66, c_824])).
% 5.96/2.20  tff(c_396, plain, (![A_143, B_144]: (k1_relat_1(k4_tmap_1(A_143, B_144))=u1_struct_0(B_144) | ~m1_pre_topc(B_144, A_143) | ~l1_pre_topc(A_143) | ~v2_pre_topc(A_143) | v2_struct_0(A_143) | u1_struct_0(A_143)=k1_xboole_0 | ~m1_pre_topc(B_144, A_143) | ~l1_pre_topc(A_143) | ~v2_pre_topc(A_143) | v2_struct_0(A_143))), inference(superposition, [status(thm), theory('equality')], [c_390, c_222])).
% 5.96/2.20  tff(c_339, plain, (![A_134, C_135]: (k1_funct_1(k4_tmap_1(A_134, '#skF_4'), C_135)=C_135 | ~r2_hidden(C_135, k1_relat_1('#skF_5')) | ~m1_subset_1(C_135, u1_struct_0(A_134)) | ~m1_pre_topc('#skF_4', A_134) | ~l1_pre_topc(A_134) | ~v2_pre_topc(A_134) | v2_struct_0(A_134))), inference(negUnitSimplification, [status(thm)], [c_70, c_337])).
% 5.96/2.20  tff(c_342, plain, (![A_134, B_34]: (k1_funct_1(k4_tmap_1(A_134, '#skF_4'), '#skF_2'('#skF_5', B_34))='#skF_2'('#skF_5', B_34) | ~m1_subset_1('#skF_2'('#skF_5', B_34), u1_struct_0(A_134)) | ~m1_pre_topc('#skF_4', A_134) | ~l1_pre_topc(A_134) | ~v2_pre_topc(A_134) | v2_struct_0(A_134) | r1_tarski('#skF_5', B_34) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(B_34)) | ~v1_funct_1(B_34) | ~v1_relat_1(B_34) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_339])).
% 5.96/2.20  tff(c_367, plain, (![A_139, B_140]: (k1_funct_1(k4_tmap_1(A_139, '#skF_4'), '#skF_2'('#skF_5', B_140))='#skF_2'('#skF_5', B_140) | ~m1_subset_1('#skF_2'('#skF_5', B_140), u1_struct_0(A_139)) | ~m1_pre_topc('#skF_4', A_139) | ~l1_pre_topc(A_139) | ~v2_pre_topc(A_139) | v2_struct_0(A_139) | r1_tarski('#skF_5', B_140) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(B_140)) | ~v1_funct_1(B_140) | ~v1_relat_1(B_140))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_66, c_342])).
% 5.96/2.20  tff(c_524, plain, (![A_153, B_154]: (k1_funct_1(k4_tmap_1(A_153, '#skF_4'), '#skF_2'('#skF_5', B_154))='#skF_2'('#skF_5', B_154) | ~v2_pre_topc(A_153) | r1_tarski('#skF_5', B_154) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(B_154)) | ~v1_funct_1(B_154) | ~v1_relat_1(B_154) | ~m1_subset_1('#skF_2'('#skF_5', B_154), k1_relat_1('#skF_5')) | ~m1_pre_topc('#skF_4', A_153) | ~l1_pre_topc(A_153) | v2_struct_0(A_153))), inference(resolution, [status(thm)], [c_151, c_367])).
% 5.96/2.20  tff(c_528, plain, (![A_153, A_143, B_144]: (k1_funct_1(k4_tmap_1(A_153, '#skF_4'), '#skF_2'('#skF_5', k4_tmap_1(A_143, B_144)))='#skF_2'('#skF_5', k4_tmap_1(A_143, B_144)) | ~v2_pre_topc(A_153) | r1_tarski('#skF_5', k4_tmap_1(A_143, B_144)) | ~r1_tarski(k1_relat_1('#skF_5'), u1_struct_0(B_144)) | ~v1_funct_1(k4_tmap_1(A_143, B_144)) | ~v1_relat_1(k4_tmap_1(A_143, B_144)) | ~m1_subset_1('#skF_2'('#skF_5', k4_tmap_1(A_143, B_144)), k1_relat_1('#skF_5')) | ~m1_pre_topc('#skF_4', A_153) | ~l1_pre_topc(A_153) | v2_struct_0(A_153) | ~m1_pre_topc(B_144, A_143) | ~l1_pre_topc(A_143) | ~v2_pre_topc(A_143) | v2_struct_0(A_143) | u1_struct_0(A_143)=k1_xboole_0 | ~m1_pre_topc(B_144, A_143) | ~l1_pre_topc(A_143) | ~v2_pre_topc(A_143) | v2_struct_0(A_143))), inference(superposition, [status(thm), theory('equality')], [c_396, c_524])).
% 5.96/2.20  tff(c_859, plain, (![A_153, A_218]: (k1_funct_1(k4_tmap_1(A_153, '#skF_4'), '#skF_2'('#skF_5', k4_tmap_1(A_218, '#skF_4')))='#skF_2'('#skF_5', k4_tmap_1(A_218, '#skF_4')) | ~v2_pre_topc(A_153) | ~r1_tarski(k1_relat_1('#skF_5'), u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_4', A_153) | ~l1_pre_topc(A_153) | v2_struct_0(A_153) | r1_tarski('#skF_5', k4_tmap_1(A_218, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_218, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_218, '#skF_4')) | u1_struct_0(A_218)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_218) | ~l1_pre_topc(A_218) | ~v2_pre_topc(A_218) | v2_struct_0(A_218))), inference(resolution, [status(thm)], [c_857, c_528])).
% 5.96/2.20  tff(c_938, plain, (![A_232, A_233]: (k1_funct_1(k4_tmap_1(A_232, '#skF_4'), '#skF_2'('#skF_5', k4_tmap_1(A_233, '#skF_4')))='#skF_2'('#skF_5', k4_tmap_1(A_233, '#skF_4')) | ~v2_pre_topc(A_232) | ~m1_pre_topc('#skF_4', A_232) | ~l1_pre_topc(A_232) | v2_struct_0(A_232) | r1_tarski('#skF_5', k4_tmap_1(A_233, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_233, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_233, '#skF_4')) | u1_struct_0(A_233)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_233) | ~l1_pre_topc(A_233) | ~v2_pre_topc(A_233) | v2_struct_0(A_233))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_129, c_859])).
% 5.96/2.20  tff(c_947, plain, (![A_233]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', k4_tmap_1(A_233, '#skF_4')))!='#skF_2'('#skF_5', k4_tmap_1(A_233, '#skF_4')) | r1_tarski('#skF_5', k4_tmap_1(A_233, '#skF_4')) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(k4_tmap_1(A_233, '#skF_4'))) | ~v1_funct_1(k4_tmap_1(A_233, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_233, '#skF_4')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v2_pre_topc(A_233) | ~m1_pre_topc('#skF_4', A_233) | ~l1_pre_topc(A_233) | v2_struct_0(A_233) | r1_tarski('#skF_5', k4_tmap_1(A_233, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_233, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_233, '#skF_4')) | u1_struct_0(A_233)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_233) | ~l1_pre_topc(A_233) | ~v2_pre_topc(A_233) | v2_struct_0(A_233))), inference(superposition, [status(thm), theory('equality')], [c_938, c_36])).
% 5.96/2.20  tff(c_959, plain, (![A_234]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', k4_tmap_1(A_234, '#skF_4')))!='#skF_2'('#skF_5', k4_tmap_1(A_234, '#skF_4')) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(k4_tmap_1(A_234, '#skF_4'))) | r1_tarski('#skF_5', k4_tmap_1(A_234, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_234, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_234, '#skF_4')) | u1_struct_0(A_234)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_234) | ~l1_pre_topc(A_234) | ~v2_pre_topc(A_234) | v2_struct_0(A_234))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_66, c_947])).
% 5.96/2.20  tff(c_981, plain, (![A_235]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', k4_tmap_1(A_235, '#skF_4')))!='#skF_2'('#skF_5', k4_tmap_1(A_235, '#skF_4')) | r1_tarski('#skF_5', k4_tmap_1(A_235, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_235, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_235, '#skF_4')) | u1_struct_0(A_235)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_235) | ~l1_pre_topc(A_235) | ~v2_pre_topc(A_235) | v2_struct_0(A_235))), inference(resolution, [status(thm)], [c_807, c_959])).
% 5.96/2.20  tff(c_989, plain, (![A_236]: (r1_tarski('#skF_5', k4_tmap_1(A_236, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_236, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_236, '#skF_4')) | u1_struct_0(A_236)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_236) | ~l1_pre_topc(A_236) | ~v2_pre_topc(A_236) | v2_struct_0(A_236))), inference(superposition, [status(thm), theory('equality')], [c_897, c_981])).
% 5.96/2.20  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.96/2.20  tff(c_1007, plain, (![A_236]: (k4_tmap_1(A_236, '#skF_4')='#skF_5' | ~r1_tarski(k4_tmap_1(A_236, '#skF_4'), '#skF_5') | ~v1_funct_1(k4_tmap_1(A_236, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_236, '#skF_4')) | u1_struct_0(A_236)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_236) | ~l1_pre_topc(A_236) | ~v2_pre_topc(A_236) | v2_struct_0(A_236))), inference(resolution, [status(thm)], [c_989, c_4])).
% 5.96/2.20  tff(c_1606, plain, (![A_351]: (k4_tmap_1(A_351, '#skF_4')='#skF_5' | ~v1_funct_1(k4_tmap_1(A_351, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_351, '#skF_4')) | u1_struct_0(A_351)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_351) | ~l1_pre_topc(A_351) | ~v2_pre_topc(A_351) | v2_struct_0(A_351))), inference(resolution, [status(thm)], [c_1561, c_1007])).
% 5.96/2.20  tff(c_1612, plain, (![A_352]: (k4_tmap_1(A_352, '#skF_4')='#skF_5' | ~v1_funct_1(k4_tmap_1(A_352, '#skF_4')) | u1_struct_0(A_352)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_352) | ~l1_pre_topc(A_352) | ~v2_pre_topc(A_352) | v2_struct_0(A_352))), inference(resolution, [status(thm)], [c_225, c_1606])).
% 5.96/2.20  tff(c_1618, plain, (![A_353]: (k4_tmap_1(A_353, '#skF_4')='#skF_5' | u1_struct_0(A_353)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_353) | ~l1_pre_topc(A_353) | ~v2_pre_topc(A_353) | v2_struct_0(A_353))), inference(resolution, [status(thm)], [c_54, c_1612])).
% 5.96/2.20  tff(c_1621, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5' | u1_struct_0('#skF_3')=k1_xboole_0 | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1618])).
% 5.96/2.20  tff(c_1624, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5' | u1_struct_0('#skF_3')=k1_xboole_0 | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_1621])).
% 5.96/2.20  tff(c_1625, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5' | u1_struct_0('#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_76, c_1624])).
% 5.96/2.20  tff(c_1626, plain, (u1_struct_0('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1625])).
% 5.96/2.20  tff(c_46, plain, (![A_39]: (~v1_xboole_0(u1_struct_0(A_39)) | ~l1_struct_0(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.96/2.20  tff(c_1751, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1626, c_46])).
% 5.96/2.20  tff(c_1834, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1751])).
% 5.96/2.20  tff(c_1835, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_76, c_1834])).
% 5.96/2.20  tff(c_1839, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_1835])).
% 5.96/2.20  tff(c_1843, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_1839])).
% 5.96/2.20  tff(c_1844, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_1625])).
% 5.96/2.20  tff(c_58, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_198])).
% 5.96/2.20  tff(c_132, plain, (~r2_funct_2(k1_relat_1('#skF_5'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_58])).
% 5.96/2.20  tff(c_1846, plain, (~r2_funct_2(k1_relat_1('#skF_5'), u1_struct_0('#skF_3'), '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1844, c_132])).
% 5.96/2.20  tff(c_1849, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_622, c_1846])).
% 5.96/2.20  tff(c_1850, plain, (u1_struct_0('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_128])).
% 5.96/2.20  tff(c_1860, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1850, c_46])).
% 5.96/2.20  tff(c_1864, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1860])).
% 5.96/2.20  tff(c_1865, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_76, c_1864])).
% 5.96/2.20  tff(c_1879, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_1865])).
% 5.96/2.20  tff(c_1883, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_1879])).
% 5.96/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.96/2.20  
% 5.96/2.20  Inference rules
% 5.96/2.20  ----------------------
% 5.96/2.20  #Ref     : 3
% 5.96/2.20  #Sup     : 404
% 5.96/2.20  #Fact    : 0
% 5.96/2.20  #Define  : 0
% 5.96/2.20  #Split   : 4
% 5.96/2.20  #Chain   : 0
% 5.96/2.20  #Close   : 0
% 5.96/2.20  
% 5.96/2.20  Ordering : KBO
% 5.96/2.20  
% 5.96/2.20  Simplification rules
% 5.96/2.20  ----------------------
% 5.96/2.20  #Subsume      : 118
% 5.96/2.20  #Demod        : 432
% 5.96/2.20  #Tautology    : 92
% 5.96/2.20  #SimpNegUnit  : 64
% 5.96/2.20  #BackRed      : 22
% 5.96/2.20  
% 5.96/2.20  #Partial instantiations: 0
% 5.96/2.20  #Strategies tried      : 1
% 5.96/2.20  
% 5.96/2.20  Timing (in seconds)
% 5.96/2.20  ----------------------
% 5.96/2.20  Preprocessing        : 0.38
% 5.96/2.20  Parsing              : 0.19
% 5.96/2.20  CNF conversion       : 0.03
% 5.96/2.21  Main loop            : 1.04
% 5.96/2.21  Inferencing          : 0.33
% 5.96/2.21  Reduction            : 0.29
% 5.96/2.21  Demodulation         : 0.21
% 5.96/2.21  BG Simplification    : 0.05
% 5.96/2.21  Subsumption          : 0.31
% 5.96/2.21  Abstraction          : 0.05
% 5.96/2.21  MUC search           : 0.00
% 5.96/2.21  Cooper               : 0.00
% 5.96/2.21  Total                : 1.47
% 5.96/2.21  Index Insertion      : 0.00
% 5.96/2.21  Index Deletion       : 0.00
% 5.96/2.21  Index Matching       : 0.00
% 5.96/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
