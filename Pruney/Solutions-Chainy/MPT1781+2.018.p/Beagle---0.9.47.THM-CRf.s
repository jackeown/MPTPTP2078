%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:47 EST 2020

% Result     : Theorem 12.39s
% Output     : CNFRefutation 12.63s
% Verified   : 
% Statistics : Number of formulae       :  321 (801501 expanded)
%              Number of leaves         :   38 (271779 expanded)
%              Depth                    :   48
%              Number of atoms          : 1337 (4264113 expanded)
%              Number of equality atoms :  216 (856593 expanded)
%              Maximal formula depth    :   26 (   6 average)
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

tff(f_174,negated_conjecture,(
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

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_68,axiom,(
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

tff(f_84,axiom,(
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

tff(f_117,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_funct_1(k4_tmap_1(A,B))
        & v1_funct_2(k4_tmap_1(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(k4_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_tmap_1)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_44,axiom,(
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

tff(f_102,axiom,(
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

tff(f_124,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_144,axiom,(
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

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_56,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_102,plain,(
    ! [A_72,B_73,C_74] :
      ( k1_relset_1(A_72,B_73,C_74) = k1_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_106,plain,(
    k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_102])).

tff(c_126,plain,(
    ! [B_91,A_92,C_93] :
      ( k1_xboole_0 = B_91
      | k1_relset_1(A_92,B_91,C_93) = A_92
      | ~ v1_funct_2(C_93,A_92,B_91)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_92,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_129,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4') = u1_struct_0('#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_126])).

tff(c_132,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | u1_struct_0('#skF_3') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_106,c_129])).

tff(c_133,plain,(
    u1_struct_0('#skF_3') = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_139,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_56])).

tff(c_138,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_54])).

tff(c_184,plain,(
    ! [A_94,B_95,D_96] :
      ( r2_funct_2(A_94,B_95,D_96,D_96)
      | ~ m1_subset_1(D_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95)))
      | ~ v1_funct_2(D_96,A_94,B_95)
      | ~ v1_funct_1(D_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_186,plain,
    ( r2_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'),'#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_138,c_184])).

tff(c_189,plain,(
    r2_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_139,c_186])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_66,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_64,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_60,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_44,plain,(
    ! [A_31,B_32] :
      ( v1_funct_1(k4_tmap_1(A_31,B_32))
      | ~ m1_pre_topc(B_32,A_31)
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_12,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6814,plain,(
    ! [A_475,B_476] :
      ( m1_subset_1(k4_tmap_1(A_475,B_476),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_476),u1_struct_0(A_475))))
      | ~ m1_pre_topc(B_476,A_475)
      | ~ l1_pre_topc(A_475)
      | ~ v2_pre_topc(A_475)
      | v2_struct_0(A_475) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_10,plain,(
    ! [B_8,A_6] :
      ( v1_relat_1(B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_6))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6830,plain,(
    ! [A_475,B_476] :
      ( v1_relat_1(k4_tmap_1(A_475,B_476))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(B_476),u1_struct_0(A_475)))
      | ~ m1_pre_topc(B_476,A_475)
      | ~ l1_pre_topc(A_475)
      | ~ v2_pre_topc(A_475)
      | v2_struct_0(A_475) ) ),
    inference(resolution,[status(thm)],[c_6814,c_10])).

tff(c_6844,plain,(
    ! [A_475,B_476] :
      ( v1_relat_1(k4_tmap_1(A_475,B_476))
      | ~ m1_pre_topc(B_476,A_475)
      | ~ l1_pre_topc(A_475)
      | ~ v2_pre_topc(A_475)
      | v2_struct_0(A_475) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_6830])).

tff(c_72,plain,(
    ! [B_58,A_59] :
      ( v1_relat_1(B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59))
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_75,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_54,c_72])).

tff(c_78,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_75])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ! [A_31,B_32] :
      ( v1_funct_2(k4_tmap_1(A_31,B_32),u1_struct_0(B_32),u1_struct_0(A_31))
      | ~ m1_pre_topc(B_32,A_31)
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_26,plain,(
    ! [B_15,A_14,C_16] :
      ( k1_xboole_0 = B_15
      | k1_relset_1(A_14,B_15,C_16) = A_14
      | ~ v1_funct_2(C_16,A_14,B_15)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_7004,plain,(
    ! [A_507,B_508] :
      ( u1_struct_0(A_507) = k1_xboole_0
      | k1_relset_1(u1_struct_0(B_508),u1_struct_0(A_507),k4_tmap_1(A_507,B_508)) = u1_struct_0(B_508)
      | ~ v1_funct_2(k4_tmap_1(A_507,B_508),u1_struct_0(B_508),u1_struct_0(A_507))
      | ~ m1_pre_topc(B_508,A_507)
      | ~ l1_pre_topc(A_507)
      | ~ v2_pre_topc(A_507)
      | v2_struct_0(A_507) ) ),
    inference(resolution,[status(thm)],[c_6814,c_26])).

tff(c_7019,plain,(
    ! [A_509,B_510] :
      ( u1_struct_0(A_509) = k1_xboole_0
      | k1_relset_1(u1_struct_0(B_510),u1_struct_0(A_509),k4_tmap_1(A_509,B_510)) = u1_struct_0(B_510)
      | ~ m1_pre_topc(B_510,A_509)
      | ~ l1_pre_topc(A_509)
      | ~ v2_pre_topc(A_509)
      | v2_struct_0(A_509) ) ),
    inference(resolution,[status(thm)],[c_42,c_7004])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13] :
      ( k1_relset_1(A_11,B_12,C_13) = k1_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6840,plain,(
    ! [B_476,A_475] :
      ( k1_relset_1(u1_struct_0(B_476),u1_struct_0(A_475),k4_tmap_1(A_475,B_476)) = k1_relat_1(k4_tmap_1(A_475,B_476))
      | ~ m1_pre_topc(B_476,A_475)
      | ~ l1_pre_topc(A_475)
      | ~ v2_pre_topc(A_475)
      | v2_struct_0(A_475) ) ),
    inference(resolution,[status(thm)],[c_6814,c_14])).

tff(c_7064,plain,(
    ! [A_512,B_513] :
      ( k1_relat_1(k4_tmap_1(A_512,B_513)) = u1_struct_0(B_513)
      | ~ m1_pre_topc(B_513,A_512)
      | ~ l1_pre_topc(A_512)
      | ~ v2_pre_topc(A_512)
      | v2_struct_0(A_512)
      | u1_struct_0(A_512) = k1_xboole_0
      | ~ m1_pre_topc(B_513,A_512)
      | ~ l1_pre_topc(A_512)
      | ~ v2_pre_topc(A_512)
      | v2_struct_0(A_512) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7019,c_6840])).

tff(c_38,plain,(
    ! [A_21,B_27] :
      ( r1_tarski(k1_relat_1(A_21),k1_relat_1(B_27))
      | ~ r1_tarski(A_21,B_27)
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_7318,plain,(
    ! [A_542,B_543,A_544] :
      ( r1_tarski(k1_relat_1(A_542),u1_struct_0(B_543))
      | ~ r1_tarski(A_542,k4_tmap_1(A_544,B_543))
      | ~ v1_funct_1(k4_tmap_1(A_544,B_543))
      | ~ v1_relat_1(k4_tmap_1(A_544,B_543))
      | ~ v1_funct_1(A_542)
      | ~ v1_relat_1(A_542)
      | ~ m1_pre_topc(B_543,A_544)
      | ~ l1_pre_topc(A_544)
      | ~ v2_pre_topc(A_544)
      | v2_struct_0(A_544)
      | u1_struct_0(A_544) = k1_xboole_0
      | ~ m1_pre_topc(B_543,A_544)
      | ~ l1_pre_topc(A_544)
      | ~ v2_pre_topc(A_544)
      | v2_struct_0(A_544) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7064,c_38])).

tff(c_7323,plain,(
    ! [A_545,B_546] :
      ( r1_tarski(k1_relat_1(k4_tmap_1(A_545,B_546)),u1_struct_0(B_546))
      | ~ v1_funct_1(k4_tmap_1(A_545,B_546))
      | ~ v1_relat_1(k4_tmap_1(A_545,B_546))
      | u1_struct_0(A_545) = k1_xboole_0
      | ~ m1_pre_topc(B_546,A_545)
      | ~ l1_pre_topc(A_545)
      | ~ v2_pre_topc(A_545)
      | v2_struct_0(A_545) ) ),
    inference(resolution,[status(thm)],[c_6,c_7318])).

tff(c_7336,plain,(
    ! [A_545] :
      ( r1_tarski(k1_relat_1(k4_tmap_1(A_545,'#skF_3')),k1_relat_1('#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_545,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_545,'#skF_3'))
      | u1_struct_0(A_545) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_545)
      | ~ l1_pre_topc(A_545)
      | ~ v2_pre_topc(A_545)
      | v2_struct_0(A_545) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_7323])).

tff(c_34,plain,(
    ! [A_21,B_27] :
      ( r2_hidden('#skF_1'(A_21,B_27),k1_relat_1(A_21))
      | r1_tarski(A_21,B_27)
      | ~ r1_tarski(k1_relat_1(A_21),k1_relat_1(B_27))
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_7714,plain,(
    ! [A_604,B_605,B_606] :
      ( r2_hidden('#skF_1'(k4_tmap_1(A_604,B_605),B_606),u1_struct_0(B_605))
      | r1_tarski(k4_tmap_1(A_604,B_605),B_606)
      | ~ r1_tarski(k1_relat_1(k4_tmap_1(A_604,B_605)),k1_relat_1(B_606))
      | ~ v1_funct_1(B_606)
      | ~ v1_relat_1(B_606)
      | ~ v1_funct_1(k4_tmap_1(A_604,B_605))
      | ~ v1_relat_1(k4_tmap_1(A_604,B_605))
      | ~ m1_pre_topc(B_605,A_604)
      | ~ l1_pre_topc(A_604)
      | ~ v2_pre_topc(A_604)
      | v2_struct_0(A_604)
      | u1_struct_0(A_604) = k1_xboole_0
      | ~ m1_pre_topc(B_605,A_604)
      | ~ l1_pre_topc(A_604)
      | ~ v2_pre_topc(A_604)
      | v2_struct_0(A_604) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7064,c_34])).

tff(c_90,plain,(
    ! [B_65,A_66] :
      ( m1_subset_1(u1_struct_0(B_65),k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ m1_pre_topc(B_65,A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( m1_subset_1(A_3,C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_96,plain,(
    ! [A_3,A_66,B_65] :
      ( m1_subset_1(A_3,u1_struct_0(A_66))
      | ~ r2_hidden(A_3,u1_struct_0(B_65))
      | ~ m1_pre_topc(B_65,A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_90,c_8])).

tff(c_7727,plain,(
    ! [A_607,B_608,B_609,A_610] :
      ( m1_subset_1('#skF_1'(k4_tmap_1(A_607,B_608),B_609),u1_struct_0(A_610))
      | ~ m1_pre_topc(B_608,A_610)
      | ~ l1_pre_topc(A_610)
      | r1_tarski(k4_tmap_1(A_607,B_608),B_609)
      | ~ r1_tarski(k1_relat_1(k4_tmap_1(A_607,B_608)),k1_relat_1(B_609))
      | ~ v1_funct_1(B_609)
      | ~ v1_relat_1(B_609)
      | ~ v1_funct_1(k4_tmap_1(A_607,B_608))
      | ~ v1_relat_1(k4_tmap_1(A_607,B_608))
      | u1_struct_0(A_607) = k1_xboole_0
      | ~ m1_pre_topc(B_608,A_607)
      | ~ l1_pre_topc(A_607)
      | ~ v2_pre_topc(A_607)
      | v2_struct_0(A_607) ) ),
    inference(resolution,[status(thm)],[c_7714,c_96])).

tff(c_7729,plain,(
    ! [A_545,A_610] :
      ( m1_subset_1('#skF_1'(k4_tmap_1(A_545,'#skF_3'),'#skF_4'),u1_struct_0(A_610))
      | ~ m1_pre_topc('#skF_3',A_610)
      | ~ l1_pre_topc(A_610)
      | r1_tarski(k4_tmap_1(A_545,'#skF_3'),'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_funct_1(k4_tmap_1(A_545,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_545,'#skF_3'))
      | u1_struct_0(A_545) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_545)
      | ~ l1_pre_topc(A_545)
      | ~ v2_pre_topc(A_545)
      | v2_struct_0(A_545) ) ),
    inference(resolution,[status(thm)],[c_7336,c_7727])).

tff(c_7746,plain,(
    ! [A_545,A_610] :
      ( m1_subset_1('#skF_1'(k4_tmap_1(A_545,'#skF_3'),'#skF_4'),u1_struct_0(A_610))
      | ~ m1_pre_topc('#skF_3',A_610)
      | ~ l1_pre_topc(A_610)
      | r1_tarski(k4_tmap_1(A_545,'#skF_3'),'#skF_4')
      | ~ v1_funct_1(k4_tmap_1(A_545,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_545,'#skF_3'))
      | u1_struct_0(A_545) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_545)
      | ~ l1_pre_topc(A_545)
      | ~ v2_pre_topc(A_545)
      | v2_struct_0(A_545) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_58,c_7729])).

tff(c_7034,plain,(
    ! [A_509] :
      ( u1_struct_0(A_509) = k1_xboole_0
      | k1_relset_1(k1_relat_1('#skF_4'),u1_struct_0(A_509),k4_tmap_1(A_509,'#skF_3')) = u1_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_3',A_509)
      | ~ l1_pre_topc(A_509)
      | ~ v2_pre_topc(A_509)
      | v2_struct_0(A_509) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_7019])).

tff(c_7043,plain,(
    ! [A_511] :
      ( u1_struct_0(A_511) = k1_xboole_0
      | k1_relset_1(k1_relat_1('#skF_4'),u1_struct_0(A_511),k4_tmap_1(A_511,'#skF_3')) = k1_relat_1('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_511)
      | ~ l1_pre_topc(A_511)
      | ~ v2_pre_topc(A_511)
      | v2_struct_0(A_511) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_7034])).

tff(c_6905,plain,(
    ! [B_489,A_490] :
      ( k1_relset_1(u1_struct_0(B_489),u1_struct_0(A_490),k4_tmap_1(A_490,B_489)) = k1_relat_1(k4_tmap_1(A_490,B_489))
      | ~ m1_pre_topc(B_489,A_490)
      | ~ l1_pre_topc(A_490)
      | ~ v2_pre_topc(A_490)
      | v2_struct_0(A_490) ) ),
    inference(resolution,[status(thm)],[c_6814,c_14])).

tff(c_6914,plain,(
    ! [A_490] :
      ( k1_relset_1(k1_relat_1('#skF_4'),u1_struct_0(A_490),k4_tmap_1(A_490,'#skF_3')) = k1_relat_1(k4_tmap_1(A_490,'#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_490)
      | ~ l1_pre_topc(A_490)
      | ~ v2_pre_topc(A_490)
      | v2_struct_0(A_490) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_6905])).

tff(c_7102,plain,(
    ! [A_518] :
      ( k1_relat_1(k4_tmap_1(A_518,'#skF_3')) = k1_relat_1('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_518)
      | ~ l1_pre_topc(A_518)
      | ~ v2_pre_topc(A_518)
      | v2_struct_0(A_518)
      | u1_struct_0(A_518) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_518)
      | ~ l1_pre_topc(A_518)
      | ~ v2_pre_topc(A_518)
      | v2_struct_0(A_518) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7043,c_6914])).

tff(c_7754,plain,(
    ! [A_613,B_614] :
      ( r2_hidden('#skF_1'(k4_tmap_1(A_613,'#skF_3'),B_614),k1_relat_1('#skF_4'))
      | r1_tarski(k4_tmap_1(A_613,'#skF_3'),B_614)
      | ~ r1_tarski(k1_relat_1(k4_tmap_1(A_613,'#skF_3')),k1_relat_1(B_614))
      | ~ v1_funct_1(B_614)
      | ~ v1_relat_1(B_614)
      | ~ v1_funct_1(k4_tmap_1(A_613,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_613,'#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_613)
      | ~ l1_pre_topc(A_613)
      | ~ v2_pre_topc(A_613)
      | v2_struct_0(A_613)
      | u1_struct_0(A_613) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_613)
      | ~ l1_pre_topc(A_613)
      | ~ v2_pre_topc(A_613)
      | v2_struct_0(A_613) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7102,c_34])).

tff(c_52,plain,(
    ! [D_54] :
      ( k1_funct_1('#skF_4',D_54) = D_54
      | ~ r2_hidden(D_54,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_54,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_135,plain,(
    ! [D_54] :
      ( k1_funct_1('#skF_4',D_54) = D_54
      | ~ r2_hidden(D_54,k1_relat_1('#skF_4'))
      | ~ m1_subset_1(D_54,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_52])).

tff(c_7803,plain,(
    ! [A_627,B_628] :
      ( k1_funct_1('#skF_4','#skF_1'(k4_tmap_1(A_627,'#skF_3'),B_628)) = '#skF_1'(k4_tmap_1(A_627,'#skF_3'),B_628)
      | ~ m1_subset_1('#skF_1'(k4_tmap_1(A_627,'#skF_3'),B_628),u1_struct_0('#skF_2'))
      | r1_tarski(k4_tmap_1(A_627,'#skF_3'),B_628)
      | ~ r1_tarski(k1_relat_1(k4_tmap_1(A_627,'#skF_3')),k1_relat_1(B_628))
      | ~ v1_funct_1(B_628)
      | ~ v1_relat_1(B_628)
      | ~ v1_funct_1(k4_tmap_1(A_627,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_627,'#skF_3'))
      | u1_struct_0(A_627) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_627)
      | ~ l1_pre_topc(A_627)
      | ~ v2_pre_topc(A_627)
      | v2_struct_0(A_627) ) ),
    inference(resolution,[status(thm)],[c_7754,c_135])).

tff(c_7806,plain,(
    ! [A_545] :
      ( k1_funct_1('#skF_4','#skF_1'(k4_tmap_1(A_545,'#skF_3'),'#skF_4')) = '#skF_1'(k4_tmap_1(A_545,'#skF_3'),'#skF_4')
      | ~ m1_subset_1('#skF_1'(k4_tmap_1(A_545,'#skF_3'),'#skF_4'),u1_struct_0('#skF_2'))
      | r1_tarski(k4_tmap_1(A_545,'#skF_3'),'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_funct_1(k4_tmap_1(A_545,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_545,'#skF_3'))
      | u1_struct_0(A_545) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_545)
      | ~ l1_pre_topc(A_545)
      | ~ v2_pre_topc(A_545)
      | v2_struct_0(A_545) ) ),
    inference(resolution,[status(thm)],[c_7336,c_7803])).

tff(c_7835,plain,(
    ! [A_629] :
      ( k1_funct_1('#skF_4','#skF_1'(k4_tmap_1(A_629,'#skF_3'),'#skF_4')) = '#skF_1'(k4_tmap_1(A_629,'#skF_3'),'#skF_4')
      | ~ m1_subset_1('#skF_1'(k4_tmap_1(A_629,'#skF_3'),'#skF_4'),u1_struct_0('#skF_2'))
      | r1_tarski(k4_tmap_1(A_629,'#skF_3'),'#skF_4')
      | ~ v1_funct_1(k4_tmap_1(A_629,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_629,'#skF_3'))
      | u1_struct_0(A_629) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_629)
      | ~ l1_pre_topc(A_629)
      | ~ v2_pre_topc(A_629)
      | v2_struct_0(A_629) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_58,c_7806])).

tff(c_7839,plain,(
    ! [A_545] :
      ( k1_funct_1('#skF_4','#skF_1'(k4_tmap_1(A_545,'#skF_3'),'#skF_4')) = '#skF_1'(k4_tmap_1(A_545,'#skF_3'),'#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | r1_tarski(k4_tmap_1(A_545,'#skF_3'),'#skF_4')
      | ~ v1_funct_1(k4_tmap_1(A_545,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_545,'#skF_3'))
      | u1_struct_0(A_545) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_545)
      | ~ l1_pre_topc(A_545)
      | ~ v2_pre_topc(A_545)
      | v2_struct_0(A_545) ) ),
    inference(resolution,[status(thm)],[c_7746,c_7835])).

tff(c_7842,plain,(
    ! [A_545] :
      ( k1_funct_1('#skF_4','#skF_1'(k4_tmap_1(A_545,'#skF_3'),'#skF_4')) = '#skF_1'(k4_tmap_1(A_545,'#skF_3'),'#skF_4')
      | r1_tarski(k4_tmap_1(A_545,'#skF_3'),'#skF_4')
      | ~ v1_funct_1(k4_tmap_1(A_545,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_545,'#skF_3'))
      | u1_struct_0(A_545) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_545)
      | ~ l1_pre_topc(A_545)
      | ~ v2_pre_topc(A_545)
      | v2_struct_0(A_545) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_7839])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_6959,plain,(
    ! [A_497,B_498,C_499] :
      ( k1_funct_1(k4_tmap_1(A_497,B_498),C_499) = C_499
      | ~ r2_hidden(C_499,u1_struct_0(B_498))
      | ~ m1_subset_1(C_499,u1_struct_0(A_497))
      | ~ m1_pre_topc(B_498,A_497)
      | v2_struct_0(B_498)
      | ~ l1_pre_topc(A_497)
      | ~ v2_pre_topc(A_497)
      | v2_struct_0(A_497) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_6961,plain,(
    ! [A_497,C_499] :
      ( k1_funct_1(k4_tmap_1(A_497,'#skF_3'),C_499) = C_499
      | ~ r2_hidden(C_499,k1_relat_1('#skF_4'))
      | ~ m1_subset_1(C_499,u1_struct_0(A_497))
      | ~ m1_pre_topc('#skF_3',A_497)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_497)
      | ~ v2_pre_topc(A_497)
      | v2_struct_0(A_497) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_6959])).

tff(c_6962,plain,(
    ! [A_497,C_499] :
      ( k1_funct_1(k4_tmap_1(A_497,'#skF_3'),C_499) = C_499
      | ~ r2_hidden(C_499,k1_relat_1('#skF_4'))
      | ~ m1_subset_1(C_499,u1_struct_0(A_497))
      | ~ m1_pre_topc('#skF_3',A_497)
      | ~ l1_pre_topc(A_497)
      | ~ v2_pre_topc(A_497)
      | v2_struct_0(A_497) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_6961])).

tff(c_7876,plain,(
    ! [A_636,A_637,B_638] :
      ( k1_funct_1(k4_tmap_1(A_636,'#skF_3'),'#skF_1'(k4_tmap_1(A_637,'#skF_3'),B_638)) = '#skF_1'(k4_tmap_1(A_637,'#skF_3'),B_638)
      | ~ m1_subset_1('#skF_1'(k4_tmap_1(A_637,'#skF_3'),B_638),u1_struct_0(A_636))
      | ~ m1_pre_topc('#skF_3',A_636)
      | ~ l1_pre_topc(A_636)
      | ~ v2_pre_topc(A_636)
      | v2_struct_0(A_636)
      | r1_tarski(k4_tmap_1(A_637,'#skF_3'),B_638)
      | ~ r1_tarski(k1_relat_1(k4_tmap_1(A_637,'#skF_3')),k1_relat_1(B_638))
      | ~ v1_funct_1(B_638)
      | ~ v1_relat_1(B_638)
      | ~ v1_funct_1(k4_tmap_1(A_637,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_637,'#skF_3'))
      | u1_struct_0(A_637) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_637)
      | ~ l1_pre_topc(A_637)
      | ~ v2_pre_topc(A_637)
      | v2_struct_0(A_637) ) ),
    inference(resolution,[status(thm)],[c_7754,c_6962])).

tff(c_7878,plain,(
    ! [A_610,A_545] :
      ( k1_funct_1(k4_tmap_1(A_610,'#skF_3'),'#skF_1'(k4_tmap_1(A_545,'#skF_3'),'#skF_4')) = '#skF_1'(k4_tmap_1(A_545,'#skF_3'),'#skF_4')
      | ~ v2_pre_topc(A_610)
      | v2_struct_0(A_610)
      | ~ r1_tarski(k1_relat_1(k4_tmap_1(A_545,'#skF_3')),k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_610)
      | ~ l1_pre_topc(A_610)
      | r1_tarski(k4_tmap_1(A_545,'#skF_3'),'#skF_4')
      | ~ v1_funct_1(k4_tmap_1(A_545,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_545,'#skF_3'))
      | u1_struct_0(A_545) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_545)
      | ~ l1_pre_topc(A_545)
      | ~ v2_pre_topc(A_545)
      | v2_struct_0(A_545) ) ),
    inference(resolution,[status(thm)],[c_7746,c_7876])).

tff(c_7885,plain,(
    ! [A_639,A_640] :
      ( k1_funct_1(k4_tmap_1(A_639,'#skF_3'),'#skF_1'(k4_tmap_1(A_640,'#skF_3'),'#skF_4')) = '#skF_1'(k4_tmap_1(A_640,'#skF_3'),'#skF_4')
      | ~ v2_pre_topc(A_639)
      | v2_struct_0(A_639)
      | ~ r1_tarski(k1_relat_1(k4_tmap_1(A_640,'#skF_3')),k1_relat_1('#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_639)
      | ~ l1_pre_topc(A_639)
      | r1_tarski(k4_tmap_1(A_640,'#skF_3'),'#skF_4')
      | ~ v1_funct_1(k4_tmap_1(A_640,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_640,'#skF_3'))
      | u1_struct_0(A_640) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_640)
      | ~ l1_pre_topc(A_640)
      | ~ v2_pre_topc(A_640)
      | v2_struct_0(A_640) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_58,c_7878])).

tff(c_7904,plain,(
    ! [A_641,A_642] :
      ( k1_funct_1(k4_tmap_1(A_641,'#skF_3'),'#skF_1'(k4_tmap_1(A_642,'#skF_3'),'#skF_4')) = '#skF_1'(k4_tmap_1(A_642,'#skF_3'),'#skF_4')
      | ~ v2_pre_topc(A_641)
      | v2_struct_0(A_641)
      | ~ m1_pre_topc('#skF_3',A_641)
      | ~ l1_pre_topc(A_641)
      | r1_tarski(k4_tmap_1(A_642,'#skF_3'),'#skF_4')
      | ~ v1_funct_1(k4_tmap_1(A_642,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_642,'#skF_3'))
      | u1_struct_0(A_642) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_642)
      | ~ l1_pre_topc(A_642)
      | ~ v2_pre_topc(A_642)
      | v2_struct_0(A_642) ) ),
    inference(resolution,[status(thm)],[c_7336,c_7885])).

tff(c_32,plain,(
    ! [B_27,A_21] :
      ( k1_funct_1(B_27,'#skF_1'(A_21,B_27)) != k1_funct_1(A_21,'#skF_1'(A_21,B_27))
      | r1_tarski(A_21,B_27)
      | ~ r1_tarski(k1_relat_1(A_21),k1_relat_1(B_27))
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_7919,plain,(
    ! [A_642] :
      ( k1_funct_1('#skF_4','#skF_1'(k4_tmap_1(A_642,'#skF_3'),'#skF_4')) != '#skF_1'(k4_tmap_1(A_642,'#skF_3'),'#skF_4')
      | r1_tarski(k4_tmap_1(A_642,'#skF_3'),'#skF_4')
      | ~ r1_tarski(k1_relat_1(k4_tmap_1(A_642,'#skF_3')),k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_funct_1(k4_tmap_1(A_642,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_642,'#skF_3'))
      | ~ v2_pre_topc(A_642)
      | v2_struct_0(A_642)
      | ~ m1_pre_topc('#skF_3',A_642)
      | ~ l1_pre_topc(A_642)
      | r1_tarski(k4_tmap_1(A_642,'#skF_3'),'#skF_4')
      | ~ v1_funct_1(k4_tmap_1(A_642,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_642,'#skF_3'))
      | u1_struct_0(A_642) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_642)
      | ~ l1_pre_topc(A_642)
      | ~ v2_pre_topc(A_642)
      | v2_struct_0(A_642) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7904,c_32])).

tff(c_7934,plain,(
    ! [A_643] :
      ( k1_funct_1('#skF_4','#skF_1'(k4_tmap_1(A_643,'#skF_3'),'#skF_4')) != '#skF_1'(k4_tmap_1(A_643,'#skF_3'),'#skF_4')
      | ~ r1_tarski(k1_relat_1(k4_tmap_1(A_643,'#skF_3')),k1_relat_1('#skF_4'))
      | r1_tarski(k4_tmap_1(A_643,'#skF_3'),'#skF_4')
      | ~ v1_funct_1(k4_tmap_1(A_643,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_643,'#skF_3'))
      | u1_struct_0(A_643) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_643)
      | ~ l1_pre_topc(A_643)
      | ~ v2_pre_topc(A_643)
      | v2_struct_0(A_643) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_58,c_7919])).

tff(c_7956,plain,(
    ! [A_644] :
      ( k1_funct_1('#skF_4','#skF_1'(k4_tmap_1(A_644,'#skF_3'),'#skF_4')) != '#skF_1'(k4_tmap_1(A_644,'#skF_3'),'#skF_4')
      | r1_tarski(k4_tmap_1(A_644,'#skF_3'),'#skF_4')
      | ~ v1_funct_1(k4_tmap_1(A_644,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_644,'#skF_3'))
      | u1_struct_0(A_644) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_644)
      | ~ l1_pre_topc(A_644)
      | ~ v2_pre_topc(A_644)
      | v2_struct_0(A_644) ) ),
    inference(resolution,[status(thm)],[c_7336,c_7934])).

tff(c_7961,plain,(
    ! [A_645] :
      ( r1_tarski(k4_tmap_1(A_645,'#skF_3'),'#skF_4')
      | ~ v1_funct_1(k4_tmap_1(A_645,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_645,'#skF_3'))
      | u1_struct_0(A_645) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_645)
      | ~ l1_pre_topc(A_645)
      | ~ v2_pre_topc(A_645)
      | v2_struct_0(A_645) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7842,c_7956])).

tff(c_6942,plain,(
    ! [A_495,B_496] :
      ( r2_hidden('#skF_1'(A_495,B_496),k1_relat_1(A_495))
      | r1_tarski(A_495,B_496)
      | ~ r1_tarski(k1_relat_1(A_495),k1_relat_1(B_496))
      | ~ v1_funct_1(B_496)
      | ~ v1_relat_1(B_496)
      | ~ v1_funct_1(A_495)
      | ~ v1_relat_1(A_495) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_142,plain,(
    ! [A_3,A_66] :
      ( m1_subset_1(A_3,u1_struct_0(A_66))
      | ~ r2_hidden(A_3,k1_relat_1('#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_96])).

tff(c_6947,plain,(
    ! [B_496,A_66] :
      ( m1_subset_1('#skF_1'('#skF_4',B_496),u1_struct_0(A_66))
      | ~ m1_pre_topc('#skF_3',A_66)
      | ~ l1_pre_topc(A_66)
      | r1_tarski('#skF_4',B_496)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_496))
      | ~ v1_funct_1(B_496)
      | ~ v1_relat_1(B_496)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6942,c_142])).

tff(c_6955,plain,(
    ! [B_496,A_66] :
      ( m1_subset_1('#skF_1'('#skF_4',B_496),u1_struct_0(A_66))
      | ~ m1_pre_topc('#skF_3',A_66)
      | ~ l1_pre_topc(A_66)
      | r1_tarski('#skF_4',B_496)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_496))
      | ~ v1_funct_1(B_496)
      | ~ v1_relat_1(B_496) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_58,c_6947])).

tff(c_7113,plain,(
    ! [A_518,A_66] :
      ( m1_subset_1('#skF_1'('#skF_4',k4_tmap_1(A_518,'#skF_3')),u1_struct_0(A_66))
      | ~ m1_pre_topc('#skF_3',A_66)
      | ~ l1_pre_topc(A_66)
      | r1_tarski('#skF_4',k4_tmap_1(A_518,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_518,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_518,'#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_518)
      | ~ l1_pre_topc(A_518)
      | ~ v2_pre_topc(A_518)
      | v2_struct_0(A_518)
      | u1_struct_0(A_518) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_518)
      | ~ l1_pre_topc(A_518)
      | ~ v2_pre_topc(A_518)
      | v2_struct_0(A_518) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7102,c_6955])).

tff(c_7230,plain,(
    ! [A_533,A_534] :
      ( m1_subset_1('#skF_1'('#skF_4',k4_tmap_1(A_533,'#skF_3')),u1_struct_0(A_534))
      | ~ m1_pre_topc('#skF_3',A_534)
      | ~ l1_pre_topc(A_534)
      | r1_tarski('#skF_4',k4_tmap_1(A_533,'#skF_3'))
      | ~ v1_funct_1(k4_tmap_1(A_533,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_533,'#skF_3'))
      | u1_struct_0(A_533) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_533)
      | ~ l1_pre_topc(A_533)
      | ~ v2_pre_topc(A_533)
      | v2_struct_0(A_533) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_7113])).

tff(c_6951,plain,(
    ! [B_496] :
      ( k1_funct_1('#skF_4','#skF_1'('#skF_4',B_496)) = '#skF_1'('#skF_4',B_496)
      | ~ m1_subset_1('#skF_1'('#skF_4',B_496),u1_struct_0('#skF_2'))
      | r1_tarski('#skF_4',B_496)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_496))
      | ~ v1_funct_1(B_496)
      | ~ v1_relat_1(B_496)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6942,c_135])).

tff(c_6958,plain,(
    ! [B_496] :
      ( k1_funct_1('#skF_4','#skF_1'('#skF_4',B_496)) = '#skF_1'('#skF_4',B_496)
      | ~ m1_subset_1('#skF_1'('#skF_4',B_496),u1_struct_0('#skF_2'))
      | r1_tarski('#skF_4',B_496)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_496))
      | ~ v1_funct_1(B_496)
      | ~ v1_relat_1(B_496) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_58,c_6951])).

tff(c_7070,plain,(
    ! [A_512,B_513] :
      ( k1_funct_1('#skF_4','#skF_1'('#skF_4',k4_tmap_1(A_512,B_513))) = '#skF_1'('#skF_4',k4_tmap_1(A_512,B_513))
      | ~ m1_subset_1('#skF_1'('#skF_4',k4_tmap_1(A_512,B_513)),u1_struct_0('#skF_2'))
      | r1_tarski('#skF_4',k4_tmap_1(A_512,B_513))
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(B_513))
      | ~ v1_funct_1(k4_tmap_1(A_512,B_513))
      | ~ v1_relat_1(k4_tmap_1(A_512,B_513))
      | ~ m1_pre_topc(B_513,A_512)
      | ~ l1_pre_topc(A_512)
      | ~ v2_pre_topc(A_512)
      | v2_struct_0(A_512)
      | u1_struct_0(A_512) = k1_xboole_0
      | ~ m1_pre_topc(B_513,A_512)
      | ~ l1_pre_topc(A_512)
      | ~ v2_pre_topc(A_512)
      | v2_struct_0(A_512) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7064,c_6958])).

tff(c_7234,plain,(
    ! [A_533] :
      ( k1_funct_1('#skF_4','#skF_1'('#skF_4',k4_tmap_1(A_533,'#skF_3'))) = '#skF_1'('#skF_4',k4_tmap_1(A_533,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | r1_tarski('#skF_4',k4_tmap_1(A_533,'#skF_3'))
      | ~ v1_funct_1(k4_tmap_1(A_533,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_533,'#skF_3'))
      | u1_struct_0(A_533) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_533)
      | ~ l1_pre_topc(A_533)
      | ~ v2_pre_topc(A_533)
      | v2_struct_0(A_533) ) ),
    inference(resolution,[status(thm)],[c_7230,c_7070])).

tff(c_7242,plain,(
    ! [A_533] :
      ( k1_funct_1('#skF_4','#skF_1'('#skF_4',k4_tmap_1(A_533,'#skF_3'))) = '#skF_1'('#skF_4',k4_tmap_1(A_533,'#skF_3'))
      | r1_tarski('#skF_4',k4_tmap_1(A_533,'#skF_3'))
      | ~ v1_funct_1(k4_tmap_1(A_533,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_533,'#skF_3'))
      | u1_struct_0(A_533) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_533)
      | ~ l1_pre_topc(A_533)
      | ~ v2_pre_topc(A_533)
      | v2_struct_0(A_533) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_6,c_133,c_7234])).

tff(c_7253,plain,(
    ! [B_536,B_537,A_538] :
      ( r1_tarski(u1_struct_0(B_536),k1_relat_1(B_537))
      | ~ r1_tarski(k4_tmap_1(A_538,B_536),B_537)
      | ~ v1_funct_1(B_537)
      | ~ v1_relat_1(B_537)
      | ~ v1_funct_1(k4_tmap_1(A_538,B_536))
      | ~ v1_relat_1(k4_tmap_1(A_538,B_536))
      | ~ m1_pre_topc(B_536,A_538)
      | ~ l1_pre_topc(A_538)
      | ~ v2_pre_topc(A_538)
      | v2_struct_0(A_538)
      | u1_struct_0(A_538) = k1_xboole_0
      | ~ m1_pre_topc(B_536,A_538)
      | ~ l1_pre_topc(A_538)
      | ~ v2_pre_topc(A_538)
      | v2_struct_0(A_538) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7064,c_38])).

tff(c_7258,plain,(
    ! [B_539,A_540] :
      ( r1_tarski(u1_struct_0(B_539),k1_relat_1(k4_tmap_1(A_540,B_539)))
      | ~ v1_funct_1(k4_tmap_1(A_540,B_539))
      | ~ v1_relat_1(k4_tmap_1(A_540,B_539))
      | u1_struct_0(A_540) = k1_xboole_0
      | ~ m1_pre_topc(B_539,A_540)
      | ~ l1_pre_topc(A_540)
      | ~ v2_pre_topc(A_540)
      | v2_struct_0(A_540) ) ),
    inference(resolution,[status(thm)],[c_6,c_7253])).

tff(c_7271,plain,(
    ! [A_540] :
      ( r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(k4_tmap_1(A_540,'#skF_3')))
      | ~ v1_funct_1(k4_tmap_1(A_540,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_540,'#skF_3'))
      | u1_struct_0(A_540) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_540)
      | ~ l1_pre_topc(A_540)
      | ~ v2_pre_topc(A_540)
      | v2_struct_0(A_540) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_7258])).

tff(c_7025,plain,(
    ! [A_509,B_510] :
      ( k1_relat_1(k4_tmap_1(A_509,B_510)) = u1_struct_0(B_510)
      | ~ m1_pre_topc(B_510,A_509)
      | ~ l1_pre_topc(A_509)
      | ~ v2_pre_topc(A_509)
      | v2_struct_0(A_509)
      | u1_struct_0(A_509) = k1_xboole_0
      | ~ m1_pre_topc(B_510,A_509)
      | ~ l1_pre_topc(A_509)
      | ~ v2_pre_topc(A_509)
      | v2_struct_0(A_509) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7019,c_6840])).

tff(c_6963,plain,(
    ! [A_500,C_501] :
      ( k1_funct_1(k4_tmap_1(A_500,'#skF_3'),C_501) = C_501
      | ~ r2_hidden(C_501,k1_relat_1('#skF_4'))
      | ~ m1_subset_1(C_501,u1_struct_0(A_500))
      | ~ m1_pre_topc('#skF_3',A_500)
      | ~ l1_pre_topc(A_500)
      | ~ v2_pre_topc(A_500)
      | v2_struct_0(A_500) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_6961])).

tff(c_6966,plain,(
    ! [A_500,B_27] :
      ( k1_funct_1(k4_tmap_1(A_500,'#skF_3'),'#skF_1'('#skF_4',B_27)) = '#skF_1'('#skF_4',B_27)
      | ~ m1_subset_1('#skF_1'('#skF_4',B_27),u1_struct_0(A_500))
      | ~ m1_pre_topc('#skF_3',A_500)
      | ~ l1_pre_topc(A_500)
      | ~ v2_pre_topc(A_500)
      | v2_struct_0(A_500)
      | r1_tarski('#skF_4',B_27)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_27))
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_6963])).

tff(c_6969,plain,(
    ! [A_500,B_27] :
      ( k1_funct_1(k4_tmap_1(A_500,'#skF_3'),'#skF_1'('#skF_4',B_27)) = '#skF_1'('#skF_4',B_27)
      | ~ m1_subset_1('#skF_1'('#skF_4',B_27),u1_struct_0(A_500))
      | ~ m1_pre_topc('#skF_3',A_500)
      | ~ l1_pre_topc(A_500)
      | ~ v2_pre_topc(A_500)
      | v2_struct_0(A_500)
      | r1_tarski('#skF_4',B_27)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_27))
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_58,c_6966])).

tff(c_7377,plain,(
    ! [A_549,A_550] :
      ( k1_funct_1(k4_tmap_1(A_549,'#skF_3'),'#skF_1'('#skF_4',k4_tmap_1(A_550,'#skF_3'))) = '#skF_1'('#skF_4',k4_tmap_1(A_550,'#skF_3'))
      | ~ v2_pre_topc(A_549)
      | v2_struct_0(A_549)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(k4_tmap_1(A_550,'#skF_3')))
      | ~ m1_pre_topc('#skF_3',A_549)
      | ~ l1_pre_topc(A_549)
      | r1_tarski('#skF_4',k4_tmap_1(A_550,'#skF_3'))
      | ~ v1_funct_1(k4_tmap_1(A_550,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_550,'#skF_3'))
      | u1_struct_0(A_550) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_550)
      | ~ l1_pre_topc(A_550)
      | ~ v2_pre_topc(A_550)
      | v2_struct_0(A_550) ) ),
    inference(resolution,[status(thm)],[c_7230,c_6969])).

tff(c_7384,plain,(
    ! [A_549,A_509] :
      ( k1_funct_1(k4_tmap_1(A_549,'#skF_3'),'#skF_1'('#skF_4',k4_tmap_1(A_509,'#skF_3'))) = '#skF_1'('#skF_4',k4_tmap_1(A_509,'#skF_3'))
      | ~ v2_pre_topc(A_549)
      | v2_struct_0(A_549)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_549)
      | ~ l1_pre_topc(A_549)
      | r1_tarski('#skF_4',k4_tmap_1(A_509,'#skF_3'))
      | ~ v1_funct_1(k4_tmap_1(A_509,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_509,'#skF_3'))
      | u1_struct_0(A_509) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_509)
      | ~ l1_pre_topc(A_509)
      | ~ v2_pre_topc(A_509)
      | v2_struct_0(A_509)
      | ~ m1_pre_topc('#skF_3',A_509)
      | ~ l1_pre_topc(A_509)
      | ~ v2_pre_topc(A_509)
      | v2_struct_0(A_509)
      | u1_struct_0(A_509) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_509)
      | ~ l1_pre_topc(A_509)
      | ~ v2_pre_topc(A_509)
      | v2_struct_0(A_509) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7025,c_7377])).

tff(c_7513,plain,(
    ! [A_573,A_574] :
      ( k1_funct_1(k4_tmap_1(A_573,'#skF_3'),'#skF_1'('#skF_4',k4_tmap_1(A_574,'#skF_3'))) = '#skF_1'('#skF_4',k4_tmap_1(A_574,'#skF_3'))
      | ~ v2_pre_topc(A_573)
      | v2_struct_0(A_573)
      | ~ m1_pre_topc('#skF_3',A_573)
      | ~ l1_pre_topc(A_573)
      | r1_tarski('#skF_4',k4_tmap_1(A_574,'#skF_3'))
      | ~ v1_funct_1(k4_tmap_1(A_574,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_574,'#skF_3'))
      | u1_struct_0(A_574) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_574)
      | ~ l1_pre_topc(A_574)
      | ~ v2_pre_topc(A_574)
      | v2_struct_0(A_574) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_133,c_7384])).

tff(c_7522,plain,(
    ! [A_574] :
      ( k1_funct_1('#skF_4','#skF_1'('#skF_4',k4_tmap_1(A_574,'#skF_3'))) != '#skF_1'('#skF_4',k4_tmap_1(A_574,'#skF_3'))
      | r1_tarski('#skF_4',k4_tmap_1(A_574,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(k4_tmap_1(A_574,'#skF_3')))
      | ~ v1_funct_1(k4_tmap_1(A_574,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_574,'#skF_3'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ v2_pre_topc(A_574)
      | v2_struct_0(A_574)
      | ~ m1_pre_topc('#skF_3',A_574)
      | ~ l1_pre_topc(A_574)
      | r1_tarski('#skF_4',k4_tmap_1(A_574,'#skF_3'))
      | ~ v1_funct_1(k4_tmap_1(A_574,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_574,'#skF_3'))
      | u1_struct_0(A_574) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_574)
      | ~ l1_pre_topc(A_574)
      | ~ v2_pre_topc(A_574)
      | v2_struct_0(A_574) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7513,c_32])).

tff(c_7534,plain,(
    ! [A_575] :
      ( k1_funct_1('#skF_4','#skF_1'('#skF_4',k4_tmap_1(A_575,'#skF_3'))) != '#skF_1'('#skF_4',k4_tmap_1(A_575,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(k4_tmap_1(A_575,'#skF_3')))
      | r1_tarski('#skF_4',k4_tmap_1(A_575,'#skF_3'))
      | ~ v1_funct_1(k4_tmap_1(A_575,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_575,'#skF_3'))
      | u1_struct_0(A_575) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_575)
      | ~ l1_pre_topc(A_575)
      | ~ v2_pre_topc(A_575)
      | v2_struct_0(A_575) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_58,c_7522])).

tff(c_7556,plain,(
    ! [A_576] :
      ( k1_funct_1('#skF_4','#skF_1'('#skF_4',k4_tmap_1(A_576,'#skF_3'))) != '#skF_1'('#skF_4',k4_tmap_1(A_576,'#skF_3'))
      | r1_tarski('#skF_4',k4_tmap_1(A_576,'#skF_3'))
      | ~ v1_funct_1(k4_tmap_1(A_576,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_576,'#skF_3'))
      | u1_struct_0(A_576) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_576)
      | ~ l1_pre_topc(A_576)
      | ~ v2_pre_topc(A_576)
      | v2_struct_0(A_576) ) ),
    inference(resolution,[status(thm)],[c_7271,c_7534])).

tff(c_7586,plain,(
    ! [A_579] :
      ( r1_tarski('#skF_4',k4_tmap_1(A_579,'#skF_3'))
      | ~ v1_funct_1(k4_tmap_1(A_579,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_579,'#skF_3'))
      | u1_struct_0(A_579) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_579)
      | ~ l1_pre_topc(A_579)
      | ~ v2_pre_topc(A_579)
      | v2_struct_0(A_579) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7242,c_7556])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_7610,plain,(
    ! [A_579] :
      ( k4_tmap_1(A_579,'#skF_3') = '#skF_4'
      | ~ r1_tarski(k4_tmap_1(A_579,'#skF_3'),'#skF_4')
      | ~ v1_funct_1(k4_tmap_1(A_579,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_579,'#skF_3'))
      | u1_struct_0(A_579) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_579)
      | ~ l1_pre_topc(A_579)
      | ~ v2_pre_topc(A_579)
      | v2_struct_0(A_579) ) ),
    inference(resolution,[status(thm)],[c_7586,c_2])).

tff(c_8005,plain,(
    ! [A_649] :
      ( k4_tmap_1(A_649,'#skF_3') = '#skF_4'
      | ~ v1_funct_1(k4_tmap_1(A_649,'#skF_3'))
      | ~ v1_relat_1(k4_tmap_1(A_649,'#skF_3'))
      | u1_struct_0(A_649) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_649)
      | ~ l1_pre_topc(A_649)
      | ~ v2_pre_topc(A_649)
      | v2_struct_0(A_649) ) ),
    inference(resolution,[status(thm)],[c_7961,c_7610])).

tff(c_8011,plain,(
    ! [A_650] :
      ( k4_tmap_1(A_650,'#skF_3') = '#skF_4'
      | ~ v1_funct_1(k4_tmap_1(A_650,'#skF_3'))
      | u1_struct_0(A_650) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_650)
      | ~ l1_pre_topc(A_650)
      | ~ v2_pre_topc(A_650)
      | v2_struct_0(A_650) ) ),
    inference(resolution,[status(thm)],[c_6844,c_8005])).

tff(c_8017,plain,(
    ! [A_651] :
      ( k4_tmap_1(A_651,'#skF_3') = '#skF_4'
      | u1_struct_0(A_651) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_651)
      | ~ l1_pre_topc(A_651)
      | ~ v2_pre_topc(A_651)
      | v2_struct_0(A_651) ) ),
    inference(resolution,[status(thm)],[c_44,c_8011])).

tff(c_8020,plain,
    ( k4_tmap_1('#skF_2','#skF_3') = '#skF_4'
    | u1_struct_0('#skF_2') = k1_xboole_0
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_8017])).

tff(c_8023,plain,
    ( k4_tmap_1('#skF_2','#skF_3') = '#skF_4'
    | u1_struct_0('#skF_2') = k1_xboole_0
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_8020])).

tff(c_8024,plain,
    ( k4_tmap_1('#skF_2','#skF_3') = '#skF_4'
    | u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_8023])).

tff(c_8025,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8024])).

tff(c_8034,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8025,c_139])).

tff(c_8032,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8025,c_138])).

tff(c_18,plain,(
    ! [C_16,A_14] :
      ( k1_xboole_0 = C_16
      | ~ v1_funct_2(C_16,A_14,k1_xboole_0)
      | k1_xboole_0 = A_14
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8240,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k1_xboole_0)
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8032,c_18])).

tff(c_8262,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8034,c_8240])).

tff(c_8269,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8262])).

tff(c_8031,plain,(
    r2_funct_2(k1_relat_1('#skF_4'),k1_xboole_0,'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8025,c_189])).

tff(c_8272,plain,(
    r2_funct_2(k1_xboole_0,k1_xboole_0,'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8269,c_8031])).

tff(c_6833,plain,(
    ! [A_475] :
      ( m1_subset_1(k4_tmap_1(A_475,'#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(A_475))))
      | ~ m1_pre_topc('#skF_3',A_475)
      | ~ l1_pre_topc(A_475)
      | ~ v2_pre_topc(A_475)
      | v2_struct_0(A_475) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_6814])).

tff(c_8106,plain,
    ( m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k1_xboole_0)))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8025,c_6833])).

tff(c_8173,plain,
    ( m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k1_xboole_0)))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_8106])).

tff(c_8174,plain,(
    m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k1_xboole_0))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_8173])).

tff(c_8583,plain,(
    m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8269,c_8174])).

tff(c_8608,plain,
    ( v1_relat_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_8583,c_10])).

tff(c_8632,plain,(
    v1_relat_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_8608])).

tff(c_204,plain,(
    ! [A_100,B_101] :
      ( v1_funct_2(k4_tmap_1(A_100,B_101),u1_struct_0(B_101),u1_struct_0(A_100))
      | ~ m1_pre_topc(B_101,A_100)
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_207,plain,(
    ! [A_100] :
      ( v1_funct_2(k4_tmap_1(A_100,'#skF_3'),k1_relat_1('#skF_4'),u1_struct_0(A_100))
      | ~ m1_pre_topc('#skF_3',A_100)
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_204])).

tff(c_8115,plain,
    ( v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),k1_relat_1('#skF_4'),k1_xboole_0)
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8025,c_207])).

tff(c_8179,plain,
    ( v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),k1_relat_1('#skF_4'),k1_xboole_0)
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_8115])).

tff(c_8180,plain,(
    v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_8179])).

tff(c_8382,plain,(
    v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8269,c_8180])).

tff(c_28,plain,(
    ! [A_17,B_18,D_20] :
      ( r2_funct_2(A_17,B_18,D_20,D_20)
      | ~ m1_subset_1(D_20,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18)))
      | ~ v1_funct_2(D_20,A_17,B_18)
      | ~ v1_funct_1(D_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_8585,plain,
    ( r2_funct_2(k1_xboole_0,k1_xboole_0,k4_tmap_1('#skF_2','#skF_3'),k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_8583,c_28])).

tff(c_8611,plain,
    ( r2_funct_2(k1_xboole_0,k1_xboole_0,k4_tmap_1('#skF_2','#skF_3'),k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8382,c_8585])).

tff(c_9015,plain,(
    ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_8611])).

tff(c_9018,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_9015])).

tff(c_9021,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_9018])).

tff(c_9023,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_9021])).

tff(c_9025,plain,(
    v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_8611])).

tff(c_24,plain,(
    ! [B_15,C_16] :
      ( k1_relset_1(k1_xboole_0,B_15,C_16) = k1_xboole_0
      | ~ v1_funct_2(C_16,k1_xboole_0,B_15)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8594,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1('#skF_2','#skF_3')) = k1_xboole_0
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8583,c_24])).

tff(c_8621,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8382,c_8594])).

tff(c_8628,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1('#skF_2','#skF_3')) = k1_relat_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_8583,c_14])).

tff(c_8749,plain,(
    k1_relat_1(k4_tmap_1('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8621,c_8628])).

tff(c_8330,plain,(
    ! [B_27] :
      ( r2_hidden('#skF_1'('#skF_4',B_27),k1_xboole_0)
      | r1_tarski('#skF_4',B_27)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_27))
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8269,c_34])).

tff(c_9144,plain,(
    ! [B_697] :
      ( r2_hidden('#skF_1'('#skF_4',B_697),k1_xboole_0)
      | r1_tarski('#skF_4',B_697)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_697))
      | ~ v1_funct_1(B_697)
      | ~ v1_relat_1(B_697) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_58,c_8269,c_8330])).

tff(c_46,plain,(
    ! [B_35,A_33] :
      ( m1_subset_1(u1_struct_0(B_35),k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ m1_pre_topc(B_35,A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_147,plain,(
    ! [A_33] :
      ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ m1_pre_topc('#skF_3',A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_46])).

tff(c_8124,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8025,c_147])).

tff(c_8185,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_8124])).

tff(c_8273,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8269,c_8185])).

tff(c_8477,plain,(
    ! [A_3] :
      ( m1_subset_1(A_3,k1_xboole_0)
      | ~ r2_hidden(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8273,c_8])).

tff(c_9157,plain,(
    ! [B_698] :
      ( m1_subset_1('#skF_1'('#skF_4',B_698),k1_xboole_0)
      | r1_tarski('#skF_4',B_698)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_698))
      | ~ v1_funct_1(B_698)
      | ~ v1_relat_1(B_698) ) ),
    inference(resolution,[status(thm)],[c_9144,c_8477])).

tff(c_9163,plain,
    ( m1_subset_1('#skF_1'('#skF_4',k4_tmap_1('#skF_2','#skF_3')),k1_xboole_0)
    | r1_tarski('#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_relat_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8749,c_9157])).

tff(c_9172,plain,
    ( m1_subset_1('#skF_1'('#skF_4',k4_tmap_1('#skF_2','#skF_3')),k1_xboole_0)
    | r1_tarski('#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8632,c_9025,c_6,c_9163])).

tff(c_9175,plain,(
    r1_tarski('#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_9172])).

tff(c_9220,plain,
    ( k4_tmap_1('#skF_2','#skF_3') = '#skF_4'
    | ~ r1_tarski(k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_9175,c_2])).

tff(c_9221,plain,(
    ~ r1_tarski(k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_9220])).

tff(c_8795,plain,(
    ! [B_27] :
      ( r2_hidden('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),B_27),k1_xboole_0)
      | r1_tarski(k4_tmap_1('#skF_2','#skF_3'),B_27)
      | ~ r1_tarski(k1_relat_1(k4_tmap_1('#skF_2','#skF_3')),k1_relat_1(B_27))
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27)
      | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
      | ~ v1_relat_1(k4_tmap_1('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8749,c_34])).

tff(c_8859,plain,(
    ! [B_27] :
      ( r2_hidden('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),B_27),k1_xboole_0)
      | r1_tarski(k4_tmap_1('#skF_2','#skF_3'),B_27)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_27))
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27)
      | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8632,c_8749,c_8795])).

tff(c_10489,plain,(
    ! [B_27] :
      ( r2_hidden('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),B_27),k1_xboole_0)
      | r1_tarski(k4_tmap_1('#skF_2','#skF_3'),B_27)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_27))
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9025,c_8859])).

tff(c_10490,plain,(
    ! [B_762] :
      ( r2_hidden('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),B_762),k1_xboole_0)
      | r1_tarski(k4_tmap_1('#skF_2','#skF_3'),B_762)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_762))
      | ~ v1_funct_1(B_762)
      | ~ v1_relat_1(B_762) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9025,c_8859])).

tff(c_10501,plain,(
    ! [B_762] :
      ( m1_subset_1('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),B_762),k1_xboole_0)
      | r1_tarski(k4_tmap_1('#skF_2','#skF_3'),B_762)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_762))
      | ~ v1_funct_1(B_762)
      | ~ v1_relat_1(B_762) ) ),
    inference(resolution,[status(thm)],[c_10490,c_8477])).

tff(c_8302,plain,(
    u1_struct_0('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8269,c_133])).

tff(c_48,plain,(
    ! [A_36,B_40,C_42] :
      ( k1_funct_1(k4_tmap_1(A_36,B_40),C_42) = C_42
      | ~ r2_hidden(C_42,u1_struct_0(B_40))
      | ~ m1_subset_1(C_42,u1_struct_0(A_36))
      | ~ m1_pre_topc(B_40,A_36)
      | v2_struct_0(B_40)
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_8420,plain,(
    ! [A_36,C_42] :
      ( k1_funct_1(k4_tmap_1(A_36,'#skF_3'),C_42) = C_42
      | ~ r2_hidden(C_42,k1_xboole_0)
      | ~ m1_subset_1(C_42,u1_struct_0(A_36))
      | ~ m1_pre_topc('#skF_3',A_36)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36)
      | v2_struct_0(A_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8302,c_48])).

tff(c_9380,plain,(
    ! [A_709,C_710] :
      ( k1_funct_1(k4_tmap_1(A_709,'#skF_3'),C_710) = C_710
      | ~ r2_hidden(C_710,k1_xboole_0)
      | ~ m1_subset_1(C_710,u1_struct_0(A_709))
      | ~ m1_pre_topc('#skF_3',A_709)
      | ~ l1_pre_topc(A_709)
      | ~ v2_pre_topc(A_709)
      | v2_struct_0(A_709) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_8420])).

tff(c_9392,plain,(
    ! [C_710] :
      ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),C_710) = C_710
      | ~ r2_hidden(C_710,k1_xboole_0)
      | ~ m1_subset_1(C_710,k1_xboole_0)
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8025,c_9380])).

tff(c_9397,plain,(
    ! [C_710] :
      ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),C_710) = C_710
      | ~ r2_hidden(C_710,k1_xboole_0)
      | ~ m1_subset_1(C_710,k1_xboole_0)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_9392])).

tff(c_9398,plain,(
    ! [C_710] :
      ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),C_710) = C_710
      | ~ r2_hidden(C_710,k1_xboole_0)
      | ~ m1_subset_1(C_710,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_9397])).

tff(c_36,plain,(
    ! [B_27,C_30,A_21] :
      ( k1_funct_1(B_27,C_30) = k1_funct_1(A_21,C_30)
      | ~ r2_hidden(C_30,k1_relat_1(A_21))
      | ~ r1_tarski(A_21,B_27)
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_6952,plain,(
    ! [B_27,A_495,B_496] :
      ( k1_funct_1(B_27,'#skF_1'(A_495,B_496)) = k1_funct_1(A_495,'#skF_1'(A_495,B_496))
      | ~ r1_tarski(A_495,B_27)
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27)
      | r1_tarski(A_495,B_496)
      | ~ r1_tarski(k1_relat_1(A_495),k1_relat_1(B_496))
      | ~ v1_funct_1(B_496)
      | ~ v1_relat_1(B_496)
      | ~ v1_funct_1(A_495)
      | ~ v1_relat_1(A_495) ) ),
    inference(resolution,[status(thm)],[c_6942,c_36])).

tff(c_8327,plain,(
    ! [B_27,A_495] :
      ( k1_funct_1(B_27,'#skF_1'(A_495,'#skF_4')) = k1_funct_1(A_495,'#skF_1'(A_495,'#skF_4'))
      | ~ r1_tarski(A_495,B_27)
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27)
      | r1_tarski(A_495,'#skF_4')
      | ~ r1_tarski(k1_relat_1(A_495),k1_xboole_0)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_funct_1(A_495)
      | ~ v1_relat_1(A_495) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8269,c_6952])).

tff(c_11260,plain,(
    ! [B_792,A_793] :
      ( k1_funct_1(B_792,'#skF_1'(A_793,'#skF_4')) = k1_funct_1(A_793,'#skF_1'(A_793,'#skF_4'))
      | ~ r1_tarski(A_793,B_792)
      | ~ v1_funct_1(B_792)
      | ~ v1_relat_1(B_792)
      | r1_tarski(A_793,'#skF_4')
      | ~ r1_tarski(k1_relat_1(A_793),k1_xboole_0)
      | ~ v1_funct_1(A_793)
      | ~ v1_relat_1(A_793) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_58,c_8327])).

tff(c_11274,plain,(
    ! [B_792] :
      ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = k1_funct_1(B_792,'#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'))
      | ~ r1_tarski(k4_tmap_1('#skF_2','#skF_3'),B_792)
      | ~ v1_funct_1(B_792)
      | ~ v1_relat_1(B_792)
      | r1_tarski(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
      | ~ v1_relat_1(k4_tmap_1('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8749,c_11260])).

tff(c_11288,plain,(
    ! [B_792] :
      ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = k1_funct_1(B_792,'#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'))
      | ~ r1_tarski(k4_tmap_1('#skF_2','#skF_3'),B_792)
      | ~ v1_funct_1(B_792)
      | ~ v1_relat_1(B_792)
      | r1_tarski(k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8632,c_9025,c_6,c_11274])).

tff(c_11402,plain,(
    ! [B_796] :
      ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = k1_funct_1(B_796,'#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'))
      | ~ r1_tarski(k4_tmap_1('#skF_2','#skF_3'),B_796)
      | ~ v1_funct_1(B_796)
      | ~ v1_relat_1(B_796) ) ),
    inference(negUnitSimplification,[status(thm)],[c_9221,c_11288])).

tff(c_11447,plain,(
    ! [B_796] :
      ( k1_funct_1(B_796,'#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) != k1_funct_1('#skF_4','#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'))
      | r1_tarski(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
      | ~ r1_tarski(k1_relat_1(k4_tmap_1('#skF_2','#skF_3')),k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
      | ~ v1_relat_1(k4_tmap_1('#skF_2','#skF_3'))
      | ~ r1_tarski(k4_tmap_1('#skF_2','#skF_3'),B_796)
      | ~ v1_funct_1(B_796)
      | ~ v1_relat_1(B_796) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11402,c_32])).

tff(c_11523,plain,(
    ! [B_796] :
      ( k1_funct_1(B_796,'#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) != k1_funct_1('#skF_4','#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'))
      | r1_tarski(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
      | ~ r1_tarski(k4_tmap_1('#skF_2','#skF_3'),B_796)
      | ~ v1_funct_1(B_796)
      | ~ v1_relat_1(B_796) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8632,c_9025,c_78,c_58,c_6,c_8269,c_8749,c_11447])).

tff(c_11557,plain,(
    ! [B_797] :
      ( k1_funct_1(B_797,'#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) != k1_funct_1('#skF_4','#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'))
      | ~ r1_tarski(k4_tmap_1('#skF_2','#skF_3'),B_797)
      | ~ v1_funct_1(B_797)
      | ~ v1_relat_1(B_797) ) ),
    inference(negUnitSimplification,[status(thm)],[c_9221,c_11523])).

tff(c_11587,plain,
    ( k1_funct_1('#skF_4','#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) != '#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | ~ r1_tarski(k4_tmap_1('#skF_2','#skF_3'),k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_relat_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ r2_hidden('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_xboole_0)
    | ~ m1_subset_1('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_9398,c_11557])).

tff(c_11616,plain,
    ( k1_funct_1('#skF_4','#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) != '#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | ~ r2_hidden('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_xboole_0)
    | ~ m1_subset_1('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8632,c_9025,c_6,c_11587])).

tff(c_11629,plain,(
    ~ m1_subset_1('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_11616])).

tff(c_11632,plain,
    ( r1_tarski(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | ~ r1_tarski(k1_xboole_0,k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10501,c_11629])).

tff(c_11635,plain,(
    r1_tarski(k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_58,c_6,c_8269,c_11632])).

tff(c_11637,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9221,c_11635])).

tff(c_11638,plain,
    ( ~ r2_hidden('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_xboole_0)
    | k1_funct_1('#skF_4','#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) != '#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_11616])).

tff(c_11870,plain,(
    k1_funct_1('#skF_4','#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) != '#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_11638])).

tff(c_11639,plain,(
    m1_subset_1('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_11616])).

tff(c_8300,plain,(
    ! [A_3,A_66] :
      ( m1_subset_1(A_3,u1_struct_0(A_66))
      | ~ r2_hidden(A_3,k1_xboole_0)
      | ~ m1_pre_topc('#skF_3',A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8269,c_142])).

tff(c_9393,plain,(
    ! [A_66,A_3] :
      ( k1_funct_1(k4_tmap_1(A_66,'#skF_3'),A_3) = A_3
      | ~ v2_pre_topc(A_66)
      | v2_struct_0(A_66)
      | ~ r2_hidden(A_3,k1_xboole_0)
      | ~ m1_pre_topc('#skF_3',A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_8300,c_9380])).

tff(c_11463,plain,(
    ! [B_796] :
      ( k1_funct_1(B_796,'#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
      | ~ r1_tarski(k4_tmap_1('#skF_2','#skF_3'),B_796)
      | ~ v1_funct_1(B_796)
      | ~ v1_relat_1(B_796)
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r2_hidden('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_xboole_0)
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9393,c_11402])).

tff(c_11536,plain,(
    ! [B_796] :
      ( k1_funct_1(B_796,'#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
      | ~ r1_tarski(k4_tmap_1('#skF_2','#skF_3'),B_796)
      | ~ v1_funct_1(B_796)
      | ~ v1_relat_1(B_796)
      | v2_struct_0('#skF_2')
      | ~ r2_hidden('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_66,c_11463])).

tff(c_11537,plain,(
    ! [B_796] :
      ( k1_funct_1(B_796,'#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
      | ~ r1_tarski(k4_tmap_1('#skF_2','#skF_3'),B_796)
      | ~ v1_funct_1(B_796)
      | ~ v1_relat_1(B_796)
      | ~ r2_hidden('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_11536])).

tff(c_11899,plain,(
    ~ r2_hidden('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_11537])).

tff(c_11902,plain,
    ( r1_tarski(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | ~ r1_tarski(k1_xboole_0,k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10489,c_11899])).

tff(c_11905,plain,(
    r1_tarski(k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_58,c_6,c_8269,c_11902])).

tff(c_11907,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9221,c_11905])).

tff(c_11909,plain,(
    r2_hidden('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_11537])).

tff(c_8028,plain,(
    ! [D_54] :
      ( k1_funct_1('#skF_4',D_54) = D_54
      | ~ r2_hidden(D_54,k1_relat_1('#skF_4'))
      | ~ m1_subset_1(D_54,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8025,c_135])).

tff(c_8874,plain,(
    ! [D_54] :
      ( k1_funct_1('#skF_4',D_54) = D_54
      | ~ r2_hidden(D_54,k1_xboole_0)
      | ~ m1_subset_1(D_54,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8269,c_8028])).

tff(c_11914,plain,
    ( k1_funct_1('#skF_4','#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | ~ m1_subset_1('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_11909,c_8874])).

tff(c_11921,plain,(
    k1_funct_1('#skF_4','#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11639,c_11914])).

tff(c_11923,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11870,c_11921])).

tff(c_11924,plain,(
    ~ r2_hidden('#skF_1'(k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_11638])).

tff(c_11928,plain,
    ( r1_tarski(k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | ~ r1_tarski(k1_xboole_0,k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10489,c_11924])).

tff(c_11931,plain,(
    r1_tarski(k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_58,c_6,c_8269,c_11928])).

tff(c_11933,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9221,c_11931])).

tff(c_11934,plain,(
    k4_tmap_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9220])).

tff(c_50,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_137,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_50])).

tff(c_8030,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),k1_xboole_0,k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8025,c_137])).

tff(c_8646,plain,(
    ~ r2_funct_2(k1_xboole_0,k1_xboole_0,k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8269,c_8030])).

tff(c_11941,plain,(
    ~ r2_funct_2(k1_xboole_0,k1_xboole_0,'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11934,c_8646])).

tff(c_11952,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8272,c_11941])).

tff(c_11954,plain,(
    ~ r1_tarski('#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_9172])).

tff(c_11953,plain,(
    m1_subset_1('#skF_1'('#skF_4',k4_tmap_1('#skF_2','#skF_3')),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_9172])).

tff(c_8074,plain,(
    ! [B_27] :
      ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_4',B_27)) = '#skF_1'('#skF_4',B_27)
      | ~ m1_subset_1('#skF_1'('#skF_4',B_27),k1_xboole_0)
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | r1_tarski('#skF_4',B_27)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_27))
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8025,c_6969])).

tff(c_8150,plain,(
    ! [B_27] :
      ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_4',B_27)) = '#skF_1'('#skF_4',B_27)
      | ~ m1_subset_1('#skF_1'('#skF_4',B_27),k1_xboole_0)
      | v2_struct_0('#skF_2')
      | r1_tarski('#skF_4',B_27)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_27))
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_8074])).

tff(c_8151,plain,(
    ! [B_27] :
      ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_4',B_27)) = '#skF_1'('#skF_4',B_27)
      | ~ m1_subset_1('#skF_1'('#skF_4',B_27),k1_xboole_0)
      | r1_tarski('#skF_4',B_27)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_27))
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_8150])).

tff(c_12635,plain,(
    ! [B_841] :
      ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_4',B_841)) = '#skF_1'('#skF_4',B_841)
      | ~ m1_subset_1('#skF_1'('#skF_4',B_841),k1_xboole_0)
      | r1_tarski('#skF_4',B_841)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_841))
      | ~ v1_funct_1(B_841)
      | ~ v1_relat_1(B_841) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8269,c_8151])).

tff(c_12651,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_12635,c_32])).

tff(c_12674,plain,
    ( k1_funct_1('#skF_4','#skF_1'('#skF_4',k4_tmap_1('#skF_2','#skF_3'))) != '#skF_1'('#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | r1_tarski('#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8632,c_9025,c_6,c_8749,c_11953,c_78,c_58,c_8632,c_9025,c_6,c_8269,c_8749,c_12651])).

tff(c_12675,plain,(
    k1_funct_1('#skF_4','#skF_1'('#skF_4',k4_tmap_1('#skF_2','#skF_3'))) != '#skF_1'('#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_11954,c_12674])).

tff(c_13196,plain,(
    ! [B_864] :
      ( k1_funct_1('#skF_4','#skF_1'('#skF_4',B_864)) = '#skF_1'('#skF_4',B_864)
      | ~ m1_subset_1('#skF_1'('#skF_4',B_864),k1_xboole_0)
      | r1_tarski('#skF_4',B_864)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_864))
      | ~ v1_funct_1(B_864)
      | ~ v1_relat_1(B_864) ) ),
    inference(resolution,[status(thm)],[c_9144,c_8874])).

tff(c_13208,plain,
    ( k1_funct_1('#skF_4','#skF_1'('#skF_4',k4_tmap_1('#skF_2','#skF_3'))) = '#skF_1'('#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_4',k4_tmap_1('#skF_2','#skF_3')),k1_xboole_0)
    | r1_tarski('#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_relat_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8749,c_13196])).

tff(c_13221,plain,
    ( k1_funct_1('#skF_4','#skF_1'('#skF_4',k4_tmap_1('#skF_2','#skF_3'))) = '#skF_1'('#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | r1_tarski('#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8632,c_9025,c_6,c_11953,c_13208])).

tff(c_13223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11954,c_12675,c_13221])).

tff(c_13224,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8262])).

tff(c_13229,plain,(
    r2_funct_2(k1_relat_1('#skF_4'),'#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13224,c_8031])).

tff(c_13225,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8262])).

tff(c_13282,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13224,c_13225])).

tff(c_13414,plain,(
    v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),k1_relat_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13224,c_8180])).

tff(c_13469,plain,(
    m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13224,c_8174])).

tff(c_13682,plain,(
    ! [C_895,A_896] :
      ( C_895 = '#skF_4'
      | ~ v1_funct_2(C_895,A_896,'#skF_4')
      | A_896 = '#skF_4'
      | ~ m1_subset_1(C_895,k1_zfmisc_1(k2_zfmisc_1(A_896,'#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13224,c_13224,c_13224,c_13224,c_18])).

tff(c_13688,plain,
    ( k4_tmap_1('#skF_2','#skF_3') = '#skF_4'
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),k1_relat_1('#skF_4'),'#skF_4')
    | k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_13469,c_13682])).

tff(c_13695,plain,
    ( k4_tmap_1('#skF_2','#skF_3') = '#skF_4'
    | k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13414,c_13688])).

tff(c_13696,plain,(
    k4_tmap_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_13282,c_13695])).

tff(c_13468,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13224,c_8030])).

tff(c_13706,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),'#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13696,c_13468])).

tff(c_13713,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13229,c_13706])).

tff(c_13714,plain,(
    k4_tmap_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8024])).

tff(c_13716,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13714,c_137])).

tff(c_13719,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_13716])).

tff(c_13720,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_13727,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13720,c_56])).

tff(c_13726,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13720,c_54])).

tff(c_13758,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),k1_xboole_0)
    | u1_struct_0('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_13726,c_18])).

tff(c_13776,plain,
    ( k1_xboole_0 = '#skF_4'
    | u1_struct_0('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13727,c_13758])).

tff(c_13789,plain,(
    u1_struct_0('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_13776])).

tff(c_13721,plain,(
    u1_struct_0('#skF_3') != k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_13793,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13789,c_13721])).

tff(c_13792,plain,(
    v1_funct_2('#skF_4',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13789,c_13727])).

tff(c_13790,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13789,c_13726])).

tff(c_13820,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_4',k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_13790,c_24])).

tff(c_13847,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13792,c_13820])).

tff(c_13722,plain,(
    k1_relset_1(u1_struct_0('#skF_3'),k1_xboole_0,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13720,c_106])).

tff(c_13791,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13789,c_13722])).

tff(c_13863,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13847,c_13791])).

tff(c_13864,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13793,c_13863])).

tff(c_13865,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_13776])).

tff(c_13783,plain,(
    ! [A_897,B_898,D_899] :
      ( r2_funct_2(A_897,B_898,D_899,D_899)
      | ~ m1_subset_1(D_899,k1_zfmisc_1(k2_zfmisc_1(A_897,B_898)))
      | ~ v1_funct_2(D_899,A_897,B_898)
      | ~ v1_funct_1(D_899) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_13785,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),k1_xboole_0,'#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),k1_xboole_0)
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_13726,c_13783])).

tff(c_13788,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),k1_xboole_0,'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_13727,c_13785])).

tff(c_13920,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),'#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13865,c_13788])).

tff(c_13866,plain,(
    u1_struct_0('#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_13776])).

tff(c_13891,plain,(
    u1_struct_0('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13865,c_13866])).

tff(c_13867,plain,(
    ! [A_900,B_901] :
      ( v1_funct_2(k4_tmap_1(A_900,B_901),u1_struct_0(B_901),u1_struct_0(A_900))
      | ~ m1_pre_topc(B_901,A_900)
      | ~ l1_pre_topc(A_900)
      | ~ v2_pre_topc(A_900)
      | v2_struct_0(A_900) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_13873,plain,(
    ! [B_901] :
      ( v1_funct_2(k4_tmap_1('#skF_2',B_901),u1_struct_0(B_901),k1_xboole_0)
      | ~ m1_pre_topc(B_901,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13720,c_13867])).

tff(c_13875,plain,(
    ! [B_901] :
      ( v1_funct_2(k4_tmap_1('#skF_2',B_901),u1_struct_0(B_901),k1_xboole_0)
      | ~ m1_pre_topc(B_901,'#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_13873])).

tff(c_13876,plain,(
    ! [B_901] :
      ( v1_funct_2(k4_tmap_1('#skF_2',B_901),u1_struct_0(B_901),k1_xboole_0)
      | ~ m1_pre_topc(B_901,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_13875])).

tff(c_13993,plain,(
    ! [B_901] :
      ( v1_funct_2(k4_tmap_1('#skF_2',B_901),u1_struct_0(B_901),'#skF_4')
      | ~ m1_pre_topc(B_901,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13865,c_13876])).

tff(c_13880,plain,(
    u1_struct_0('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13865,c_13720])).

tff(c_13951,plain,(
    ! [A_903,B_904] :
      ( m1_subset_1(k4_tmap_1(A_903,B_904),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_904),u1_struct_0(A_903))))
      | ~ m1_pre_topc(B_904,A_903)
      | ~ l1_pre_topc(A_903)
      | ~ v2_pre_topc(A_903)
      | v2_struct_0(A_903) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_13967,plain,(
    ! [B_904] :
      ( m1_subset_1(k4_tmap_1('#skF_2',B_904),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_904),'#skF_4')))
      | ~ m1_pre_topc(B_904,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13880,c_13951])).

tff(c_13975,plain,(
    ! [B_904] :
      ( m1_subset_1(k4_tmap_1('#skF_2',B_904),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_904),'#skF_4')))
      | ~ m1_pre_topc(B_904,'#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_13967])).

tff(c_13976,plain,(
    ! [B_904] :
      ( m1_subset_1(k4_tmap_1('#skF_2',B_904),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_904),'#skF_4')))
      | ~ m1_pre_topc(B_904,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_13975])).

tff(c_14075,plain,(
    ! [C_928,A_929] :
      ( C_928 = '#skF_4'
      | ~ v1_funct_2(C_928,A_929,'#skF_4')
      | A_929 = '#skF_4'
      | ~ m1_subset_1(C_928,k1_zfmisc_1(k2_zfmisc_1(A_929,'#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13865,c_13865,c_13865,c_13865,c_18])).

tff(c_14157,plain,(
    ! [B_947] :
      ( k4_tmap_1('#skF_2',B_947) = '#skF_4'
      | ~ v1_funct_2(k4_tmap_1('#skF_2',B_947),u1_struct_0(B_947),'#skF_4')
      | u1_struct_0(B_947) = '#skF_4'
      | ~ m1_pre_topc(B_947,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_13976,c_14075])).

tff(c_14166,plain,(
    ! [B_948] :
      ( k4_tmap_1('#skF_2',B_948) = '#skF_4'
      | u1_struct_0(B_948) = '#skF_4'
      | ~ m1_pre_topc(B_948,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_13993,c_14157])).

tff(c_14169,plain,
    ( k4_tmap_1('#skF_2','#skF_3') = '#skF_4'
    | u1_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_60,c_14166])).

tff(c_14172,plain,(
    k4_tmap_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_13891,c_14169])).

tff(c_13725,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),k1_xboole_0,k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13720,c_50])).

tff(c_13919,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13865,c_13725])).

tff(c_14179,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),'#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14172,c_13919])).

tff(c_14182,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13920,c_14179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:30:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.39/4.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.63/5.00  
% 12.63/5.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.63/5.00  %$ r2_funct_2 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k1_relset_1 > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 12.63/5.00  
% 12.63/5.00  %Foreground sorts:
% 12.63/5.00  
% 12.63/5.00  
% 12.63/5.00  %Background operators:
% 12.63/5.00  
% 12.63/5.00  
% 12.63/5.00  %Foreground operators:
% 12.63/5.00  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 12.63/5.00  tff(k4_tmap_1, type, k4_tmap_1: ($i * $i) > $i).
% 12.63/5.00  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.63/5.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.63/5.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.63/5.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.63/5.00  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.63/5.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.63/5.00  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.63/5.00  tff('#skF_2', type, '#skF_2': $i).
% 12.63/5.00  tff('#skF_3', type, '#skF_3': $i).
% 12.63/5.00  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 12.63/5.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.63/5.00  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 12.63/5.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.63/5.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.63/5.00  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.63/5.00  tff('#skF_4', type, '#skF_4': $i).
% 12.63/5.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.63/5.00  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 12.63/5.00  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 12.63/5.00  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.63/5.00  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.63/5.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.63/5.00  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 12.63/5.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.63/5.00  
% 12.63/5.04  tff(f_174, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, u1_struct_0(B)) => (D = k1_funct_1(C, D))))) => r2_funct_2(u1_struct_0(B), u1_struct_0(A), k4_tmap_1(A, B), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_tmap_1)).
% 12.63/5.04  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 12.63/5.04  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 12.63/5.04  tff(f_84, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 12.63/5.04  tff(f_117, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_funct_1(k4_tmap_1(A, B)) & v1_funct_2(k4_tmap_1(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(k4_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_tmap_1)).
% 12.63/5.04  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 12.63/5.04  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 12.63/5.04  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.63/5.04  tff(f_102, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, B) <=> (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_grfunc_1)).
% 12.63/5.04  tff(f_124, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 12.63/5.04  tff(f_37, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 12.63/5.04  tff(f_144, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, u1_struct_0(B)) => (k1_funct_1(k4_tmap_1(A, B), C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_tmap_1)).
% 12.63/5.04  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_174])).
% 12.63/5.04  tff(c_56, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_174])).
% 12.63/5.04  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_174])).
% 12.63/5.04  tff(c_102, plain, (![A_72, B_73, C_74]: (k1_relset_1(A_72, B_73, C_74)=k1_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.63/5.04  tff(c_106, plain, (k1_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_102])).
% 12.63/5.04  tff(c_126, plain, (![B_91, A_92, C_93]: (k1_xboole_0=B_91 | k1_relset_1(A_92, B_91, C_93)=A_92 | ~v1_funct_2(C_93, A_92, B_91) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_92, B_91))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 12.63/5.04  tff(c_129, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | k1_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4')=u1_struct_0('#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_126])).
% 12.63/5.04  tff(c_132, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | u1_struct_0('#skF_3')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_106, c_129])).
% 12.63/5.04  tff(c_133, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_132])).
% 12.63/5.04  tff(c_139, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_56])).
% 12.63/5.04  tff(c_138, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_54])).
% 12.63/5.04  tff(c_184, plain, (![A_94, B_95, D_96]: (r2_funct_2(A_94, B_95, D_96, D_96) | ~m1_subset_1(D_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))) | ~v1_funct_2(D_96, A_94, B_95) | ~v1_funct_1(D_96))), inference(cnfTransformation, [status(thm)], [f_84])).
% 12.63/5.04  tff(c_186, plain, (r2_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_138, c_184])).
% 12.63/5.04  tff(c_189, plain, (r2_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_139, c_186])).
% 12.63/5.04  tff(c_68, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 12.63/5.04  tff(c_66, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 12.63/5.04  tff(c_64, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 12.63/5.04  tff(c_60, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 12.63/5.04  tff(c_44, plain, (![A_31, B_32]: (v1_funct_1(k4_tmap_1(A_31, B_32)) | ~m1_pre_topc(B_32, A_31) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_117])).
% 12.63/5.04  tff(c_12, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.63/5.04  tff(c_6814, plain, (![A_475, B_476]: (m1_subset_1(k4_tmap_1(A_475, B_476), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_476), u1_struct_0(A_475)))) | ~m1_pre_topc(B_476, A_475) | ~l1_pre_topc(A_475) | ~v2_pre_topc(A_475) | v2_struct_0(A_475))), inference(cnfTransformation, [status(thm)], [f_117])).
% 12.63/5.04  tff(c_10, plain, (![B_8, A_6]: (v1_relat_1(B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_6)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.63/5.04  tff(c_6830, plain, (![A_475, B_476]: (v1_relat_1(k4_tmap_1(A_475, B_476)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(B_476), u1_struct_0(A_475))) | ~m1_pre_topc(B_476, A_475) | ~l1_pre_topc(A_475) | ~v2_pre_topc(A_475) | v2_struct_0(A_475))), inference(resolution, [status(thm)], [c_6814, c_10])).
% 12.63/5.04  tff(c_6844, plain, (![A_475, B_476]: (v1_relat_1(k4_tmap_1(A_475, B_476)) | ~m1_pre_topc(B_476, A_475) | ~l1_pre_topc(A_475) | ~v2_pre_topc(A_475) | v2_struct_0(A_475))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_6830])).
% 12.63/5.04  tff(c_72, plain, (![B_58, A_59]: (v1_relat_1(B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.63/5.04  tff(c_75, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_54, c_72])).
% 12.63/5.04  tff(c_78, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_75])).
% 12.63/5.04  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.63/5.04  tff(c_42, plain, (![A_31, B_32]: (v1_funct_2(k4_tmap_1(A_31, B_32), u1_struct_0(B_32), u1_struct_0(A_31)) | ~m1_pre_topc(B_32, A_31) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_117])).
% 12.63/5.04  tff(c_26, plain, (![B_15, A_14, C_16]: (k1_xboole_0=B_15 | k1_relset_1(A_14, B_15, C_16)=A_14 | ~v1_funct_2(C_16, A_14, B_15) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 12.63/5.04  tff(c_7004, plain, (![A_507, B_508]: (u1_struct_0(A_507)=k1_xboole_0 | k1_relset_1(u1_struct_0(B_508), u1_struct_0(A_507), k4_tmap_1(A_507, B_508))=u1_struct_0(B_508) | ~v1_funct_2(k4_tmap_1(A_507, B_508), u1_struct_0(B_508), u1_struct_0(A_507)) | ~m1_pre_topc(B_508, A_507) | ~l1_pre_topc(A_507) | ~v2_pre_topc(A_507) | v2_struct_0(A_507))), inference(resolution, [status(thm)], [c_6814, c_26])).
% 12.63/5.04  tff(c_7019, plain, (![A_509, B_510]: (u1_struct_0(A_509)=k1_xboole_0 | k1_relset_1(u1_struct_0(B_510), u1_struct_0(A_509), k4_tmap_1(A_509, B_510))=u1_struct_0(B_510) | ~m1_pre_topc(B_510, A_509) | ~l1_pre_topc(A_509) | ~v2_pre_topc(A_509) | v2_struct_0(A_509))), inference(resolution, [status(thm)], [c_42, c_7004])).
% 12.63/5.04  tff(c_14, plain, (![A_11, B_12, C_13]: (k1_relset_1(A_11, B_12, C_13)=k1_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.63/5.04  tff(c_6840, plain, (![B_476, A_475]: (k1_relset_1(u1_struct_0(B_476), u1_struct_0(A_475), k4_tmap_1(A_475, B_476))=k1_relat_1(k4_tmap_1(A_475, B_476)) | ~m1_pre_topc(B_476, A_475) | ~l1_pre_topc(A_475) | ~v2_pre_topc(A_475) | v2_struct_0(A_475))), inference(resolution, [status(thm)], [c_6814, c_14])).
% 12.63/5.04  tff(c_7064, plain, (![A_512, B_513]: (k1_relat_1(k4_tmap_1(A_512, B_513))=u1_struct_0(B_513) | ~m1_pre_topc(B_513, A_512) | ~l1_pre_topc(A_512) | ~v2_pre_topc(A_512) | v2_struct_0(A_512) | u1_struct_0(A_512)=k1_xboole_0 | ~m1_pre_topc(B_513, A_512) | ~l1_pre_topc(A_512) | ~v2_pre_topc(A_512) | v2_struct_0(A_512))), inference(superposition, [status(thm), theory('equality')], [c_7019, c_6840])).
% 12.63/5.04  tff(c_38, plain, (![A_21, B_27]: (r1_tarski(k1_relat_1(A_21), k1_relat_1(B_27)) | ~r1_tarski(A_21, B_27) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.63/5.04  tff(c_7318, plain, (![A_542, B_543, A_544]: (r1_tarski(k1_relat_1(A_542), u1_struct_0(B_543)) | ~r1_tarski(A_542, k4_tmap_1(A_544, B_543)) | ~v1_funct_1(k4_tmap_1(A_544, B_543)) | ~v1_relat_1(k4_tmap_1(A_544, B_543)) | ~v1_funct_1(A_542) | ~v1_relat_1(A_542) | ~m1_pre_topc(B_543, A_544) | ~l1_pre_topc(A_544) | ~v2_pre_topc(A_544) | v2_struct_0(A_544) | u1_struct_0(A_544)=k1_xboole_0 | ~m1_pre_topc(B_543, A_544) | ~l1_pre_topc(A_544) | ~v2_pre_topc(A_544) | v2_struct_0(A_544))), inference(superposition, [status(thm), theory('equality')], [c_7064, c_38])).
% 12.63/5.04  tff(c_7323, plain, (![A_545, B_546]: (r1_tarski(k1_relat_1(k4_tmap_1(A_545, B_546)), u1_struct_0(B_546)) | ~v1_funct_1(k4_tmap_1(A_545, B_546)) | ~v1_relat_1(k4_tmap_1(A_545, B_546)) | u1_struct_0(A_545)=k1_xboole_0 | ~m1_pre_topc(B_546, A_545) | ~l1_pre_topc(A_545) | ~v2_pre_topc(A_545) | v2_struct_0(A_545))), inference(resolution, [status(thm)], [c_6, c_7318])).
% 12.63/5.04  tff(c_7336, plain, (![A_545]: (r1_tarski(k1_relat_1(k4_tmap_1(A_545, '#skF_3')), k1_relat_1('#skF_4')) | ~v1_funct_1(k4_tmap_1(A_545, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_545, '#skF_3')) | u1_struct_0(A_545)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_545) | ~l1_pre_topc(A_545) | ~v2_pre_topc(A_545) | v2_struct_0(A_545))), inference(superposition, [status(thm), theory('equality')], [c_133, c_7323])).
% 12.63/5.04  tff(c_34, plain, (![A_21, B_27]: (r2_hidden('#skF_1'(A_21, B_27), k1_relat_1(A_21)) | r1_tarski(A_21, B_27) | ~r1_tarski(k1_relat_1(A_21), k1_relat_1(B_27)) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.63/5.04  tff(c_7714, plain, (![A_604, B_605, B_606]: (r2_hidden('#skF_1'(k4_tmap_1(A_604, B_605), B_606), u1_struct_0(B_605)) | r1_tarski(k4_tmap_1(A_604, B_605), B_606) | ~r1_tarski(k1_relat_1(k4_tmap_1(A_604, B_605)), k1_relat_1(B_606)) | ~v1_funct_1(B_606) | ~v1_relat_1(B_606) | ~v1_funct_1(k4_tmap_1(A_604, B_605)) | ~v1_relat_1(k4_tmap_1(A_604, B_605)) | ~m1_pre_topc(B_605, A_604) | ~l1_pre_topc(A_604) | ~v2_pre_topc(A_604) | v2_struct_0(A_604) | u1_struct_0(A_604)=k1_xboole_0 | ~m1_pre_topc(B_605, A_604) | ~l1_pre_topc(A_604) | ~v2_pre_topc(A_604) | v2_struct_0(A_604))), inference(superposition, [status(thm), theory('equality')], [c_7064, c_34])).
% 12.63/5.04  tff(c_90, plain, (![B_65, A_66]: (m1_subset_1(u1_struct_0(B_65), k1_zfmisc_1(u1_struct_0(A_66))) | ~m1_pre_topc(B_65, A_66) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_124])).
% 12.63/5.04  tff(c_8, plain, (![A_3, C_5, B_4]: (m1_subset_1(A_3, C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.63/5.04  tff(c_96, plain, (![A_3, A_66, B_65]: (m1_subset_1(A_3, u1_struct_0(A_66)) | ~r2_hidden(A_3, u1_struct_0(B_65)) | ~m1_pre_topc(B_65, A_66) | ~l1_pre_topc(A_66))), inference(resolution, [status(thm)], [c_90, c_8])).
% 12.63/5.04  tff(c_7727, plain, (![A_607, B_608, B_609, A_610]: (m1_subset_1('#skF_1'(k4_tmap_1(A_607, B_608), B_609), u1_struct_0(A_610)) | ~m1_pre_topc(B_608, A_610) | ~l1_pre_topc(A_610) | r1_tarski(k4_tmap_1(A_607, B_608), B_609) | ~r1_tarski(k1_relat_1(k4_tmap_1(A_607, B_608)), k1_relat_1(B_609)) | ~v1_funct_1(B_609) | ~v1_relat_1(B_609) | ~v1_funct_1(k4_tmap_1(A_607, B_608)) | ~v1_relat_1(k4_tmap_1(A_607, B_608)) | u1_struct_0(A_607)=k1_xboole_0 | ~m1_pre_topc(B_608, A_607) | ~l1_pre_topc(A_607) | ~v2_pre_topc(A_607) | v2_struct_0(A_607))), inference(resolution, [status(thm)], [c_7714, c_96])).
% 12.63/5.04  tff(c_7729, plain, (![A_545, A_610]: (m1_subset_1('#skF_1'(k4_tmap_1(A_545, '#skF_3'), '#skF_4'), u1_struct_0(A_610)) | ~m1_pre_topc('#skF_3', A_610) | ~l1_pre_topc(A_610) | r1_tarski(k4_tmap_1(A_545, '#skF_3'), '#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1(k4_tmap_1(A_545, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_545, '#skF_3')) | u1_struct_0(A_545)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_545) | ~l1_pre_topc(A_545) | ~v2_pre_topc(A_545) | v2_struct_0(A_545))), inference(resolution, [status(thm)], [c_7336, c_7727])).
% 12.63/5.04  tff(c_7746, plain, (![A_545, A_610]: (m1_subset_1('#skF_1'(k4_tmap_1(A_545, '#skF_3'), '#skF_4'), u1_struct_0(A_610)) | ~m1_pre_topc('#skF_3', A_610) | ~l1_pre_topc(A_610) | r1_tarski(k4_tmap_1(A_545, '#skF_3'), '#skF_4') | ~v1_funct_1(k4_tmap_1(A_545, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_545, '#skF_3')) | u1_struct_0(A_545)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_545) | ~l1_pre_topc(A_545) | ~v2_pre_topc(A_545) | v2_struct_0(A_545))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_58, c_7729])).
% 12.63/5.04  tff(c_7034, plain, (![A_509]: (u1_struct_0(A_509)=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_4'), u1_struct_0(A_509), k4_tmap_1(A_509, '#skF_3'))=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', A_509) | ~l1_pre_topc(A_509) | ~v2_pre_topc(A_509) | v2_struct_0(A_509))), inference(superposition, [status(thm), theory('equality')], [c_133, c_7019])).
% 12.63/5.04  tff(c_7043, plain, (![A_511]: (u1_struct_0(A_511)=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_4'), u1_struct_0(A_511), k4_tmap_1(A_511, '#skF_3'))=k1_relat_1('#skF_4') | ~m1_pre_topc('#skF_3', A_511) | ~l1_pre_topc(A_511) | ~v2_pre_topc(A_511) | v2_struct_0(A_511))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_7034])).
% 12.63/5.04  tff(c_6905, plain, (![B_489, A_490]: (k1_relset_1(u1_struct_0(B_489), u1_struct_0(A_490), k4_tmap_1(A_490, B_489))=k1_relat_1(k4_tmap_1(A_490, B_489)) | ~m1_pre_topc(B_489, A_490) | ~l1_pre_topc(A_490) | ~v2_pre_topc(A_490) | v2_struct_0(A_490))), inference(resolution, [status(thm)], [c_6814, c_14])).
% 12.63/5.04  tff(c_6914, plain, (![A_490]: (k1_relset_1(k1_relat_1('#skF_4'), u1_struct_0(A_490), k4_tmap_1(A_490, '#skF_3'))=k1_relat_1(k4_tmap_1(A_490, '#skF_3')) | ~m1_pre_topc('#skF_3', A_490) | ~l1_pre_topc(A_490) | ~v2_pre_topc(A_490) | v2_struct_0(A_490))), inference(superposition, [status(thm), theory('equality')], [c_133, c_6905])).
% 12.63/5.04  tff(c_7102, plain, (![A_518]: (k1_relat_1(k4_tmap_1(A_518, '#skF_3'))=k1_relat_1('#skF_4') | ~m1_pre_topc('#skF_3', A_518) | ~l1_pre_topc(A_518) | ~v2_pre_topc(A_518) | v2_struct_0(A_518) | u1_struct_0(A_518)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_518) | ~l1_pre_topc(A_518) | ~v2_pre_topc(A_518) | v2_struct_0(A_518))), inference(superposition, [status(thm), theory('equality')], [c_7043, c_6914])).
% 12.63/5.04  tff(c_7754, plain, (![A_613, B_614]: (r2_hidden('#skF_1'(k4_tmap_1(A_613, '#skF_3'), B_614), k1_relat_1('#skF_4')) | r1_tarski(k4_tmap_1(A_613, '#skF_3'), B_614) | ~r1_tarski(k1_relat_1(k4_tmap_1(A_613, '#skF_3')), k1_relat_1(B_614)) | ~v1_funct_1(B_614) | ~v1_relat_1(B_614) | ~v1_funct_1(k4_tmap_1(A_613, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_613, '#skF_3')) | ~m1_pre_topc('#skF_3', A_613) | ~l1_pre_topc(A_613) | ~v2_pre_topc(A_613) | v2_struct_0(A_613) | u1_struct_0(A_613)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_613) | ~l1_pre_topc(A_613) | ~v2_pre_topc(A_613) | v2_struct_0(A_613))), inference(superposition, [status(thm), theory('equality')], [c_7102, c_34])).
% 12.63/5.04  tff(c_52, plain, (![D_54]: (k1_funct_1('#skF_4', D_54)=D_54 | ~r2_hidden(D_54, u1_struct_0('#skF_3')) | ~m1_subset_1(D_54, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_174])).
% 12.63/5.04  tff(c_135, plain, (![D_54]: (k1_funct_1('#skF_4', D_54)=D_54 | ~r2_hidden(D_54, k1_relat_1('#skF_4')) | ~m1_subset_1(D_54, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_52])).
% 12.63/5.04  tff(c_7803, plain, (![A_627, B_628]: (k1_funct_1('#skF_4', '#skF_1'(k4_tmap_1(A_627, '#skF_3'), B_628))='#skF_1'(k4_tmap_1(A_627, '#skF_3'), B_628) | ~m1_subset_1('#skF_1'(k4_tmap_1(A_627, '#skF_3'), B_628), u1_struct_0('#skF_2')) | r1_tarski(k4_tmap_1(A_627, '#skF_3'), B_628) | ~r1_tarski(k1_relat_1(k4_tmap_1(A_627, '#skF_3')), k1_relat_1(B_628)) | ~v1_funct_1(B_628) | ~v1_relat_1(B_628) | ~v1_funct_1(k4_tmap_1(A_627, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_627, '#skF_3')) | u1_struct_0(A_627)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_627) | ~l1_pre_topc(A_627) | ~v2_pre_topc(A_627) | v2_struct_0(A_627))), inference(resolution, [status(thm)], [c_7754, c_135])).
% 12.63/5.04  tff(c_7806, plain, (![A_545]: (k1_funct_1('#skF_4', '#skF_1'(k4_tmap_1(A_545, '#skF_3'), '#skF_4'))='#skF_1'(k4_tmap_1(A_545, '#skF_3'), '#skF_4') | ~m1_subset_1('#skF_1'(k4_tmap_1(A_545, '#skF_3'), '#skF_4'), u1_struct_0('#skF_2')) | r1_tarski(k4_tmap_1(A_545, '#skF_3'), '#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1(k4_tmap_1(A_545, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_545, '#skF_3')) | u1_struct_0(A_545)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_545) | ~l1_pre_topc(A_545) | ~v2_pre_topc(A_545) | v2_struct_0(A_545))), inference(resolution, [status(thm)], [c_7336, c_7803])).
% 12.63/5.04  tff(c_7835, plain, (![A_629]: (k1_funct_1('#skF_4', '#skF_1'(k4_tmap_1(A_629, '#skF_3'), '#skF_4'))='#skF_1'(k4_tmap_1(A_629, '#skF_3'), '#skF_4') | ~m1_subset_1('#skF_1'(k4_tmap_1(A_629, '#skF_3'), '#skF_4'), u1_struct_0('#skF_2')) | r1_tarski(k4_tmap_1(A_629, '#skF_3'), '#skF_4') | ~v1_funct_1(k4_tmap_1(A_629, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_629, '#skF_3')) | u1_struct_0(A_629)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_629) | ~l1_pre_topc(A_629) | ~v2_pre_topc(A_629) | v2_struct_0(A_629))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_58, c_7806])).
% 12.63/5.04  tff(c_7839, plain, (![A_545]: (k1_funct_1('#skF_4', '#skF_1'(k4_tmap_1(A_545, '#skF_3'), '#skF_4'))='#skF_1'(k4_tmap_1(A_545, '#skF_3'), '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | r1_tarski(k4_tmap_1(A_545, '#skF_3'), '#skF_4') | ~v1_funct_1(k4_tmap_1(A_545, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_545, '#skF_3')) | u1_struct_0(A_545)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_545) | ~l1_pre_topc(A_545) | ~v2_pre_topc(A_545) | v2_struct_0(A_545))), inference(resolution, [status(thm)], [c_7746, c_7835])).
% 12.63/5.04  tff(c_7842, plain, (![A_545]: (k1_funct_1('#skF_4', '#skF_1'(k4_tmap_1(A_545, '#skF_3'), '#skF_4'))='#skF_1'(k4_tmap_1(A_545, '#skF_3'), '#skF_4') | r1_tarski(k4_tmap_1(A_545, '#skF_3'), '#skF_4') | ~v1_funct_1(k4_tmap_1(A_545, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_545, '#skF_3')) | u1_struct_0(A_545)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_545) | ~l1_pre_topc(A_545) | ~v2_pre_topc(A_545) | v2_struct_0(A_545))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_7839])).
% 12.63/5.04  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_174])).
% 12.63/5.04  tff(c_6959, plain, (![A_497, B_498, C_499]: (k1_funct_1(k4_tmap_1(A_497, B_498), C_499)=C_499 | ~r2_hidden(C_499, u1_struct_0(B_498)) | ~m1_subset_1(C_499, u1_struct_0(A_497)) | ~m1_pre_topc(B_498, A_497) | v2_struct_0(B_498) | ~l1_pre_topc(A_497) | ~v2_pre_topc(A_497) | v2_struct_0(A_497))), inference(cnfTransformation, [status(thm)], [f_144])).
% 12.63/5.04  tff(c_6961, plain, (![A_497, C_499]: (k1_funct_1(k4_tmap_1(A_497, '#skF_3'), C_499)=C_499 | ~r2_hidden(C_499, k1_relat_1('#skF_4')) | ~m1_subset_1(C_499, u1_struct_0(A_497)) | ~m1_pre_topc('#skF_3', A_497) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_497) | ~v2_pre_topc(A_497) | v2_struct_0(A_497))), inference(superposition, [status(thm), theory('equality')], [c_133, c_6959])).
% 12.63/5.04  tff(c_6962, plain, (![A_497, C_499]: (k1_funct_1(k4_tmap_1(A_497, '#skF_3'), C_499)=C_499 | ~r2_hidden(C_499, k1_relat_1('#skF_4')) | ~m1_subset_1(C_499, u1_struct_0(A_497)) | ~m1_pre_topc('#skF_3', A_497) | ~l1_pre_topc(A_497) | ~v2_pre_topc(A_497) | v2_struct_0(A_497))), inference(negUnitSimplification, [status(thm)], [c_62, c_6961])).
% 12.63/5.04  tff(c_7876, plain, (![A_636, A_637, B_638]: (k1_funct_1(k4_tmap_1(A_636, '#skF_3'), '#skF_1'(k4_tmap_1(A_637, '#skF_3'), B_638))='#skF_1'(k4_tmap_1(A_637, '#skF_3'), B_638) | ~m1_subset_1('#skF_1'(k4_tmap_1(A_637, '#skF_3'), B_638), u1_struct_0(A_636)) | ~m1_pre_topc('#skF_3', A_636) | ~l1_pre_topc(A_636) | ~v2_pre_topc(A_636) | v2_struct_0(A_636) | r1_tarski(k4_tmap_1(A_637, '#skF_3'), B_638) | ~r1_tarski(k1_relat_1(k4_tmap_1(A_637, '#skF_3')), k1_relat_1(B_638)) | ~v1_funct_1(B_638) | ~v1_relat_1(B_638) | ~v1_funct_1(k4_tmap_1(A_637, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_637, '#skF_3')) | u1_struct_0(A_637)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_637) | ~l1_pre_topc(A_637) | ~v2_pre_topc(A_637) | v2_struct_0(A_637))), inference(resolution, [status(thm)], [c_7754, c_6962])).
% 12.63/5.04  tff(c_7878, plain, (![A_610, A_545]: (k1_funct_1(k4_tmap_1(A_610, '#skF_3'), '#skF_1'(k4_tmap_1(A_545, '#skF_3'), '#skF_4'))='#skF_1'(k4_tmap_1(A_545, '#skF_3'), '#skF_4') | ~v2_pre_topc(A_610) | v2_struct_0(A_610) | ~r1_tarski(k1_relat_1(k4_tmap_1(A_545, '#skF_3')), k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~m1_pre_topc('#skF_3', A_610) | ~l1_pre_topc(A_610) | r1_tarski(k4_tmap_1(A_545, '#skF_3'), '#skF_4') | ~v1_funct_1(k4_tmap_1(A_545, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_545, '#skF_3')) | u1_struct_0(A_545)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_545) | ~l1_pre_topc(A_545) | ~v2_pre_topc(A_545) | v2_struct_0(A_545))), inference(resolution, [status(thm)], [c_7746, c_7876])).
% 12.63/5.04  tff(c_7885, plain, (![A_639, A_640]: (k1_funct_1(k4_tmap_1(A_639, '#skF_3'), '#skF_1'(k4_tmap_1(A_640, '#skF_3'), '#skF_4'))='#skF_1'(k4_tmap_1(A_640, '#skF_3'), '#skF_4') | ~v2_pre_topc(A_639) | v2_struct_0(A_639) | ~r1_tarski(k1_relat_1(k4_tmap_1(A_640, '#skF_3')), k1_relat_1('#skF_4')) | ~m1_pre_topc('#skF_3', A_639) | ~l1_pre_topc(A_639) | r1_tarski(k4_tmap_1(A_640, '#skF_3'), '#skF_4') | ~v1_funct_1(k4_tmap_1(A_640, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_640, '#skF_3')) | u1_struct_0(A_640)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_640) | ~l1_pre_topc(A_640) | ~v2_pre_topc(A_640) | v2_struct_0(A_640))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_58, c_7878])).
% 12.63/5.04  tff(c_7904, plain, (![A_641, A_642]: (k1_funct_1(k4_tmap_1(A_641, '#skF_3'), '#skF_1'(k4_tmap_1(A_642, '#skF_3'), '#skF_4'))='#skF_1'(k4_tmap_1(A_642, '#skF_3'), '#skF_4') | ~v2_pre_topc(A_641) | v2_struct_0(A_641) | ~m1_pre_topc('#skF_3', A_641) | ~l1_pre_topc(A_641) | r1_tarski(k4_tmap_1(A_642, '#skF_3'), '#skF_4') | ~v1_funct_1(k4_tmap_1(A_642, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_642, '#skF_3')) | u1_struct_0(A_642)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_642) | ~l1_pre_topc(A_642) | ~v2_pre_topc(A_642) | v2_struct_0(A_642))), inference(resolution, [status(thm)], [c_7336, c_7885])).
% 12.63/5.04  tff(c_32, plain, (![B_27, A_21]: (k1_funct_1(B_27, '#skF_1'(A_21, B_27))!=k1_funct_1(A_21, '#skF_1'(A_21, B_27)) | r1_tarski(A_21, B_27) | ~r1_tarski(k1_relat_1(A_21), k1_relat_1(B_27)) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.63/5.04  tff(c_7919, plain, (![A_642]: (k1_funct_1('#skF_4', '#skF_1'(k4_tmap_1(A_642, '#skF_3'), '#skF_4'))!='#skF_1'(k4_tmap_1(A_642, '#skF_3'), '#skF_4') | r1_tarski(k4_tmap_1(A_642, '#skF_3'), '#skF_4') | ~r1_tarski(k1_relat_1(k4_tmap_1(A_642, '#skF_3')), k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1(k4_tmap_1(A_642, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_642, '#skF_3')) | ~v2_pre_topc(A_642) | v2_struct_0(A_642) | ~m1_pre_topc('#skF_3', A_642) | ~l1_pre_topc(A_642) | r1_tarski(k4_tmap_1(A_642, '#skF_3'), '#skF_4') | ~v1_funct_1(k4_tmap_1(A_642, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_642, '#skF_3')) | u1_struct_0(A_642)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_642) | ~l1_pre_topc(A_642) | ~v2_pre_topc(A_642) | v2_struct_0(A_642))), inference(superposition, [status(thm), theory('equality')], [c_7904, c_32])).
% 12.63/5.04  tff(c_7934, plain, (![A_643]: (k1_funct_1('#skF_4', '#skF_1'(k4_tmap_1(A_643, '#skF_3'), '#skF_4'))!='#skF_1'(k4_tmap_1(A_643, '#skF_3'), '#skF_4') | ~r1_tarski(k1_relat_1(k4_tmap_1(A_643, '#skF_3')), k1_relat_1('#skF_4')) | r1_tarski(k4_tmap_1(A_643, '#skF_3'), '#skF_4') | ~v1_funct_1(k4_tmap_1(A_643, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_643, '#skF_3')) | u1_struct_0(A_643)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_643) | ~l1_pre_topc(A_643) | ~v2_pre_topc(A_643) | v2_struct_0(A_643))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_58, c_7919])).
% 12.63/5.04  tff(c_7956, plain, (![A_644]: (k1_funct_1('#skF_4', '#skF_1'(k4_tmap_1(A_644, '#skF_3'), '#skF_4'))!='#skF_1'(k4_tmap_1(A_644, '#skF_3'), '#skF_4') | r1_tarski(k4_tmap_1(A_644, '#skF_3'), '#skF_4') | ~v1_funct_1(k4_tmap_1(A_644, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_644, '#skF_3')) | u1_struct_0(A_644)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_644) | ~l1_pre_topc(A_644) | ~v2_pre_topc(A_644) | v2_struct_0(A_644))), inference(resolution, [status(thm)], [c_7336, c_7934])).
% 12.63/5.04  tff(c_7961, plain, (![A_645]: (r1_tarski(k4_tmap_1(A_645, '#skF_3'), '#skF_4') | ~v1_funct_1(k4_tmap_1(A_645, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_645, '#skF_3')) | u1_struct_0(A_645)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_645) | ~l1_pre_topc(A_645) | ~v2_pre_topc(A_645) | v2_struct_0(A_645))), inference(superposition, [status(thm), theory('equality')], [c_7842, c_7956])).
% 12.63/5.04  tff(c_6942, plain, (![A_495, B_496]: (r2_hidden('#skF_1'(A_495, B_496), k1_relat_1(A_495)) | r1_tarski(A_495, B_496) | ~r1_tarski(k1_relat_1(A_495), k1_relat_1(B_496)) | ~v1_funct_1(B_496) | ~v1_relat_1(B_496) | ~v1_funct_1(A_495) | ~v1_relat_1(A_495))), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.63/5.04  tff(c_142, plain, (![A_3, A_66]: (m1_subset_1(A_3, u1_struct_0(A_66)) | ~r2_hidden(A_3, k1_relat_1('#skF_4')) | ~m1_pre_topc('#skF_3', A_66) | ~l1_pre_topc(A_66))), inference(superposition, [status(thm), theory('equality')], [c_133, c_96])).
% 12.63/5.04  tff(c_6947, plain, (![B_496, A_66]: (m1_subset_1('#skF_1'('#skF_4', B_496), u1_struct_0(A_66)) | ~m1_pre_topc('#skF_3', A_66) | ~l1_pre_topc(A_66) | r1_tarski('#skF_4', B_496) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_496)) | ~v1_funct_1(B_496) | ~v1_relat_1(B_496) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_6942, c_142])).
% 12.63/5.04  tff(c_6955, plain, (![B_496, A_66]: (m1_subset_1('#skF_1'('#skF_4', B_496), u1_struct_0(A_66)) | ~m1_pre_topc('#skF_3', A_66) | ~l1_pre_topc(A_66) | r1_tarski('#skF_4', B_496) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_496)) | ~v1_funct_1(B_496) | ~v1_relat_1(B_496))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_58, c_6947])).
% 12.63/5.04  tff(c_7113, plain, (![A_518, A_66]: (m1_subset_1('#skF_1'('#skF_4', k4_tmap_1(A_518, '#skF_3')), u1_struct_0(A_66)) | ~m1_pre_topc('#skF_3', A_66) | ~l1_pre_topc(A_66) | r1_tarski('#skF_4', k4_tmap_1(A_518, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_funct_1(k4_tmap_1(A_518, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_518, '#skF_3')) | ~m1_pre_topc('#skF_3', A_518) | ~l1_pre_topc(A_518) | ~v2_pre_topc(A_518) | v2_struct_0(A_518) | u1_struct_0(A_518)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_518) | ~l1_pre_topc(A_518) | ~v2_pre_topc(A_518) | v2_struct_0(A_518))), inference(superposition, [status(thm), theory('equality')], [c_7102, c_6955])).
% 12.63/5.04  tff(c_7230, plain, (![A_533, A_534]: (m1_subset_1('#skF_1'('#skF_4', k4_tmap_1(A_533, '#skF_3')), u1_struct_0(A_534)) | ~m1_pre_topc('#skF_3', A_534) | ~l1_pre_topc(A_534) | r1_tarski('#skF_4', k4_tmap_1(A_533, '#skF_3')) | ~v1_funct_1(k4_tmap_1(A_533, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_533, '#skF_3')) | u1_struct_0(A_533)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_533) | ~l1_pre_topc(A_533) | ~v2_pre_topc(A_533) | v2_struct_0(A_533))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_7113])).
% 12.63/5.04  tff(c_6951, plain, (![B_496]: (k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_496))='#skF_1'('#skF_4', B_496) | ~m1_subset_1('#skF_1'('#skF_4', B_496), u1_struct_0('#skF_2')) | r1_tarski('#skF_4', B_496) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_496)) | ~v1_funct_1(B_496) | ~v1_relat_1(B_496) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_6942, c_135])).
% 12.63/5.04  tff(c_6958, plain, (![B_496]: (k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_496))='#skF_1'('#skF_4', B_496) | ~m1_subset_1('#skF_1'('#skF_4', B_496), u1_struct_0('#skF_2')) | r1_tarski('#skF_4', B_496) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_496)) | ~v1_funct_1(B_496) | ~v1_relat_1(B_496))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_58, c_6951])).
% 12.63/5.04  tff(c_7070, plain, (![A_512, B_513]: (k1_funct_1('#skF_4', '#skF_1'('#skF_4', k4_tmap_1(A_512, B_513)))='#skF_1'('#skF_4', k4_tmap_1(A_512, B_513)) | ~m1_subset_1('#skF_1'('#skF_4', k4_tmap_1(A_512, B_513)), u1_struct_0('#skF_2')) | r1_tarski('#skF_4', k4_tmap_1(A_512, B_513)) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(B_513)) | ~v1_funct_1(k4_tmap_1(A_512, B_513)) | ~v1_relat_1(k4_tmap_1(A_512, B_513)) | ~m1_pre_topc(B_513, A_512) | ~l1_pre_topc(A_512) | ~v2_pre_topc(A_512) | v2_struct_0(A_512) | u1_struct_0(A_512)=k1_xboole_0 | ~m1_pre_topc(B_513, A_512) | ~l1_pre_topc(A_512) | ~v2_pre_topc(A_512) | v2_struct_0(A_512))), inference(superposition, [status(thm), theory('equality')], [c_7064, c_6958])).
% 12.63/5.04  tff(c_7234, plain, (![A_533]: (k1_funct_1('#skF_4', '#skF_1'('#skF_4', k4_tmap_1(A_533, '#skF_3')))='#skF_1'('#skF_4', k4_tmap_1(A_533, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | r1_tarski('#skF_4', k4_tmap_1(A_533, '#skF_3')) | ~v1_funct_1(k4_tmap_1(A_533, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_533, '#skF_3')) | u1_struct_0(A_533)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_533) | ~l1_pre_topc(A_533) | ~v2_pre_topc(A_533) | v2_struct_0(A_533))), inference(resolution, [status(thm)], [c_7230, c_7070])).
% 12.63/5.04  tff(c_7242, plain, (![A_533]: (k1_funct_1('#skF_4', '#skF_1'('#skF_4', k4_tmap_1(A_533, '#skF_3')))='#skF_1'('#skF_4', k4_tmap_1(A_533, '#skF_3')) | r1_tarski('#skF_4', k4_tmap_1(A_533, '#skF_3')) | ~v1_funct_1(k4_tmap_1(A_533, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_533, '#skF_3')) | u1_struct_0(A_533)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_533) | ~l1_pre_topc(A_533) | ~v2_pre_topc(A_533) | v2_struct_0(A_533))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_6, c_133, c_7234])).
% 12.63/5.04  tff(c_7253, plain, (![B_536, B_537, A_538]: (r1_tarski(u1_struct_0(B_536), k1_relat_1(B_537)) | ~r1_tarski(k4_tmap_1(A_538, B_536), B_537) | ~v1_funct_1(B_537) | ~v1_relat_1(B_537) | ~v1_funct_1(k4_tmap_1(A_538, B_536)) | ~v1_relat_1(k4_tmap_1(A_538, B_536)) | ~m1_pre_topc(B_536, A_538) | ~l1_pre_topc(A_538) | ~v2_pre_topc(A_538) | v2_struct_0(A_538) | u1_struct_0(A_538)=k1_xboole_0 | ~m1_pre_topc(B_536, A_538) | ~l1_pre_topc(A_538) | ~v2_pre_topc(A_538) | v2_struct_0(A_538))), inference(superposition, [status(thm), theory('equality')], [c_7064, c_38])).
% 12.63/5.04  tff(c_7258, plain, (![B_539, A_540]: (r1_tarski(u1_struct_0(B_539), k1_relat_1(k4_tmap_1(A_540, B_539))) | ~v1_funct_1(k4_tmap_1(A_540, B_539)) | ~v1_relat_1(k4_tmap_1(A_540, B_539)) | u1_struct_0(A_540)=k1_xboole_0 | ~m1_pre_topc(B_539, A_540) | ~l1_pre_topc(A_540) | ~v2_pre_topc(A_540) | v2_struct_0(A_540))), inference(resolution, [status(thm)], [c_6, c_7253])).
% 12.63/5.04  tff(c_7271, plain, (![A_540]: (r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(k4_tmap_1(A_540, '#skF_3'))) | ~v1_funct_1(k4_tmap_1(A_540, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_540, '#skF_3')) | u1_struct_0(A_540)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_540) | ~l1_pre_topc(A_540) | ~v2_pre_topc(A_540) | v2_struct_0(A_540))), inference(superposition, [status(thm), theory('equality')], [c_133, c_7258])).
% 12.63/5.04  tff(c_7025, plain, (![A_509, B_510]: (k1_relat_1(k4_tmap_1(A_509, B_510))=u1_struct_0(B_510) | ~m1_pre_topc(B_510, A_509) | ~l1_pre_topc(A_509) | ~v2_pre_topc(A_509) | v2_struct_0(A_509) | u1_struct_0(A_509)=k1_xboole_0 | ~m1_pre_topc(B_510, A_509) | ~l1_pre_topc(A_509) | ~v2_pre_topc(A_509) | v2_struct_0(A_509))), inference(superposition, [status(thm), theory('equality')], [c_7019, c_6840])).
% 12.63/5.04  tff(c_6963, plain, (![A_500, C_501]: (k1_funct_1(k4_tmap_1(A_500, '#skF_3'), C_501)=C_501 | ~r2_hidden(C_501, k1_relat_1('#skF_4')) | ~m1_subset_1(C_501, u1_struct_0(A_500)) | ~m1_pre_topc('#skF_3', A_500) | ~l1_pre_topc(A_500) | ~v2_pre_topc(A_500) | v2_struct_0(A_500))), inference(negUnitSimplification, [status(thm)], [c_62, c_6961])).
% 12.63/5.04  tff(c_6966, plain, (![A_500, B_27]: (k1_funct_1(k4_tmap_1(A_500, '#skF_3'), '#skF_1'('#skF_4', B_27))='#skF_1'('#skF_4', B_27) | ~m1_subset_1('#skF_1'('#skF_4', B_27), u1_struct_0(A_500)) | ~m1_pre_topc('#skF_3', A_500) | ~l1_pre_topc(A_500) | ~v2_pre_topc(A_500) | v2_struct_0(A_500) | r1_tarski('#skF_4', B_27) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_27)) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_6963])).
% 12.63/5.04  tff(c_6969, plain, (![A_500, B_27]: (k1_funct_1(k4_tmap_1(A_500, '#skF_3'), '#skF_1'('#skF_4', B_27))='#skF_1'('#skF_4', B_27) | ~m1_subset_1('#skF_1'('#skF_4', B_27), u1_struct_0(A_500)) | ~m1_pre_topc('#skF_3', A_500) | ~l1_pre_topc(A_500) | ~v2_pre_topc(A_500) | v2_struct_0(A_500) | r1_tarski('#skF_4', B_27) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_27)) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_58, c_6966])).
% 12.63/5.04  tff(c_7377, plain, (![A_549, A_550]: (k1_funct_1(k4_tmap_1(A_549, '#skF_3'), '#skF_1'('#skF_4', k4_tmap_1(A_550, '#skF_3')))='#skF_1'('#skF_4', k4_tmap_1(A_550, '#skF_3')) | ~v2_pre_topc(A_549) | v2_struct_0(A_549) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(k4_tmap_1(A_550, '#skF_3'))) | ~m1_pre_topc('#skF_3', A_549) | ~l1_pre_topc(A_549) | r1_tarski('#skF_4', k4_tmap_1(A_550, '#skF_3')) | ~v1_funct_1(k4_tmap_1(A_550, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_550, '#skF_3')) | u1_struct_0(A_550)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_550) | ~l1_pre_topc(A_550) | ~v2_pre_topc(A_550) | v2_struct_0(A_550))), inference(resolution, [status(thm)], [c_7230, c_6969])).
% 12.63/5.04  tff(c_7384, plain, (![A_549, A_509]: (k1_funct_1(k4_tmap_1(A_549, '#skF_3'), '#skF_1'('#skF_4', k4_tmap_1(A_509, '#skF_3')))='#skF_1'('#skF_4', k4_tmap_1(A_509, '#skF_3')) | ~v2_pre_topc(A_549) | v2_struct_0(A_549) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', A_549) | ~l1_pre_topc(A_549) | r1_tarski('#skF_4', k4_tmap_1(A_509, '#skF_3')) | ~v1_funct_1(k4_tmap_1(A_509, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_509, '#skF_3')) | u1_struct_0(A_509)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_509) | ~l1_pre_topc(A_509) | ~v2_pre_topc(A_509) | v2_struct_0(A_509) | ~m1_pre_topc('#skF_3', A_509) | ~l1_pre_topc(A_509) | ~v2_pre_topc(A_509) | v2_struct_0(A_509) | u1_struct_0(A_509)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_509) | ~l1_pre_topc(A_509) | ~v2_pre_topc(A_509) | v2_struct_0(A_509))), inference(superposition, [status(thm), theory('equality')], [c_7025, c_7377])).
% 12.63/5.04  tff(c_7513, plain, (![A_573, A_574]: (k1_funct_1(k4_tmap_1(A_573, '#skF_3'), '#skF_1'('#skF_4', k4_tmap_1(A_574, '#skF_3')))='#skF_1'('#skF_4', k4_tmap_1(A_574, '#skF_3')) | ~v2_pre_topc(A_573) | v2_struct_0(A_573) | ~m1_pre_topc('#skF_3', A_573) | ~l1_pre_topc(A_573) | r1_tarski('#skF_4', k4_tmap_1(A_574, '#skF_3')) | ~v1_funct_1(k4_tmap_1(A_574, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_574, '#skF_3')) | u1_struct_0(A_574)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_574) | ~l1_pre_topc(A_574) | ~v2_pre_topc(A_574) | v2_struct_0(A_574))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_133, c_7384])).
% 12.63/5.04  tff(c_7522, plain, (![A_574]: (k1_funct_1('#skF_4', '#skF_1'('#skF_4', k4_tmap_1(A_574, '#skF_3')))!='#skF_1'('#skF_4', k4_tmap_1(A_574, '#skF_3')) | r1_tarski('#skF_4', k4_tmap_1(A_574, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(k4_tmap_1(A_574, '#skF_3'))) | ~v1_funct_1(k4_tmap_1(A_574, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_574, '#skF_3')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v2_pre_topc(A_574) | v2_struct_0(A_574) | ~m1_pre_topc('#skF_3', A_574) | ~l1_pre_topc(A_574) | r1_tarski('#skF_4', k4_tmap_1(A_574, '#skF_3')) | ~v1_funct_1(k4_tmap_1(A_574, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_574, '#skF_3')) | u1_struct_0(A_574)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_574) | ~l1_pre_topc(A_574) | ~v2_pre_topc(A_574) | v2_struct_0(A_574))), inference(superposition, [status(thm), theory('equality')], [c_7513, c_32])).
% 12.63/5.04  tff(c_7534, plain, (![A_575]: (k1_funct_1('#skF_4', '#skF_1'('#skF_4', k4_tmap_1(A_575, '#skF_3')))!='#skF_1'('#skF_4', k4_tmap_1(A_575, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(k4_tmap_1(A_575, '#skF_3'))) | r1_tarski('#skF_4', k4_tmap_1(A_575, '#skF_3')) | ~v1_funct_1(k4_tmap_1(A_575, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_575, '#skF_3')) | u1_struct_0(A_575)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_575) | ~l1_pre_topc(A_575) | ~v2_pre_topc(A_575) | v2_struct_0(A_575))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_58, c_7522])).
% 12.63/5.04  tff(c_7556, plain, (![A_576]: (k1_funct_1('#skF_4', '#skF_1'('#skF_4', k4_tmap_1(A_576, '#skF_3')))!='#skF_1'('#skF_4', k4_tmap_1(A_576, '#skF_3')) | r1_tarski('#skF_4', k4_tmap_1(A_576, '#skF_3')) | ~v1_funct_1(k4_tmap_1(A_576, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_576, '#skF_3')) | u1_struct_0(A_576)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_576) | ~l1_pre_topc(A_576) | ~v2_pre_topc(A_576) | v2_struct_0(A_576))), inference(resolution, [status(thm)], [c_7271, c_7534])).
% 12.63/5.04  tff(c_7586, plain, (![A_579]: (r1_tarski('#skF_4', k4_tmap_1(A_579, '#skF_3')) | ~v1_funct_1(k4_tmap_1(A_579, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_579, '#skF_3')) | u1_struct_0(A_579)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_579) | ~l1_pre_topc(A_579) | ~v2_pre_topc(A_579) | v2_struct_0(A_579))), inference(superposition, [status(thm), theory('equality')], [c_7242, c_7556])).
% 12.63/5.04  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.63/5.04  tff(c_7610, plain, (![A_579]: (k4_tmap_1(A_579, '#skF_3')='#skF_4' | ~r1_tarski(k4_tmap_1(A_579, '#skF_3'), '#skF_4') | ~v1_funct_1(k4_tmap_1(A_579, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_579, '#skF_3')) | u1_struct_0(A_579)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_579) | ~l1_pre_topc(A_579) | ~v2_pre_topc(A_579) | v2_struct_0(A_579))), inference(resolution, [status(thm)], [c_7586, c_2])).
% 12.63/5.04  tff(c_8005, plain, (![A_649]: (k4_tmap_1(A_649, '#skF_3')='#skF_4' | ~v1_funct_1(k4_tmap_1(A_649, '#skF_3')) | ~v1_relat_1(k4_tmap_1(A_649, '#skF_3')) | u1_struct_0(A_649)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_649) | ~l1_pre_topc(A_649) | ~v2_pre_topc(A_649) | v2_struct_0(A_649))), inference(resolution, [status(thm)], [c_7961, c_7610])).
% 12.63/5.04  tff(c_8011, plain, (![A_650]: (k4_tmap_1(A_650, '#skF_3')='#skF_4' | ~v1_funct_1(k4_tmap_1(A_650, '#skF_3')) | u1_struct_0(A_650)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_650) | ~l1_pre_topc(A_650) | ~v2_pre_topc(A_650) | v2_struct_0(A_650))), inference(resolution, [status(thm)], [c_6844, c_8005])).
% 12.63/5.04  tff(c_8017, plain, (![A_651]: (k4_tmap_1(A_651, '#skF_3')='#skF_4' | u1_struct_0(A_651)=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_651) | ~l1_pre_topc(A_651) | ~v2_pre_topc(A_651) | v2_struct_0(A_651))), inference(resolution, [status(thm)], [c_44, c_8011])).
% 12.63/5.04  tff(c_8020, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4' | u1_struct_0('#skF_2')=k1_xboole_0 | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_8017])).
% 12.63/5.04  tff(c_8023, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4' | u1_struct_0('#skF_2')=k1_xboole_0 | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_8020])).
% 12.63/5.04  tff(c_8024, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4' | u1_struct_0('#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_8023])).
% 12.63/5.04  tff(c_8025, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_8024])).
% 12.63/5.04  tff(c_8034, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8025, c_139])).
% 12.63/5.04  tff(c_8032, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8025, c_138])).
% 12.63/5.04  tff(c_18, plain, (![C_16, A_14]: (k1_xboole_0=C_16 | ~v1_funct_2(C_16, A_14, k1_xboole_0) | k1_xboole_0=A_14 | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 12.63/5.04  tff(c_8240, plain, (k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k1_xboole_0) | k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_8032, c_18])).
% 12.63/5.04  tff(c_8262, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8034, c_8240])).
% 12.63/5.04  tff(c_8269, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_8262])).
% 12.63/5.04  tff(c_8031, plain, (r2_funct_2(k1_relat_1('#skF_4'), k1_xboole_0, '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8025, c_189])).
% 12.63/5.04  tff(c_8272, plain, (r2_funct_2(k1_xboole_0, k1_xboole_0, '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8269, c_8031])).
% 12.63/5.04  tff(c_6833, plain, (![A_475]: (m1_subset_1(k4_tmap_1(A_475, '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(A_475)))) | ~m1_pre_topc('#skF_3', A_475) | ~l1_pre_topc(A_475) | ~v2_pre_topc(A_475) | v2_struct_0(A_475))), inference(superposition, [status(thm), theory('equality')], [c_133, c_6814])).
% 12.63/5.04  tff(c_8106, plain, (m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k1_xboole_0))) | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8025, c_6833])).
% 12.63/5.04  tff(c_8173, plain, (m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k1_xboole_0))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_8106])).
% 12.63/5.04  tff(c_8174, plain, (m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_68, c_8173])).
% 12.63/5.04  tff(c_8583, plain, (m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8269, c_8174])).
% 12.63/5.04  tff(c_8608, plain, (v1_relat_1(k4_tmap_1('#skF_2', '#skF_3')) | ~v1_relat_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_8583, c_10])).
% 12.63/5.04  tff(c_8632, plain, (v1_relat_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_8608])).
% 12.63/5.04  tff(c_204, plain, (![A_100, B_101]: (v1_funct_2(k4_tmap_1(A_100, B_101), u1_struct_0(B_101), u1_struct_0(A_100)) | ~m1_pre_topc(B_101, A_100) | ~l1_pre_topc(A_100) | ~v2_pre_topc(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_117])).
% 12.63/5.04  tff(c_207, plain, (![A_100]: (v1_funct_2(k4_tmap_1(A_100, '#skF_3'), k1_relat_1('#skF_4'), u1_struct_0(A_100)) | ~m1_pre_topc('#skF_3', A_100) | ~l1_pre_topc(A_100) | ~v2_pre_topc(A_100) | v2_struct_0(A_100))), inference(superposition, [status(thm), theory('equality')], [c_133, c_204])).
% 12.63/5.04  tff(c_8115, plain, (v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), k1_relat_1('#skF_4'), k1_xboole_0) | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8025, c_207])).
% 12.63/5.04  tff(c_8179, plain, (v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), k1_relat_1('#skF_4'), k1_xboole_0) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_8115])).
% 12.63/5.04  tff(c_8180, plain, (v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), k1_relat_1('#skF_4'), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_68, c_8179])).
% 12.63/5.04  tff(c_8382, plain, (v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8269, c_8180])).
% 12.63/5.04  tff(c_28, plain, (![A_17, B_18, D_20]: (r2_funct_2(A_17, B_18, D_20, D_20) | ~m1_subset_1(D_20, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))) | ~v1_funct_2(D_20, A_17, B_18) | ~v1_funct_1(D_20))), inference(cnfTransformation, [status(thm)], [f_84])).
% 12.63/5.04  tff(c_8585, plain, (r2_funct_2(k1_xboole_0, k1_xboole_0, k4_tmap_1('#skF_2', '#skF_3'), k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_8583, c_28])).
% 12.63/5.04  tff(c_8611, plain, (r2_funct_2(k1_xboole_0, k1_xboole_0, k4_tmap_1('#skF_2', '#skF_3'), k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8382, c_8585])).
% 12.63/5.04  tff(c_9015, plain, (~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_8611])).
% 12.63/5.04  tff(c_9018, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_9015])).
% 12.63/5.04  tff(c_9021, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_9018])).
% 12.63/5.04  tff(c_9023, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_9021])).
% 12.63/5.04  tff(c_9025, plain, (v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_8611])).
% 12.63/5.04  tff(c_24, plain, (![B_15, C_16]: (k1_relset_1(k1_xboole_0, B_15, C_16)=k1_xboole_0 | ~v1_funct_2(C_16, k1_xboole_0, B_15) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_15))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 12.63/5.04  tff(c_8594, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, k4_tmap_1('#skF_2', '#skF_3'))=k1_xboole_0 | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_8583, c_24])).
% 12.63/5.04  tff(c_8621, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, k4_tmap_1('#skF_2', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8382, c_8594])).
% 12.63/5.04  tff(c_8628, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, k4_tmap_1('#skF_2', '#skF_3'))=k1_relat_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_8583, c_14])).
% 12.63/5.04  tff(c_8749, plain, (k1_relat_1(k4_tmap_1('#skF_2', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8621, c_8628])).
% 12.63/5.04  tff(c_8330, plain, (![B_27]: (r2_hidden('#skF_1'('#skF_4', B_27), k1_xboole_0) | r1_tarski('#skF_4', B_27) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_27)) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8269, c_34])).
% 12.63/5.04  tff(c_9144, plain, (![B_697]: (r2_hidden('#skF_1'('#skF_4', B_697), k1_xboole_0) | r1_tarski('#skF_4', B_697) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_697)) | ~v1_funct_1(B_697) | ~v1_relat_1(B_697))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_58, c_8269, c_8330])).
% 12.63/5.04  tff(c_46, plain, (![B_35, A_33]: (m1_subset_1(u1_struct_0(B_35), k1_zfmisc_1(u1_struct_0(A_33))) | ~m1_pre_topc(B_35, A_33) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_124])).
% 12.63/5.04  tff(c_147, plain, (![A_33]: (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(u1_struct_0(A_33))) | ~m1_pre_topc('#skF_3', A_33) | ~l1_pre_topc(A_33))), inference(superposition, [status(thm), theory('equality')], [c_133, c_46])).
% 12.63/5.04  tff(c_8124, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(k1_xboole_0)) | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8025, c_147])).
% 12.63/5.04  tff(c_8185, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_8124])).
% 12.63/5.04  tff(c_8273, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8269, c_8185])).
% 12.63/5.04  tff(c_8477, plain, (![A_3]: (m1_subset_1(A_3, k1_xboole_0) | ~r2_hidden(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8273, c_8])).
% 12.63/5.04  tff(c_9157, plain, (![B_698]: (m1_subset_1('#skF_1'('#skF_4', B_698), k1_xboole_0) | r1_tarski('#skF_4', B_698) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_698)) | ~v1_funct_1(B_698) | ~v1_relat_1(B_698))), inference(resolution, [status(thm)], [c_9144, c_8477])).
% 12.63/5.04  tff(c_9163, plain, (m1_subset_1('#skF_1'('#skF_4', k4_tmap_1('#skF_2', '#skF_3')), k1_xboole_0) | r1_tarski('#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~v1_relat_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_8749, c_9157])).
% 12.63/5.04  tff(c_9172, plain, (m1_subset_1('#skF_1'('#skF_4', k4_tmap_1('#skF_2', '#skF_3')), k1_xboole_0) | r1_tarski('#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8632, c_9025, c_6, c_9163])).
% 12.63/5.04  tff(c_9175, plain, (r1_tarski('#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_9172])).
% 12.63/5.04  tff(c_9220, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4' | ~r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_9175, c_2])).
% 12.63/5.04  tff(c_9221, plain, (~r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_9220])).
% 12.63/5.04  tff(c_8795, plain, (![B_27]: (r2_hidden('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), B_27), k1_xboole_0) | r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), B_27) | ~r1_tarski(k1_relat_1(k4_tmap_1('#skF_2', '#skF_3')), k1_relat_1(B_27)) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~v1_relat_1(k4_tmap_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_8749, c_34])).
% 12.63/5.04  tff(c_8859, plain, (![B_27]: (r2_hidden('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), B_27), k1_xboole_0) | r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), B_27) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_27)) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_8632, c_8749, c_8795])).
% 12.63/5.04  tff(c_10489, plain, (![B_27]: (r2_hidden('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), B_27), k1_xboole_0) | r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), B_27) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_27)) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27))), inference(demodulation, [status(thm), theory('equality')], [c_9025, c_8859])).
% 12.63/5.04  tff(c_10490, plain, (![B_762]: (r2_hidden('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), B_762), k1_xboole_0) | r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), B_762) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_762)) | ~v1_funct_1(B_762) | ~v1_relat_1(B_762))), inference(demodulation, [status(thm), theory('equality')], [c_9025, c_8859])).
% 12.63/5.04  tff(c_10501, plain, (![B_762]: (m1_subset_1('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), B_762), k1_xboole_0) | r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), B_762) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_762)) | ~v1_funct_1(B_762) | ~v1_relat_1(B_762))), inference(resolution, [status(thm)], [c_10490, c_8477])).
% 12.63/5.04  tff(c_8302, plain, (u1_struct_0('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8269, c_133])).
% 12.63/5.04  tff(c_48, plain, (![A_36, B_40, C_42]: (k1_funct_1(k4_tmap_1(A_36, B_40), C_42)=C_42 | ~r2_hidden(C_42, u1_struct_0(B_40)) | ~m1_subset_1(C_42, u1_struct_0(A_36)) | ~m1_pre_topc(B_40, A_36) | v2_struct_0(B_40) | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_144])).
% 12.63/5.04  tff(c_8420, plain, (![A_36, C_42]: (k1_funct_1(k4_tmap_1(A_36, '#skF_3'), C_42)=C_42 | ~r2_hidden(C_42, k1_xboole_0) | ~m1_subset_1(C_42, u1_struct_0(A_36)) | ~m1_pre_topc('#skF_3', A_36) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36) | v2_struct_0(A_36))), inference(superposition, [status(thm), theory('equality')], [c_8302, c_48])).
% 12.63/5.04  tff(c_9380, plain, (![A_709, C_710]: (k1_funct_1(k4_tmap_1(A_709, '#skF_3'), C_710)=C_710 | ~r2_hidden(C_710, k1_xboole_0) | ~m1_subset_1(C_710, u1_struct_0(A_709)) | ~m1_pre_topc('#skF_3', A_709) | ~l1_pre_topc(A_709) | ~v2_pre_topc(A_709) | v2_struct_0(A_709))), inference(negUnitSimplification, [status(thm)], [c_62, c_8420])).
% 12.63/5.04  tff(c_9392, plain, (![C_710]: (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), C_710)=C_710 | ~r2_hidden(C_710, k1_xboole_0) | ~m1_subset_1(C_710, k1_xboole_0) | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_8025, c_9380])).
% 12.63/5.04  tff(c_9397, plain, (![C_710]: (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), C_710)=C_710 | ~r2_hidden(C_710, k1_xboole_0) | ~m1_subset_1(C_710, k1_xboole_0) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_9392])).
% 12.63/5.04  tff(c_9398, plain, (![C_710]: (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), C_710)=C_710 | ~r2_hidden(C_710, k1_xboole_0) | ~m1_subset_1(C_710, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_68, c_9397])).
% 12.63/5.04  tff(c_36, plain, (![B_27, C_30, A_21]: (k1_funct_1(B_27, C_30)=k1_funct_1(A_21, C_30) | ~r2_hidden(C_30, k1_relat_1(A_21)) | ~r1_tarski(A_21, B_27) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.63/5.04  tff(c_6952, plain, (![B_27, A_495, B_496]: (k1_funct_1(B_27, '#skF_1'(A_495, B_496))=k1_funct_1(A_495, '#skF_1'(A_495, B_496)) | ~r1_tarski(A_495, B_27) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27) | r1_tarski(A_495, B_496) | ~r1_tarski(k1_relat_1(A_495), k1_relat_1(B_496)) | ~v1_funct_1(B_496) | ~v1_relat_1(B_496) | ~v1_funct_1(A_495) | ~v1_relat_1(A_495))), inference(resolution, [status(thm)], [c_6942, c_36])).
% 12.63/5.04  tff(c_8327, plain, (![B_27, A_495]: (k1_funct_1(B_27, '#skF_1'(A_495, '#skF_4'))=k1_funct_1(A_495, '#skF_1'(A_495, '#skF_4')) | ~r1_tarski(A_495, B_27) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27) | r1_tarski(A_495, '#skF_4') | ~r1_tarski(k1_relat_1(A_495), k1_xboole_0) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1(A_495) | ~v1_relat_1(A_495))), inference(superposition, [status(thm), theory('equality')], [c_8269, c_6952])).
% 12.63/5.04  tff(c_11260, plain, (![B_792, A_793]: (k1_funct_1(B_792, '#skF_1'(A_793, '#skF_4'))=k1_funct_1(A_793, '#skF_1'(A_793, '#skF_4')) | ~r1_tarski(A_793, B_792) | ~v1_funct_1(B_792) | ~v1_relat_1(B_792) | r1_tarski(A_793, '#skF_4') | ~r1_tarski(k1_relat_1(A_793), k1_xboole_0) | ~v1_funct_1(A_793) | ~v1_relat_1(A_793))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_58, c_8327])).
% 12.63/5.04  tff(c_11274, plain, (![B_792]: (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))=k1_funct_1(B_792, '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')) | ~r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), B_792) | ~v1_funct_1(B_792) | ~v1_relat_1(B_792) | r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~v1_relat_1(k4_tmap_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_8749, c_11260])).
% 12.63/5.04  tff(c_11288, plain, (![B_792]: (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))=k1_funct_1(B_792, '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')) | ~r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), B_792) | ~v1_funct_1(B_792) | ~v1_relat_1(B_792) | r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8632, c_9025, c_6, c_11274])).
% 12.63/5.04  tff(c_11402, plain, (![B_796]: (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))=k1_funct_1(B_796, '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')) | ~r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), B_796) | ~v1_funct_1(B_796) | ~v1_relat_1(B_796))), inference(negUnitSimplification, [status(thm)], [c_9221, c_11288])).
% 12.63/5.04  tff(c_11447, plain, (![B_796]: (k1_funct_1(B_796, '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))!=k1_funct_1('#skF_4', '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')) | r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~r1_tarski(k1_relat_1(k4_tmap_1('#skF_2', '#skF_3')), k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~v1_relat_1(k4_tmap_1('#skF_2', '#skF_3')) | ~r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), B_796) | ~v1_funct_1(B_796) | ~v1_relat_1(B_796))), inference(superposition, [status(thm), theory('equality')], [c_11402, c_32])).
% 12.63/5.04  tff(c_11523, plain, (![B_796]: (k1_funct_1(B_796, '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))!=k1_funct_1('#skF_4', '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')) | r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), B_796) | ~v1_funct_1(B_796) | ~v1_relat_1(B_796))), inference(demodulation, [status(thm), theory('equality')], [c_8632, c_9025, c_78, c_58, c_6, c_8269, c_8749, c_11447])).
% 12.63/5.04  tff(c_11557, plain, (![B_797]: (k1_funct_1(B_797, '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))!=k1_funct_1('#skF_4', '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')) | ~r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), B_797) | ~v1_funct_1(B_797) | ~v1_relat_1(B_797))), inference(negUnitSimplification, [status(thm)], [c_9221, c_11523])).
% 12.63/5.04  tff(c_11587, plain, (k1_funct_1('#skF_4', '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))!='#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~v1_relat_1(k4_tmap_1('#skF_2', '#skF_3')) | ~r2_hidden('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), k1_xboole_0) | ~m1_subset_1('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9398, c_11557])).
% 12.63/5.04  tff(c_11616, plain, (k1_funct_1('#skF_4', '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))!='#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~r2_hidden('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), k1_xboole_0) | ~m1_subset_1('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8632, c_9025, c_6, c_11587])).
% 12.63/5.04  tff(c_11629, plain, (~m1_subset_1('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_11616])).
% 12.63/5.04  tff(c_11632, plain, (r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~r1_tarski(k1_xboole_0, k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10501, c_11629])).
% 12.63/5.04  tff(c_11635, plain, (r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_58, c_6, c_8269, c_11632])).
% 12.63/5.04  tff(c_11637, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9221, c_11635])).
% 12.63/5.04  tff(c_11638, plain, (~r2_hidden('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), k1_xboole_0) | k1_funct_1('#skF_4', '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))!='#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_11616])).
% 12.63/5.04  tff(c_11870, plain, (k1_funct_1('#skF_4', '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))!='#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_11638])).
% 12.63/5.04  tff(c_11639, plain, (m1_subset_1('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_11616])).
% 12.63/5.04  tff(c_8300, plain, (![A_3, A_66]: (m1_subset_1(A_3, u1_struct_0(A_66)) | ~r2_hidden(A_3, k1_xboole_0) | ~m1_pre_topc('#skF_3', A_66) | ~l1_pre_topc(A_66))), inference(demodulation, [status(thm), theory('equality')], [c_8269, c_142])).
% 12.63/5.04  tff(c_9393, plain, (![A_66, A_3]: (k1_funct_1(k4_tmap_1(A_66, '#skF_3'), A_3)=A_3 | ~v2_pre_topc(A_66) | v2_struct_0(A_66) | ~r2_hidden(A_3, k1_xboole_0) | ~m1_pre_topc('#skF_3', A_66) | ~l1_pre_topc(A_66))), inference(resolution, [status(thm)], [c_8300, c_9380])).
% 12.63/5.04  tff(c_11463, plain, (![B_796]: (k1_funct_1(B_796, '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), B_796) | ~v1_funct_1(B_796) | ~v1_relat_1(B_796) | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r2_hidden('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), k1_xboole_0) | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_9393, c_11402])).
% 12.63/5.04  tff(c_11536, plain, (![B_796]: (k1_funct_1(B_796, '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), B_796) | ~v1_funct_1(B_796) | ~v1_relat_1(B_796) | v2_struct_0('#skF_2') | ~r2_hidden('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_66, c_11463])).
% 12.63/5.04  tff(c_11537, plain, (![B_796]: (k1_funct_1(B_796, '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), B_796) | ~v1_funct_1(B_796) | ~v1_relat_1(B_796) | ~r2_hidden('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_68, c_11536])).
% 12.63/5.04  tff(c_11899, plain, (~r2_hidden('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_11537])).
% 12.63/5.04  tff(c_11902, plain, (r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~r1_tarski(k1_xboole_0, k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10489, c_11899])).
% 12.63/5.04  tff(c_11905, plain, (r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_58, c_6, c_8269, c_11902])).
% 12.63/5.04  tff(c_11907, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9221, c_11905])).
% 12.63/5.04  tff(c_11909, plain, (r2_hidden('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_11537])).
% 12.63/5.04  tff(c_8028, plain, (![D_54]: (k1_funct_1('#skF_4', D_54)=D_54 | ~r2_hidden(D_54, k1_relat_1('#skF_4')) | ~m1_subset_1(D_54, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8025, c_135])).
% 12.63/5.04  tff(c_8874, plain, (![D_54]: (k1_funct_1('#skF_4', D_54)=D_54 | ~r2_hidden(D_54, k1_xboole_0) | ~m1_subset_1(D_54, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8269, c_8028])).
% 12.63/5.04  tff(c_11914, plain, (k1_funct_1('#skF_4', '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~m1_subset_1('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), k1_xboole_0)), inference(resolution, [status(thm)], [c_11909, c_8874])).
% 12.63/5.04  tff(c_11921, plain, (k1_funct_1('#skF_4', '#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11639, c_11914])).
% 12.63/5.04  tff(c_11923, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11870, c_11921])).
% 12.63/5.04  tff(c_11924, plain, (~r2_hidden('#skF_1'(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_11638])).
% 12.63/5.04  tff(c_11928, plain, (r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~r1_tarski(k1_xboole_0, k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10489, c_11924])).
% 12.63/5.04  tff(c_11931, plain, (r1_tarski(k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_58, c_6, c_8269, c_11928])).
% 12.63/5.04  tff(c_11933, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9221, c_11931])).
% 12.63/5.04  tff(c_11934, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_9220])).
% 12.63/5.04  tff(c_50, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_174])).
% 12.63/5.04  tff(c_137, plain, (~r2_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_50])).
% 12.63/5.04  tff(c_8030, plain, (~r2_funct_2(k1_relat_1('#skF_4'), k1_xboole_0, k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8025, c_137])).
% 12.63/5.04  tff(c_8646, plain, (~r2_funct_2(k1_xboole_0, k1_xboole_0, k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8269, c_8030])).
% 12.63/5.04  tff(c_11941, plain, (~r2_funct_2(k1_xboole_0, k1_xboole_0, '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11934, c_8646])).
% 12.63/5.04  tff(c_11952, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8272, c_11941])).
% 12.63/5.04  tff(c_11954, plain, (~r1_tarski('#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_9172])).
% 12.63/5.04  tff(c_11953, plain, (m1_subset_1('#skF_1'('#skF_4', k4_tmap_1('#skF_2', '#skF_3')), k1_xboole_0)), inference(splitRight, [status(thm)], [c_9172])).
% 12.63/5.04  tff(c_8074, plain, (![B_27]: (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_4', B_27))='#skF_1'('#skF_4', B_27) | ~m1_subset_1('#skF_1'('#skF_4', B_27), k1_xboole_0) | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | r1_tarski('#skF_4', B_27) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_27)) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27))), inference(superposition, [status(thm), theory('equality')], [c_8025, c_6969])).
% 12.63/5.04  tff(c_8150, plain, (![B_27]: (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_4', B_27))='#skF_1'('#skF_4', B_27) | ~m1_subset_1('#skF_1'('#skF_4', B_27), k1_xboole_0) | v2_struct_0('#skF_2') | r1_tarski('#skF_4', B_27) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_27)) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_8074])).
% 12.63/5.04  tff(c_8151, plain, (![B_27]: (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_4', B_27))='#skF_1'('#skF_4', B_27) | ~m1_subset_1('#skF_1'('#skF_4', B_27), k1_xboole_0) | r1_tarski('#skF_4', B_27) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_27)) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27))), inference(negUnitSimplification, [status(thm)], [c_68, c_8150])).
% 12.63/5.04  tff(c_12635, plain, (![B_841]: (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_4', B_841))='#skF_1'('#skF_4', B_841) | ~m1_subset_1('#skF_1'('#skF_4', B_841), k1_xboole_0) | r1_tarski('#skF_4', B_841) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_841)) | ~v1_funct_1(B_841) | ~v1_relat_1(B_841))), inference(demodulation, [status(thm), theory('equality')], [c_8269, c_8151])).
% 12.63/5.04  tff(c_12651, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_4', k4_tmap_1('#skF_2', '#skF_3')))!='#skF_1'('#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | r1_tarski('#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(k4_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~v1_relat_1(k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~m1_subset_1('#skF_1'('#skF_4', k4_tmap_1('#skF_2', '#skF_3')), k1_xboole_0) | r1_tarski('#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~r1_tarski(k1_xboole_0, k1_relat_1(k4_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~v1_relat_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_12635, c_32])).
% 12.63/5.04  tff(c_12674, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_4', k4_tmap_1('#skF_2', '#skF_3')))!='#skF_1'('#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | r1_tarski('#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8632, c_9025, c_6, c_8749, c_11953, c_78, c_58, c_8632, c_9025, c_6, c_8269, c_8749, c_12651])).
% 12.63/5.04  tff(c_12675, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_4', k4_tmap_1('#skF_2', '#skF_3')))!='#skF_1'('#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_11954, c_12674])).
% 12.63/5.04  tff(c_13196, plain, (![B_864]: (k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_864))='#skF_1'('#skF_4', B_864) | ~m1_subset_1('#skF_1'('#skF_4', B_864), k1_xboole_0) | r1_tarski('#skF_4', B_864) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_864)) | ~v1_funct_1(B_864) | ~v1_relat_1(B_864))), inference(resolution, [status(thm)], [c_9144, c_8874])).
% 12.63/5.04  tff(c_13208, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_4', k4_tmap_1('#skF_2', '#skF_3')))='#skF_1'('#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_1'('#skF_4', k4_tmap_1('#skF_2', '#skF_3')), k1_xboole_0) | r1_tarski('#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~v1_relat_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_8749, c_13196])).
% 12.63/5.04  tff(c_13221, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_4', k4_tmap_1('#skF_2', '#skF_3')))='#skF_1'('#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | r1_tarski('#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8632, c_9025, c_6, c_11953, c_13208])).
% 12.63/5.04  tff(c_13223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11954, c_12675, c_13221])).
% 12.63/5.04  tff(c_13224, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_8262])).
% 12.63/5.04  tff(c_13229, plain, (r2_funct_2(k1_relat_1('#skF_4'), '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13224, c_8031])).
% 12.63/5.04  tff(c_13225, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_8262])).
% 12.63/5.04  tff(c_13282, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13224, c_13225])).
% 12.63/5.04  tff(c_13414, plain, (v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), k1_relat_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13224, c_8180])).
% 12.63/5.04  tff(c_13469, plain, (m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_13224, c_8174])).
% 12.63/5.04  tff(c_13682, plain, (![C_895, A_896]: (C_895='#skF_4' | ~v1_funct_2(C_895, A_896, '#skF_4') | A_896='#skF_4' | ~m1_subset_1(C_895, k1_zfmisc_1(k2_zfmisc_1(A_896, '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_13224, c_13224, c_13224, c_13224, c_18])).
% 12.63/5.04  tff(c_13688, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4' | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), k1_relat_1('#skF_4'), '#skF_4') | k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_13469, c_13682])).
% 12.63/5.04  tff(c_13695, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4' | k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13414, c_13688])).
% 12.63/5.04  tff(c_13696, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_13282, c_13695])).
% 12.63/5.04  tff(c_13468, plain, (~r2_funct_2(k1_relat_1('#skF_4'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13224, c_8030])).
% 12.63/5.04  tff(c_13706, plain, (~r2_funct_2(k1_relat_1('#skF_4'), '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13696, c_13468])).
% 12.63/5.04  tff(c_13713, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13229, c_13706])).
% 12.63/5.04  tff(c_13714, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_8024])).
% 12.63/5.04  tff(c_13716, plain, (~r2_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13714, c_137])).
% 12.63/5.04  tff(c_13719, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_189, c_13716])).
% 12.63/5.04  tff(c_13720, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_132])).
% 12.63/5.04  tff(c_13727, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_13720, c_56])).
% 12.63/5.04  tff(c_13726, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_13720, c_54])).
% 12.63/5.04  tff(c_13758, plain, (k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), k1_xboole_0) | u1_struct_0('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_13726, c_18])).
% 12.63/5.04  tff(c_13776, plain, (k1_xboole_0='#skF_4' | u1_struct_0('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_13727, c_13758])).
% 12.63/5.04  tff(c_13789, plain, (u1_struct_0('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_13776])).
% 12.63/5.04  tff(c_13721, plain, (u1_struct_0('#skF_3')!=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_132])).
% 12.63/5.04  tff(c_13793, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_13789, c_13721])).
% 12.63/5.04  tff(c_13792, plain, (v1_funct_2('#skF_4', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_13789, c_13727])).
% 12.63/5.04  tff(c_13790, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_13789, c_13726])).
% 12.63/5.04  tff(c_13820, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_4', k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_13790, c_24])).
% 12.63/5.04  tff(c_13847, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_13792, c_13820])).
% 12.63/5.04  tff(c_13722, plain, (k1_relset_1(u1_struct_0('#skF_3'), k1_xboole_0, '#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13720, c_106])).
% 12.63/5.04  tff(c_13791, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13789, c_13722])).
% 12.63/5.04  tff(c_13863, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_13847, c_13791])).
% 12.63/5.04  tff(c_13864, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13793, c_13863])).
% 12.63/5.04  tff(c_13865, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_13776])).
% 12.63/5.04  tff(c_13783, plain, (![A_897, B_898, D_899]: (r2_funct_2(A_897, B_898, D_899, D_899) | ~m1_subset_1(D_899, k1_zfmisc_1(k2_zfmisc_1(A_897, B_898))) | ~v1_funct_2(D_899, A_897, B_898) | ~v1_funct_1(D_899))), inference(cnfTransformation, [status(thm)], [f_84])).
% 12.63/5.04  tff(c_13785, plain, (r2_funct_2(u1_struct_0('#skF_3'), k1_xboole_0, '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), k1_xboole_0) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_13726, c_13783])).
% 12.63/5.04  tff(c_13788, plain, (r2_funct_2(u1_struct_0('#skF_3'), k1_xboole_0, '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_13727, c_13785])).
% 12.63/5.04  tff(c_13920, plain, (r2_funct_2(u1_struct_0('#skF_3'), '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13865, c_13788])).
% 12.63/5.04  tff(c_13866, plain, (u1_struct_0('#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_13776])).
% 12.63/5.04  tff(c_13891, plain, (u1_struct_0('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13865, c_13866])).
% 12.63/5.04  tff(c_13867, plain, (![A_900, B_901]: (v1_funct_2(k4_tmap_1(A_900, B_901), u1_struct_0(B_901), u1_struct_0(A_900)) | ~m1_pre_topc(B_901, A_900) | ~l1_pre_topc(A_900) | ~v2_pre_topc(A_900) | v2_struct_0(A_900))), inference(cnfTransformation, [status(thm)], [f_117])).
% 12.63/5.04  tff(c_13873, plain, (![B_901]: (v1_funct_2(k4_tmap_1('#skF_2', B_901), u1_struct_0(B_901), k1_xboole_0) | ~m1_pre_topc(B_901, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_13720, c_13867])).
% 12.63/5.04  tff(c_13875, plain, (![B_901]: (v1_funct_2(k4_tmap_1('#skF_2', B_901), u1_struct_0(B_901), k1_xboole_0) | ~m1_pre_topc(B_901, '#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_13873])).
% 12.63/5.04  tff(c_13876, plain, (![B_901]: (v1_funct_2(k4_tmap_1('#skF_2', B_901), u1_struct_0(B_901), k1_xboole_0) | ~m1_pre_topc(B_901, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_68, c_13875])).
% 12.63/5.04  tff(c_13993, plain, (![B_901]: (v1_funct_2(k4_tmap_1('#skF_2', B_901), u1_struct_0(B_901), '#skF_4') | ~m1_pre_topc(B_901, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_13865, c_13876])).
% 12.63/5.04  tff(c_13880, plain, (u1_struct_0('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13865, c_13720])).
% 12.63/5.04  tff(c_13951, plain, (![A_903, B_904]: (m1_subset_1(k4_tmap_1(A_903, B_904), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_904), u1_struct_0(A_903)))) | ~m1_pre_topc(B_904, A_903) | ~l1_pre_topc(A_903) | ~v2_pre_topc(A_903) | v2_struct_0(A_903))), inference(cnfTransformation, [status(thm)], [f_117])).
% 12.63/5.04  tff(c_13967, plain, (![B_904]: (m1_subset_1(k4_tmap_1('#skF_2', B_904), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_904), '#skF_4'))) | ~m1_pre_topc(B_904, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_13880, c_13951])).
% 12.63/5.04  tff(c_13975, plain, (![B_904]: (m1_subset_1(k4_tmap_1('#skF_2', B_904), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_904), '#skF_4'))) | ~m1_pre_topc(B_904, '#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_13967])).
% 12.63/5.04  tff(c_13976, plain, (![B_904]: (m1_subset_1(k4_tmap_1('#skF_2', B_904), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_904), '#skF_4'))) | ~m1_pre_topc(B_904, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_68, c_13975])).
% 12.63/5.04  tff(c_14075, plain, (![C_928, A_929]: (C_928='#skF_4' | ~v1_funct_2(C_928, A_929, '#skF_4') | A_929='#skF_4' | ~m1_subset_1(C_928, k1_zfmisc_1(k2_zfmisc_1(A_929, '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_13865, c_13865, c_13865, c_13865, c_18])).
% 12.63/5.04  tff(c_14157, plain, (![B_947]: (k4_tmap_1('#skF_2', B_947)='#skF_4' | ~v1_funct_2(k4_tmap_1('#skF_2', B_947), u1_struct_0(B_947), '#skF_4') | u1_struct_0(B_947)='#skF_4' | ~m1_pre_topc(B_947, '#skF_2'))), inference(resolution, [status(thm)], [c_13976, c_14075])).
% 12.63/5.04  tff(c_14166, plain, (![B_948]: (k4_tmap_1('#skF_2', B_948)='#skF_4' | u1_struct_0(B_948)='#skF_4' | ~m1_pre_topc(B_948, '#skF_2'))), inference(resolution, [status(thm)], [c_13993, c_14157])).
% 12.63/5.04  tff(c_14169, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4' | u1_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_60, c_14166])).
% 12.63/5.04  tff(c_14172, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_13891, c_14169])).
% 12.63/5.04  tff(c_13725, plain, (~r2_funct_2(u1_struct_0('#skF_3'), k1_xboole_0, k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13720, c_50])).
% 12.63/5.04  tff(c_13919, plain, (~r2_funct_2(u1_struct_0('#skF_3'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13865, c_13725])).
% 12.63/5.04  tff(c_14179, plain, (~r2_funct_2(u1_struct_0('#skF_3'), '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14172, c_13919])).
% 12.63/5.04  tff(c_14182, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13920, c_14179])).
% 12.63/5.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.63/5.04  
% 12.63/5.04  Inference rules
% 12.63/5.04  ----------------------
% 12.63/5.04  #Ref     : 8
% 12.63/5.04  #Sup     : 3041
% 12.63/5.04  #Fact    : 0
% 12.63/5.04  #Define  : 0
% 12.63/5.04  #Split   : 24
% 12.63/5.04  #Chain   : 0
% 12.63/5.04  #Close   : 0
% 12.63/5.04  
% 12.63/5.04  Ordering : KBO
% 12.63/5.04  
% 12.63/5.04  Simplification rules
% 12.63/5.04  ----------------------
% 12.63/5.04  #Subsume      : 822
% 12.63/5.04  #Demod        : 5394
% 12.63/5.04  #Tautology    : 986
% 12.63/5.04  #SimpNegUnit  : 518
% 12.63/5.04  #BackRed      : 252
% 12.63/5.04  
% 12.63/5.04  #Partial instantiations: 0
% 12.63/5.04  #Strategies tried      : 1
% 12.63/5.04  
% 12.63/5.04  Timing (in seconds)
% 12.63/5.04  ----------------------
% 12.63/5.04  Preprocessing        : 0.35
% 12.63/5.04  Parsing              : 0.19
% 12.63/5.04  CNF conversion       : 0.02
% 12.63/5.04  Main loop            : 3.85
% 12.63/5.04  Inferencing          : 1.01
% 12.63/5.04  Reduction            : 1.12
% 12.63/5.04  Demodulation         : 0.81
% 12.63/5.05  BG Simplification    : 0.11
% 12.63/5.05  Subsumption          : 1.44
% 12.63/5.05  Abstraction          : 0.15
% 12.63/5.05  MUC search           : 0.00
% 12.63/5.05  Cooper               : 0.00
% 12.63/5.05  Total                : 4.30
% 12.63/5.05  Index Insertion      : 0.00
% 12.63/5.05  Index Deletion       : 0.00
% 12.63/5.05  Index Matching       : 0.00
% 12.63/5.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
