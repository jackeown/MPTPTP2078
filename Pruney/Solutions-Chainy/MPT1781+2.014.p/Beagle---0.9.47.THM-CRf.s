%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:47 EST 2020

% Result     : Theorem 6.38s
% Output     : CNFRefutation 6.51s
% Verified   : 
% Statistics : Number of formulae       :  158 (1240 expanded)
%              Number of leaves         :   43 ( 440 expanded)
%              Depth                    :   28
%              Number of atoms          :  750 (6537 expanded)
%              Number of equality atoms :  114 (1278 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal term depth       :    4 (   1 average)

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

tff(f_193,negated_conjecture,(
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

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_62,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_2)).

tff(f_143,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_funct_1(k4_tmap_1(A,B))
        & v1_funct_2(k4_tmap_1(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(k4_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_tmap_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_32,axiom,(
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

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_128,axiom,(
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

tff(f_163,axiom,(
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

tff(f_112,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_70,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_42,plain,(
    ! [A_36] :
      ( l1_struct_0(A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_64,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_62,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_93,plain,(
    ! [A_77,B_78,C_79] :
      ( k1_relset_1(A_77,B_78,C_79) = k1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_97,plain,(
    k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_93])).

tff(c_117,plain,(
    ! [B_94,A_95,C_96] :
      ( k1_xboole_0 = B_94
      | k1_relset_1(A_95,B_94,C_96) = A_95
      | ~ v1_funct_2(C_96,A_95,B_94)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_95,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_120,plain,
    ( u1_struct_0('#skF_3') = k1_xboole_0
    | k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5') = u1_struct_0('#skF_4')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_60,c_117])).

tff(c_123,plain,
    ( u1_struct_0('#skF_3') = k1_xboole_0
    | u1_struct_0('#skF_4') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_97,c_120])).

tff(c_124,plain,(
    u1_struct_0('#skF_4') = k1_relat_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_123])).

tff(c_129,plain,(
    v1_funct_2('#skF_5',k1_relat_1('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_62])).

tff(c_128,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_60])).

tff(c_30,plain,(
    ! [D_22,A_14,B_15,C_16] :
      ( k1_funct_1(D_22,'#skF_1'(A_14,B_15,C_16,D_22)) != k1_funct_1(C_16,'#skF_1'(A_14,B_15,C_16,D_22))
      | r2_funct_2(A_14,B_15,C_16,D_22)
      | ~ m1_subset_1(D_22,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15)))
      | ~ v1_funct_2(D_22,A_14,B_15)
      | ~ v1_funct_1(D_22)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15)))
      | ~ v1_funct_2(C_16,A_14,B_15)
      | ~ v1_funct_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_601,plain,(
    ! [A_169,B_170,C_171] :
      ( r2_funct_2(A_169,B_170,C_171,C_171)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170)))
      | ~ v1_funct_2(C_171,A_169,B_170)
      | ~ v1_funct_1(C_171)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170)))
      | ~ v1_funct_2(C_171,A_169,B_170)
      | ~ v1_funct_1(C_171) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_30])).

tff(c_607,plain,
    ( r2_funct_2(k1_relat_1('#skF_5'),u1_struct_0('#skF_3'),'#skF_5','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_128,c_601])).

tff(c_612,plain,(
    r2_funct_2(k1_relat_1('#skF_5'),u1_struct_0('#skF_3'),'#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_129,c_128,c_607])).

tff(c_72,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_66,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_52,plain,(
    ! [A_45,B_46] :
      ( v1_funct_1(k4_tmap_1(A_45,B_46))
      | ~ m1_pre_topc(B_46,A_45)
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_195,plain,(
    ! [A_106,B_107] :
      ( m1_subset_1(k4_tmap_1(A_106,B_107),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_107),u1_struct_0(A_106))))
      | ~ m1_pre_topc(B_107,A_106)
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_12,plain,(
    ! [C_7,A_5,B_6] :
      ( v1_relat_1(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_217,plain,(
    ! [A_106,B_107] :
      ( v1_relat_1(k4_tmap_1(A_106,B_107))
      | ~ m1_pre_topc(B_107,A_106)
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(resolution,[status(thm)],[c_195,c_12])).

tff(c_91,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_12])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    ! [A_45,B_46] :
      ( v1_funct_2(k4_tmap_1(A_45,B_46),u1_struct_0(B_46),u1_struct_0(A_45))
      | ~ m1_pre_topc(B_46,A_45)
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_26,plain,(
    ! [B_12,A_11,C_13] :
      ( k1_xboole_0 = B_12
      | k1_relset_1(A_11,B_12,C_13) = A_11
      | ~ v1_funct_2(C_13,A_11,B_12)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_357,plain,(
    ! [A_136,B_137] :
      ( u1_struct_0(A_136) = k1_xboole_0
      | k1_relset_1(u1_struct_0(B_137),u1_struct_0(A_136),k4_tmap_1(A_136,B_137)) = u1_struct_0(B_137)
      | ~ v1_funct_2(k4_tmap_1(A_136,B_137),u1_struct_0(B_137),u1_struct_0(A_136))
      | ~ m1_pre_topc(B_137,A_136)
      | ~ l1_pre_topc(A_136)
      | ~ v2_pre_topc(A_136)
      | v2_struct_0(A_136) ) ),
    inference(resolution,[status(thm)],[c_195,c_26])).

tff(c_380,plain,(
    ! [A_140,B_141] :
      ( u1_struct_0(A_140) = k1_xboole_0
      | k1_relset_1(u1_struct_0(B_141),u1_struct_0(A_140),k4_tmap_1(A_140,B_141)) = u1_struct_0(B_141)
      | ~ m1_pre_topc(B_141,A_140)
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140) ) ),
    inference(resolution,[status(thm)],[c_50,c_357])).

tff(c_14,plain,(
    ! [A_8,B_9,C_10] :
      ( k1_relset_1(A_8,B_9,C_10) = k1_relat_1(C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_216,plain,(
    ! [B_107,A_106] :
      ( k1_relset_1(u1_struct_0(B_107),u1_struct_0(A_106),k4_tmap_1(A_106,B_107)) = k1_relat_1(k4_tmap_1(A_106,B_107))
      | ~ m1_pre_topc(B_107,A_106)
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(resolution,[status(thm)],[c_195,c_14])).

tff(c_425,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_380,c_216])).

tff(c_40,plain,(
    ! [A_26,B_32] :
      ( r1_tarski(k1_relat_1(A_26),k1_relat_1(B_32))
      | ~ r1_tarski(A_26,B_32)
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_649,plain,(
    ! [B_182,B_183,A_184] :
      ( r1_tarski(u1_struct_0(B_182),k1_relat_1(B_183))
      | ~ r1_tarski(k4_tmap_1(A_184,B_182),B_183)
      | ~ v1_funct_1(B_183)
      | ~ v1_relat_1(B_183)
      | ~ v1_funct_1(k4_tmap_1(A_184,B_182))
      | ~ v1_relat_1(k4_tmap_1(A_184,B_182))
      | ~ m1_pre_topc(B_182,A_184)
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184)
      | u1_struct_0(A_184) = k1_xboole_0
      | ~ m1_pre_topc(B_182,A_184)
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_40])).

tff(c_674,plain,(
    ! [B_188,A_189] :
      ( r1_tarski(u1_struct_0(B_188),k1_relat_1(k4_tmap_1(A_189,B_188)))
      | ~ v1_funct_1(k4_tmap_1(A_189,B_188))
      | ~ v1_relat_1(k4_tmap_1(A_189,B_188))
      | u1_struct_0(A_189) = k1_xboole_0
      | ~ m1_pre_topc(B_188,A_189)
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189)
      | v2_struct_0(A_189) ) ),
    inference(resolution,[status(thm)],[c_8,c_649])).

tff(c_692,plain,(
    ! [A_190] :
      ( r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(k4_tmap_1(A_190,'#skF_4')))
      | ~ v1_funct_1(k4_tmap_1(A_190,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_190,'#skF_4'))
      | u1_struct_0(A_190) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_190)
      | ~ l1_pre_topc(A_190)
      | ~ v2_pre_topc(A_190)
      | v2_struct_0(A_190) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_674])).

tff(c_301,plain,(
    ! [A_124,B_125] :
      ( r2_hidden('#skF_2'(A_124,B_125),k1_relat_1(A_124))
      | r1_tarski(A_124,B_125)
      | ~ r1_tarski(k1_relat_1(A_124),k1_relat_1(B_125))
      | ~ v1_funct_1(B_125)
      | ~ v1_relat_1(B_125)
      | ~ v1_funct_1(A_124)
      | ~ v1_relat_1(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,B_4)
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_315,plain,(
    ! [A_124,B_125] :
      ( m1_subset_1('#skF_2'(A_124,B_125),k1_relat_1(A_124))
      | r1_tarski(A_124,B_125)
      | ~ r1_tarski(k1_relat_1(A_124),k1_relat_1(B_125))
      | ~ v1_funct_1(B_125)
      | ~ v1_relat_1(B_125)
      | ~ v1_funct_1(A_124)
      | ~ v1_relat_1(A_124) ) ),
    inference(resolution,[status(thm)],[c_301,c_10])).

tff(c_704,plain,(
    ! [A_190] :
      ( m1_subset_1('#skF_2'('#skF_5',k4_tmap_1(A_190,'#skF_4')),k1_relat_1('#skF_5'))
      | r1_tarski('#skF_5',k4_tmap_1(A_190,'#skF_4'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_funct_1(k4_tmap_1(A_190,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_190,'#skF_4'))
      | u1_struct_0(A_190) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_190)
      | ~ l1_pre_topc(A_190)
      | ~ v2_pre_topc(A_190)
      | v2_struct_0(A_190) ) ),
    inference(resolution,[status(thm)],[c_692,c_315])).

tff(c_729,plain,(
    ! [A_190] :
      ( m1_subset_1('#skF_2'('#skF_5',k4_tmap_1(A_190,'#skF_4')),k1_relat_1('#skF_5'))
      | r1_tarski('#skF_5',k4_tmap_1(A_190,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_190,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_190,'#skF_4'))
      | u1_struct_0(A_190) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_190)
      | ~ l1_pre_topc(A_190)
      | ~ v2_pre_topc(A_190)
      | v2_struct_0(A_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_64,c_704])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_183,plain,(
    ! [C_101,A_102,B_103] :
      ( m1_subset_1(C_101,u1_struct_0(A_102))
      | ~ m1_subset_1(C_101,u1_struct_0(B_103))
      | ~ m1_pre_topc(B_103,A_102)
      | v2_struct_0(B_103)
      | ~ l1_pre_topc(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_185,plain,(
    ! [C_101,A_102] :
      ( m1_subset_1(C_101,u1_struct_0(A_102))
      | ~ m1_subset_1(C_101,k1_relat_1('#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_102)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_102)
      | v2_struct_0(A_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_183])).

tff(c_186,plain,(
    ! [C_101,A_102] :
      ( m1_subset_1(C_101,u1_struct_0(A_102))
      | ~ m1_subset_1(C_101,k1_relat_1('#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_102)
      | ~ l1_pre_topc(A_102)
      | v2_struct_0(A_102) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_185])).

tff(c_395,plain,(
    ! [A_140] :
      ( u1_struct_0(A_140) = k1_xboole_0
      | k1_relset_1(k1_relat_1('#skF_5'),u1_struct_0(A_140),k4_tmap_1(A_140,'#skF_4')) = u1_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_4',A_140)
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_380])).

tff(c_404,plain,(
    ! [A_142] :
      ( u1_struct_0(A_142) = k1_xboole_0
      | k1_relset_1(k1_relat_1('#skF_5'),u1_struct_0(A_142),k4_tmap_1(A_142,'#skF_4')) = k1_relat_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_142)
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_395])).

tff(c_265,plain,(
    ! [B_118,A_119] :
      ( k1_relset_1(u1_struct_0(B_118),u1_struct_0(A_119),k4_tmap_1(A_119,B_118)) = k1_relat_1(k4_tmap_1(A_119,B_118))
      | ~ m1_pre_topc(B_118,A_119)
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119)
      | v2_struct_0(A_119) ) ),
    inference(resolution,[status(thm)],[c_195,c_14])).

tff(c_274,plain,(
    ! [A_119] :
      ( k1_relset_1(k1_relat_1('#skF_5'),u1_struct_0(A_119),k4_tmap_1(A_119,'#skF_4')) = k1_relat_1(k4_tmap_1(A_119,'#skF_4'))
      | ~ m1_pre_topc('#skF_4',A_119)
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119)
      | v2_struct_0(A_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_265])).

tff(c_458,plain,(
    ! [A_145] :
      ( k1_relat_1(k4_tmap_1(A_145,'#skF_4')) = k1_relat_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_145)
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145)
      | v2_struct_0(A_145)
      | u1_struct_0(A_145) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_145)
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145)
      | v2_struct_0(A_145) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_274])).

tff(c_58,plain,(
    ! [D_65] :
      ( k1_funct_1('#skF_5',D_65) = D_65
      | ~ r2_hidden(D_65,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(D_65,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_126,plain,(
    ! [D_65] :
      ( k1_funct_1('#skF_5',D_65) = D_65
      | ~ r2_hidden(D_65,k1_relat_1('#skF_5'))
      | ~ m1_subset_1(D_65,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_58])).

tff(c_307,plain,(
    ! [B_125] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',B_125)) = '#skF_2'('#skF_5',B_125)
      | ~ m1_subset_1('#skF_2'('#skF_5',B_125),u1_struct_0('#skF_3'))
      | r1_tarski('#skF_5',B_125)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(B_125))
      | ~ v1_funct_1(B_125)
      | ~ v1_relat_1(B_125)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_301,c_126])).

tff(c_314,plain,(
    ! [B_125] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',B_125)) = '#skF_2'('#skF_5',B_125)
      | ~ m1_subset_1('#skF_2'('#skF_5',B_125),u1_struct_0('#skF_3'))
      | r1_tarski('#skF_5',B_125)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(B_125))
      | ~ v1_funct_1(B_125)
      | ~ v1_relat_1(B_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_64,c_307])).

tff(c_467,plain,(
    ! [A_145] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',k4_tmap_1(A_145,'#skF_4'))) = '#skF_2'('#skF_5',k4_tmap_1(A_145,'#skF_4'))
      | ~ m1_subset_1('#skF_2'('#skF_5',k4_tmap_1(A_145,'#skF_4')),u1_struct_0('#skF_3'))
      | r1_tarski('#skF_5',k4_tmap_1(A_145,'#skF_4'))
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1('#skF_5'))
      | ~ v1_funct_1(k4_tmap_1(A_145,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_145,'#skF_4'))
      | ~ m1_pre_topc('#skF_4',A_145)
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145)
      | v2_struct_0(A_145)
      | u1_struct_0(A_145) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_145)
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145)
      | v2_struct_0(A_145) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_314])).

tff(c_864,plain,(
    ! [A_219] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',k4_tmap_1(A_219,'#skF_4'))) = '#skF_2'('#skF_5',k4_tmap_1(A_219,'#skF_4'))
      | ~ m1_subset_1('#skF_2'('#skF_5',k4_tmap_1(A_219,'#skF_4')),u1_struct_0('#skF_3'))
      | r1_tarski('#skF_5',k4_tmap_1(A_219,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_219,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_219,'#skF_4'))
      | u1_struct_0(A_219) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_219)
      | ~ l1_pre_topc(A_219)
      | ~ v2_pre_topc(A_219)
      | v2_struct_0(A_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_467])).

tff(c_867,plain,(
    ! [A_219] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',k4_tmap_1(A_219,'#skF_4'))) = '#skF_2'('#skF_5',k4_tmap_1(A_219,'#skF_4'))
      | r1_tarski('#skF_5',k4_tmap_1(A_219,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_219,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_219,'#skF_4'))
      | u1_struct_0(A_219) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_219)
      | ~ l1_pre_topc(A_219)
      | ~ v2_pre_topc(A_219)
      | v2_struct_0(A_219)
      | ~ m1_subset_1('#skF_2'('#skF_5',k4_tmap_1(A_219,'#skF_4')),k1_relat_1('#skF_5'))
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_186,c_864])).

tff(c_870,plain,(
    ! [A_219] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',k4_tmap_1(A_219,'#skF_4'))) = '#skF_2'('#skF_5',k4_tmap_1(A_219,'#skF_4'))
      | r1_tarski('#skF_5',k4_tmap_1(A_219,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_219,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_219,'#skF_4'))
      | u1_struct_0(A_219) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_219)
      | ~ l1_pre_topc(A_219)
      | ~ v2_pre_topc(A_219)
      | v2_struct_0(A_219)
      | ~ m1_subset_1('#skF_2'('#skF_5',k4_tmap_1(A_219,'#skF_4')),k1_relat_1('#skF_5'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_867])).

tff(c_881,plain,(
    ! [A_222] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',k4_tmap_1(A_222,'#skF_4'))) = '#skF_2'('#skF_5',k4_tmap_1(A_222,'#skF_4'))
      | r1_tarski('#skF_5',k4_tmap_1(A_222,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_222,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_222,'#skF_4'))
      | u1_struct_0(A_222) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_222)
      | ~ l1_pre_topc(A_222)
      | ~ v2_pre_topc(A_222)
      | v2_struct_0(A_222)
      | ~ m1_subset_1('#skF_2'('#skF_5',k4_tmap_1(A_222,'#skF_4')),k1_relat_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_870])).

tff(c_885,plain,(
    ! [A_190] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',k4_tmap_1(A_190,'#skF_4'))) = '#skF_2'('#skF_5',k4_tmap_1(A_190,'#skF_4'))
      | r1_tarski('#skF_5',k4_tmap_1(A_190,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_190,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_190,'#skF_4'))
      | u1_struct_0(A_190) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_190)
      | ~ l1_pre_topc(A_190)
      | ~ v2_pre_topc(A_190)
      | v2_struct_0(A_190) ) ),
    inference(resolution,[status(thm)],[c_729,c_881])).

tff(c_687,plain,(
    ! [A_189] :
      ( r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(k4_tmap_1(A_189,'#skF_4')))
      | ~ v1_funct_1(k4_tmap_1(A_189,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_189,'#skF_4'))
      | u1_struct_0(A_189) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_189)
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189)
      | v2_struct_0(A_189) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_674])).

tff(c_36,plain,(
    ! [A_26,B_32] :
      ( r2_hidden('#skF_2'(A_26,B_32),k1_relat_1(A_26))
      | r1_tarski(A_26,B_32)
      | ~ r1_tarski(k1_relat_1(A_26),k1_relat_1(B_32))
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_325,plain,(
    ! [A_128,B_129,C_130] :
      ( k1_funct_1(k4_tmap_1(A_128,B_129),C_130) = C_130
      | ~ r2_hidden(C_130,u1_struct_0(B_129))
      | ~ m1_subset_1(C_130,u1_struct_0(A_128))
      | ~ m1_pre_topc(B_129,A_128)
      | v2_struct_0(B_129)
      | ~ l1_pre_topc(A_128)
      | ~ v2_pre_topc(A_128)
      | v2_struct_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_327,plain,(
    ! [A_128,C_130] :
      ( k1_funct_1(k4_tmap_1(A_128,'#skF_4'),C_130) = C_130
      | ~ r2_hidden(C_130,k1_relat_1('#skF_5'))
      | ~ m1_subset_1(C_130,u1_struct_0(A_128))
      | ~ m1_pre_topc('#skF_4',A_128)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_128)
      | ~ v2_pre_topc(A_128)
      | v2_struct_0(A_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_325])).

tff(c_335,plain,(
    ! [A_133,C_134] :
      ( k1_funct_1(k4_tmap_1(A_133,'#skF_4'),C_134) = C_134
      | ~ r2_hidden(C_134,k1_relat_1('#skF_5'))
      | ~ m1_subset_1(C_134,u1_struct_0(A_133))
      | ~ m1_pre_topc('#skF_4',A_133)
      | ~ l1_pre_topc(A_133)
      | ~ v2_pre_topc(A_133)
      | v2_struct_0(A_133) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_327])).

tff(c_338,plain,(
    ! [A_133,B_32] :
      ( k1_funct_1(k4_tmap_1(A_133,'#skF_4'),'#skF_2'('#skF_5',B_32)) = '#skF_2'('#skF_5',B_32)
      | ~ m1_subset_1('#skF_2'('#skF_5',B_32),u1_struct_0(A_133))
      | ~ m1_pre_topc('#skF_4',A_133)
      | ~ l1_pre_topc(A_133)
      | ~ v2_pre_topc(A_133)
      | v2_struct_0(A_133)
      | r1_tarski('#skF_5',B_32)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(B_32))
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_335])).

tff(c_371,plain,(
    ! [A_138,B_139] :
      ( k1_funct_1(k4_tmap_1(A_138,'#skF_4'),'#skF_2'('#skF_5',B_139)) = '#skF_2'('#skF_5',B_139)
      | ~ m1_subset_1('#skF_2'('#skF_5',B_139),u1_struct_0(A_138))
      | ~ m1_pre_topc('#skF_4',A_138)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138)
      | r1_tarski('#skF_5',B_139)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(B_139))
      | ~ v1_funct_1(B_139)
      | ~ v1_relat_1(B_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_64,c_338])).

tff(c_377,plain,(
    ! [A_102,B_139] :
      ( k1_funct_1(k4_tmap_1(A_102,'#skF_4'),'#skF_2'('#skF_5',B_139)) = '#skF_2'('#skF_5',B_139)
      | ~ v2_pre_topc(A_102)
      | r1_tarski('#skF_5',B_139)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(B_139))
      | ~ v1_funct_1(B_139)
      | ~ v1_relat_1(B_139)
      | ~ m1_subset_1('#skF_2'('#skF_5',B_139),k1_relat_1('#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_102)
      | ~ l1_pre_topc(A_102)
      | v2_struct_0(A_102) ) ),
    inference(resolution,[status(thm)],[c_186,c_371])).

tff(c_800,plain,(
    ! [A_211,A_212] :
      ( k1_funct_1(k4_tmap_1(A_211,'#skF_4'),'#skF_2'('#skF_5',k4_tmap_1(A_212,'#skF_4'))) = '#skF_2'('#skF_5',k4_tmap_1(A_212,'#skF_4'))
      | ~ v2_pre_topc(A_211)
      | r1_tarski('#skF_5',k4_tmap_1(A_212,'#skF_4'))
      | ~ m1_subset_1('#skF_2'('#skF_5',k4_tmap_1(A_212,'#skF_4')),k1_relat_1('#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_211)
      | ~ l1_pre_topc(A_211)
      | v2_struct_0(A_211)
      | ~ v1_funct_1(k4_tmap_1(A_212,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_212,'#skF_4'))
      | u1_struct_0(A_212) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_212)
      | ~ l1_pre_topc(A_212)
      | ~ v2_pre_topc(A_212)
      | v2_struct_0(A_212) ) ),
    inference(resolution,[status(thm)],[c_692,c_377])).

tff(c_928,plain,(
    ! [A_229,A_230] :
      ( k1_funct_1(k4_tmap_1(A_229,'#skF_4'),'#skF_2'('#skF_5',k4_tmap_1(A_230,'#skF_4'))) = '#skF_2'('#skF_5',k4_tmap_1(A_230,'#skF_4'))
      | ~ v2_pre_topc(A_229)
      | ~ m1_pre_topc('#skF_4',A_229)
      | ~ l1_pre_topc(A_229)
      | v2_struct_0(A_229)
      | r1_tarski('#skF_5',k4_tmap_1(A_230,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_230,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_230,'#skF_4'))
      | u1_struct_0(A_230) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_230)
      | ~ l1_pre_topc(A_230)
      | ~ v2_pre_topc(A_230)
      | v2_struct_0(A_230) ) ),
    inference(resolution,[status(thm)],[c_729,c_800])).

tff(c_34,plain,(
    ! [B_32,A_26] :
      ( k1_funct_1(B_32,'#skF_2'(A_26,B_32)) != k1_funct_1(A_26,'#skF_2'(A_26,B_32))
      | r1_tarski(A_26,B_32)
      | ~ r1_tarski(k1_relat_1(A_26),k1_relat_1(B_32))
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_937,plain,(
    ! [A_230] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',k4_tmap_1(A_230,'#skF_4'))) != '#skF_2'('#skF_5',k4_tmap_1(A_230,'#skF_4'))
      | r1_tarski('#skF_5',k4_tmap_1(A_230,'#skF_4'))
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(k4_tmap_1(A_230,'#skF_4')))
      | ~ v1_funct_1(k4_tmap_1(A_230,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_230,'#skF_4'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ v2_pre_topc(A_230)
      | ~ m1_pre_topc('#skF_4',A_230)
      | ~ l1_pre_topc(A_230)
      | v2_struct_0(A_230)
      | r1_tarski('#skF_5',k4_tmap_1(A_230,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_230,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_230,'#skF_4'))
      | u1_struct_0(A_230) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_230)
      | ~ l1_pre_topc(A_230)
      | ~ v2_pre_topc(A_230)
      | v2_struct_0(A_230) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_928,c_34])).

tff(c_949,plain,(
    ! [A_231] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',k4_tmap_1(A_231,'#skF_4'))) != '#skF_2'('#skF_5',k4_tmap_1(A_231,'#skF_4'))
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(k4_tmap_1(A_231,'#skF_4')))
      | r1_tarski('#skF_5',k4_tmap_1(A_231,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_231,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_231,'#skF_4'))
      | u1_struct_0(A_231) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_231)
      | ~ l1_pre_topc(A_231)
      | ~ v2_pre_topc(A_231)
      | v2_struct_0(A_231) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_64,c_937])).

tff(c_971,plain,(
    ! [A_232] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',k4_tmap_1(A_232,'#skF_4'))) != '#skF_2'('#skF_5',k4_tmap_1(A_232,'#skF_4'))
      | r1_tarski('#skF_5',k4_tmap_1(A_232,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_232,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_232,'#skF_4'))
      | u1_struct_0(A_232) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_232)
      | ~ l1_pre_topc(A_232)
      | ~ v2_pre_topc(A_232)
      | v2_struct_0(A_232) ) ),
    inference(resolution,[status(thm)],[c_687,c_949])).

tff(c_978,plain,(
    ! [A_190] :
      ( r1_tarski('#skF_5',k4_tmap_1(A_190,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_190,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_190,'#skF_4'))
      | u1_struct_0(A_190) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_190)
      | ~ l1_pre_topc(A_190)
      | ~ v2_pre_topc(A_190)
      | v2_struct_0(A_190) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_885,c_971])).

tff(c_777,plain,(
    ! [A_206,B_207,A_208] :
      ( r1_tarski(k1_relat_1(A_206),u1_struct_0(B_207))
      | ~ r1_tarski(A_206,k4_tmap_1(A_208,B_207))
      | ~ v1_funct_1(k4_tmap_1(A_208,B_207))
      | ~ v1_relat_1(k4_tmap_1(A_208,B_207))
      | ~ v1_funct_1(A_206)
      | ~ v1_relat_1(A_206)
      | ~ m1_pre_topc(B_207,A_208)
      | ~ l1_pre_topc(A_208)
      | ~ v2_pre_topc(A_208)
      | v2_struct_0(A_208)
      | u1_struct_0(A_208) = k1_xboole_0
      | ~ m1_pre_topc(B_207,A_208)
      | ~ l1_pre_topc(A_208)
      | ~ v2_pre_topc(A_208)
      | v2_struct_0(A_208) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_40])).

tff(c_782,plain,(
    ! [A_209,B_210] :
      ( r1_tarski(k1_relat_1(k4_tmap_1(A_209,B_210)),u1_struct_0(B_210))
      | ~ v1_funct_1(k4_tmap_1(A_209,B_210))
      | ~ v1_relat_1(k4_tmap_1(A_209,B_210))
      | u1_struct_0(A_209) = k1_xboole_0
      | ~ m1_pre_topc(B_210,A_209)
      | ~ l1_pre_topc(A_209)
      | ~ v2_pre_topc(A_209)
      | v2_struct_0(A_209) ) ),
    inference(resolution,[status(thm)],[c_8,c_777])).

tff(c_795,plain,(
    ! [A_209] :
      ( r1_tarski(k1_relat_1(k4_tmap_1(A_209,'#skF_4')),k1_relat_1('#skF_5'))
      | ~ v1_funct_1(k4_tmap_1(A_209,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_209,'#skF_4'))
      | u1_struct_0(A_209) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_209)
      | ~ l1_pre_topc(A_209)
      | ~ v2_pre_topc(A_209)
      | v2_struct_0(A_209) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_782])).

tff(c_1303,plain,(
    ! [A_306,B_307] :
      ( r2_hidden('#skF_2'(k4_tmap_1(A_306,'#skF_4'),B_307),k1_relat_1('#skF_5'))
      | r1_tarski(k4_tmap_1(A_306,'#skF_4'),B_307)
      | ~ r1_tarski(k1_relat_1(k4_tmap_1(A_306,'#skF_4')),k1_relat_1(B_307))
      | ~ v1_funct_1(B_307)
      | ~ v1_relat_1(B_307)
      | ~ v1_funct_1(k4_tmap_1(A_306,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_306,'#skF_4'))
      | ~ m1_pre_topc('#skF_4',A_306)
      | ~ l1_pre_topc(A_306)
      | ~ v2_pre_topc(A_306)
      | v2_struct_0(A_306)
      | u1_struct_0(A_306) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_306)
      | ~ l1_pre_topc(A_306)
      | ~ v2_pre_topc(A_306)
      | v2_struct_0(A_306) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_36])).

tff(c_38,plain,(
    ! [B_32,C_35,A_26] :
      ( k1_funct_1(B_32,C_35) = k1_funct_1(A_26,C_35)
      | ~ r2_hidden(C_35,k1_relat_1(A_26))
      | ~ r1_tarski(A_26,B_32)
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1309,plain,(
    ! [B_32,A_306,B_307] :
      ( k1_funct_1(B_32,'#skF_2'(k4_tmap_1(A_306,'#skF_4'),B_307)) = k1_funct_1('#skF_5','#skF_2'(k4_tmap_1(A_306,'#skF_4'),B_307))
      | ~ r1_tarski('#skF_5',B_32)
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | r1_tarski(k4_tmap_1(A_306,'#skF_4'),B_307)
      | ~ r1_tarski(k1_relat_1(k4_tmap_1(A_306,'#skF_4')),k1_relat_1(B_307))
      | ~ v1_funct_1(B_307)
      | ~ v1_relat_1(B_307)
      | ~ v1_funct_1(k4_tmap_1(A_306,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_306,'#skF_4'))
      | u1_struct_0(A_306) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_306)
      | ~ l1_pre_topc(A_306)
      | ~ v2_pre_topc(A_306)
      | v2_struct_0(A_306) ) ),
    inference(resolution,[status(thm)],[c_1303,c_38])).

tff(c_1465,plain,(
    ! [B_334,A_335,B_336] :
      ( k1_funct_1(B_334,'#skF_2'(k4_tmap_1(A_335,'#skF_4'),B_336)) = k1_funct_1('#skF_5','#skF_2'(k4_tmap_1(A_335,'#skF_4'),B_336))
      | ~ r1_tarski('#skF_5',B_334)
      | ~ v1_funct_1(B_334)
      | ~ v1_relat_1(B_334)
      | r1_tarski(k4_tmap_1(A_335,'#skF_4'),B_336)
      | ~ r1_tarski(k1_relat_1(k4_tmap_1(A_335,'#skF_4')),k1_relat_1(B_336))
      | ~ v1_funct_1(B_336)
      | ~ v1_relat_1(B_336)
      | ~ v1_funct_1(k4_tmap_1(A_335,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_335,'#skF_4'))
      | u1_struct_0(A_335) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_335)
      | ~ l1_pre_topc(A_335)
      | ~ v2_pre_topc(A_335)
      | v2_struct_0(A_335) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_64,c_1309])).

tff(c_1467,plain,(
    ! [B_334,A_209] :
      ( k1_funct_1(B_334,'#skF_2'(k4_tmap_1(A_209,'#skF_4'),'#skF_5')) = k1_funct_1('#skF_5','#skF_2'(k4_tmap_1(A_209,'#skF_4'),'#skF_5'))
      | ~ r1_tarski('#skF_5',B_334)
      | ~ v1_funct_1(B_334)
      | ~ v1_relat_1(B_334)
      | r1_tarski(k4_tmap_1(A_209,'#skF_4'),'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_funct_1(k4_tmap_1(A_209,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_209,'#skF_4'))
      | u1_struct_0(A_209) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_209)
      | ~ l1_pre_topc(A_209)
      | ~ v2_pre_topc(A_209)
      | v2_struct_0(A_209) ) ),
    inference(resolution,[status(thm)],[c_795,c_1465])).

tff(c_1515,plain,(
    ! [B_340,A_341] :
      ( k1_funct_1(B_340,'#skF_2'(k4_tmap_1(A_341,'#skF_4'),'#skF_5')) = k1_funct_1('#skF_5','#skF_2'(k4_tmap_1(A_341,'#skF_4'),'#skF_5'))
      | ~ r1_tarski('#skF_5',B_340)
      | ~ v1_funct_1(B_340)
      | ~ v1_relat_1(B_340)
      | r1_tarski(k4_tmap_1(A_341,'#skF_4'),'#skF_5')
      | ~ v1_funct_1(k4_tmap_1(A_341,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_341,'#skF_4'))
      | u1_struct_0(A_341) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_341)
      | ~ l1_pre_topc(A_341)
      | ~ v2_pre_topc(A_341)
      | v2_struct_0(A_341) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_64,c_1467])).

tff(c_1538,plain,(
    ! [A_341] :
      ( ~ r1_tarski(k1_relat_1(k4_tmap_1(A_341,'#skF_4')),k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_5',k4_tmap_1(A_341,'#skF_4'))
      | r1_tarski(k4_tmap_1(A_341,'#skF_4'),'#skF_5')
      | ~ v1_funct_1(k4_tmap_1(A_341,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_341,'#skF_4'))
      | u1_struct_0(A_341) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_341)
      | ~ l1_pre_topc(A_341)
      | ~ v2_pre_topc(A_341)
      | v2_struct_0(A_341) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1515,c_34])).

tff(c_1560,plain,(
    ! [A_342] :
      ( ~ r1_tarski(k1_relat_1(k4_tmap_1(A_342,'#skF_4')),k1_relat_1('#skF_5'))
      | ~ r1_tarski('#skF_5',k4_tmap_1(A_342,'#skF_4'))
      | r1_tarski(k4_tmap_1(A_342,'#skF_4'),'#skF_5')
      | ~ v1_funct_1(k4_tmap_1(A_342,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_342,'#skF_4'))
      | u1_struct_0(A_342) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_342)
      | ~ l1_pre_topc(A_342)
      | ~ v2_pre_topc(A_342)
      | v2_struct_0(A_342) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_64,c_1538])).

tff(c_1582,plain,(
    ! [A_343] :
      ( ~ r1_tarski('#skF_5',k4_tmap_1(A_343,'#skF_4'))
      | r1_tarski(k4_tmap_1(A_343,'#skF_4'),'#skF_5')
      | ~ v1_funct_1(k4_tmap_1(A_343,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_343,'#skF_4'))
      | u1_struct_0(A_343) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_343)
      | ~ l1_pre_topc(A_343)
      | ~ v2_pre_topc(A_343)
      | v2_struct_0(A_343) ) ),
    inference(resolution,[status(thm)],[c_795,c_1560])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1616,plain,(
    ! [A_344] :
      ( k4_tmap_1(A_344,'#skF_4') = '#skF_5'
      | ~ r1_tarski('#skF_5',k4_tmap_1(A_344,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_344,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_344,'#skF_4'))
      | u1_struct_0(A_344) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_344)
      | ~ l1_pre_topc(A_344)
      | ~ v2_pre_topc(A_344)
      | v2_struct_0(A_344) ) ),
    inference(resolution,[status(thm)],[c_1582,c_4])).

tff(c_1621,plain,(
    ! [A_345] :
      ( k4_tmap_1(A_345,'#skF_4') = '#skF_5'
      | ~ v1_funct_1(k4_tmap_1(A_345,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_345,'#skF_4'))
      | u1_struct_0(A_345) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_345)
      | ~ l1_pre_topc(A_345)
      | ~ v2_pre_topc(A_345)
      | v2_struct_0(A_345) ) ),
    inference(resolution,[status(thm)],[c_978,c_1616])).

tff(c_1638,plain,(
    ! [A_350] :
      ( k4_tmap_1(A_350,'#skF_4') = '#skF_5'
      | ~ v1_funct_1(k4_tmap_1(A_350,'#skF_4'))
      | u1_struct_0(A_350) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_350)
      | ~ l1_pre_topc(A_350)
      | ~ v2_pre_topc(A_350)
      | v2_struct_0(A_350) ) ),
    inference(resolution,[status(thm)],[c_217,c_1621])).

tff(c_1644,plain,(
    ! [A_351] :
      ( k4_tmap_1(A_351,'#skF_4') = '#skF_5'
      | u1_struct_0(A_351) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_351)
      | ~ l1_pre_topc(A_351)
      | ~ v2_pre_topc(A_351)
      | v2_struct_0(A_351) ) ),
    inference(resolution,[status(thm)],[c_52,c_1638])).

tff(c_1647,plain,
    ( k4_tmap_1('#skF_3','#skF_4') = '#skF_5'
    | u1_struct_0('#skF_3') = k1_xboole_0
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1644])).

tff(c_1650,plain,
    ( k4_tmap_1('#skF_3','#skF_4') = '#skF_5'
    | u1_struct_0('#skF_3') = k1_xboole_0
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_1647])).

tff(c_1651,plain,
    ( k4_tmap_1('#skF_3','#skF_4') = '#skF_5'
    | u1_struct_0('#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1650])).

tff(c_1652,plain,(
    u1_struct_0('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1651])).

tff(c_44,plain,(
    ! [A_37] :
      ( ~ v1_xboole_0(u1_struct_0(A_37))
      | ~ l1_struct_0(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1777,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1652,c_44])).

tff(c_1860,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1777])).

tff(c_1861,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1860])).

tff(c_1865,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_1861])).

tff(c_1869,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1865])).

tff(c_1870,plain,(
    k4_tmap_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1651])).

tff(c_56,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_127,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_5'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_56])).

tff(c_1872,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_5'),u1_struct_0('#skF_3'),'#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1870,c_127])).

tff(c_1875,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_1872])).

tff(c_1876,plain,(
    u1_struct_0('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_1886,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1876,c_44])).

tff(c_1890,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1886])).

tff(c_1891,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1890])).

tff(c_1895,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_1891])).

tff(c_1899,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1895])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:38:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.38/2.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.38/2.27  
% 6.38/2.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.38/2.27  %$ r2_funct_2 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k1_relset_1 > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 6.38/2.27  
% 6.38/2.27  %Foreground sorts:
% 6.38/2.27  
% 6.38/2.27  
% 6.38/2.27  %Background operators:
% 6.38/2.27  
% 6.38/2.27  
% 6.38/2.27  %Foreground operators:
% 6.38/2.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.38/2.27  tff(k4_tmap_1, type, k4_tmap_1: ($i * $i) > $i).
% 6.38/2.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.38/2.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.38/2.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.38/2.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.38/2.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.38/2.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.38/2.27  tff('#skF_5', type, '#skF_5': $i).
% 6.38/2.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.38/2.27  tff('#skF_3', type, '#skF_3': $i).
% 6.38/2.27  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.38/2.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.38/2.27  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.38/2.27  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.38/2.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.38/2.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.38/2.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.38/2.27  tff('#skF_4', type, '#skF_4': $i).
% 6.38/2.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.38/2.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.38/2.27  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.38/2.27  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.38/2.27  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 6.38/2.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.38/2.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.38/2.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.38/2.27  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 6.38/2.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.38/2.27  
% 6.51/2.30  tff(f_193, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, u1_struct_0(B)) => (D = k1_funct_1(C, D))))) => r2_funct_2(u1_struct_0(B), u1_struct_0(A), k4_tmap_1(A, B), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_tmap_1)).
% 6.51/2.30  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.51/2.30  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.51/2.30  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.51/2.30  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.51/2.30  tff(f_82, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_2)).
% 6.51/2.30  tff(f_143, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_funct_1(k4_tmap_1(A, B)) & v1_funct_2(k4_tmap_1(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(k4_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_tmap_1)).
% 6.51/2.30  tff(f_40, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.51/2.30  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.51/2.30  tff(f_100, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, B) <=> (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_grfunc_1)).
% 6.51/2.30  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 6.51/2.30  tff(f_128, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 6.51/2.30  tff(f_163, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, u1_struct_0(B)) => (k1_funct_1(k4_tmap_1(A, B), C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_tmap_1)).
% 6.51/2.30  tff(f_112, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 6.51/2.30  tff(c_70, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_193])).
% 6.51/2.30  tff(c_42, plain, (![A_36]: (l1_struct_0(A_36) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.51/2.30  tff(c_74, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_193])).
% 6.51/2.30  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.51/2.30  tff(c_64, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_193])).
% 6.51/2.30  tff(c_62, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_193])).
% 6.51/2.30  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_193])).
% 6.51/2.30  tff(c_93, plain, (![A_77, B_78, C_79]: (k1_relset_1(A_77, B_78, C_79)=k1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.51/2.30  tff(c_97, plain, (k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_93])).
% 6.51/2.30  tff(c_117, plain, (![B_94, A_95, C_96]: (k1_xboole_0=B_94 | k1_relset_1(A_95, B_94, C_96)=A_95 | ~v1_funct_2(C_96, A_95, B_94) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_95, B_94))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.51/2.30  tff(c_120, plain, (u1_struct_0('#skF_3')=k1_xboole_0 | k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5')=u1_struct_0('#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_60, c_117])).
% 6.51/2.30  tff(c_123, plain, (u1_struct_0('#skF_3')=k1_xboole_0 | u1_struct_0('#skF_4')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_97, c_120])).
% 6.51/2.30  tff(c_124, plain, (u1_struct_0('#skF_4')=k1_relat_1('#skF_5')), inference(splitLeft, [status(thm)], [c_123])).
% 6.51/2.30  tff(c_129, plain, (v1_funct_2('#skF_5', k1_relat_1('#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_62])).
% 6.51/2.30  tff(c_128, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_60])).
% 6.51/2.30  tff(c_30, plain, (![D_22, A_14, B_15, C_16]: (k1_funct_1(D_22, '#skF_1'(A_14, B_15, C_16, D_22))!=k1_funct_1(C_16, '#skF_1'(A_14, B_15, C_16, D_22)) | r2_funct_2(A_14, B_15, C_16, D_22) | ~m1_subset_1(D_22, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))) | ~v1_funct_2(D_22, A_14, B_15) | ~v1_funct_1(D_22) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))) | ~v1_funct_2(C_16, A_14, B_15) | ~v1_funct_1(C_16))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.51/2.30  tff(c_601, plain, (![A_169, B_170, C_171]: (r2_funct_2(A_169, B_170, C_171, C_171) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))) | ~v1_funct_2(C_171, A_169, B_170) | ~v1_funct_1(C_171) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))) | ~v1_funct_2(C_171, A_169, B_170) | ~v1_funct_1(C_171))), inference(reflexivity, [status(thm), theory('equality')], [c_30])).
% 6.51/2.30  tff(c_607, plain, (r2_funct_2(k1_relat_1('#skF_5'), u1_struct_0('#skF_3'), '#skF_5', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_128, c_601])).
% 6.51/2.30  tff(c_612, plain, (r2_funct_2(k1_relat_1('#skF_5'), u1_struct_0('#skF_3'), '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_129, c_128, c_607])).
% 6.51/2.30  tff(c_72, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_193])).
% 6.51/2.30  tff(c_66, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_193])).
% 6.51/2.30  tff(c_52, plain, (![A_45, B_46]: (v1_funct_1(k4_tmap_1(A_45, B_46)) | ~m1_pre_topc(B_46, A_45) | ~l1_pre_topc(A_45) | ~v2_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.51/2.30  tff(c_195, plain, (![A_106, B_107]: (m1_subset_1(k4_tmap_1(A_106, B_107), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_107), u1_struct_0(A_106)))) | ~m1_pre_topc(B_107, A_106) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.51/2.30  tff(c_12, plain, (![C_7, A_5, B_6]: (v1_relat_1(C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.51/2.30  tff(c_217, plain, (![A_106, B_107]: (v1_relat_1(k4_tmap_1(A_106, B_107)) | ~m1_pre_topc(B_107, A_106) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106) | v2_struct_0(A_106))), inference(resolution, [status(thm)], [c_195, c_12])).
% 6.51/2.30  tff(c_91, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_12])).
% 6.51/2.30  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.51/2.30  tff(c_50, plain, (![A_45, B_46]: (v1_funct_2(k4_tmap_1(A_45, B_46), u1_struct_0(B_46), u1_struct_0(A_45)) | ~m1_pre_topc(B_46, A_45) | ~l1_pre_topc(A_45) | ~v2_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.51/2.30  tff(c_26, plain, (![B_12, A_11, C_13]: (k1_xboole_0=B_12 | k1_relset_1(A_11, B_12, C_13)=A_11 | ~v1_funct_2(C_13, A_11, B_12) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.51/2.30  tff(c_357, plain, (![A_136, B_137]: (u1_struct_0(A_136)=k1_xboole_0 | k1_relset_1(u1_struct_0(B_137), u1_struct_0(A_136), k4_tmap_1(A_136, B_137))=u1_struct_0(B_137) | ~v1_funct_2(k4_tmap_1(A_136, B_137), u1_struct_0(B_137), u1_struct_0(A_136)) | ~m1_pre_topc(B_137, A_136) | ~l1_pre_topc(A_136) | ~v2_pre_topc(A_136) | v2_struct_0(A_136))), inference(resolution, [status(thm)], [c_195, c_26])).
% 6.51/2.30  tff(c_380, plain, (![A_140, B_141]: (u1_struct_0(A_140)=k1_xboole_0 | k1_relset_1(u1_struct_0(B_141), u1_struct_0(A_140), k4_tmap_1(A_140, B_141))=u1_struct_0(B_141) | ~m1_pre_topc(B_141, A_140) | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140))), inference(resolution, [status(thm)], [c_50, c_357])).
% 6.51/2.30  tff(c_14, plain, (![A_8, B_9, C_10]: (k1_relset_1(A_8, B_9, C_10)=k1_relat_1(C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.51/2.30  tff(c_216, plain, (![B_107, A_106]: (k1_relset_1(u1_struct_0(B_107), u1_struct_0(A_106), k4_tmap_1(A_106, B_107))=k1_relat_1(k4_tmap_1(A_106, B_107)) | ~m1_pre_topc(B_107, A_106) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106) | v2_struct_0(A_106))), inference(resolution, [status(thm)], [c_195, c_14])).
% 6.51/2.30  tff(c_425, plain, (![A_143, B_144]: (k1_relat_1(k4_tmap_1(A_143, B_144))=u1_struct_0(B_144) | ~m1_pre_topc(B_144, A_143) | ~l1_pre_topc(A_143) | ~v2_pre_topc(A_143) | v2_struct_0(A_143) | u1_struct_0(A_143)=k1_xboole_0 | ~m1_pre_topc(B_144, A_143) | ~l1_pre_topc(A_143) | ~v2_pre_topc(A_143) | v2_struct_0(A_143))), inference(superposition, [status(thm), theory('equality')], [c_380, c_216])).
% 6.51/2.30  tff(c_40, plain, (![A_26, B_32]: (r1_tarski(k1_relat_1(A_26), k1_relat_1(B_32)) | ~r1_tarski(A_26, B_32) | ~v1_funct_1(B_32) | ~v1_relat_1(B_32) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.51/2.30  tff(c_649, plain, (![B_182, B_183, A_184]: (r1_tarski(u1_struct_0(B_182), k1_relat_1(B_183)) | ~r1_tarski(k4_tmap_1(A_184, B_182), B_183) | ~v1_funct_1(B_183) | ~v1_relat_1(B_183) | ~v1_funct_1(k4_tmap_1(A_184, B_182)) | ~v1_relat_1(k4_tmap_1(A_184, B_182)) | ~m1_pre_topc(B_182, A_184) | ~l1_pre_topc(A_184) | ~v2_pre_topc(A_184) | v2_struct_0(A_184) | u1_struct_0(A_184)=k1_xboole_0 | ~m1_pre_topc(B_182, A_184) | ~l1_pre_topc(A_184) | ~v2_pre_topc(A_184) | v2_struct_0(A_184))), inference(superposition, [status(thm), theory('equality')], [c_425, c_40])).
% 6.51/2.30  tff(c_674, plain, (![B_188, A_189]: (r1_tarski(u1_struct_0(B_188), k1_relat_1(k4_tmap_1(A_189, B_188))) | ~v1_funct_1(k4_tmap_1(A_189, B_188)) | ~v1_relat_1(k4_tmap_1(A_189, B_188)) | u1_struct_0(A_189)=k1_xboole_0 | ~m1_pre_topc(B_188, A_189) | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189) | v2_struct_0(A_189))), inference(resolution, [status(thm)], [c_8, c_649])).
% 6.51/2.30  tff(c_692, plain, (![A_190]: (r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(k4_tmap_1(A_190, '#skF_4'))) | ~v1_funct_1(k4_tmap_1(A_190, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_190, '#skF_4')) | u1_struct_0(A_190)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_190) | ~l1_pre_topc(A_190) | ~v2_pre_topc(A_190) | v2_struct_0(A_190))), inference(superposition, [status(thm), theory('equality')], [c_124, c_674])).
% 6.51/2.30  tff(c_301, plain, (![A_124, B_125]: (r2_hidden('#skF_2'(A_124, B_125), k1_relat_1(A_124)) | r1_tarski(A_124, B_125) | ~r1_tarski(k1_relat_1(A_124), k1_relat_1(B_125)) | ~v1_funct_1(B_125) | ~v1_relat_1(B_125) | ~v1_funct_1(A_124) | ~v1_relat_1(A_124))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.51/2.30  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, B_4) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.51/2.30  tff(c_315, plain, (![A_124, B_125]: (m1_subset_1('#skF_2'(A_124, B_125), k1_relat_1(A_124)) | r1_tarski(A_124, B_125) | ~r1_tarski(k1_relat_1(A_124), k1_relat_1(B_125)) | ~v1_funct_1(B_125) | ~v1_relat_1(B_125) | ~v1_funct_1(A_124) | ~v1_relat_1(A_124))), inference(resolution, [status(thm)], [c_301, c_10])).
% 6.51/2.30  tff(c_704, plain, (![A_190]: (m1_subset_1('#skF_2'('#skF_5', k4_tmap_1(A_190, '#skF_4')), k1_relat_1('#skF_5')) | r1_tarski('#skF_5', k4_tmap_1(A_190, '#skF_4')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1(k4_tmap_1(A_190, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_190, '#skF_4')) | u1_struct_0(A_190)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_190) | ~l1_pre_topc(A_190) | ~v2_pre_topc(A_190) | v2_struct_0(A_190))), inference(resolution, [status(thm)], [c_692, c_315])).
% 6.51/2.30  tff(c_729, plain, (![A_190]: (m1_subset_1('#skF_2'('#skF_5', k4_tmap_1(A_190, '#skF_4')), k1_relat_1('#skF_5')) | r1_tarski('#skF_5', k4_tmap_1(A_190, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_190, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_190, '#skF_4')) | u1_struct_0(A_190)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_190) | ~l1_pre_topc(A_190) | ~v2_pre_topc(A_190) | v2_struct_0(A_190))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_64, c_704])).
% 6.51/2.30  tff(c_68, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_193])).
% 6.51/2.30  tff(c_183, plain, (![C_101, A_102, B_103]: (m1_subset_1(C_101, u1_struct_0(A_102)) | ~m1_subset_1(C_101, u1_struct_0(B_103)) | ~m1_pre_topc(B_103, A_102) | v2_struct_0(B_103) | ~l1_pre_topc(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.51/2.30  tff(c_185, plain, (![C_101, A_102]: (m1_subset_1(C_101, u1_struct_0(A_102)) | ~m1_subset_1(C_101, k1_relat_1('#skF_5')) | ~m1_pre_topc('#skF_4', A_102) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_102) | v2_struct_0(A_102))), inference(superposition, [status(thm), theory('equality')], [c_124, c_183])).
% 6.51/2.30  tff(c_186, plain, (![C_101, A_102]: (m1_subset_1(C_101, u1_struct_0(A_102)) | ~m1_subset_1(C_101, k1_relat_1('#skF_5')) | ~m1_pre_topc('#skF_4', A_102) | ~l1_pre_topc(A_102) | v2_struct_0(A_102))), inference(negUnitSimplification, [status(thm)], [c_68, c_185])).
% 6.51/2.30  tff(c_395, plain, (![A_140]: (u1_struct_0(A_140)=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_5'), u1_struct_0(A_140), k4_tmap_1(A_140, '#skF_4'))=u1_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', A_140) | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140))), inference(superposition, [status(thm), theory('equality')], [c_124, c_380])).
% 6.51/2.30  tff(c_404, plain, (![A_142]: (u1_struct_0(A_142)=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_5'), u1_struct_0(A_142), k4_tmap_1(A_142, '#skF_4'))=k1_relat_1('#skF_5') | ~m1_pre_topc('#skF_4', A_142) | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142) | v2_struct_0(A_142))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_395])).
% 6.51/2.30  tff(c_265, plain, (![B_118, A_119]: (k1_relset_1(u1_struct_0(B_118), u1_struct_0(A_119), k4_tmap_1(A_119, B_118))=k1_relat_1(k4_tmap_1(A_119, B_118)) | ~m1_pre_topc(B_118, A_119) | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119) | v2_struct_0(A_119))), inference(resolution, [status(thm)], [c_195, c_14])).
% 6.51/2.30  tff(c_274, plain, (![A_119]: (k1_relset_1(k1_relat_1('#skF_5'), u1_struct_0(A_119), k4_tmap_1(A_119, '#skF_4'))=k1_relat_1(k4_tmap_1(A_119, '#skF_4')) | ~m1_pre_topc('#skF_4', A_119) | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119) | v2_struct_0(A_119))), inference(superposition, [status(thm), theory('equality')], [c_124, c_265])).
% 6.51/2.30  tff(c_458, plain, (![A_145]: (k1_relat_1(k4_tmap_1(A_145, '#skF_4'))=k1_relat_1('#skF_5') | ~m1_pre_topc('#skF_4', A_145) | ~l1_pre_topc(A_145) | ~v2_pre_topc(A_145) | v2_struct_0(A_145) | u1_struct_0(A_145)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_145) | ~l1_pre_topc(A_145) | ~v2_pre_topc(A_145) | v2_struct_0(A_145))), inference(superposition, [status(thm), theory('equality')], [c_404, c_274])).
% 6.51/2.30  tff(c_58, plain, (![D_65]: (k1_funct_1('#skF_5', D_65)=D_65 | ~r2_hidden(D_65, u1_struct_0('#skF_4')) | ~m1_subset_1(D_65, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_193])).
% 6.51/2.30  tff(c_126, plain, (![D_65]: (k1_funct_1('#skF_5', D_65)=D_65 | ~r2_hidden(D_65, k1_relat_1('#skF_5')) | ~m1_subset_1(D_65, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_58])).
% 6.51/2.30  tff(c_307, plain, (![B_125]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', B_125))='#skF_2'('#skF_5', B_125) | ~m1_subset_1('#skF_2'('#skF_5', B_125), u1_struct_0('#skF_3')) | r1_tarski('#skF_5', B_125) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(B_125)) | ~v1_funct_1(B_125) | ~v1_relat_1(B_125) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_301, c_126])).
% 6.51/2.30  tff(c_314, plain, (![B_125]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', B_125))='#skF_2'('#skF_5', B_125) | ~m1_subset_1('#skF_2'('#skF_5', B_125), u1_struct_0('#skF_3')) | r1_tarski('#skF_5', B_125) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(B_125)) | ~v1_funct_1(B_125) | ~v1_relat_1(B_125))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_64, c_307])).
% 6.51/2.30  tff(c_467, plain, (![A_145]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', k4_tmap_1(A_145, '#skF_4')))='#skF_2'('#skF_5', k4_tmap_1(A_145, '#skF_4')) | ~m1_subset_1('#skF_2'('#skF_5', k4_tmap_1(A_145, '#skF_4')), u1_struct_0('#skF_3')) | r1_tarski('#skF_5', k4_tmap_1(A_145, '#skF_4')) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1('#skF_5')) | ~v1_funct_1(k4_tmap_1(A_145, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_145, '#skF_4')) | ~m1_pre_topc('#skF_4', A_145) | ~l1_pre_topc(A_145) | ~v2_pre_topc(A_145) | v2_struct_0(A_145) | u1_struct_0(A_145)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_145) | ~l1_pre_topc(A_145) | ~v2_pre_topc(A_145) | v2_struct_0(A_145))), inference(superposition, [status(thm), theory('equality')], [c_458, c_314])).
% 6.51/2.30  tff(c_864, plain, (![A_219]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', k4_tmap_1(A_219, '#skF_4')))='#skF_2'('#skF_5', k4_tmap_1(A_219, '#skF_4')) | ~m1_subset_1('#skF_2'('#skF_5', k4_tmap_1(A_219, '#skF_4')), u1_struct_0('#skF_3')) | r1_tarski('#skF_5', k4_tmap_1(A_219, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_219, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_219, '#skF_4')) | u1_struct_0(A_219)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_219) | ~l1_pre_topc(A_219) | ~v2_pre_topc(A_219) | v2_struct_0(A_219))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_467])).
% 6.51/2.30  tff(c_867, plain, (![A_219]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', k4_tmap_1(A_219, '#skF_4')))='#skF_2'('#skF_5', k4_tmap_1(A_219, '#skF_4')) | r1_tarski('#skF_5', k4_tmap_1(A_219, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_219, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_219, '#skF_4')) | u1_struct_0(A_219)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_219) | ~l1_pre_topc(A_219) | ~v2_pre_topc(A_219) | v2_struct_0(A_219) | ~m1_subset_1('#skF_2'('#skF_5', k4_tmap_1(A_219, '#skF_4')), k1_relat_1('#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_186, c_864])).
% 6.51/2.30  tff(c_870, plain, (![A_219]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', k4_tmap_1(A_219, '#skF_4')))='#skF_2'('#skF_5', k4_tmap_1(A_219, '#skF_4')) | r1_tarski('#skF_5', k4_tmap_1(A_219, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_219, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_219, '#skF_4')) | u1_struct_0(A_219)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_219) | ~l1_pre_topc(A_219) | ~v2_pre_topc(A_219) | v2_struct_0(A_219) | ~m1_subset_1('#skF_2'('#skF_5', k4_tmap_1(A_219, '#skF_4')), k1_relat_1('#skF_5')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_867])).
% 6.51/2.30  tff(c_881, plain, (![A_222]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', k4_tmap_1(A_222, '#skF_4')))='#skF_2'('#skF_5', k4_tmap_1(A_222, '#skF_4')) | r1_tarski('#skF_5', k4_tmap_1(A_222, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_222, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_222, '#skF_4')) | u1_struct_0(A_222)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_222) | ~l1_pre_topc(A_222) | ~v2_pre_topc(A_222) | v2_struct_0(A_222) | ~m1_subset_1('#skF_2'('#skF_5', k4_tmap_1(A_222, '#skF_4')), k1_relat_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_74, c_870])).
% 6.51/2.30  tff(c_885, plain, (![A_190]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', k4_tmap_1(A_190, '#skF_4')))='#skF_2'('#skF_5', k4_tmap_1(A_190, '#skF_4')) | r1_tarski('#skF_5', k4_tmap_1(A_190, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_190, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_190, '#skF_4')) | u1_struct_0(A_190)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_190) | ~l1_pre_topc(A_190) | ~v2_pre_topc(A_190) | v2_struct_0(A_190))), inference(resolution, [status(thm)], [c_729, c_881])).
% 6.51/2.30  tff(c_687, plain, (![A_189]: (r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(k4_tmap_1(A_189, '#skF_4'))) | ~v1_funct_1(k4_tmap_1(A_189, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_189, '#skF_4')) | u1_struct_0(A_189)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_189) | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189) | v2_struct_0(A_189))), inference(superposition, [status(thm), theory('equality')], [c_124, c_674])).
% 6.51/2.30  tff(c_36, plain, (![A_26, B_32]: (r2_hidden('#skF_2'(A_26, B_32), k1_relat_1(A_26)) | r1_tarski(A_26, B_32) | ~r1_tarski(k1_relat_1(A_26), k1_relat_1(B_32)) | ~v1_funct_1(B_32) | ~v1_relat_1(B_32) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.51/2.30  tff(c_325, plain, (![A_128, B_129, C_130]: (k1_funct_1(k4_tmap_1(A_128, B_129), C_130)=C_130 | ~r2_hidden(C_130, u1_struct_0(B_129)) | ~m1_subset_1(C_130, u1_struct_0(A_128)) | ~m1_pre_topc(B_129, A_128) | v2_struct_0(B_129) | ~l1_pre_topc(A_128) | ~v2_pre_topc(A_128) | v2_struct_0(A_128))), inference(cnfTransformation, [status(thm)], [f_163])).
% 6.51/2.30  tff(c_327, plain, (![A_128, C_130]: (k1_funct_1(k4_tmap_1(A_128, '#skF_4'), C_130)=C_130 | ~r2_hidden(C_130, k1_relat_1('#skF_5')) | ~m1_subset_1(C_130, u1_struct_0(A_128)) | ~m1_pre_topc('#skF_4', A_128) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_128) | ~v2_pre_topc(A_128) | v2_struct_0(A_128))), inference(superposition, [status(thm), theory('equality')], [c_124, c_325])).
% 6.51/2.30  tff(c_335, plain, (![A_133, C_134]: (k1_funct_1(k4_tmap_1(A_133, '#skF_4'), C_134)=C_134 | ~r2_hidden(C_134, k1_relat_1('#skF_5')) | ~m1_subset_1(C_134, u1_struct_0(A_133)) | ~m1_pre_topc('#skF_4', A_133) | ~l1_pre_topc(A_133) | ~v2_pre_topc(A_133) | v2_struct_0(A_133))), inference(negUnitSimplification, [status(thm)], [c_68, c_327])).
% 6.51/2.30  tff(c_338, plain, (![A_133, B_32]: (k1_funct_1(k4_tmap_1(A_133, '#skF_4'), '#skF_2'('#skF_5', B_32))='#skF_2'('#skF_5', B_32) | ~m1_subset_1('#skF_2'('#skF_5', B_32), u1_struct_0(A_133)) | ~m1_pre_topc('#skF_4', A_133) | ~l1_pre_topc(A_133) | ~v2_pre_topc(A_133) | v2_struct_0(A_133) | r1_tarski('#skF_5', B_32) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(B_32)) | ~v1_funct_1(B_32) | ~v1_relat_1(B_32) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_335])).
% 6.51/2.30  tff(c_371, plain, (![A_138, B_139]: (k1_funct_1(k4_tmap_1(A_138, '#skF_4'), '#skF_2'('#skF_5', B_139))='#skF_2'('#skF_5', B_139) | ~m1_subset_1('#skF_2'('#skF_5', B_139), u1_struct_0(A_138)) | ~m1_pre_topc('#skF_4', A_138) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138) | r1_tarski('#skF_5', B_139) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(B_139)) | ~v1_funct_1(B_139) | ~v1_relat_1(B_139))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_64, c_338])).
% 6.51/2.30  tff(c_377, plain, (![A_102, B_139]: (k1_funct_1(k4_tmap_1(A_102, '#skF_4'), '#skF_2'('#skF_5', B_139))='#skF_2'('#skF_5', B_139) | ~v2_pre_topc(A_102) | r1_tarski('#skF_5', B_139) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(B_139)) | ~v1_funct_1(B_139) | ~v1_relat_1(B_139) | ~m1_subset_1('#skF_2'('#skF_5', B_139), k1_relat_1('#skF_5')) | ~m1_pre_topc('#skF_4', A_102) | ~l1_pre_topc(A_102) | v2_struct_0(A_102))), inference(resolution, [status(thm)], [c_186, c_371])).
% 6.51/2.30  tff(c_800, plain, (![A_211, A_212]: (k1_funct_1(k4_tmap_1(A_211, '#skF_4'), '#skF_2'('#skF_5', k4_tmap_1(A_212, '#skF_4')))='#skF_2'('#skF_5', k4_tmap_1(A_212, '#skF_4')) | ~v2_pre_topc(A_211) | r1_tarski('#skF_5', k4_tmap_1(A_212, '#skF_4')) | ~m1_subset_1('#skF_2'('#skF_5', k4_tmap_1(A_212, '#skF_4')), k1_relat_1('#skF_5')) | ~m1_pre_topc('#skF_4', A_211) | ~l1_pre_topc(A_211) | v2_struct_0(A_211) | ~v1_funct_1(k4_tmap_1(A_212, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_212, '#skF_4')) | u1_struct_0(A_212)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_212) | ~l1_pre_topc(A_212) | ~v2_pre_topc(A_212) | v2_struct_0(A_212))), inference(resolution, [status(thm)], [c_692, c_377])).
% 6.51/2.30  tff(c_928, plain, (![A_229, A_230]: (k1_funct_1(k4_tmap_1(A_229, '#skF_4'), '#skF_2'('#skF_5', k4_tmap_1(A_230, '#skF_4')))='#skF_2'('#skF_5', k4_tmap_1(A_230, '#skF_4')) | ~v2_pre_topc(A_229) | ~m1_pre_topc('#skF_4', A_229) | ~l1_pre_topc(A_229) | v2_struct_0(A_229) | r1_tarski('#skF_5', k4_tmap_1(A_230, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_230, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_230, '#skF_4')) | u1_struct_0(A_230)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_230) | ~l1_pre_topc(A_230) | ~v2_pre_topc(A_230) | v2_struct_0(A_230))), inference(resolution, [status(thm)], [c_729, c_800])).
% 6.51/2.30  tff(c_34, plain, (![B_32, A_26]: (k1_funct_1(B_32, '#skF_2'(A_26, B_32))!=k1_funct_1(A_26, '#skF_2'(A_26, B_32)) | r1_tarski(A_26, B_32) | ~r1_tarski(k1_relat_1(A_26), k1_relat_1(B_32)) | ~v1_funct_1(B_32) | ~v1_relat_1(B_32) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.51/2.30  tff(c_937, plain, (![A_230]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', k4_tmap_1(A_230, '#skF_4')))!='#skF_2'('#skF_5', k4_tmap_1(A_230, '#skF_4')) | r1_tarski('#skF_5', k4_tmap_1(A_230, '#skF_4')) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(k4_tmap_1(A_230, '#skF_4'))) | ~v1_funct_1(k4_tmap_1(A_230, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_230, '#skF_4')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v2_pre_topc(A_230) | ~m1_pre_topc('#skF_4', A_230) | ~l1_pre_topc(A_230) | v2_struct_0(A_230) | r1_tarski('#skF_5', k4_tmap_1(A_230, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_230, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_230, '#skF_4')) | u1_struct_0(A_230)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_230) | ~l1_pre_topc(A_230) | ~v2_pre_topc(A_230) | v2_struct_0(A_230))), inference(superposition, [status(thm), theory('equality')], [c_928, c_34])).
% 6.51/2.30  tff(c_949, plain, (![A_231]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', k4_tmap_1(A_231, '#skF_4')))!='#skF_2'('#skF_5', k4_tmap_1(A_231, '#skF_4')) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(k4_tmap_1(A_231, '#skF_4'))) | r1_tarski('#skF_5', k4_tmap_1(A_231, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_231, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_231, '#skF_4')) | u1_struct_0(A_231)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_231) | ~l1_pre_topc(A_231) | ~v2_pre_topc(A_231) | v2_struct_0(A_231))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_64, c_937])).
% 6.51/2.30  tff(c_971, plain, (![A_232]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', k4_tmap_1(A_232, '#skF_4')))!='#skF_2'('#skF_5', k4_tmap_1(A_232, '#skF_4')) | r1_tarski('#skF_5', k4_tmap_1(A_232, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_232, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_232, '#skF_4')) | u1_struct_0(A_232)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_232) | ~l1_pre_topc(A_232) | ~v2_pre_topc(A_232) | v2_struct_0(A_232))), inference(resolution, [status(thm)], [c_687, c_949])).
% 6.51/2.30  tff(c_978, plain, (![A_190]: (r1_tarski('#skF_5', k4_tmap_1(A_190, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_190, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_190, '#skF_4')) | u1_struct_0(A_190)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_190) | ~l1_pre_topc(A_190) | ~v2_pre_topc(A_190) | v2_struct_0(A_190))), inference(superposition, [status(thm), theory('equality')], [c_885, c_971])).
% 6.51/2.30  tff(c_777, plain, (![A_206, B_207, A_208]: (r1_tarski(k1_relat_1(A_206), u1_struct_0(B_207)) | ~r1_tarski(A_206, k4_tmap_1(A_208, B_207)) | ~v1_funct_1(k4_tmap_1(A_208, B_207)) | ~v1_relat_1(k4_tmap_1(A_208, B_207)) | ~v1_funct_1(A_206) | ~v1_relat_1(A_206) | ~m1_pre_topc(B_207, A_208) | ~l1_pre_topc(A_208) | ~v2_pre_topc(A_208) | v2_struct_0(A_208) | u1_struct_0(A_208)=k1_xboole_0 | ~m1_pre_topc(B_207, A_208) | ~l1_pre_topc(A_208) | ~v2_pre_topc(A_208) | v2_struct_0(A_208))), inference(superposition, [status(thm), theory('equality')], [c_425, c_40])).
% 6.51/2.30  tff(c_782, plain, (![A_209, B_210]: (r1_tarski(k1_relat_1(k4_tmap_1(A_209, B_210)), u1_struct_0(B_210)) | ~v1_funct_1(k4_tmap_1(A_209, B_210)) | ~v1_relat_1(k4_tmap_1(A_209, B_210)) | u1_struct_0(A_209)=k1_xboole_0 | ~m1_pre_topc(B_210, A_209) | ~l1_pre_topc(A_209) | ~v2_pre_topc(A_209) | v2_struct_0(A_209))), inference(resolution, [status(thm)], [c_8, c_777])).
% 6.51/2.30  tff(c_795, plain, (![A_209]: (r1_tarski(k1_relat_1(k4_tmap_1(A_209, '#skF_4')), k1_relat_1('#skF_5')) | ~v1_funct_1(k4_tmap_1(A_209, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_209, '#skF_4')) | u1_struct_0(A_209)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_209) | ~l1_pre_topc(A_209) | ~v2_pre_topc(A_209) | v2_struct_0(A_209))), inference(superposition, [status(thm), theory('equality')], [c_124, c_782])).
% 6.51/2.30  tff(c_1303, plain, (![A_306, B_307]: (r2_hidden('#skF_2'(k4_tmap_1(A_306, '#skF_4'), B_307), k1_relat_1('#skF_5')) | r1_tarski(k4_tmap_1(A_306, '#skF_4'), B_307) | ~r1_tarski(k1_relat_1(k4_tmap_1(A_306, '#skF_4')), k1_relat_1(B_307)) | ~v1_funct_1(B_307) | ~v1_relat_1(B_307) | ~v1_funct_1(k4_tmap_1(A_306, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_306, '#skF_4')) | ~m1_pre_topc('#skF_4', A_306) | ~l1_pre_topc(A_306) | ~v2_pre_topc(A_306) | v2_struct_0(A_306) | u1_struct_0(A_306)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_306) | ~l1_pre_topc(A_306) | ~v2_pre_topc(A_306) | v2_struct_0(A_306))), inference(superposition, [status(thm), theory('equality')], [c_458, c_36])).
% 6.51/2.30  tff(c_38, plain, (![B_32, C_35, A_26]: (k1_funct_1(B_32, C_35)=k1_funct_1(A_26, C_35) | ~r2_hidden(C_35, k1_relat_1(A_26)) | ~r1_tarski(A_26, B_32) | ~v1_funct_1(B_32) | ~v1_relat_1(B_32) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.51/2.30  tff(c_1309, plain, (![B_32, A_306, B_307]: (k1_funct_1(B_32, '#skF_2'(k4_tmap_1(A_306, '#skF_4'), B_307))=k1_funct_1('#skF_5', '#skF_2'(k4_tmap_1(A_306, '#skF_4'), B_307)) | ~r1_tarski('#skF_5', B_32) | ~v1_funct_1(B_32) | ~v1_relat_1(B_32) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | r1_tarski(k4_tmap_1(A_306, '#skF_4'), B_307) | ~r1_tarski(k1_relat_1(k4_tmap_1(A_306, '#skF_4')), k1_relat_1(B_307)) | ~v1_funct_1(B_307) | ~v1_relat_1(B_307) | ~v1_funct_1(k4_tmap_1(A_306, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_306, '#skF_4')) | u1_struct_0(A_306)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_306) | ~l1_pre_topc(A_306) | ~v2_pre_topc(A_306) | v2_struct_0(A_306))), inference(resolution, [status(thm)], [c_1303, c_38])).
% 6.51/2.30  tff(c_1465, plain, (![B_334, A_335, B_336]: (k1_funct_1(B_334, '#skF_2'(k4_tmap_1(A_335, '#skF_4'), B_336))=k1_funct_1('#skF_5', '#skF_2'(k4_tmap_1(A_335, '#skF_4'), B_336)) | ~r1_tarski('#skF_5', B_334) | ~v1_funct_1(B_334) | ~v1_relat_1(B_334) | r1_tarski(k4_tmap_1(A_335, '#skF_4'), B_336) | ~r1_tarski(k1_relat_1(k4_tmap_1(A_335, '#skF_4')), k1_relat_1(B_336)) | ~v1_funct_1(B_336) | ~v1_relat_1(B_336) | ~v1_funct_1(k4_tmap_1(A_335, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_335, '#skF_4')) | u1_struct_0(A_335)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_335) | ~l1_pre_topc(A_335) | ~v2_pre_topc(A_335) | v2_struct_0(A_335))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_64, c_1309])).
% 6.51/2.30  tff(c_1467, plain, (![B_334, A_209]: (k1_funct_1(B_334, '#skF_2'(k4_tmap_1(A_209, '#skF_4'), '#skF_5'))=k1_funct_1('#skF_5', '#skF_2'(k4_tmap_1(A_209, '#skF_4'), '#skF_5')) | ~r1_tarski('#skF_5', B_334) | ~v1_funct_1(B_334) | ~v1_relat_1(B_334) | r1_tarski(k4_tmap_1(A_209, '#skF_4'), '#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1(k4_tmap_1(A_209, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_209, '#skF_4')) | u1_struct_0(A_209)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_209) | ~l1_pre_topc(A_209) | ~v2_pre_topc(A_209) | v2_struct_0(A_209))), inference(resolution, [status(thm)], [c_795, c_1465])).
% 6.51/2.30  tff(c_1515, plain, (![B_340, A_341]: (k1_funct_1(B_340, '#skF_2'(k4_tmap_1(A_341, '#skF_4'), '#skF_5'))=k1_funct_1('#skF_5', '#skF_2'(k4_tmap_1(A_341, '#skF_4'), '#skF_5')) | ~r1_tarski('#skF_5', B_340) | ~v1_funct_1(B_340) | ~v1_relat_1(B_340) | r1_tarski(k4_tmap_1(A_341, '#skF_4'), '#skF_5') | ~v1_funct_1(k4_tmap_1(A_341, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_341, '#skF_4')) | u1_struct_0(A_341)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_341) | ~l1_pre_topc(A_341) | ~v2_pre_topc(A_341) | v2_struct_0(A_341))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_64, c_1467])).
% 6.51/2.30  tff(c_1538, plain, (![A_341]: (~r1_tarski(k1_relat_1(k4_tmap_1(A_341, '#skF_4')), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r1_tarski('#skF_5', k4_tmap_1(A_341, '#skF_4')) | r1_tarski(k4_tmap_1(A_341, '#skF_4'), '#skF_5') | ~v1_funct_1(k4_tmap_1(A_341, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_341, '#skF_4')) | u1_struct_0(A_341)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_341) | ~l1_pre_topc(A_341) | ~v2_pre_topc(A_341) | v2_struct_0(A_341))), inference(superposition, [status(thm), theory('equality')], [c_1515, c_34])).
% 6.51/2.30  tff(c_1560, plain, (![A_342]: (~r1_tarski(k1_relat_1(k4_tmap_1(A_342, '#skF_4')), k1_relat_1('#skF_5')) | ~r1_tarski('#skF_5', k4_tmap_1(A_342, '#skF_4')) | r1_tarski(k4_tmap_1(A_342, '#skF_4'), '#skF_5') | ~v1_funct_1(k4_tmap_1(A_342, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_342, '#skF_4')) | u1_struct_0(A_342)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_342) | ~l1_pre_topc(A_342) | ~v2_pre_topc(A_342) | v2_struct_0(A_342))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_64, c_1538])).
% 6.51/2.30  tff(c_1582, plain, (![A_343]: (~r1_tarski('#skF_5', k4_tmap_1(A_343, '#skF_4')) | r1_tarski(k4_tmap_1(A_343, '#skF_4'), '#skF_5') | ~v1_funct_1(k4_tmap_1(A_343, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_343, '#skF_4')) | u1_struct_0(A_343)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_343) | ~l1_pre_topc(A_343) | ~v2_pre_topc(A_343) | v2_struct_0(A_343))), inference(resolution, [status(thm)], [c_795, c_1560])).
% 6.51/2.30  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.51/2.30  tff(c_1616, plain, (![A_344]: (k4_tmap_1(A_344, '#skF_4')='#skF_5' | ~r1_tarski('#skF_5', k4_tmap_1(A_344, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_344, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_344, '#skF_4')) | u1_struct_0(A_344)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_344) | ~l1_pre_topc(A_344) | ~v2_pre_topc(A_344) | v2_struct_0(A_344))), inference(resolution, [status(thm)], [c_1582, c_4])).
% 6.51/2.30  tff(c_1621, plain, (![A_345]: (k4_tmap_1(A_345, '#skF_4')='#skF_5' | ~v1_funct_1(k4_tmap_1(A_345, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_345, '#skF_4')) | u1_struct_0(A_345)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_345) | ~l1_pre_topc(A_345) | ~v2_pre_topc(A_345) | v2_struct_0(A_345))), inference(resolution, [status(thm)], [c_978, c_1616])).
% 6.51/2.30  tff(c_1638, plain, (![A_350]: (k4_tmap_1(A_350, '#skF_4')='#skF_5' | ~v1_funct_1(k4_tmap_1(A_350, '#skF_4')) | u1_struct_0(A_350)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_350) | ~l1_pre_topc(A_350) | ~v2_pre_topc(A_350) | v2_struct_0(A_350))), inference(resolution, [status(thm)], [c_217, c_1621])).
% 6.51/2.30  tff(c_1644, plain, (![A_351]: (k4_tmap_1(A_351, '#skF_4')='#skF_5' | u1_struct_0(A_351)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_351) | ~l1_pre_topc(A_351) | ~v2_pre_topc(A_351) | v2_struct_0(A_351))), inference(resolution, [status(thm)], [c_52, c_1638])).
% 6.51/2.30  tff(c_1647, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5' | u1_struct_0('#skF_3')=k1_xboole_0 | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1644])).
% 6.51/2.30  tff(c_1650, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5' | u1_struct_0('#skF_3')=k1_xboole_0 | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_1647])).
% 6.51/2.30  tff(c_1651, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5' | u1_struct_0('#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_74, c_1650])).
% 6.51/2.30  tff(c_1652, plain, (u1_struct_0('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1651])).
% 6.51/2.30  tff(c_44, plain, (![A_37]: (~v1_xboole_0(u1_struct_0(A_37)) | ~l1_struct_0(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.51/2.30  tff(c_1777, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1652, c_44])).
% 6.51/2.30  tff(c_1860, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1777])).
% 6.51/2.30  tff(c_1861, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_74, c_1860])).
% 6.51/2.30  tff(c_1865, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_1861])).
% 6.51/2.30  tff(c_1869, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_1865])).
% 6.51/2.30  tff(c_1870, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_1651])).
% 6.51/2.30  tff(c_56, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_193])).
% 6.51/2.30  tff(c_127, plain, (~r2_funct_2(k1_relat_1('#skF_5'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_56])).
% 6.51/2.30  tff(c_1872, plain, (~r2_funct_2(k1_relat_1('#skF_5'), u1_struct_0('#skF_3'), '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1870, c_127])).
% 6.51/2.30  tff(c_1875, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_612, c_1872])).
% 6.51/2.30  tff(c_1876, plain, (u1_struct_0('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_123])).
% 6.51/2.30  tff(c_1886, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1876, c_44])).
% 6.51/2.30  tff(c_1890, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1886])).
% 6.51/2.30  tff(c_1891, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_74, c_1890])).
% 6.51/2.30  tff(c_1895, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_1891])).
% 6.51/2.30  tff(c_1899, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_1895])).
% 6.51/2.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.51/2.30  
% 6.51/2.30  Inference rules
% 6.51/2.30  ----------------------
% 6.51/2.30  #Ref     : 3
% 6.51/2.30  #Sup     : 413
% 6.51/2.30  #Fact    : 0
% 6.51/2.30  #Define  : 0
% 6.51/2.30  #Split   : 4
% 6.51/2.30  #Chain   : 0
% 6.51/2.30  #Close   : 0
% 6.51/2.30  
% 6.51/2.30  Ordering : KBO
% 6.51/2.30  
% 6.51/2.30  Simplification rules
% 6.51/2.30  ----------------------
% 6.51/2.30  #Subsume      : 109
% 6.51/2.30  #Demod        : 430
% 6.51/2.30  #Tautology    : 94
% 6.51/2.30  #SimpNegUnit  : 63
% 6.51/2.30  #BackRed      : 22
% 6.51/2.30  
% 6.51/2.30  #Partial instantiations: 0
% 6.51/2.30  #Strategies tried      : 1
% 6.51/2.30  
% 6.51/2.30  Timing (in seconds)
% 6.51/2.30  ----------------------
% 6.51/2.31  Preprocessing        : 0.36
% 6.51/2.31  Parsing              : 0.19
% 6.51/2.31  CNF conversion       : 0.03
% 6.51/2.31  Main loop            : 1.17
% 6.51/2.31  Inferencing          : 0.38
% 6.51/2.31  Reduction            : 0.32
% 6.51/2.31  Demodulation         : 0.22
% 6.51/2.31  BG Simplification    : 0.06
% 6.51/2.31  Subsumption          : 0.35
% 6.51/2.31  Abstraction          : 0.05
% 6.51/2.31  MUC search           : 0.00
% 6.51/2.31  Cooper               : 0.00
% 6.51/2.31  Total                : 1.58
% 6.51/2.31  Index Insertion      : 0.00
% 6.51/2.31  Index Deletion       : 0.00
% 6.51/2.31  Index Matching       : 0.00
% 6.51/2.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
