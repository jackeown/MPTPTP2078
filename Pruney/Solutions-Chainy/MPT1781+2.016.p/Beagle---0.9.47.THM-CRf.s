%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:47 EST 2020

% Result     : Theorem 14.96s
% Output     : CNFRefutation 15.14s
% Verified   : 
% Statistics : Number of formulae       :  309 (565175 expanded)
%              Number of leaves         :   40 (191416 expanded)
%              Depth                    :   45
%              Number of atoms          : 1228 (2980843 expanded)
%              Number of equality atoms :  196 (579909 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k1_relset_1 > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_182,negated_conjecture,(
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

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_72,axiom,(
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

tff(f_92,axiom,(
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

tff(f_125,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_funct_1(k4_tmap_1(A,B))
        & v1_funct_2(k4_tmap_1(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(k4_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_tmap_1)).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_48,axiom,(
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

tff(f_110,axiom,(
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

tff(f_132,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_152,axiom,(
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

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_60,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_107,plain,(
    ! [A_84,B_85,C_86] :
      ( k1_relset_1(A_84,B_85,C_86) = k1_relat_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_111,plain,(
    k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_107])).

tff(c_131,plain,(
    ! [B_103,A_104,C_105] :
      ( k1_xboole_0 = B_103
      | k1_relset_1(A_104,B_103,C_105) = A_104
      | ~ v1_funct_2(C_105,A_104,B_103)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_104,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_134,plain,
    ( u1_struct_0('#skF_3') = k1_xboole_0
    | k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5') = u1_struct_0('#skF_4')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_58,c_131])).

tff(c_137,plain,
    ( u1_struct_0('#skF_3') = k1_xboole_0
    | u1_struct_0('#skF_4') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_111,c_134])).

tff(c_138,plain,(
    u1_struct_0('#skF_4') = k1_relat_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_144,plain,(
    v1_funct_2('#skF_5',k1_relat_1('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_60])).

tff(c_143,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_58])).

tff(c_32,plain,(
    ! [D_27,A_19,B_20,C_21] :
      ( k1_funct_1(D_27,'#skF_1'(A_19,B_20,C_21,D_27)) != k1_funct_1(C_21,'#skF_1'(A_19,B_20,C_21,D_27))
      | r2_funct_2(A_19,B_20,C_21,D_27)
      | ~ m1_subset_1(D_27,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20)))
      | ~ v1_funct_2(D_27,A_19,B_20)
      | ~ v1_funct_1(D_27)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20)))
      | ~ v1_funct_2(C_21,A_19,B_20)
      | ~ v1_funct_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_7571,plain,(
    ! [A_652,B_653,C_654] :
      ( r2_funct_2(A_652,B_653,C_654,C_654)
      | ~ m1_subset_1(C_654,k1_zfmisc_1(k2_zfmisc_1(A_652,B_653)))
      | ~ v1_funct_2(C_654,A_652,B_653)
      | ~ v1_funct_1(C_654)
      | ~ m1_subset_1(C_654,k1_zfmisc_1(k2_zfmisc_1(A_652,B_653)))
      | ~ v1_funct_2(C_654,A_652,B_653)
      | ~ v1_funct_1(C_654) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_32])).

tff(c_7577,plain,
    ( r2_funct_2(k1_relat_1('#skF_5'),u1_struct_0('#skF_3'),'#skF_5','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_143,c_7571])).

tff(c_7582,plain,(
    r2_funct_2(k1_relat_1('#skF_5'),u1_struct_0('#skF_3'),'#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_144,c_143,c_7577])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_70,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_68,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_64,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_48,plain,(
    ! [A_41,B_42] :
      ( v1_funct_1(k4_tmap_1(A_41,B_42))
      | ~ m1_pre_topc(B_42,A_41)
      | ~ l1_pre_topc(A_41)
      | ~ v2_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_14,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_211,plain,(
    ! [A_111,B_112] :
      ( m1_subset_1(k4_tmap_1(A_111,B_112),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_112),u1_struct_0(A_111))))
      | ~ m1_pre_topc(B_112,A_111)
      | ~ l1_pre_topc(A_111)
      | ~ v2_pre_topc(A_111)
      | v2_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_12,plain,(
    ! [B_10,A_8] :
      ( v1_relat_1(B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_8))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_225,plain,(
    ! [A_111,B_112] :
      ( v1_relat_1(k4_tmap_1(A_111,B_112))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(B_112),u1_struct_0(A_111)))
      | ~ m1_pre_topc(B_112,A_111)
      | ~ l1_pre_topc(A_111)
      | ~ v2_pre_topc(A_111)
      | v2_struct_0(A_111) ) ),
    inference(resolution,[status(thm)],[c_211,c_12])).

tff(c_238,plain,(
    ! [A_111,B_112] :
      ( v1_relat_1(k4_tmap_1(A_111,B_112))
      | ~ m1_pre_topc(B_112,A_111)
      | ~ l1_pre_topc(A_111)
      | ~ v2_pre_topc(A_111)
      | v2_struct_0(A_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_225])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_13,B_14,C_15] :
      ( k1_relset_1(A_13,B_14,C_15) = k1_relat_1(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_7201,plain,(
    ! [B_596,A_597] :
      ( k1_relset_1(u1_struct_0(B_596),u1_struct_0(A_597),k4_tmap_1(A_597,B_596)) = k1_relat_1(k4_tmap_1(A_597,B_596))
      | ~ m1_pre_topc(B_596,A_597)
      | ~ l1_pre_topc(A_597)
      | ~ v2_pre_topc(A_597)
      | v2_struct_0(A_597) ) ),
    inference(resolution,[status(thm)],[c_211,c_16])).

tff(c_7210,plain,(
    ! [A_597] :
      ( k1_relset_1(k1_relat_1('#skF_5'),u1_struct_0(A_597),k4_tmap_1(A_597,'#skF_4')) = k1_relat_1(k4_tmap_1(A_597,'#skF_4'))
      | ~ m1_pre_topc('#skF_4',A_597)
      | ~ l1_pre_topc(A_597)
      | ~ v2_pre_topc(A_597)
      | v2_struct_0(A_597) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_7201])).

tff(c_46,plain,(
    ! [A_41,B_42] :
      ( v1_funct_2(k4_tmap_1(A_41,B_42),u1_struct_0(B_42),u1_struct_0(A_41))
      | ~ m1_pre_topc(B_42,A_41)
      | ~ l1_pre_topc(A_41)
      | ~ v2_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_28,plain,(
    ! [B_17,A_16,C_18] :
      ( k1_xboole_0 = B_17
      | k1_relset_1(A_16,B_17,C_18) = A_16
      | ~ v1_funct_2(C_18,A_16,B_17)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_7313,plain,(
    ! [A_616,B_617] :
      ( u1_struct_0(A_616) = k1_xboole_0
      | k1_relset_1(u1_struct_0(B_617),u1_struct_0(A_616),k4_tmap_1(A_616,B_617)) = u1_struct_0(B_617)
      | ~ v1_funct_2(k4_tmap_1(A_616,B_617),u1_struct_0(B_617),u1_struct_0(A_616))
      | ~ m1_pre_topc(B_617,A_616)
      | ~ l1_pre_topc(A_616)
      | ~ v2_pre_topc(A_616)
      | v2_struct_0(A_616) ) ),
    inference(resolution,[status(thm)],[c_211,c_28])).

tff(c_7328,plain,(
    ! [A_618,B_619] :
      ( u1_struct_0(A_618) = k1_xboole_0
      | k1_relset_1(u1_struct_0(B_619),u1_struct_0(A_618),k4_tmap_1(A_618,B_619)) = u1_struct_0(B_619)
      | ~ m1_pre_topc(B_619,A_618)
      | ~ l1_pre_topc(A_618)
      | ~ v2_pre_topc(A_618)
      | v2_struct_0(A_618) ) ),
    inference(resolution,[status(thm)],[c_46,c_7313])).

tff(c_7343,plain,(
    ! [A_618] :
      ( u1_struct_0(A_618) = k1_xboole_0
      | k1_relset_1(k1_relat_1('#skF_5'),u1_struct_0(A_618),k4_tmap_1(A_618,'#skF_4')) = u1_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_4',A_618)
      | ~ l1_pre_topc(A_618)
      | ~ v2_pre_topc(A_618)
      | v2_struct_0(A_618) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_7328])).

tff(c_7352,plain,(
    ! [A_620] :
      ( u1_struct_0(A_620) = k1_xboole_0
      | k1_relset_1(k1_relat_1('#skF_5'),u1_struct_0(A_620),k4_tmap_1(A_620,'#skF_4')) = k1_relat_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_620)
      | ~ l1_pre_topc(A_620)
      | ~ v2_pre_topc(A_620)
      | v2_struct_0(A_620) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_7343])).

tff(c_7420,plain,(
    ! [A_627] :
      ( u1_struct_0(A_627) = k1_xboole_0
      | k1_relat_1(k4_tmap_1(A_627,'#skF_4')) = k1_relat_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_627)
      | ~ l1_pre_topc(A_627)
      | ~ v2_pre_topc(A_627)
      | v2_struct_0(A_627)
      | ~ m1_pre_topc('#skF_4',A_627)
      | ~ l1_pre_topc(A_627)
      | ~ v2_pre_topc(A_627)
      | v2_struct_0(A_627) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7210,c_7352])).

tff(c_84,plain,(
    ! [B_72,A_73] :
      ( v1_relat_1(B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_73))
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_87,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_58,c_84])).

tff(c_90,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_87])).

tff(c_7238,plain,(
    ! [A_602,B_603] :
      ( r2_hidden('#skF_2'(A_602,B_603),k1_relat_1(A_602))
      | r1_tarski(A_602,B_603)
      | ~ r1_tarski(k1_relat_1(A_602),k1_relat_1(B_603))
      | ~ v1_funct_1(B_603)
      | ~ v1_relat_1(B_603)
      | ~ v1_funct_1(A_602)
      | ~ v1_relat_1(A_602) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_96,plain,(
    ! [B_78,A_79] :
      ( m1_subset_1(u1_struct_0(B_78),k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ m1_pre_topc(B_78,A_79)
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( m1_subset_1(A_5,C_7)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(C_7))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_102,plain,(
    ! [A_5,A_79,B_78] :
      ( m1_subset_1(A_5,u1_struct_0(A_79))
      | ~ r2_hidden(A_5,u1_struct_0(B_78))
      | ~ m1_pre_topc(B_78,A_79)
      | ~ l1_pre_topc(A_79) ) ),
    inference(resolution,[status(thm)],[c_96,c_10])).

tff(c_147,plain,(
    ! [A_5,A_79] :
      ( m1_subset_1(A_5,u1_struct_0(A_79))
      | ~ r2_hidden(A_5,k1_relat_1('#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_79)
      | ~ l1_pre_topc(A_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_102])).

tff(c_7243,plain,(
    ! [B_603,A_79] :
      ( m1_subset_1('#skF_2'('#skF_5',B_603),u1_struct_0(A_79))
      | ~ m1_pre_topc('#skF_4',A_79)
      | ~ l1_pre_topc(A_79)
      | r1_tarski('#skF_5',B_603)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(B_603))
      | ~ v1_funct_1(B_603)
      | ~ v1_relat_1(B_603)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_7238,c_147])).

tff(c_7254,plain,(
    ! [B_603,A_79] :
      ( m1_subset_1('#skF_2'('#skF_5',B_603),u1_struct_0(A_79))
      | ~ m1_pre_topc('#skF_4',A_79)
      | ~ l1_pre_topc(A_79)
      | r1_tarski('#skF_5',B_603)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(B_603))
      | ~ v1_funct_1(B_603)
      | ~ v1_relat_1(B_603) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_62,c_7243])).

tff(c_7431,plain,(
    ! [A_627,A_79] :
      ( m1_subset_1('#skF_2'('#skF_5',k4_tmap_1(A_627,'#skF_4')),u1_struct_0(A_79))
      | ~ m1_pre_topc('#skF_4',A_79)
      | ~ l1_pre_topc(A_79)
      | r1_tarski('#skF_5',k4_tmap_1(A_627,'#skF_4'))
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1('#skF_5'))
      | ~ v1_funct_1(k4_tmap_1(A_627,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_627,'#skF_4'))
      | u1_struct_0(A_627) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_627)
      | ~ l1_pre_topc(A_627)
      | ~ v2_pre_topc(A_627)
      | v2_struct_0(A_627)
      | ~ m1_pre_topc('#skF_4',A_627)
      | ~ l1_pre_topc(A_627)
      | ~ v2_pre_topc(A_627)
      | v2_struct_0(A_627) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7420,c_7254])).

tff(c_7465,plain,(
    ! [A_627,A_79] :
      ( m1_subset_1('#skF_2'('#skF_5',k4_tmap_1(A_627,'#skF_4')),u1_struct_0(A_79))
      | ~ m1_pre_topc('#skF_4',A_79)
      | ~ l1_pre_topc(A_79)
      | r1_tarski('#skF_5',k4_tmap_1(A_627,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_627,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_627,'#skF_4'))
      | u1_struct_0(A_627) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_627)
      | ~ l1_pre_topc(A_627)
      | ~ v2_pre_topc(A_627)
      | v2_struct_0(A_627) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_7431])).

tff(c_234,plain,(
    ! [B_112,A_111] :
      ( k1_relset_1(u1_struct_0(B_112),u1_struct_0(A_111),k4_tmap_1(A_111,B_112)) = k1_relat_1(k4_tmap_1(A_111,B_112))
      | ~ m1_pre_topc(B_112,A_111)
      | ~ l1_pre_topc(A_111)
      | ~ v2_pre_topc(A_111)
      | v2_struct_0(A_111) ) ),
    inference(resolution,[status(thm)],[c_211,c_16])).

tff(c_7373,plain,(
    ! [A_621,B_622] :
      ( k1_relat_1(k4_tmap_1(A_621,B_622)) = u1_struct_0(B_622)
      | ~ m1_pre_topc(B_622,A_621)
      | ~ l1_pre_topc(A_621)
      | ~ v2_pre_topc(A_621)
      | v2_struct_0(A_621)
      | u1_struct_0(A_621) = k1_xboole_0
      | ~ m1_pre_topc(B_622,A_621)
      | ~ l1_pre_topc(A_621)
      | ~ v2_pre_topc(A_621)
      | v2_struct_0(A_621) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7328,c_234])).

tff(c_42,plain,(
    ! [A_31,B_37] :
      ( r1_tarski(k1_relat_1(A_31),k1_relat_1(B_37))
      | ~ r1_tarski(A_31,B_37)
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_7750,plain,(
    ! [B_687,B_688,A_689] :
      ( r1_tarski(u1_struct_0(B_687),k1_relat_1(B_688))
      | ~ r1_tarski(k4_tmap_1(A_689,B_687),B_688)
      | ~ v1_funct_1(B_688)
      | ~ v1_relat_1(B_688)
      | ~ v1_funct_1(k4_tmap_1(A_689,B_687))
      | ~ v1_relat_1(k4_tmap_1(A_689,B_687))
      | ~ m1_pre_topc(B_687,A_689)
      | ~ l1_pre_topc(A_689)
      | ~ v2_pre_topc(A_689)
      | v2_struct_0(A_689)
      | u1_struct_0(A_689) = k1_xboole_0
      | ~ m1_pre_topc(B_687,A_689)
      | ~ l1_pre_topc(A_689)
      | ~ v2_pre_topc(A_689)
      | v2_struct_0(A_689) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7373,c_42])).

tff(c_7755,plain,(
    ! [B_690,A_691] :
      ( r1_tarski(u1_struct_0(B_690),k1_relat_1(k4_tmap_1(A_691,B_690)))
      | ~ v1_funct_1(k4_tmap_1(A_691,B_690))
      | ~ v1_relat_1(k4_tmap_1(A_691,B_690))
      | u1_struct_0(A_691) = k1_xboole_0
      | ~ m1_pre_topc(B_690,A_691)
      | ~ l1_pre_topc(A_691)
      | ~ v2_pre_topc(A_691)
      | v2_struct_0(A_691) ) ),
    inference(resolution,[status(thm)],[c_6,c_7750])).

tff(c_7781,plain,(
    ! [A_697] :
      ( r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(k4_tmap_1(A_697,'#skF_4')))
      | ~ v1_funct_1(k4_tmap_1(A_697,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_697,'#skF_4'))
      | u1_struct_0(A_697) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_697)
      | ~ l1_pre_topc(A_697)
      | ~ v2_pre_topc(A_697)
      | v2_struct_0(A_697) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_7755])).

tff(c_56,plain,(
    ! [D_64] :
      ( k1_funct_1('#skF_5',D_64) = D_64
      | ~ r2_hidden(D_64,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(D_64,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_140,plain,(
    ! [D_64] :
      ( k1_funct_1('#skF_5',D_64) = D_64
      | ~ r2_hidden(D_64,k1_relat_1('#skF_5'))
      | ~ m1_subset_1(D_64,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_56])).

tff(c_7247,plain,(
    ! [B_603] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',B_603)) = '#skF_2'('#skF_5',B_603)
      | ~ m1_subset_1('#skF_2'('#skF_5',B_603),u1_struct_0('#skF_3'))
      | r1_tarski('#skF_5',B_603)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(B_603))
      | ~ v1_funct_1(B_603)
      | ~ v1_relat_1(B_603)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_7238,c_140])).

tff(c_7257,plain,(
    ! [B_603] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',B_603)) = '#skF_2'('#skF_5',B_603)
      | ~ m1_subset_1('#skF_2'('#skF_5',B_603),u1_struct_0('#skF_3'))
      | r1_tarski('#skF_5',B_603)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(B_603))
      | ~ v1_funct_1(B_603)
      | ~ v1_relat_1(B_603) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_62,c_7247])).

tff(c_7840,plain,(
    ! [A_701] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',k4_tmap_1(A_701,'#skF_4'))) = '#skF_2'('#skF_5',k4_tmap_1(A_701,'#skF_4'))
      | ~ m1_subset_1('#skF_2'('#skF_5',k4_tmap_1(A_701,'#skF_4')),u1_struct_0('#skF_3'))
      | r1_tarski('#skF_5',k4_tmap_1(A_701,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_701,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_701,'#skF_4'))
      | u1_struct_0(A_701) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_701)
      | ~ l1_pre_topc(A_701)
      | ~ v2_pre_topc(A_701)
      | v2_struct_0(A_701) ) ),
    inference(resolution,[status(thm)],[c_7781,c_7257])).

tff(c_7844,plain,(
    ! [A_627] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',k4_tmap_1(A_627,'#skF_4'))) = '#skF_2'('#skF_5',k4_tmap_1(A_627,'#skF_4'))
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | r1_tarski('#skF_5',k4_tmap_1(A_627,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_627,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_627,'#skF_4'))
      | u1_struct_0(A_627) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_627)
      | ~ l1_pre_topc(A_627)
      | ~ v2_pre_topc(A_627)
      | v2_struct_0(A_627) ) ),
    inference(resolution,[status(thm)],[c_7465,c_7840])).

tff(c_7847,plain,(
    ! [A_627] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',k4_tmap_1(A_627,'#skF_4'))) = '#skF_2'('#skF_5',k4_tmap_1(A_627,'#skF_4'))
      | r1_tarski('#skF_5',k4_tmap_1(A_627,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_627,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_627,'#skF_4'))
      | u1_struct_0(A_627) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_627)
      | ~ l1_pre_topc(A_627)
      | ~ v2_pre_topc(A_627)
      | v2_struct_0(A_627) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_7844])).

tff(c_7768,plain,(
    ! [A_691] :
      ( r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(k4_tmap_1(A_691,'#skF_4')))
      | ~ v1_funct_1(k4_tmap_1(A_691,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_691,'#skF_4'))
      | u1_struct_0(A_691) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_691)
      | ~ l1_pre_topc(A_691)
      | ~ v2_pre_topc(A_691)
      | v2_struct_0(A_691) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_7755])).

tff(c_7557,plain,(
    ! [A_646,A_647] :
      ( m1_subset_1('#skF_2'('#skF_5',k4_tmap_1(A_646,'#skF_4')),u1_struct_0(A_647))
      | ~ m1_pre_topc('#skF_4',A_647)
      | ~ l1_pre_topc(A_647)
      | r1_tarski('#skF_5',k4_tmap_1(A_646,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_646,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_646,'#skF_4'))
      | u1_struct_0(A_646) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_646)
      | ~ l1_pre_topc(A_646)
      | ~ v2_pre_topc(A_646)
      | v2_struct_0(A_646) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_7431])).

tff(c_38,plain,(
    ! [A_31,B_37] :
      ( r2_hidden('#skF_2'(A_31,B_37),k1_relat_1(A_31))
      | r1_tarski(A_31,B_37)
      | ~ r1_tarski(k1_relat_1(A_31),k1_relat_1(B_37))
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_7259,plain,(
    ! [A_604,B_605,C_606] :
      ( k1_funct_1(k4_tmap_1(A_604,B_605),C_606) = C_606
      | ~ r2_hidden(C_606,u1_struct_0(B_605))
      | ~ m1_subset_1(C_606,u1_struct_0(A_604))
      | ~ m1_pre_topc(B_605,A_604)
      | v2_struct_0(B_605)
      | ~ l1_pre_topc(A_604)
      | ~ v2_pre_topc(A_604)
      | v2_struct_0(A_604) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_7261,plain,(
    ! [A_604,C_606] :
      ( k1_funct_1(k4_tmap_1(A_604,'#skF_4'),C_606) = C_606
      | ~ r2_hidden(C_606,k1_relat_1('#skF_5'))
      | ~ m1_subset_1(C_606,u1_struct_0(A_604))
      | ~ m1_pre_topc('#skF_4',A_604)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_604)
      | ~ v2_pre_topc(A_604)
      | v2_struct_0(A_604) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_7259])).

tff(c_7272,plain,(
    ! [A_609,C_610] :
      ( k1_funct_1(k4_tmap_1(A_609,'#skF_4'),C_610) = C_610
      | ~ r2_hidden(C_610,k1_relat_1('#skF_5'))
      | ~ m1_subset_1(C_610,u1_struct_0(A_609))
      | ~ m1_pre_topc('#skF_4',A_609)
      | ~ l1_pre_topc(A_609)
      | ~ v2_pre_topc(A_609)
      | v2_struct_0(A_609) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_7261])).

tff(c_7275,plain,(
    ! [A_609,B_37] :
      ( k1_funct_1(k4_tmap_1(A_609,'#skF_4'),'#skF_2'('#skF_5',B_37)) = '#skF_2'('#skF_5',B_37)
      | ~ m1_subset_1('#skF_2'('#skF_5',B_37),u1_struct_0(A_609))
      | ~ m1_pre_topc('#skF_4',A_609)
      | ~ l1_pre_topc(A_609)
      | ~ v2_pre_topc(A_609)
      | v2_struct_0(A_609)
      | r1_tarski('#skF_5',B_37)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(B_37))
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_38,c_7272])).

tff(c_7278,plain,(
    ! [A_609,B_37] :
      ( k1_funct_1(k4_tmap_1(A_609,'#skF_4'),'#skF_2'('#skF_5',B_37)) = '#skF_2'('#skF_5',B_37)
      | ~ m1_subset_1('#skF_2'('#skF_5',B_37),u1_struct_0(A_609))
      | ~ m1_pre_topc('#skF_4',A_609)
      | ~ l1_pre_topc(A_609)
      | ~ v2_pre_topc(A_609)
      | v2_struct_0(A_609)
      | r1_tarski('#skF_5',B_37)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(B_37))
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_62,c_7275])).

tff(c_7565,plain,(
    ! [A_647,A_646] :
      ( k1_funct_1(k4_tmap_1(A_647,'#skF_4'),'#skF_2'('#skF_5',k4_tmap_1(A_646,'#skF_4'))) = '#skF_2'('#skF_5',k4_tmap_1(A_646,'#skF_4'))
      | ~ v2_pre_topc(A_647)
      | v2_struct_0(A_647)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(k4_tmap_1(A_646,'#skF_4')))
      | ~ m1_pre_topc('#skF_4',A_647)
      | ~ l1_pre_topc(A_647)
      | r1_tarski('#skF_5',k4_tmap_1(A_646,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_646,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_646,'#skF_4'))
      | u1_struct_0(A_646) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_646)
      | ~ l1_pre_topc(A_646)
      | ~ v2_pre_topc(A_646)
      | v2_struct_0(A_646) ) ),
    inference(resolution,[status(thm)],[c_7557,c_7278])).

tff(c_7889,plain,(
    ! [A_707,A_708] :
      ( k1_funct_1(k4_tmap_1(A_707,'#skF_4'),'#skF_2'('#skF_5',k4_tmap_1(A_708,'#skF_4'))) = '#skF_2'('#skF_5',k4_tmap_1(A_708,'#skF_4'))
      | ~ v2_pre_topc(A_707)
      | v2_struct_0(A_707)
      | ~ m1_pre_topc('#skF_4',A_707)
      | ~ l1_pre_topc(A_707)
      | r1_tarski('#skF_5',k4_tmap_1(A_708,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_708,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_708,'#skF_4'))
      | u1_struct_0(A_708) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_708)
      | ~ l1_pre_topc(A_708)
      | ~ v2_pre_topc(A_708)
      | v2_struct_0(A_708) ) ),
    inference(resolution,[status(thm)],[c_7781,c_7565])).

tff(c_36,plain,(
    ! [B_37,A_31] :
      ( k1_funct_1(B_37,'#skF_2'(A_31,B_37)) != k1_funct_1(A_31,'#skF_2'(A_31,B_37))
      | r1_tarski(A_31,B_37)
      | ~ r1_tarski(k1_relat_1(A_31),k1_relat_1(B_37))
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_7898,plain,(
    ! [A_708] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',k4_tmap_1(A_708,'#skF_4'))) != '#skF_2'('#skF_5',k4_tmap_1(A_708,'#skF_4'))
      | r1_tarski('#skF_5',k4_tmap_1(A_708,'#skF_4'))
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(k4_tmap_1(A_708,'#skF_4')))
      | ~ v1_funct_1(k4_tmap_1(A_708,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_708,'#skF_4'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ v2_pre_topc(A_708)
      | v2_struct_0(A_708)
      | ~ m1_pre_topc('#skF_4',A_708)
      | ~ l1_pre_topc(A_708)
      | r1_tarski('#skF_5',k4_tmap_1(A_708,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_708,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_708,'#skF_4'))
      | u1_struct_0(A_708) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_708)
      | ~ l1_pre_topc(A_708)
      | ~ v2_pre_topc(A_708)
      | v2_struct_0(A_708) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7889,c_36])).

tff(c_7919,plain,(
    ! [A_711] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',k4_tmap_1(A_711,'#skF_4'))) != '#skF_2'('#skF_5',k4_tmap_1(A_711,'#skF_4'))
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(k4_tmap_1(A_711,'#skF_4')))
      | r1_tarski('#skF_5',k4_tmap_1(A_711,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_711,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_711,'#skF_4'))
      | u1_struct_0(A_711) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_711)
      | ~ l1_pre_topc(A_711)
      | ~ v2_pre_topc(A_711)
      | v2_struct_0(A_711) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_62,c_7898])).

tff(c_7941,plain,(
    ! [A_712] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',k4_tmap_1(A_712,'#skF_4'))) != '#skF_2'('#skF_5',k4_tmap_1(A_712,'#skF_4'))
      | r1_tarski('#skF_5',k4_tmap_1(A_712,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_712,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_712,'#skF_4'))
      | u1_struct_0(A_712) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_712)
      | ~ l1_pre_topc(A_712)
      | ~ v2_pre_topc(A_712)
      | v2_struct_0(A_712) ) ),
    inference(resolution,[status(thm)],[c_7768,c_7919])).

tff(c_7948,plain,(
    ! [A_627] :
      ( r1_tarski('#skF_5',k4_tmap_1(A_627,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_627,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_627,'#skF_4'))
      | u1_struct_0(A_627) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_627)
      | ~ l1_pre_topc(A_627)
      | ~ v2_pre_topc(A_627)
      | v2_struct_0(A_627) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7847,c_7941])).

tff(c_7615,plain,(
    ! [A_669,B_670,A_671] :
      ( r1_tarski(k1_relat_1(A_669),u1_struct_0(B_670))
      | ~ r1_tarski(A_669,k4_tmap_1(A_671,B_670))
      | ~ v1_funct_1(k4_tmap_1(A_671,B_670))
      | ~ v1_relat_1(k4_tmap_1(A_671,B_670))
      | ~ v1_funct_1(A_669)
      | ~ v1_relat_1(A_669)
      | ~ m1_pre_topc(B_670,A_671)
      | ~ l1_pre_topc(A_671)
      | ~ v2_pre_topc(A_671)
      | v2_struct_0(A_671)
      | u1_struct_0(A_671) = k1_xboole_0
      | ~ m1_pre_topc(B_670,A_671)
      | ~ l1_pre_topc(A_671)
      | ~ v2_pre_topc(A_671)
      | v2_struct_0(A_671) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7373,c_42])).

tff(c_7620,plain,(
    ! [A_672,B_673] :
      ( r1_tarski(k1_relat_1(k4_tmap_1(A_672,B_673)),u1_struct_0(B_673))
      | ~ v1_funct_1(k4_tmap_1(A_672,B_673))
      | ~ v1_relat_1(k4_tmap_1(A_672,B_673))
      | u1_struct_0(A_672) = k1_xboole_0
      | ~ m1_pre_topc(B_673,A_672)
      | ~ l1_pre_topc(A_672)
      | ~ v2_pre_topc(A_672)
      | v2_struct_0(A_672) ) ),
    inference(resolution,[status(thm)],[c_6,c_7615])).

tff(c_7633,plain,(
    ! [A_672] :
      ( r1_tarski(k1_relat_1(k4_tmap_1(A_672,'#skF_4')),k1_relat_1('#skF_5'))
      | ~ v1_funct_1(k4_tmap_1(A_672,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_672,'#skF_4'))
      | u1_struct_0(A_672) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_672)
      | ~ l1_pre_topc(A_672)
      | ~ v2_pre_topc(A_672)
      | v2_struct_0(A_672) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_7620])).

tff(c_8200,plain,(
    ! [A_775,B_776,B_777] :
      ( r2_hidden('#skF_2'(k4_tmap_1(A_775,B_776),B_777),u1_struct_0(B_776))
      | r1_tarski(k4_tmap_1(A_775,B_776),B_777)
      | ~ r1_tarski(k1_relat_1(k4_tmap_1(A_775,B_776)),k1_relat_1(B_777))
      | ~ v1_funct_1(B_777)
      | ~ v1_relat_1(B_777)
      | ~ v1_funct_1(k4_tmap_1(A_775,B_776))
      | ~ v1_relat_1(k4_tmap_1(A_775,B_776))
      | ~ m1_pre_topc(B_776,A_775)
      | ~ l1_pre_topc(A_775)
      | ~ v2_pre_topc(A_775)
      | v2_struct_0(A_775)
      | u1_struct_0(A_775) = k1_xboole_0
      | ~ m1_pre_topc(B_776,A_775)
      | ~ l1_pre_topc(A_775)
      | ~ v2_pre_topc(A_775)
      | v2_struct_0(A_775) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7373,c_38])).

tff(c_8301,plain,(
    ! [A_799,B_800] :
      ( r2_hidden('#skF_2'(k4_tmap_1(A_799,'#skF_4'),B_800),k1_relat_1('#skF_5'))
      | r1_tarski(k4_tmap_1(A_799,'#skF_4'),B_800)
      | ~ r1_tarski(k1_relat_1(k4_tmap_1(A_799,'#skF_4')),k1_relat_1(B_800))
      | ~ v1_funct_1(B_800)
      | ~ v1_relat_1(B_800)
      | ~ v1_funct_1(k4_tmap_1(A_799,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_799,'#skF_4'))
      | ~ m1_pre_topc('#skF_4',A_799)
      | ~ l1_pre_topc(A_799)
      | ~ v2_pre_topc(A_799)
      | v2_struct_0(A_799)
      | u1_struct_0(A_799) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_799)
      | ~ l1_pre_topc(A_799)
      | ~ v2_pre_topc(A_799)
      | v2_struct_0(A_799) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_8200])).

tff(c_40,plain,(
    ! [B_37,C_40,A_31] :
      ( k1_funct_1(B_37,C_40) = k1_funct_1(A_31,C_40)
      | ~ r2_hidden(C_40,k1_relat_1(A_31))
      | ~ r1_tarski(A_31,B_37)
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_8307,plain,(
    ! [B_37,A_799,B_800] :
      ( k1_funct_1(B_37,'#skF_2'(k4_tmap_1(A_799,'#skF_4'),B_800)) = k1_funct_1('#skF_5','#skF_2'(k4_tmap_1(A_799,'#skF_4'),B_800))
      | ~ r1_tarski('#skF_5',B_37)
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | r1_tarski(k4_tmap_1(A_799,'#skF_4'),B_800)
      | ~ r1_tarski(k1_relat_1(k4_tmap_1(A_799,'#skF_4')),k1_relat_1(B_800))
      | ~ v1_funct_1(B_800)
      | ~ v1_relat_1(B_800)
      | ~ v1_funct_1(k4_tmap_1(A_799,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_799,'#skF_4'))
      | u1_struct_0(A_799) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_799)
      | ~ l1_pre_topc(A_799)
      | ~ v2_pre_topc(A_799)
      | v2_struct_0(A_799) ) ),
    inference(resolution,[status(thm)],[c_8301,c_40])).

tff(c_8449,plain,(
    ! [B_822,A_823,B_824] :
      ( k1_funct_1(B_822,'#skF_2'(k4_tmap_1(A_823,'#skF_4'),B_824)) = k1_funct_1('#skF_5','#skF_2'(k4_tmap_1(A_823,'#skF_4'),B_824))
      | ~ r1_tarski('#skF_5',B_822)
      | ~ v1_funct_1(B_822)
      | ~ v1_relat_1(B_822)
      | r1_tarski(k4_tmap_1(A_823,'#skF_4'),B_824)
      | ~ r1_tarski(k1_relat_1(k4_tmap_1(A_823,'#skF_4')),k1_relat_1(B_824))
      | ~ v1_funct_1(B_824)
      | ~ v1_relat_1(B_824)
      | ~ v1_funct_1(k4_tmap_1(A_823,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_823,'#skF_4'))
      | u1_struct_0(A_823) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_823)
      | ~ l1_pre_topc(A_823)
      | ~ v2_pre_topc(A_823)
      | v2_struct_0(A_823) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_62,c_8307])).

tff(c_8451,plain,(
    ! [B_822,A_672] :
      ( k1_funct_1(B_822,'#skF_2'(k4_tmap_1(A_672,'#skF_4'),'#skF_5')) = k1_funct_1('#skF_5','#skF_2'(k4_tmap_1(A_672,'#skF_4'),'#skF_5'))
      | ~ r1_tarski('#skF_5',B_822)
      | ~ v1_funct_1(B_822)
      | ~ v1_relat_1(B_822)
      | r1_tarski(k4_tmap_1(A_672,'#skF_4'),'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_funct_1(k4_tmap_1(A_672,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_672,'#skF_4'))
      | u1_struct_0(A_672) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_672)
      | ~ l1_pre_topc(A_672)
      | ~ v2_pre_topc(A_672)
      | v2_struct_0(A_672) ) ),
    inference(resolution,[status(thm)],[c_7633,c_8449])).

tff(c_8483,plain,(
    ! [B_828,A_829] :
      ( k1_funct_1(B_828,'#skF_2'(k4_tmap_1(A_829,'#skF_4'),'#skF_5')) = k1_funct_1('#skF_5','#skF_2'(k4_tmap_1(A_829,'#skF_4'),'#skF_5'))
      | ~ r1_tarski('#skF_5',B_828)
      | ~ v1_funct_1(B_828)
      | ~ v1_relat_1(B_828)
      | r1_tarski(k4_tmap_1(A_829,'#skF_4'),'#skF_5')
      | ~ v1_funct_1(k4_tmap_1(A_829,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_829,'#skF_4'))
      | u1_struct_0(A_829) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_829)
      | ~ l1_pre_topc(A_829)
      | ~ v2_pre_topc(A_829)
      | v2_struct_0(A_829) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_62,c_8451])).

tff(c_8506,plain,(
    ! [A_829] :
      ( ~ r1_tarski(k1_relat_1(k4_tmap_1(A_829,'#skF_4')),k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_5',k4_tmap_1(A_829,'#skF_4'))
      | r1_tarski(k4_tmap_1(A_829,'#skF_4'),'#skF_5')
      | ~ v1_funct_1(k4_tmap_1(A_829,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_829,'#skF_4'))
      | u1_struct_0(A_829) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_829)
      | ~ l1_pre_topc(A_829)
      | ~ v2_pre_topc(A_829)
      | v2_struct_0(A_829) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8483,c_36])).

tff(c_8528,plain,(
    ! [A_830] :
      ( ~ r1_tarski(k1_relat_1(k4_tmap_1(A_830,'#skF_4')),k1_relat_1('#skF_5'))
      | ~ r1_tarski('#skF_5',k4_tmap_1(A_830,'#skF_4'))
      | r1_tarski(k4_tmap_1(A_830,'#skF_4'),'#skF_5')
      | ~ v1_funct_1(k4_tmap_1(A_830,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_830,'#skF_4'))
      | u1_struct_0(A_830) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_830)
      | ~ l1_pre_topc(A_830)
      | ~ v2_pre_topc(A_830)
      | v2_struct_0(A_830) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_62,c_8506])).

tff(c_8550,plain,(
    ! [A_831] :
      ( ~ r1_tarski('#skF_5',k4_tmap_1(A_831,'#skF_4'))
      | r1_tarski(k4_tmap_1(A_831,'#skF_4'),'#skF_5')
      | ~ v1_funct_1(k4_tmap_1(A_831,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_831,'#skF_4'))
      | u1_struct_0(A_831) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_831)
      | ~ l1_pre_topc(A_831)
      | ~ v2_pre_topc(A_831)
      | v2_struct_0(A_831) ) ),
    inference(resolution,[status(thm)],[c_7633,c_8528])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8584,plain,(
    ! [A_832] :
      ( k4_tmap_1(A_832,'#skF_4') = '#skF_5'
      | ~ r1_tarski('#skF_5',k4_tmap_1(A_832,'#skF_4'))
      | ~ v1_funct_1(k4_tmap_1(A_832,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_832,'#skF_4'))
      | u1_struct_0(A_832) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_832)
      | ~ l1_pre_topc(A_832)
      | ~ v2_pre_topc(A_832)
      | v2_struct_0(A_832) ) ),
    inference(resolution,[status(thm)],[c_8550,c_2])).

tff(c_8589,plain,(
    ! [A_833] :
      ( k4_tmap_1(A_833,'#skF_4') = '#skF_5'
      | ~ v1_funct_1(k4_tmap_1(A_833,'#skF_4'))
      | ~ v1_relat_1(k4_tmap_1(A_833,'#skF_4'))
      | u1_struct_0(A_833) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_833)
      | ~ l1_pre_topc(A_833)
      | ~ v2_pre_topc(A_833)
      | v2_struct_0(A_833) ) ),
    inference(resolution,[status(thm)],[c_7948,c_8584])).

tff(c_8595,plain,(
    ! [A_834] :
      ( k4_tmap_1(A_834,'#skF_4') = '#skF_5'
      | ~ v1_funct_1(k4_tmap_1(A_834,'#skF_4'))
      | u1_struct_0(A_834) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_834)
      | ~ l1_pre_topc(A_834)
      | ~ v2_pre_topc(A_834)
      | v2_struct_0(A_834) ) ),
    inference(resolution,[status(thm)],[c_238,c_8589])).

tff(c_8601,plain,(
    ! [A_835] :
      ( k4_tmap_1(A_835,'#skF_4') = '#skF_5'
      | u1_struct_0(A_835) = k1_xboole_0
      | ~ m1_pre_topc('#skF_4',A_835)
      | ~ l1_pre_topc(A_835)
      | ~ v2_pre_topc(A_835)
      | v2_struct_0(A_835) ) ),
    inference(resolution,[status(thm)],[c_48,c_8595])).

tff(c_8604,plain,
    ( k4_tmap_1('#skF_3','#skF_4') = '#skF_5'
    | u1_struct_0('#skF_3') = k1_xboole_0
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_8601])).

tff(c_8607,plain,
    ( k4_tmap_1('#skF_3','#skF_4') = '#skF_5'
    | u1_struct_0('#skF_3') = k1_xboole_0
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_8604])).

tff(c_8608,plain,
    ( k4_tmap_1('#skF_3','#skF_4') = '#skF_5'
    | u1_struct_0('#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_8607])).

tff(c_8609,plain,(
    u1_struct_0('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8608])).

tff(c_8622,plain,(
    v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8609,c_144])).

tff(c_8620,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8609,c_143])).

tff(c_20,plain,(
    ! [C_18,A_16] :
      ( k1_xboole_0 = C_18
      | ~ v1_funct_2(C_18,A_16,k1_xboole_0)
      | k1_xboole_0 = A_16
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8860,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k1_xboole_0)
    | k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8620,c_20])).

tff(c_8885,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8622,c_8860])).

tff(c_8891,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8885])).

tff(c_8613,plain,(
    r2_funct_2(k1_relat_1('#skF_5'),k1_xboole_0,'#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8609,c_7582])).

tff(c_8905,plain,(
    r2_funct_2(k1_xboole_0,k1_xboole_0,'#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8891,c_8613])).

tff(c_228,plain,(
    ! [A_111] :
      ( m1_subset_1(k4_tmap_1(A_111,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),u1_struct_0(A_111))))
      | ~ m1_pre_topc('#skF_4',A_111)
      | ~ l1_pre_topc(A_111)
      | ~ v2_pre_topc(A_111)
      | v2_struct_0(A_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_211])).

tff(c_8721,plain,
    ( m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k1_xboole_0)))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8609,c_228])).

tff(c_8817,plain,
    ( m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k1_xboole_0)))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_8721])).

tff(c_8818,plain,(
    m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k1_xboole_0))) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_8817])).

tff(c_9237,plain,(
    m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8891,c_8818])).

tff(c_9266,plain,
    ( v1_relat_1(k4_tmap_1('#skF_3','#skF_4'))
    | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_9237,c_12])).

tff(c_9294,plain,(
    v1_relat_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_9266])).

tff(c_163,plain,(
    ! [A_106,B_107] :
      ( v1_funct_2(k4_tmap_1(A_106,B_107),u1_struct_0(B_107),u1_struct_0(A_106))
      | ~ m1_pre_topc(B_107,A_106)
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_166,plain,(
    ! [A_106] :
      ( v1_funct_2(k4_tmap_1(A_106,'#skF_4'),k1_relat_1('#skF_5'),u1_struct_0(A_106))
      | ~ m1_pre_topc('#skF_4',A_106)
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_163])).

tff(c_8724,plain,
    ( v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),k1_relat_1('#skF_5'),k1_xboole_0)
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8609,c_166])).

tff(c_8820,plain,
    ( v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),k1_relat_1('#skF_5'),k1_xboole_0)
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_8724])).

tff(c_8821,plain,(
    v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),k1_relat_1('#skF_5'),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_8820])).

tff(c_9033,plain,(
    v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8891,c_8821])).

tff(c_7569,plain,(
    ! [A_19,B_20,C_21] :
      ( r2_funct_2(A_19,B_20,C_21,C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20)))
      | ~ v1_funct_2(C_21,A_19,B_20)
      | ~ v1_funct_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20)))
      | ~ v1_funct_2(C_21,A_19,B_20)
      | ~ v1_funct_1(C_21) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_32])).

tff(c_9239,plain,
    ( r2_funct_2(k1_xboole_0,k1_xboole_0,k4_tmap_1('#skF_3','#skF_4'),k4_tmap_1('#skF_3','#skF_4'))
    | ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_9237,c_7569])).

tff(c_9269,plain,
    ( r2_funct_2(k1_xboole_0,k1_xboole_0,k4_tmap_1('#skF_3','#skF_4'),k4_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9033,c_9237,c_9239])).

tff(c_9829,plain,(
    ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_9269])).

tff(c_9832,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_9829])).

tff(c_9835,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_9832])).

tff(c_9837,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_9835])).

tff(c_9839,plain,(
    v1_funct_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_9269])).

tff(c_26,plain,(
    ! [B_17,C_18] :
      ( k1_relset_1(k1_xboole_0,B_17,C_18) = k1_xboole_0
      | ~ v1_funct_2(C_18,k1_xboole_0,B_17)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_9255,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1('#skF_3','#skF_4')) = k1_xboole_0
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_9237,c_26])).

tff(c_9285,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9033,c_9255])).

tff(c_8703,plain,
    ( k1_relset_1(k1_relat_1('#skF_5'),k1_xboole_0,k4_tmap_1('#skF_3','#skF_4')) = k1_relat_1(k4_tmap_1('#skF_3','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8609,c_7210])).

tff(c_8805,plain,
    ( k1_relset_1(k1_relat_1('#skF_5'),k1_xboole_0,k4_tmap_1('#skF_3','#skF_4')) = k1_relat_1(k4_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_8703])).

tff(c_8806,plain,(
    k1_relset_1(k1_relat_1('#skF_5'),k1_xboole_0,k4_tmap_1('#skF_3','#skF_4')) = k1_relat_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_8805])).

tff(c_9445,plain,(
    k1_relat_1(k4_tmap_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9285,c_8891,c_8806])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,B_4)
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_7258,plain,(
    ! [A_602,B_603] :
      ( m1_subset_1('#skF_2'(A_602,B_603),k1_relat_1(A_602))
      | r1_tarski(A_602,B_603)
      | ~ r1_tarski(k1_relat_1(A_602),k1_relat_1(B_603))
      | ~ v1_funct_1(B_603)
      | ~ v1_relat_1(B_603)
      | ~ v1_funct_1(A_602)
      | ~ v1_relat_1(A_602) ) ),
    inference(resolution,[status(thm)],[c_7238,c_8])).

tff(c_8972,plain,(
    ! [B_603] :
      ( m1_subset_1('#skF_2'('#skF_5',B_603),k1_relat_1('#skF_5'))
      | r1_tarski('#skF_5',B_603)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_603))
      | ~ v1_funct_1(B_603)
      | ~ v1_relat_1(B_603)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8891,c_7258])).

tff(c_9997,plain,(
    ! [B_898] :
      ( m1_subset_1('#skF_2'('#skF_5',B_898),k1_xboole_0)
      | r1_tarski('#skF_5',B_898)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_898))
      | ~ v1_funct_1(B_898)
      | ~ v1_relat_1(B_898) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_62,c_8891,c_8972])).

tff(c_10003,plain,
    ( m1_subset_1('#skF_2'('#skF_5',k4_tmap_1('#skF_3','#skF_4')),k1_xboole_0)
    | r1_tarski('#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | ~ v1_relat_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9445,c_9997])).

tff(c_10012,plain,
    ( m1_subset_1('#skF_2'('#skF_5',k4_tmap_1('#skF_3','#skF_4')),k1_xboole_0)
    | r1_tarski('#skF_5',k4_tmap_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9294,c_9839,c_6,c_10003])).

tff(c_10015,plain,(
    r1_tarski('#skF_5',k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_10012])).

tff(c_10041,plain,
    ( k4_tmap_1('#skF_3','#skF_4') = '#skF_5'
    | ~ r1_tarski(k4_tmap_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_10015,c_2])).

tff(c_10069,plain,(
    ~ r1_tarski(k4_tmap_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_10041])).

tff(c_9508,plain,(
    ! [B_37] :
      ( r2_hidden('#skF_2'(k4_tmap_1('#skF_3','#skF_4'),B_37),k1_xboole_0)
      | r1_tarski(k4_tmap_1('#skF_3','#skF_4'),B_37)
      | ~ r1_tarski(k1_relat_1(k4_tmap_1('#skF_3','#skF_4')),k1_relat_1(B_37))
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37)
      | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
      | ~ v1_relat_1(k4_tmap_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9445,c_38])).

tff(c_9589,plain,(
    ! [B_37] :
      ( r2_hidden('#skF_2'(k4_tmap_1('#skF_3','#skF_4'),B_37),k1_xboole_0)
      | r1_tarski(k4_tmap_1('#skF_3','#skF_4'),B_37)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_37))
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37)
      | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9294,c_9445,c_9508])).

tff(c_11564,plain,(
    ! [B_37] :
      ( r2_hidden('#skF_2'(k4_tmap_1('#skF_3','#skF_4'),B_37),k1_xboole_0)
      | r1_tarski(k4_tmap_1('#skF_3','#skF_4'),B_37)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_37))
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9839,c_9589])).

tff(c_7251,plain,(
    ! [B_37,A_602,B_603] :
      ( k1_funct_1(B_37,'#skF_2'(A_602,B_603)) = k1_funct_1(A_602,'#skF_2'(A_602,B_603))
      | ~ r1_tarski(A_602,B_37)
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37)
      | r1_tarski(A_602,B_603)
      | ~ r1_tarski(k1_relat_1(A_602),k1_relat_1(B_603))
      | ~ v1_funct_1(B_603)
      | ~ v1_relat_1(B_603)
      | ~ v1_funct_1(A_602)
      | ~ v1_relat_1(A_602) ) ),
    inference(resolution,[status(thm)],[c_7238,c_40])).

tff(c_8970,plain,(
    ! [B_37,A_602] :
      ( k1_funct_1(B_37,'#skF_2'(A_602,'#skF_5')) = k1_funct_1(A_602,'#skF_2'(A_602,'#skF_5'))
      | ~ r1_tarski(A_602,B_37)
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37)
      | r1_tarski(A_602,'#skF_5')
      | ~ r1_tarski(k1_relat_1(A_602),k1_xboole_0)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_funct_1(A_602)
      | ~ v1_relat_1(A_602) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8891,c_7251])).

tff(c_11987,plain,(
    ! [B_989,A_990] :
      ( k1_funct_1(B_989,'#skF_2'(A_990,'#skF_5')) = k1_funct_1(A_990,'#skF_2'(A_990,'#skF_5'))
      | ~ r1_tarski(A_990,B_989)
      | ~ v1_funct_1(B_989)
      | ~ v1_relat_1(B_989)
      | r1_tarski(A_990,'#skF_5')
      | ~ r1_tarski(k1_relat_1(A_990),k1_xboole_0)
      | ~ v1_funct_1(A_990)
      | ~ v1_relat_1(A_990) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_62,c_8970])).

tff(c_12001,plain,(
    ! [B_989] :
      ( k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5')) = k1_funct_1(B_989,'#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5'))
      | ~ r1_tarski(k4_tmap_1('#skF_3','#skF_4'),B_989)
      | ~ v1_funct_1(B_989)
      | ~ v1_relat_1(B_989)
      | r1_tarski(k4_tmap_1('#skF_3','#skF_4'),'#skF_5')
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
      | ~ v1_relat_1(k4_tmap_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9445,c_11987])).

tff(c_12015,plain,(
    ! [B_989] :
      ( k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5')) = k1_funct_1(B_989,'#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5'))
      | ~ r1_tarski(k4_tmap_1('#skF_3','#skF_4'),B_989)
      | ~ v1_funct_1(B_989)
      | ~ v1_relat_1(B_989)
      | r1_tarski(k4_tmap_1('#skF_3','#skF_4'),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9294,c_9839,c_6,c_12001])).

tff(c_12029,plain,(
    ! [B_994] :
      ( k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5')) = k1_funct_1(B_994,'#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5'))
      | ~ r1_tarski(k4_tmap_1('#skF_3','#skF_4'),B_994)
      | ~ v1_funct_1(B_994)
      | ~ v1_relat_1(B_994) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10069,c_12015])).

tff(c_8941,plain,(
    ! [A_5,A_79] :
      ( m1_subset_1(A_5,u1_struct_0(A_79))
      | ~ r2_hidden(A_5,k1_xboole_0)
      | ~ m1_pre_topc('#skF_4',A_79)
      | ~ l1_pre_topc(A_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8891,c_147])).

tff(c_8944,plain,(
    u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8891,c_138])).

tff(c_52,plain,(
    ! [A_46,B_50,C_52] :
      ( k1_funct_1(k4_tmap_1(A_46,B_50),C_52) = C_52
      | ~ r2_hidden(C_52,u1_struct_0(B_50))
      | ~ m1_subset_1(C_52,u1_struct_0(A_46))
      | ~ m1_pre_topc(B_50,A_46)
      | v2_struct_0(B_50)
      | ~ l1_pre_topc(A_46)
      | ~ v2_pre_topc(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_9089,plain,(
    ! [A_46,C_52] :
      ( k1_funct_1(k4_tmap_1(A_46,'#skF_4'),C_52) = C_52
      | ~ r2_hidden(C_52,k1_xboole_0)
      | ~ m1_subset_1(C_52,u1_struct_0(A_46))
      | ~ m1_pre_topc('#skF_4',A_46)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_46)
      | ~ v2_pre_topc(A_46)
      | v2_struct_0(A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8944,c_52])).

tff(c_10138,plain,(
    ! [A_908,C_909] :
      ( k1_funct_1(k4_tmap_1(A_908,'#skF_4'),C_909) = C_909
      | ~ r2_hidden(C_909,k1_xboole_0)
      | ~ m1_subset_1(C_909,u1_struct_0(A_908))
      | ~ m1_pre_topc('#skF_4',A_908)
      | ~ l1_pre_topc(A_908)
      | ~ v2_pre_topc(A_908)
      | v2_struct_0(A_908) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_9089])).

tff(c_10157,plain,(
    ! [A_79,A_5] :
      ( k1_funct_1(k4_tmap_1(A_79,'#skF_4'),A_5) = A_5
      | ~ v2_pre_topc(A_79)
      | v2_struct_0(A_79)
      | ~ r2_hidden(A_5,k1_xboole_0)
      | ~ m1_pre_topc('#skF_4',A_79)
      | ~ l1_pre_topc(A_79) ) ),
    inference(resolution,[status(thm)],[c_8941,c_10138])).

tff(c_12053,plain,(
    ! [B_994] :
      ( k1_funct_1(B_994,'#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5')) = '#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden('#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5'),k1_xboole_0)
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(k4_tmap_1('#skF_3','#skF_4'),B_994)
      | ~ v1_funct_1(B_994)
      | ~ v1_relat_1(B_994) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12029,c_10157])).

tff(c_12149,plain,(
    ! [B_994] :
      ( k1_funct_1(B_994,'#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5')) = '#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden('#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5'),k1_xboole_0)
      | ~ r1_tarski(k4_tmap_1('#skF_3','#skF_4'),B_994)
      | ~ v1_funct_1(B_994)
      | ~ v1_relat_1(B_994) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_70,c_12053])).

tff(c_12150,plain,(
    ! [B_994] :
      ( k1_funct_1(B_994,'#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5')) = '#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5')
      | ~ r2_hidden('#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5'),k1_xboole_0)
      | ~ r1_tarski(k4_tmap_1('#skF_3','#skF_4'),B_994)
      | ~ v1_funct_1(B_994)
      | ~ v1_relat_1(B_994) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_12149])).

tff(c_12313,plain,(
    ~ r2_hidden('#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_12150])).

tff(c_12316,plain,
    ( r1_tarski(k4_tmap_1('#skF_3','#skF_4'),'#skF_5')
    | ~ r1_tarski(k1_xboole_0,k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_11564,c_12313])).

tff(c_12319,plain,(
    r1_tarski(k4_tmap_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_62,c_6,c_8891,c_12316])).

tff(c_12321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10069,c_12319])).

tff(c_12323,plain,(
    r2_hidden('#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_12150])).

tff(c_8974,plain,(
    ! [A_602] :
      ( m1_subset_1('#skF_2'(A_602,'#skF_5'),k1_relat_1(A_602))
      | r1_tarski(A_602,'#skF_5')
      | ~ r1_tarski(k1_relat_1(A_602),k1_xboole_0)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_funct_1(A_602)
      | ~ v1_relat_1(A_602) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8891,c_7258])).

tff(c_10117,plain,(
    ! [A_907] :
      ( m1_subset_1('#skF_2'(A_907,'#skF_5'),k1_relat_1(A_907))
      | r1_tarski(A_907,'#skF_5')
      | ~ r1_tarski(k1_relat_1(A_907),k1_xboole_0)
      | ~ v1_funct_1(A_907)
      | ~ v1_relat_1(A_907) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_62,c_8974])).

tff(c_10122,plain,
    ( m1_subset_1('#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5'),k1_xboole_0)
    | r1_tarski(k4_tmap_1('#skF_3','#skF_4'),'#skF_5')
    | ~ r1_tarski(k1_relat_1(k4_tmap_1('#skF_3','#skF_4')),k1_xboole_0)
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | ~ v1_relat_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9445,c_10117])).

tff(c_10131,plain,
    ( m1_subset_1('#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5'),k1_xboole_0)
    | r1_tarski(k4_tmap_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9294,c_9839,c_6,c_9445,c_10122])).

tff(c_10132,plain,(
    m1_subset_1('#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5'),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_10069,c_10131])).

tff(c_10150,plain,(
    ! [C_909] :
      ( k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),C_909) = C_909
      | ~ r2_hidden(C_909,k1_xboole_0)
      | ~ m1_subset_1(C_909,k1_xboole_0)
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8609,c_10138])).

tff(c_10161,plain,(
    ! [C_909] :
      ( k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),C_909) = C_909
      | ~ r2_hidden(C_909,k1_xboole_0)
      | ~ m1_subset_1(C_909,k1_xboole_0)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_10150])).

tff(c_10162,plain,(
    ! [C_909] :
      ( k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),C_909) = C_909
      | ~ r2_hidden(C_909,k1_xboole_0)
      | ~ m1_subset_1(C_909,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_10161])).

tff(c_12080,plain,(
    ! [B_994] :
      ( k1_funct_1(B_994,'#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5')) != k1_funct_1('#skF_5','#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5'))
      | r1_tarski(k4_tmap_1('#skF_3','#skF_4'),'#skF_5')
      | ~ r1_tarski(k1_relat_1(k4_tmap_1('#skF_3','#skF_4')),k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
      | ~ v1_relat_1(k4_tmap_1('#skF_3','#skF_4'))
      | ~ r1_tarski(k4_tmap_1('#skF_3','#skF_4'),B_994)
      | ~ v1_funct_1(B_994)
      | ~ v1_relat_1(B_994) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12029,c_36])).

tff(c_12174,plain,(
    ! [B_994] :
      ( k1_funct_1(B_994,'#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5')) != k1_funct_1('#skF_5','#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5'))
      | r1_tarski(k4_tmap_1('#skF_3','#skF_4'),'#skF_5')
      | ~ r1_tarski(k4_tmap_1('#skF_3','#skF_4'),B_994)
      | ~ v1_funct_1(B_994)
      | ~ v1_relat_1(B_994) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9294,c_9839,c_90,c_62,c_6,c_8891,c_9445,c_12080])).

tff(c_12220,plain,(
    ! [B_995] :
      ( k1_funct_1(B_995,'#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5')) != k1_funct_1('#skF_5','#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5'))
      | ~ r1_tarski(k4_tmap_1('#skF_3','#skF_4'),B_995)
      | ~ v1_funct_1(B_995)
      | ~ v1_relat_1(B_995) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10069,c_12174])).

tff(c_12250,plain,
    ( k1_funct_1('#skF_5','#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5')) != '#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5')
    | ~ r1_tarski(k4_tmap_1('#skF_3','#skF_4'),k4_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | ~ v1_relat_1(k4_tmap_1('#skF_3','#skF_4'))
    | ~ r2_hidden('#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5'),k1_xboole_0)
    | ~ m1_subset_1('#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10162,c_12220])).

tff(c_12289,plain,
    ( k1_funct_1('#skF_5','#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5')) != '#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5')
    | ~ r2_hidden('#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10132,c_9294,c_9839,c_6,c_12250])).

tff(c_12312,plain,(
    ~ r2_hidden('#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_12289])).

tff(c_12339,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12323,c_12312])).

tff(c_12340,plain,(
    k1_funct_1('#skF_5','#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5')) != '#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_12289])).

tff(c_12341,plain,(
    r2_hidden('#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_12289])).

tff(c_8617,plain,(
    ! [D_64] :
      ( k1_funct_1('#skF_5',D_64) = D_64
      | ~ r2_hidden(D_64,k1_relat_1('#skF_5'))
      | ~ m1_subset_1(D_64,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8609,c_140])).

tff(c_9606,plain,(
    ! [D_64] :
      ( k1_funct_1('#skF_5',D_64) = D_64
      | ~ r2_hidden(D_64,k1_xboole_0)
      | ~ m1_subset_1(D_64,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8891,c_8617])).

tff(c_12346,plain,
    ( k1_funct_1('#skF_5','#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5')) = '#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5')
    | ~ m1_subset_1('#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12341,c_9606])).

tff(c_12353,plain,(
    k1_funct_1('#skF_5','#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5')) = '#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10132,c_12346])).

tff(c_12379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12340,c_12353])).

tff(c_12380,plain,(
    k4_tmap_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_10041])).

tff(c_54,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_142,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_5'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_54])).

tff(c_8619,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_5'),k1_xboole_0,k4_tmap_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8609,c_142])).

tff(c_9308,plain,(
    ~ r2_funct_2(k1_xboole_0,k1_xboole_0,k4_tmap_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8891,c_8619])).

tff(c_12387,plain,(
    ~ r2_funct_2(k1_xboole_0,k1_xboole_0,'#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12380,c_9308])).

tff(c_12398,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8905,c_12387])).

tff(c_12400,plain,(
    ~ r1_tarski('#skF_5',k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_10012])).

tff(c_12399,plain,(
    m1_subset_1('#skF_2'('#skF_5',k4_tmap_1('#skF_3','#skF_4')),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_10012])).

tff(c_8689,plain,(
    ! [B_37] :
      ( k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_2'('#skF_5',B_37)) = '#skF_2'('#skF_5',B_37)
      | ~ m1_subset_1('#skF_2'('#skF_5',B_37),k1_xboole_0)
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | r1_tarski('#skF_5',B_37)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(B_37))
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8609,c_7278])).

tff(c_8794,plain,(
    ! [B_37] :
      ( k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_2'('#skF_5',B_37)) = '#skF_2'('#skF_5',B_37)
      | ~ m1_subset_1('#skF_2'('#skF_5',B_37),k1_xboole_0)
      | v2_struct_0('#skF_3')
      | r1_tarski('#skF_5',B_37)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(B_37))
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_8689])).

tff(c_8795,plain,(
    ! [B_37] :
      ( k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_2'('#skF_5',B_37)) = '#skF_2'('#skF_5',B_37)
      | ~ m1_subset_1('#skF_2'('#skF_5',B_37),k1_xboole_0)
      | r1_tarski('#skF_5',B_37)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(B_37))
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_8794])).

tff(c_13171,plain,(
    ! [B_1034] :
      ( k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_2'('#skF_5',B_1034)) = '#skF_2'('#skF_5',B_1034)
      | ~ m1_subset_1('#skF_2'('#skF_5',B_1034),k1_xboole_0)
      | r1_tarski('#skF_5',B_1034)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_1034))
      | ~ v1_funct_1(B_1034)
      | ~ v1_relat_1(B_1034) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8891,c_8795])).

tff(c_13187,plain,
    ( k1_funct_1('#skF_5','#skF_2'('#skF_5',k4_tmap_1('#skF_3','#skF_4'))) != '#skF_2'('#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | r1_tarski('#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(k4_tmap_1('#skF_3','#skF_4')))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | ~ v1_relat_1(k4_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ m1_subset_1('#skF_2'('#skF_5',k4_tmap_1('#skF_3','#skF_4')),k1_xboole_0)
    | r1_tarski('#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(k4_tmap_1('#skF_3','#skF_4')))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | ~ v1_relat_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13171,c_36])).

tff(c_13210,plain,
    ( k1_funct_1('#skF_5','#skF_2'('#skF_5',k4_tmap_1('#skF_3','#skF_4'))) != '#skF_2'('#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | r1_tarski('#skF_5',k4_tmap_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9294,c_9839,c_6,c_9445,c_12399,c_90,c_62,c_9294,c_9839,c_6,c_8891,c_9445,c_13187])).

tff(c_13211,plain,(
    k1_funct_1('#skF_5','#skF_2'('#skF_5',k4_tmap_1('#skF_3','#skF_4'))) != '#skF_2'('#skF_5',k4_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_12400,c_13210])).

tff(c_8977,plain,(
    ! [B_37] :
      ( r2_hidden('#skF_2'('#skF_5',B_37),k1_xboole_0)
      | r1_tarski('#skF_5',B_37)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(B_37))
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8891,c_38])).

tff(c_12438,plain,(
    ! [B_1001] :
      ( r2_hidden('#skF_2'('#skF_5',B_1001),k1_xboole_0)
      | r1_tarski('#skF_5',B_1001)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_1001))
      | ~ v1_funct_1(B_1001)
      | ~ v1_relat_1(B_1001) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_62,c_8891,c_8977])).

tff(c_13957,plain,(
    ! [B_1066] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',B_1066)) = '#skF_2'('#skF_5',B_1066)
      | ~ m1_subset_1('#skF_2'('#skF_5',B_1066),k1_xboole_0)
      | r1_tarski('#skF_5',B_1066)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_1066))
      | ~ v1_funct_1(B_1066)
      | ~ v1_relat_1(B_1066) ) ),
    inference(resolution,[status(thm)],[c_12438,c_9606])).

tff(c_13969,plain,
    ( k1_funct_1('#skF_5','#skF_2'('#skF_5',k4_tmap_1('#skF_3','#skF_4'))) = '#skF_2'('#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_2'('#skF_5',k4_tmap_1('#skF_3','#skF_4')),k1_xboole_0)
    | r1_tarski('#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | ~ v1_relat_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9445,c_13957])).

tff(c_13982,plain,
    ( k1_funct_1('#skF_5','#skF_2'('#skF_5',k4_tmap_1('#skF_3','#skF_4'))) = '#skF_2'('#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | r1_tarski('#skF_5',k4_tmap_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9294,c_9839,c_6,c_12399,c_13969])).

tff(c_13984,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12400,c_13211,c_13982])).

tff(c_13985,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_8885])).

tff(c_13999,plain,(
    r2_funct_2(k1_relat_1('#skF_5'),'#skF_5','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13985,c_8613])).

tff(c_13986,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8885])).

tff(c_14063,plain,(
    k1_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13985,c_13986])).

tff(c_14228,plain,(
    v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),k1_relat_1('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13985,c_8821])).

tff(c_14336,plain,(
    m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13985,c_8818])).

tff(c_14559,plain,(
    ! [C_1106,A_1107] :
      ( C_1106 = '#skF_5'
      | ~ v1_funct_2(C_1106,A_1107,'#skF_5')
      | A_1107 = '#skF_5'
      | ~ m1_subset_1(C_1106,k1_zfmisc_1(k2_zfmisc_1(A_1107,'#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13985,c_13985,c_13985,c_13985,c_20])).

tff(c_14565,plain,
    ( k4_tmap_1('#skF_3','#skF_4') = '#skF_5'
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),k1_relat_1('#skF_5'),'#skF_5')
    | k1_relat_1('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_14336,c_14559])).

tff(c_14572,plain,
    ( k4_tmap_1('#skF_3','#skF_4') = '#skF_5'
    | k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14228,c_14565])).

tff(c_14573,plain,(
    k4_tmap_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_14063,c_14572])).

tff(c_14304,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_5'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13985,c_8619])).

tff(c_14583,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_5'),'#skF_5','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14573,c_14304])).

tff(c_14590,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13999,c_14583])).

tff(c_14591,plain,(
    k4_tmap_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_8608])).

tff(c_14593,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_5'),u1_struct_0('#skF_3'),'#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14591,c_142])).

tff(c_14596,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7582,c_14593])).

tff(c_14597,plain,(
    u1_struct_0('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_14604,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14597,c_60])).

tff(c_14603,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14597,c_58])).

tff(c_14641,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k1_xboole_0)
    | u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14603,c_20])).

tff(c_14659,plain,
    ( k1_xboole_0 = '#skF_5'
    | u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14604,c_14641])).

tff(c_14665,plain,(
    u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_14659])).

tff(c_14598,plain,(
    u1_struct_0('#skF_4') != k1_relat_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_14669,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14665,c_14598])).

tff(c_14668,plain,(
    v1_funct_2('#skF_5',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14665,c_14604])).

tff(c_14667,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14665,c_14603])).

tff(c_14702,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_5') = k1_xboole_0
    | ~ v1_funct_2('#skF_5',k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14667,c_26])).

tff(c_14725,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14668,c_14702])).

tff(c_14730,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_14667,c_16])).

tff(c_14777,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14725,c_14730])).

tff(c_14778,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14669,c_14777])).

tff(c_14779,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_14659])).

tff(c_14780,plain,(
    u1_struct_0('#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_14659])).

tff(c_14797,plain,(
    u1_struct_0('#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14779,c_14780])).

tff(c_14623,plain,(
    ! [A_1108,B_1109] :
      ( v1_funct_2(k4_tmap_1(A_1108,B_1109),u1_struct_0(B_1109),u1_struct_0(A_1108))
      | ~ m1_pre_topc(B_1109,A_1108)
      | ~ l1_pre_topc(A_1108)
      | ~ v2_pre_topc(A_1108)
      | v2_struct_0(A_1108) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_14629,plain,(
    ! [B_1109] :
      ( v1_funct_2(k4_tmap_1('#skF_3',B_1109),u1_struct_0(B_1109),k1_xboole_0)
      | ~ m1_pre_topc(B_1109,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14597,c_14623])).

tff(c_14631,plain,(
    ! [B_1109] :
      ( v1_funct_2(k4_tmap_1('#skF_3',B_1109),u1_struct_0(B_1109),k1_xboole_0)
      | ~ m1_pre_topc(B_1109,'#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_14629])).

tff(c_14632,plain,(
    ! [B_1109] :
      ( v1_funct_2(k4_tmap_1('#skF_3',B_1109),u1_struct_0(B_1109),k1_xboole_0)
      | ~ m1_pre_topc(B_1109,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_14631])).

tff(c_14795,plain,(
    ! [B_1109] :
      ( v1_funct_2(k4_tmap_1('#skF_3',B_1109),u1_struct_0(B_1109),'#skF_5')
      | ~ m1_pre_topc(B_1109,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14779,c_14632])).

tff(c_14784,plain,(
    u1_struct_0('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14779,c_14597])).

tff(c_14841,plain,(
    ! [A_1114,B_1115] :
      ( m1_subset_1(k4_tmap_1(A_1114,B_1115),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_1115),u1_struct_0(A_1114))))
      | ~ m1_pre_topc(B_1115,A_1114)
      | ~ l1_pre_topc(A_1114)
      | ~ v2_pre_topc(A_1114)
      | v2_struct_0(A_1114) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_14855,plain,(
    ! [B_1115] :
      ( m1_subset_1(k4_tmap_1('#skF_3',B_1115),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_1115),'#skF_5')))
      | ~ m1_pre_topc(B_1115,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14784,c_14841])).

tff(c_14862,plain,(
    ! [B_1115] :
      ( m1_subset_1(k4_tmap_1('#skF_3',B_1115),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_1115),'#skF_5')))
      | ~ m1_pre_topc(B_1115,'#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_14855])).

tff(c_14863,plain,(
    ! [B_1115] :
      ( m1_subset_1(k4_tmap_1('#skF_3',B_1115),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_1115),'#skF_5')))
      | ~ m1_pre_topc(B_1115,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_14862])).

tff(c_14972,plain,(
    ! [C_1138,A_1139] :
      ( C_1138 = '#skF_5'
      | ~ v1_funct_2(C_1138,A_1139,'#skF_5')
      | A_1139 = '#skF_5'
      | ~ m1_subset_1(C_1138,k1_zfmisc_1(k2_zfmisc_1(A_1139,'#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14779,c_14779,c_14779,c_14779,c_20])).

tff(c_15054,plain,(
    ! [B_1157] :
      ( k4_tmap_1('#skF_3',B_1157) = '#skF_5'
      | ~ v1_funct_2(k4_tmap_1('#skF_3',B_1157),u1_struct_0(B_1157),'#skF_5')
      | u1_struct_0(B_1157) = '#skF_5'
      | ~ m1_pre_topc(B_1157,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_14863,c_14972])).

tff(c_15063,plain,(
    ! [B_1158] :
      ( k4_tmap_1('#skF_3',B_1158) = '#skF_5'
      | u1_struct_0(B_1158) = '#skF_5'
      | ~ m1_pre_topc(B_1158,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_14795,c_15054])).

tff(c_15066,plain,
    ( k4_tmap_1('#skF_3','#skF_4') = '#skF_5'
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_64,c_15063])).

tff(c_15069,plain,(
    k4_tmap_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_14797,c_15066])).

tff(c_14602,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),k1_xboole_0,k4_tmap_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14597,c_54])).

tff(c_14781,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14779,c_14602])).

tff(c_15076,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),'#skF_5','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15069,c_14781])).

tff(c_14783,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14779,c_14604])).

tff(c_14782,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),'#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14779,c_14603])).

tff(c_15561,plain,(
    ! [A_1214,B_1215,C_1216] :
      ( r2_funct_2(A_1214,B_1215,C_1216,C_1216)
      | ~ m1_subset_1(C_1216,k1_zfmisc_1(k2_zfmisc_1(A_1214,B_1215)))
      | ~ v1_funct_2(C_1216,A_1214,B_1215)
      | ~ v1_funct_1(C_1216)
      | ~ m1_subset_1(C_1216,k1_zfmisc_1(k2_zfmisc_1(A_1214,B_1215)))
      | ~ v1_funct_2(C_1216,A_1214,B_1215)
      | ~ v1_funct_1(C_1216) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_32])).

tff(c_15567,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),'#skF_5','#skF_5','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),'#skF_5')))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),'#skF_5')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_14782,c_15561])).

tff(c_15574,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),'#skF_5','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_14783,c_14782,c_15567])).

tff(c_15576,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15076,c_15574])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.96/5.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.14/5.80  
% 15.14/5.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.14/5.80  %$ r2_funct_2 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k1_relset_1 > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 15.14/5.80  
% 15.14/5.80  %Foreground sorts:
% 15.14/5.80  
% 15.14/5.80  
% 15.14/5.80  %Background operators:
% 15.14/5.80  
% 15.14/5.80  
% 15.14/5.80  %Foreground operators:
% 15.14/5.80  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 15.14/5.80  tff(k4_tmap_1, type, k4_tmap_1: ($i * $i) > $i).
% 15.14/5.80  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 15.14/5.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.14/5.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.14/5.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.14/5.80  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 15.14/5.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.14/5.80  tff('#skF_5', type, '#skF_5': $i).
% 15.14/5.80  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 15.14/5.80  tff('#skF_3', type, '#skF_3': $i).
% 15.14/5.80  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 15.14/5.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.14/5.80  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 15.14/5.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.14/5.80  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.14/5.80  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 15.14/5.80  tff('#skF_4', type, '#skF_4': $i).
% 15.14/5.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.14/5.80  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 15.14/5.80  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 15.14/5.80  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 15.14/5.80  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 15.14/5.80  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 15.14/5.80  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.14/5.80  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 15.14/5.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.14/5.80  
% 15.14/5.84  tff(f_182, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, u1_struct_0(B)) => (D = k1_funct_1(C, D))))) => r2_funct_2(u1_struct_0(B), u1_struct_0(A), k4_tmap_1(A, B), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_tmap_1)).
% 15.14/5.84  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 15.14/5.84  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 15.14/5.84  tff(f_92, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_2)).
% 15.14/5.84  tff(f_125, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_funct_1(k4_tmap_1(A, B)) & v1_funct_2(k4_tmap_1(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(k4_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_tmap_1)).
% 15.14/5.84  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 15.14/5.84  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 15.14/5.84  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.14/5.84  tff(f_110, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, B) <=> (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_grfunc_1)).
% 15.14/5.84  tff(f_132, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 15.14/5.84  tff(f_41, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 15.14/5.84  tff(f_152, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, u1_struct_0(B)) => (k1_funct_1(k4_tmap_1(A, B), C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_tmap_1)).
% 15.14/5.84  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 15.14/5.84  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_182])).
% 15.14/5.84  tff(c_60, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 15.14/5.84  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_182])).
% 15.14/5.84  tff(c_107, plain, (![A_84, B_85, C_86]: (k1_relset_1(A_84, B_85, C_86)=k1_relat_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.14/5.84  tff(c_111, plain, (k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_107])).
% 15.14/5.84  tff(c_131, plain, (![B_103, A_104, C_105]: (k1_xboole_0=B_103 | k1_relset_1(A_104, B_103, C_105)=A_104 | ~v1_funct_2(C_105, A_104, B_103) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_104, B_103))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.14/5.84  tff(c_134, plain, (u1_struct_0('#skF_3')=k1_xboole_0 | k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5')=u1_struct_0('#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_58, c_131])).
% 15.14/5.84  tff(c_137, plain, (u1_struct_0('#skF_3')=k1_xboole_0 | u1_struct_0('#skF_4')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_111, c_134])).
% 15.14/5.84  tff(c_138, plain, (u1_struct_0('#skF_4')=k1_relat_1('#skF_5')), inference(splitLeft, [status(thm)], [c_137])).
% 15.14/5.84  tff(c_144, plain, (v1_funct_2('#skF_5', k1_relat_1('#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_60])).
% 15.14/5.84  tff(c_143, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_58])).
% 15.14/5.84  tff(c_32, plain, (![D_27, A_19, B_20, C_21]: (k1_funct_1(D_27, '#skF_1'(A_19, B_20, C_21, D_27))!=k1_funct_1(C_21, '#skF_1'(A_19, B_20, C_21, D_27)) | r2_funct_2(A_19, B_20, C_21, D_27) | ~m1_subset_1(D_27, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))) | ~v1_funct_2(D_27, A_19, B_20) | ~v1_funct_1(D_27) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))) | ~v1_funct_2(C_21, A_19, B_20) | ~v1_funct_1(C_21))), inference(cnfTransformation, [status(thm)], [f_92])).
% 15.14/5.84  tff(c_7571, plain, (![A_652, B_653, C_654]: (r2_funct_2(A_652, B_653, C_654, C_654) | ~m1_subset_1(C_654, k1_zfmisc_1(k2_zfmisc_1(A_652, B_653))) | ~v1_funct_2(C_654, A_652, B_653) | ~v1_funct_1(C_654) | ~m1_subset_1(C_654, k1_zfmisc_1(k2_zfmisc_1(A_652, B_653))) | ~v1_funct_2(C_654, A_652, B_653) | ~v1_funct_1(C_654))), inference(reflexivity, [status(thm), theory('equality')], [c_32])).
% 15.14/5.84  tff(c_7577, plain, (r2_funct_2(k1_relat_1('#skF_5'), u1_struct_0('#skF_3'), '#skF_5', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_143, c_7571])).
% 15.14/5.84  tff(c_7582, plain, (r2_funct_2(k1_relat_1('#skF_5'), u1_struct_0('#skF_3'), '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_144, c_143, c_7577])).
% 15.14/5.84  tff(c_72, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_182])).
% 15.14/5.84  tff(c_70, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_182])).
% 15.14/5.84  tff(c_68, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_182])).
% 15.14/5.84  tff(c_64, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_182])).
% 15.14/5.84  tff(c_48, plain, (![A_41, B_42]: (v1_funct_1(k4_tmap_1(A_41, B_42)) | ~m1_pre_topc(B_42, A_41) | ~l1_pre_topc(A_41) | ~v2_pre_topc(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_125])).
% 15.14/5.84  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 15.14/5.84  tff(c_211, plain, (![A_111, B_112]: (m1_subset_1(k4_tmap_1(A_111, B_112), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_112), u1_struct_0(A_111)))) | ~m1_pre_topc(B_112, A_111) | ~l1_pre_topc(A_111) | ~v2_pre_topc(A_111) | v2_struct_0(A_111))), inference(cnfTransformation, [status(thm)], [f_125])).
% 15.14/5.84  tff(c_12, plain, (![B_10, A_8]: (v1_relat_1(B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(A_8)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 15.14/5.84  tff(c_225, plain, (![A_111, B_112]: (v1_relat_1(k4_tmap_1(A_111, B_112)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(B_112), u1_struct_0(A_111))) | ~m1_pre_topc(B_112, A_111) | ~l1_pre_topc(A_111) | ~v2_pre_topc(A_111) | v2_struct_0(A_111))), inference(resolution, [status(thm)], [c_211, c_12])).
% 15.14/5.84  tff(c_238, plain, (![A_111, B_112]: (v1_relat_1(k4_tmap_1(A_111, B_112)) | ~m1_pre_topc(B_112, A_111) | ~l1_pre_topc(A_111) | ~v2_pre_topc(A_111) | v2_struct_0(A_111))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_225])).
% 15.14/5.84  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.14/5.84  tff(c_16, plain, (![A_13, B_14, C_15]: (k1_relset_1(A_13, B_14, C_15)=k1_relat_1(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.14/5.84  tff(c_7201, plain, (![B_596, A_597]: (k1_relset_1(u1_struct_0(B_596), u1_struct_0(A_597), k4_tmap_1(A_597, B_596))=k1_relat_1(k4_tmap_1(A_597, B_596)) | ~m1_pre_topc(B_596, A_597) | ~l1_pre_topc(A_597) | ~v2_pre_topc(A_597) | v2_struct_0(A_597))), inference(resolution, [status(thm)], [c_211, c_16])).
% 15.14/5.84  tff(c_7210, plain, (![A_597]: (k1_relset_1(k1_relat_1('#skF_5'), u1_struct_0(A_597), k4_tmap_1(A_597, '#skF_4'))=k1_relat_1(k4_tmap_1(A_597, '#skF_4')) | ~m1_pre_topc('#skF_4', A_597) | ~l1_pre_topc(A_597) | ~v2_pre_topc(A_597) | v2_struct_0(A_597))), inference(superposition, [status(thm), theory('equality')], [c_138, c_7201])).
% 15.14/5.84  tff(c_46, plain, (![A_41, B_42]: (v1_funct_2(k4_tmap_1(A_41, B_42), u1_struct_0(B_42), u1_struct_0(A_41)) | ~m1_pre_topc(B_42, A_41) | ~l1_pre_topc(A_41) | ~v2_pre_topc(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_125])).
% 15.14/5.84  tff(c_28, plain, (![B_17, A_16, C_18]: (k1_xboole_0=B_17 | k1_relset_1(A_16, B_17, C_18)=A_16 | ~v1_funct_2(C_18, A_16, B_17) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.14/5.84  tff(c_7313, plain, (![A_616, B_617]: (u1_struct_0(A_616)=k1_xboole_0 | k1_relset_1(u1_struct_0(B_617), u1_struct_0(A_616), k4_tmap_1(A_616, B_617))=u1_struct_0(B_617) | ~v1_funct_2(k4_tmap_1(A_616, B_617), u1_struct_0(B_617), u1_struct_0(A_616)) | ~m1_pre_topc(B_617, A_616) | ~l1_pre_topc(A_616) | ~v2_pre_topc(A_616) | v2_struct_0(A_616))), inference(resolution, [status(thm)], [c_211, c_28])).
% 15.14/5.84  tff(c_7328, plain, (![A_618, B_619]: (u1_struct_0(A_618)=k1_xboole_0 | k1_relset_1(u1_struct_0(B_619), u1_struct_0(A_618), k4_tmap_1(A_618, B_619))=u1_struct_0(B_619) | ~m1_pre_topc(B_619, A_618) | ~l1_pre_topc(A_618) | ~v2_pre_topc(A_618) | v2_struct_0(A_618))), inference(resolution, [status(thm)], [c_46, c_7313])).
% 15.14/5.84  tff(c_7343, plain, (![A_618]: (u1_struct_0(A_618)=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_5'), u1_struct_0(A_618), k4_tmap_1(A_618, '#skF_4'))=u1_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', A_618) | ~l1_pre_topc(A_618) | ~v2_pre_topc(A_618) | v2_struct_0(A_618))), inference(superposition, [status(thm), theory('equality')], [c_138, c_7328])).
% 15.14/5.84  tff(c_7352, plain, (![A_620]: (u1_struct_0(A_620)=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_5'), u1_struct_0(A_620), k4_tmap_1(A_620, '#skF_4'))=k1_relat_1('#skF_5') | ~m1_pre_topc('#skF_4', A_620) | ~l1_pre_topc(A_620) | ~v2_pre_topc(A_620) | v2_struct_0(A_620))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_7343])).
% 15.14/5.84  tff(c_7420, plain, (![A_627]: (u1_struct_0(A_627)=k1_xboole_0 | k1_relat_1(k4_tmap_1(A_627, '#skF_4'))=k1_relat_1('#skF_5') | ~m1_pre_topc('#skF_4', A_627) | ~l1_pre_topc(A_627) | ~v2_pre_topc(A_627) | v2_struct_0(A_627) | ~m1_pre_topc('#skF_4', A_627) | ~l1_pre_topc(A_627) | ~v2_pre_topc(A_627) | v2_struct_0(A_627))), inference(superposition, [status(thm), theory('equality')], [c_7210, c_7352])).
% 15.14/5.84  tff(c_84, plain, (![B_72, A_73]: (v1_relat_1(B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(A_73)) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_48])).
% 15.14/5.84  tff(c_87, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_58, c_84])).
% 15.14/5.84  tff(c_90, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_87])).
% 15.14/5.84  tff(c_7238, plain, (![A_602, B_603]: (r2_hidden('#skF_2'(A_602, B_603), k1_relat_1(A_602)) | r1_tarski(A_602, B_603) | ~r1_tarski(k1_relat_1(A_602), k1_relat_1(B_603)) | ~v1_funct_1(B_603) | ~v1_relat_1(B_603) | ~v1_funct_1(A_602) | ~v1_relat_1(A_602))), inference(cnfTransformation, [status(thm)], [f_110])).
% 15.14/5.84  tff(c_96, plain, (![B_78, A_79]: (m1_subset_1(u1_struct_0(B_78), k1_zfmisc_1(u1_struct_0(A_79))) | ~m1_pre_topc(B_78, A_79) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_132])).
% 15.14/5.84  tff(c_10, plain, (![A_5, C_7, B_6]: (m1_subset_1(A_5, C_7) | ~m1_subset_1(B_6, k1_zfmisc_1(C_7)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.14/5.84  tff(c_102, plain, (![A_5, A_79, B_78]: (m1_subset_1(A_5, u1_struct_0(A_79)) | ~r2_hidden(A_5, u1_struct_0(B_78)) | ~m1_pre_topc(B_78, A_79) | ~l1_pre_topc(A_79))), inference(resolution, [status(thm)], [c_96, c_10])).
% 15.14/5.84  tff(c_147, plain, (![A_5, A_79]: (m1_subset_1(A_5, u1_struct_0(A_79)) | ~r2_hidden(A_5, k1_relat_1('#skF_5')) | ~m1_pre_topc('#skF_4', A_79) | ~l1_pre_topc(A_79))), inference(superposition, [status(thm), theory('equality')], [c_138, c_102])).
% 15.14/5.84  tff(c_7243, plain, (![B_603, A_79]: (m1_subset_1('#skF_2'('#skF_5', B_603), u1_struct_0(A_79)) | ~m1_pre_topc('#skF_4', A_79) | ~l1_pre_topc(A_79) | r1_tarski('#skF_5', B_603) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(B_603)) | ~v1_funct_1(B_603) | ~v1_relat_1(B_603) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_7238, c_147])).
% 15.14/5.84  tff(c_7254, plain, (![B_603, A_79]: (m1_subset_1('#skF_2'('#skF_5', B_603), u1_struct_0(A_79)) | ~m1_pre_topc('#skF_4', A_79) | ~l1_pre_topc(A_79) | r1_tarski('#skF_5', B_603) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(B_603)) | ~v1_funct_1(B_603) | ~v1_relat_1(B_603))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_62, c_7243])).
% 15.14/5.84  tff(c_7431, plain, (![A_627, A_79]: (m1_subset_1('#skF_2'('#skF_5', k4_tmap_1(A_627, '#skF_4')), u1_struct_0(A_79)) | ~m1_pre_topc('#skF_4', A_79) | ~l1_pre_topc(A_79) | r1_tarski('#skF_5', k4_tmap_1(A_627, '#skF_4')) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1('#skF_5')) | ~v1_funct_1(k4_tmap_1(A_627, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_627, '#skF_4')) | u1_struct_0(A_627)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_627) | ~l1_pre_topc(A_627) | ~v2_pre_topc(A_627) | v2_struct_0(A_627) | ~m1_pre_topc('#skF_4', A_627) | ~l1_pre_topc(A_627) | ~v2_pre_topc(A_627) | v2_struct_0(A_627))), inference(superposition, [status(thm), theory('equality')], [c_7420, c_7254])).
% 15.14/5.84  tff(c_7465, plain, (![A_627, A_79]: (m1_subset_1('#skF_2'('#skF_5', k4_tmap_1(A_627, '#skF_4')), u1_struct_0(A_79)) | ~m1_pre_topc('#skF_4', A_79) | ~l1_pre_topc(A_79) | r1_tarski('#skF_5', k4_tmap_1(A_627, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_627, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_627, '#skF_4')) | u1_struct_0(A_627)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_627) | ~l1_pre_topc(A_627) | ~v2_pre_topc(A_627) | v2_struct_0(A_627))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_7431])).
% 15.14/5.84  tff(c_234, plain, (![B_112, A_111]: (k1_relset_1(u1_struct_0(B_112), u1_struct_0(A_111), k4_tmap_1(A_111, B_112))=k1_relat_1(k4_tmap_1(A_111, B_112)) | ~m1_pre_topc(B_112, A_111) | ~l1_pre_topc(A_111) | ~v2_pre_topc(A_111) | v2_struct_0(A_111))), inference(resolution, [status(thm)], [c_211, c_16])).
% 15.14/5.84  tff(c_7373, plain, (![A_621, B_622]: (k1_relat_1(k4_tmap_1(A_621, B_622))=u1_struct_0(B_622) | ~m1_pre_topc(B_622, A_621) | ~l1_pre_topc(A_621) | ~v2_pre_topc(A_621) | v2_struct_0(A_621) | u1_struct_0(A_621)=k1_xboole_0 | ~m1_pre_topc(B_622, A_621) | ~l1_pre_topc(A_621) | ~v2_pre_topc(A_621) | v2_struct_0(A_621))), inference(superposition, [status(thm), theory('equality')], [c_7328, c_234])).
% 15.14/5.84  tff(c_42, plain, (![A_31, B_37]: (r1_tarski(k1_relat_1(A_31), k1_relat_1(B_37)) | ~r1_tarski(A_31, B_37) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_110])).
% 15.14/5.84  tff(c_7750, plain, (![B_687, B_688, A_689]: (r1_tarski(u1_struct_0(B_687), k1_relat_1(B_688)) | ~r1_tarski(k4_tmap_1(A_689, B_687), B_688) | ~v1_funct_1(B_688) | ~v1_relat_1(B_688) | ~v1_funct_1(k4_tmap_1(A_689, B_687)) | ~v1_relat_1(k4_tmap_1(A_689, B_687)) | ~m1_pre_topc(B_687, A_689) | ~l1_pre_topc(A_689) | ~v2_pre_topc(A_689) | v2_struct_0(A_689) | u1_struct_0(A_689)=k1_xboole_0 | ~m1_pre_topc(B_687, A_689) | ~l1_pre_topc(A_689) | ~v2_pre_topc(A_689) | v2_struct_0(A_689))), inference(superposition, [status(thm), theory('equality')], [c_7373, c_42])).
% 15.14/5.84  tff(c_7755, plain, (![B_690, A_691]: (r1_tarski(u1_struct_0(B_690), k1_relat_1(k4_tmap_1(A_691, B_690))) | ~v1_funct_1(k4_tmap_1(A_691, B_690)) | ~v1_relat_1(k4_tmap_1(A_691, B_690)) | u1_struct_0(A_691)=k1_xboole_0 | ~m1_pre_topc(B_690, A_691) | ~l1_pre_topc(A_691) | ~v2_pre_topc(A_691) | v2_struct_0(A_691))), inference(resolution, [status(thm)], [c_6, c_7750])).
% 15.14/5.84  tff(c_7781, plain, (![A_697]: (r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(k4_tmap_1(A_697, '#skF_4'))) | ~v1_funct_1(k4_tmap_1(A_697, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_697, '#skF_4')) | u1_struct_0(A_697)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_697) | ~l1_pre_topc(A_697) | ~v2_pre_topc(A_697) | v2_struct_0(A_697))), inference(superposition, [status(thm), theory('equality')], [c_138, c_7755])).
% 15.14/5.84  tff(c_56, plain, (![D_64]: (k1_funct_1('#skF_5', D_64)=D_64 | ~r2_hidden(D_64, u1_struct_0('#skF_4')) | ~m1_subset_1(D_64, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_182])).
% 15.14/5.84  tff(c_140, plain, (![D_64]: (k1_funct_1('#skF_5', D_64)=D_64 | ~r2_hidden(D_64, k1_relat_1('#skF_5')) | ~m1_subset_1(D_64, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_56])).
% 15.14/5.84  tff(c_7247, plain, (![B_603]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', B_603))='#skF_2'('#skF_5', B_603) | ~m1_subset_1('#skF_2'('#skF_5', B_603), u1_struct_0('#skF_3')) | r1_tarski('#skF_5', B_603) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(B_603)) | ~v1_funct_1(B_603) | ~v1_relat_1(B_603) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_7238, c_140])).
% 15.14/5.84  tff(c_7257, plain, (![B_603]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', B_603))='#skF_2'('#skF_5', B_603) | ~m1_subset_1('#skF_2'('#skF_5', B_603), u1_struct_0('#skF_3')) | r1_tarski('#skF_5', B_603) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(B_603)) | ~v1_funct_1(B_603) | ~v1_relat_1(B_603))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_62, c_7247])).
% 15.14/5.84  tff(c_7840, plain, (![A_701]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', k4_tmap_1(A_701, '#skF_4')))='#skF_2'('#skF_5', k4_tmap_1(A_701, '#skF_4')) | ~m1_subset_1('#skF_2'('#skF_5', k4_tmap_1(A_701, '#skF_4')), u1_struct_0('#skF_3')) | r1_tarski('#skF_5', k4_tmap_1(A_701, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_701, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_701, '#skF_4')) | u1_struct_0(A_701)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_701) | ~l1_pre_topc(A_701) | ~v2_pre_topc(A_701) | v2_struct_0(A_701))), inference(resolution, [status(thm)], [c_7781, c_7257])).
% 15.14/5.84  tff(c_7844, plain, (![A_627]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', k4_tmap_1(A_627, '#skF_4')))='#skF_2'('#skF_5', k4_tmap_1(A_627, '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | r1_tarski('#skF_5', k4_tmap_1(A_627, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_627, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_627, '#skF_4')) | u1_struct_0(A_627)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_627) | ~l1_pre_topc(A_627) | ~v2_pre_topc(A_627) | v2_struct_0(A_627))), inference(resolution, [status(thm)], [c_7465, c_7840])).
% 15.14/5.84  tff(c_7847, plain, (![A_627]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', k4_tmap_1(A_627, '#skF_4')))='#skF_2'('#skF_5', k4_tmap_1(A_627, '#skF_4')) | r1_tarski('#skF_5', k4_tmap_1(A_627, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_627, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_627, '#skF_4')) | u1_struct_0(A_627)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_627) | ~l1_pre_topc(A_627) | ~v2_pre_topc(A_627) | v2_struct_0(A_627))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_7844])).
% 15.14/5.84  tff(c_7768, plain, (![A_691]: (r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(k4_tmap_1(A_691, '#skF_4'))) | ~v1_funct_1(k4_tmap_1(A_691, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_691, '#skF_4')) | u1_struct_0(A_691)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_691) | ~l1_pre_topc(A_691) | ~v2_pre_topc(A_691) | v2_struct_0(A_691))), inference(superposition, [status(thm), theory('equality')], [c_138, c_7755])).
% 15.14/5.84  tff(c_7557, plain, (![A_646, A_647]: (m1_subset_1('#skF_2'('#skF_5', k4_tmap_1(A_646, '#skF_4')), u1_struct_0(A_647)) | ~m1_pre_topc('#skF_4', A_647) | ~l1_pre_topc(A_647) | r1_tarski('#skF_5', k4_tmap_1(A_646, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_646, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_646, '#skF_4')) | u1_struct_0(A_646)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_646) | ~l1_pre_topc(A_646) | ~v2_pre_topc(A_646) | v2_struct_0(A_646))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_7431])).
% 15.14/5.84  tff(c_38, plain, (![A_31, B_37]: (r2_hidden('#skF_2'(A_31, B_37), k1_relat_1(A_31)) | r1_tarski(A_31, B_37) | ~r1_tarski(k1_relat_1(A_31), k1_relat_1(B_37)) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_110])).
% 15.14/5.84  tff(c_66, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_182])).
% 15.14/5.84  tff(c_7259, plain, (![A_604, B_605, C_606]: (k1_funct_1(k4_tmap_1(A_604, B_605), C_606)=C_606 | ~r2_hidden(C_606, u1_struct_0(B_605)) | ~m1_subset_1(C_606, u1_struct_0(A_604)) | ~m1_pre_topc(B_605, A_604) | v2_struct_0(B_605) | ~l1_pre_topc(A_604) | ~v2_pre_topc(A_604) | v2_struct_0(A_604))), inference(cnfTransformation, [status(thm)], [f_152])).
% 15.14/5.84  tff(c_7261, plain, (![A_604, C_606]: (k1_funct_1(k4_tmap_1(A_604, '#skF_4'), C_606)=C_606 | ~r2_hidden(C_606, k1_relat_1('#skF_5')) | ~m1_subset_1(C_606, u1_struct_0(A_604)) | ~m1_pre_topc('#skF_4', A_604) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_604) | ~v2_pre_topc(A_604) | v2_struct_0(A_604))), inference(superposition, [status(thm), theory('equality')], [c_138, c_7259])).
% 15.14/5.84  tff(c_7272, plain, (![A_609, C_610]: (k1_funct_1(k4_tmap_1(A_609, '#skF_4'), C_610)=C_610 | ~r2_hidden(C_610, k1_relat_1('#skF_5')) | ~m1_subset_1(C_610, u1_struct_0(A_609)) | ~m1_pre_topc('#skF_4', A_609) | ~l1_pre_topc(A_609) | ~v2_pre_topc(A_609) | v2_struct_0(A_609))), inference(negUnitSimplification, [status(thm)], [c_66, c_7261])).
% 15.14/5.84  tff(c_7275, plain, (![A_609, B_37]: (k1_funct_1(k4_tmap_1(A_609, '#skF_4'), '#skF_2'('#skF_5', B_37))='#skF_2'('#skF_5', B_37) | ~m1_subset_1('#skF_2'('#skF_5', B_37), u1_struct_0(A_609)) | ~m1_pre_topc('#skF_4', A_609) | ~l1_pre_topc(A_609) | ~v2_pre_topc(A_609) | v2_struct_0(A_609) | r1_tarski('#skF_5', B_37) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(B_37)) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_7272])).
% 15.14/5.84  tff(c_7278, plain, (![A_609, B_37]: (k1_funct_1(k4_tmap_1(A_609, '#skF_4'), '#skF_2'('#skF_5', B_37))='#skF_2'('#skF_5', B_37) | ~m1_subset_1('#skF_2'('#skF_5', B_37), u1_struct_0(A_609)) | ~m1_pre_topc('#skF_4', A_609) | ~l1_pre_topc(A_609) | ~v2_pre_topc(A_609) | v2_struct_0(A_609) | r1_tarski('#skF_5', B_37) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(B_37)) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_62, c_7275])).
% 15.14/5.84  tff(c_7565, plain, (![A_647, A_646]: (k1_funct_1(k4_tmap_1(A_647, '#skF_4'), '#skF_2'('#skF_5', k4_tmap_1(A_646, '#skF_4')))='#skF_2'('#skF_5', k4_tmap_1(A_646, '#skF_4')) | ~v2_pre_topc(A_647) | v2_struct_0(A_647) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(k4_tmap_1(A_646, '#skF_4'))) | ~m1_pre_topc('#skF_4', A_647) | ~l1_pre_topc(A_647) | r1_tarski('#skF_5', k4_tmap_1(A_646, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_646, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_646, '#skF_4')) | u1_struct_0(A_646)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_646) | ~l1_pre_topc(A_646) | ~v2_pre_topc(A_646) | v2_struct_0(A_646))), inference(resolution, [status(thm)], [c_7557, c_7278])).
% 15.14/5.84  tff(c_7889, plain, (![A_707, A_708]: (k1_funct_1(k4_tmap_1(A_707, '#skF_4'), '#skF_2'('#skF_5', k4_tmap_1(A_708, '#skF_4')))='#skF_2'('#skF_5', k4_tmap_1(A_708, '#skF_4')) | ~v2_pre_topc(A_707) | v2_struct_0(A_707) | ~m1_pre_topc('#skF_4', A_707) | ~l1_pre_topc(A_707) | r1_tarski('#skF_5', k4_tmap_1(A_708, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_708, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_708, '#skF_4')) | u1_struct_0(A_708)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_708) | ~l1_pre_topc(A_708) | ~v2_pre_topc(A_708) | v2_struct_0(A_708))), inference(resolution, [status(thm)], [c_7781, c_7565])).
% 15.14/5.84  tff(c_36, plain, (![B_37, A_31]: (k1_funct_1(B_37, '#skF_2'(A_31, B_37))!=k1_funct_1(A_31, '#skF_2'(A_31, B_37)) | r1_tarski(A_31, B_37) | ~r1_tarski(k1_relat_1(A_31), k1_relat_1(B_37)) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_110])).
% 15.14/5.84  tff(c_7898, plain, (![A_708]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', k4_tmap_1(A_708, '#skF_4')))!='#skF_2'('#skF_5', k4_tmap_1(A_708, '#skF_4')) | r1_tarski('#skF_5', k4_tmap_1(A_708, '#skF_4')) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(k4_tmap_1(A_708, '#skF_4'))) | ~v1_funct_1(k4_tmap_1(A_708, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_708, '#skF_4')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v2_pre_topc(A_708) | v2_struct_0(A_708) | ~m1_pre_topc('#skF_4', A_708) | ~l1_pre_topc(A_708) | r1_tarski('#skF_5', k4_tmap_1(A_708, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_708, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_708, '#skF_4')) | u1_struct_0(A_708)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_708) | ~l1_pre_topc(A_708) | ~v2_pre_topc(A_708) | v2_struct_0(A_708))), inference(superposition, [status(thm), theory('equality')], [c_7889, c_36])).
% 15.14/5.84  tff(c_7919, plain, (![A_711]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', k4_tmap_1(A_711, '#skF_4')))!='#skF_2'('#skF_5', k4_tmap_1(A_711, '#skF_4')) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(k4_tmap_1(A_711, '#skF_4'))) | r1_tarski('#skF_5', k4_tmap_1(A_711, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_711, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_711, '#skF_4')) | u1_struct_0(A_711)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_711) | ~l1_pre_topc(A_711) | ~v2_pre_topc(A_711) | v2_struct_0(A_711))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_62, c_7898])).
% 15.14/5.84  tff(c_7941, plain, (![A_712]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', k4_tmap_1(A_712, '#skF_4')))!='#skF_2'('#skF_5', k4_tmap_1(A_712, '#skF_4')) | r1_tarski('#skF_5', k4_tmap_1(A_712, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_712, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_712, '#skF_4')) | u1_struct_0(A_712)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_712) | ~l1_pre_topc(A_712) | ~v2_pre_topc(A_712) | v2_struct_0(A_712))), inference(resolution, [status(thm)], [c_7768, c_7919])).
% 15.14/5.84  tff(c_7948, plain, (![A_627]: (r1_tarski('#skF_5', k4_tmap_1(A_627, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_627, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_627, '#skF_4')) | u1_struct_0(A_627)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_627) | ~l1_pre_topc(A_627) | ~v2_pre_topc(A_627) | v2_struct_0(A_627))), inference(superposition, [status(thm), theory('equality')], [c_7847, c_7941])).
% 15.14/5.84  tff(c_7615, plain, (![A_669, B_670, A_671]: (r1_tarski(k1_relat_1(A_669), u1_struct_0(B_670)) | ~r1_tarski(A_669, k4_tmap_1(A_671, B_670)) | ~v1_funct_1(k4_tmap_1(A_671, B_670)) | ~v1_relat_1(k4_tmap_1(A_671, B_670)) | ~v1_funct_1(A_669) | ~v1_relat_1(A_669) | ~m1_pre_topc(B_670, A_671) | ~l1_pre_topc(A_671) | ~v2_pre_topc(A_671) | v2_struct_0(A_671) | u1_struct_0(A_671)=k1_xboole_0 | ~m1_pre_topc(B_670, A_671) | ~l1_pre_topc(A_671) | ~v2_pre_topc(A_671) | v2_struct_0(A_671))), inference(superposition, [status(thm), theory('equality')], [c_7373, c_42])).
% 15.14/5.84  tff(c_7620, plain, (![A_672, B_673]: (r1_tarski(k1_relat_1(k4_tmap_1(A_672, B_673)), u1_struct_0(B_673)) | ~v1_funct_1(k4_tmap_1(A_672, B_673)) | ~v1_relat_1(k4_tmap_1(A_672, B_673)) | u1_struct_0(A_672)=k1_xboole_0 | ~m1_pre_topc(B_673, A_672) | ~l1_pre_topc(A_672) | ~v2_pre_topc(A_672) | v2_struct_0(A_672))), inference(resolution, [status(thm)], [c_6, c_7615])).
% 15.14/5.84  tff(c_7633, plain, (![A_672]: (r1_tarski(k1_relat_1(k4_tmap_1(A_672, '#skF_4')), k1_relat_1('#skF_5')) | ~v1_funct_1(k4_tmap_1(A_672, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_672, '#skF_4')) | u1_struct_0(A_672)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_672) | ~l1_pre_topc(A_672) | ~v2_pre_topc(A_672) | v2_struct_0(A_672))), inference(superposition, [status(thm), theory('equality')], [c_138, c_7620])).
% 15.14/5.84  tff(c_8200, plain, (![A_775, B_776, B_777]: (r2_hidden('#skF_2'(k4_tmap_1(A_775, B_776), B_777), u1_struct_0(B_776)) | r1_tarski(k4_tmap_1(A_775, B_776), B_777) | ~r1_tarski(k1_relat_1(k4_tmap_1(A_775, B_776)), k1_relat_1(B_777)) | ~v1_funct_1(B_777) | ~v1_relat_1(B_777) | ~v1_funct_1(k4_tmap_1(A_775, B_776)) | ~v1_relat_1(k4_tmap_1(A_775, B_776)) | ~m1_pre_topc(B_776, A_775) | ~l1_pre_topc(A_775) | ~v2_pre_topc(A_775) | v2_struct_0(A_775) | u1_struct_0(A_775)=k1_xboole_0 | ~m1_pre_topc(B_776, A_775) | ~l1_pre_topc(A_775) | ~v2_pre_topc(A_775) | v2_struct_0(A_775))), inference(superposition, [status(thm), theory('equality')], [c_7373, c_38])).
% 15.14/5.84  tff(c_8301, plain, (![A_799, B_800]: (r2_hidden('#skF_2'(k4_tmap_1(A_799, '#skF_4'), B_800), k1_relat_1('#skF_5')) | r1_tarski(k4_tmap_1(A_799, '#skF_4'), B_800) | ~r1_tarski(k1_relat_1(k4_tmap_1(A_799, '#skF_4')), k1_relat_1(B_800)) | ~v1_funct_1(B_800) | ~v1_relat_1(B_800) | ~v1_funct_1(k4_tmap_1(A_799, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_799, '#skF_4')) | ~m1_pre_topc('#skF_4', A_799) | ~l1_pre_topc(A_799) | ~v2_pre_topc(A_799) | v2_struct_0(A_799) | u1_struct_0(A_799)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_799) | ~l1_pre_topc(A_799) | ~v2_pre_topc(A_799) | v2_struct_0(A_799))), inference(superposition, [status(thm), theory('equality')], [c_138, c_8200])).
% 15.14/5.84  tff(c_40, plain, (![B_37, C_40, A_31]: (k1_funct_1(B_37, C_40)=k1_funct_1(A_31, C_40) | ~r2_hidden(C_40, k1_relat_1(A_31)) | ~r1_tarski(A_31, B_37) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_110])).
% 15.14/5.84  tff(c_8307, plain, (![B_37, A_799, B_800]: (k1_funct_1(B_37, '#skF_2'(k4_tmap_1(A_799, '#skF_4'), B_800))=k1_funct_1('#skF_5', '#skF_2'(k4_tmap_1(A_799, '#skF_4'), B_800)) | ~r1_tarski('#skF_5', B_37) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | r1_tarski(k4_tmap_1(A_799, '#skF_4'), B_800) | ~r1_tarski(k1_relat_1(k4_tmap_1(A_799, '#skF_4')), k1_relat_1(B_800)) | ~v1_funct_1(B_800) | ~v1_relat_1(B_800) | ~v1_funct_1(k4_tmap_1(A_799, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_799, '#skF_4')) | u1_struct_0(A_799)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_799) | ~l1_pre_topc(A_799) | ~v2_pre_topc(A_799) | v2_struct_0(A_799))), inference(resolution, [status(thm)], [c_8301, c_40])).
% 15.14/5.84  tff(c_8449, plain, (![B_822, A_823, B_824]: (k1_funct_1(B_822, '#skF_2'(k4_tmap_1(A_823, '#skF_4'), B_824))=k1_funct_1('#skF_5', '#skF_2'(k4_tmap_1(A_823, '#skF_4'), B_824)) | ~r1_tarski('#skF_5', B_822) | ~v1_funct_1(B_822) | ~v1_relat_1(B_822) | r1_tarski(k4_tmap_1(A_823, '#skF_4'), B_824) | ~r1_tarski(k1_relat_1(k4_tmap_1(A_823, '#skF_4')), k1_relat_1(B_824)) | ~v1_funct_1(B_824) | ~v1_relat_1(B_824) | ~v1_funct_1(k4_tmap_1(A_823, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_823, '#skF_4')) | u1_struct_0(A_823)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_823) | ~l1_pre_topc(A_823) | ~v2_pre_topc(A_823) | v2_struct_0(A_823))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_62, c_8307])).
% 15.14/5.84  tff(c_8451, plain, (![B_822, A_672]: (k1_funct_1(B_822, '#skF_2'(k4_tmap_1(A_672, '#skF_4'), '#skF_5'))=k1_funct_1('#skF_5', '#skF_2'(k4_tmap_1(A_672, '#skF_4'), '#skF_5')) | ~r1_tarski('#skF_5', B_822) | ~v1_funct_1(B_822) | ~v1_relat_1(B_822) | r1_tarski(k4_tmap_1(A_672, '#skF_4'), '#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1(k4_tmap_1(A_672, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_672, '#skF_4')) | u1_struct_0(A_672)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_672) | ~l1_pre_topc(A_672) | ~v2_pre_topc(A_672) | v2_struct_0(A_672))), inference(resolution, [status(thm)], [c_7633, c_8449])).
% 15.14/5.84  tff(c_8483, plain, (![B_828, A_829]: (k1_funct_1(B_828, '#skF_2'(k4_tmap_1(A_829, '#skF_4'), '#skF_5'))=k1_funct_1('#skF_5', '#skF_2'(k4_tmap_1(A_829, '#skF_4'), '#skF_5')) | ~r1_tarski('#skF_5', B_828) | ~v1_funct_1(B_828) | ~v1_relat_1(B_828) | r1_tarski(k4_tmap_1(A_829, '#skF_4'), '#skF_5') | ~v1_funct_1(k4_tmap_1(A_829, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_829, '#skF_4')) | u1_struct_0(A_829)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_829) | ~l1_pre_topc(A_829) | ~v2_pre_topc(A_829) | v2_struct_0(A_829))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_62, c_8451])).
% 15.14/5.84  tff(c_8506, plain, (![A_829]: (~r1_tarski(k1_relat_1(k4_tmap_1(A_829, '#skF_4')), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r1_tarski('#skF_5', k4_tmap_1(A_829, '#skF_4')) | r1_tarski(k4_tmap_1(A_829, '#skF_4'), '#skF_5') | ~v1_funct_1(k4_tmap_1(A_829, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_829, '#skF_4')) | u1_struct_0(A_829)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_829) | ~l1_pre_topc(A_829) | ~v2_pre_topc(A_829) | v2_struct_0(A_829))), inference(superposition, [status(thm), theory('equality')], [c_8483, c_36])).
% 15.14/5.84  tff(c_8528, plain, (![A_830]: (~r1_tarski(k1_relat_1(k4_tmap_1(A_830, '#skF_4')), k1_relat_1('#skF_5')) | ~r1_tarski('#skF_5', k4_tmap_1(A_830, '#skF_4')) | r1_tarski(k4_tmap_1(A_830, '#skF_4'), '#skF_5') | ~v1_funct_1(k4_tmap_1(A_830, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_830, '#skF_4')) | u1_struct_0(A_830)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_830) | ~l1_pre_topc(A_830) | ~v2_pre_topc(A_830) | v2_struct_0(A_830))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_62, c_8506])).
% 15.14/5.84  tff(c_8550, plain, (![A_831]: (~r1_tarski('#skF_5', k4_tmap_1(A_831, '#skF_4')) | r1_tarski(k4_tmap_1(A_831, '#skF_4'), '#skF_5') | ~v1_funct_1(k4_tmap_1(A_831, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_831, '#skF_4')) | u1_struct_0(A_831)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_831) | ~l1_pre_topc(A_831) | ~v2_pre_topc(A_831) | v2_struct_0(A_831))), inference(resolution, [status(thm)], [c_7633, c_8528])).
% 15.14/5.84  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.14/5.84  tff(c_8584, plain, (![A_832]: (k4_tmap_1(A_832, '#skF_4')='#skF_5' | ~r1_tarski('#skF_5', k4_tmap_1(A_832, '#skF_4')) | ~v1_funct_1(k4_tmap_1(A_832, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_832, '#skF_4')) | u1_struct_0(A_832)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_832) | ~l1_pre_topc(A_832) | ~v2_pre_topc(A_832) | v2_struct_0(A_832))), inference(resolution, [status(thm)], [c_8550, c_2])).
% 15.14/5.84  tff(c_8589, plain, (![A_833]: (k4_tmap_1(A_833, '#skF_4')='#skF_5' | ~v1_funct_1(k4_tmap_1(A_833, '#skF_4')) | ~v1_relat_1(k4_tmap_1(A_833, '#skF_4')) | u1_struct_0(A_833)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_833) | ~l1_pre_topc(A_833) | ~v2_pre_topc(A_833) | v2_struct_0(A_833))), inference(resolution, [status(thm)], [c_7948, c_8584])).
% 15.14/5.84  tff(c_8595, plain, (![A_834]: (k4_tmap_1(A_834, '#skF_4')='#skF_5' | ~v1_funct_1(k4_tmap_1(A_834, '#skF_4')) | u1_struct_0(A_834)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_834) | ~l1_pre_topc(A_834) | ~v2_pre_topc(A_834) | v2_struct_0(A_834))), inference(resolution, [status(thm)], [c_238, c_8589])).
% 15.14/5.84  tff(c_8601, plain, (![A_835]: (k4_tmap_1(A_835, '#skF_4')='#skF_5' | u1_struct_0(A_835)=k1_xboole_0 | ~m1_pre_topc('#skF_4', A_835) | ~l1_pre_topc(A_835) | ~v2_pre_topc(A_835) | v2_struct_0(A_835))), inference(resolution, [status(thm)], [c_48, c_8595])).
% 15.14/5.84  tff(c_8604, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5' | u1_struct_0('#skF_3')=k1_xboole_0 | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_8601])).
% 15.14/5.84  tff(c_8607, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5' | u1_struct_0('#skF_3')=k1_xboole_0 | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_8604])).
% 15.14/5.84  tff(c_8608, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5' | u1_struct_0('#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_72, c_8607])).
% 15.14/5.84  tff(c_8609, plain, (u1_struct_0('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_8608])).
% 15.14/5.84  tff(c_8622, plain, (v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8609, c_144])).
% 15.14/5.84  tff(c_8620, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8609, c_143])).
% 15.14/5.84  tff(c_20, plain, (![C_18, A_16]: (k1_xboole_0=C_18 | ~v1_funct_2(C_18, A_16, k1_xboole_0) | k1_xboole_0=A_16 | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.14/5.84  tff(c_8860, plain, (k1_xboole_0='#skF_5' | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k1_xboole_0) | k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_8620, c_20])).
% 15.14/5.84  tff(c_8885, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8622, c_8860])).
% 15.14/5.84  tff(c_8891, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_8885])).
% 15.14/5.84  tff(c_8613, plain, (r2_funct_2(k1_relat_1('#skF_5'), k1_xboole_0, '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8609, c_7582])).
% 15.14/5.84  tff(c_8905, plain, (r2_funct_2(k1_xboole_0, k1_xboole_0, '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8891, c_8613])).
% 15.14/5.84  tff(c_228, plain, (![A_111]: (m1_subset_1(k4_tmap_1(A_111, '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), u1_struct_0(A_111)))) | ~m1_pre_topc('#skF_4', A_111) | ~l1_pre_topc(A_111) | ~v2_pre_topc(A_111) | v2_struct_0(A_111))), inference(superposition, [status(thm), theory('equality')], [c_138, c_211])).
% 15.14/5.84  tff(c_8721, plain, (m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k1_xboole_0))) | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8609, c_228])).
% 15.14/5.84  tff(c_8817, plain, (m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k1_xboole_0))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_8721])).
% 15.14/5.84  tff(c_8818, plain, (m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_72, c_8817])).
% 15.14/5.84  tff(c_9237, plain, (m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8891, c_8818])).
% 15.14/5.84  tff(c_9266, plain, (v1_relat_1(k4_tmap_1('#skF_3', '#skF_4')) | ~v1_relat_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_9237, c_12])).
% 15.14/5.84  tff(c_9294, plain, (v1_relat_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_9266])).
% 15.14/5.84  tff(c_163, plain, (![A_106, B_107]: (v1_funct_2(k4_tmap_1(A_106, B_107), u1_struct_0(B_107), u1_struct_0(A_106)) | ~m1_pre_topc(B_107, A_106) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_125])).
% 15.14/5.84  tff(c_166, plain, (![A_106]: (v1_funct_2(k4_tmap_1(A_106, '#skF_4'), k1_relat_1('#skF_5'), u1_struct_0(A_106)) | ~m1_pre_topc('#skF_4', A_106) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106) | v2_struct_0(A_106))), inference(superposition, [status(thm), theory('equality')], [c_138, c_163])).
% 15.14/5.84  tff(c_8724, plain, (v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), k1_relat_1('#skF_5'), k1_xboole_0) | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8609, c_166])).
% 15.14/5.84  tff(c_8820, plain, (v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), k1_relat_1('#skF_5'), k1_xboole_0) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_8724])).
% 15.14/5.84  tff(c_8821, plain, (v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), k1_relat_1('#skF_5'), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_72, c_8820])).
% 15.14/5.84  tff(c_9033, plain, (v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8891, c_8821])).
% 15.14/5.84  tff(c_7569, plain, (![A_19, B_20, C_21]: (r2_funct_2(A_19, B_20, C_21, C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))) | ~v1_funct_2(C_21, A_19, B_20) | ~v1_funct_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))) | ~v1_funct_2(C_21, A_19, B_20) | ~v1_funct_1(C_21))), inference(reflexivity, [status(thm), theory('equality')], [c_32])).
% 15.14/5.84  tff(c_9239, plain, (r2_funct_2(k1_xboole_0, k1_xboole_0, k4_tmap_1('#skF_3', '#skF_4'), k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_9237, c_7569])).
% 15.14/5.84  tff(c_9269, plain, (r2_funct_2(k1_xboole_0, k1_xboole_0, k4_tmap_1('#skF_3', '#skF_4'), k4_tmap_1('#skF_3', '#skF_4')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9033, c_9237, c_9239])).
% 15.14/5.84  tff(c_9829, plain, (~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_9269])).
% 15.14/5.84  tff(c_9832, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_9829])).
% 15.14/5.84  tff(c_9835, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_9832])).
% 15.14/5.84  tff(c_9837, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_9835])).
% 15.14/5.84  tff(c_9839, plain, (v1_funct_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_9269])).
% 15.14/5.84  tff(c_26, plain, (![B_17, C_18]: (k1_relset_1(k1_xboole_0, B_17, C_18)=k1_xboole_0 | ~v1_funct_2(C_18, k1_xboole_0, B_17) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_17))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.14/5.84  tff(c_9255, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, k4_tmap_1('#skF_3', '#skF_4'))=k1_xboole_0 | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_9237, c_26])).
% 15.14/5.84  tff(c_9285, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, k4_tmap_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_9033, c_9255])).
% 15.14/5.84  tff(c_8703, plain, (k1_relset_1(k1_relat_1('#skF_5'), k1_xboole_0, k4_tmap_1('#skF_3', '#skF_4'))=k1_relat_1(k4_tmap_1('#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8609, c_7210])).
% 15.14/5.84  tff(c_8805, plain, (k1_relset_1(k1_relat_1('#skF_5'), k1_xboole_0, k4_tmap_1('#skF_3', '#skF_4'))=k1_relat_1(k4_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_8703])).
% 15.14/5.84  tff(c_8806, plain, (k1_relset_1(k1_relat_1('#skF_5'), k1_xboole_0, k4_tmap_1('#skF_3', '#skF_4'))=k1_relat_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_72, c_8805])).
% 15.14/5.84  tff(c_9445, plain, (k1_relat_1(k4_tmap_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_9285, c_8891, c_8806])).
% 15.14/5.84  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(A_3, B_4) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.14/5.84  tff(c_7258, plain, (![A_602, B_603]: (m1_subset_1('#skF_2'(A_602, B_603), k1_relat_1(A_602)) | r1_tarski(A_602, B_603) | ~r1_tarski(k1_relat_1(A_602), k1_relat_1(B_603)) | ~v1_funct_1(B_603) | ~v1_relat_1(B_603) | ~v1_funct_1(A_602) | ~v1_relat_1(A_602))), inference(resolution, [status(thm)], [c_7238, c_8])).
% 15.14/5.84  tff(c_8972, plain, (![B_603]: (m1_subset_1('#skF_2'('#skF_5', B_603), k1_relat_1('#skF_5')) | r1_tarski('#skF_5', B_603) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_603)) | ~v1_funct_1(B_603) | ~v1_relat_1(B_603) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8891, c_7258])).
% 15.14/5.84  tff(c_9997, plain, (![B_898]: (m1_subset_1('#skF_2'('#skF_5', B_898), k1_xboole_0) | r1_tarski('#skF_5', B_898) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_898)) | ~v1_funct_1(B_898) | ~v1_relat_1(B_898))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_62, c_8891, c_8972])).
% 15.14/5.84  tff(c_10003, plain, (m1_subset_1('#skF_2'('#skF_5', k4_tmap_1('#skF_3', '#skF_4')), k1_xboole_0) | r1_tarski('#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~v1_relat_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_9445, c_9997])).
% 15.14/5.84  tff(c_10012, plain, (m1_subset_1('#skF_2'('#skF_5', k4_tmap_1('#skF_3', '#skF_4')), k1_xboole_0) | r1_tarski('#skF_5', k4_tmap_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9294, c_9839, c_6, c_10003])).
% 15.14/5.84  tff(c_10015, plain, (r1_tarski('#skF_5', k4_tmap_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_10012])).
% 15.14/5.84  tff(c_10041, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5' | ~r1_tarski(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_10015, c_2])).
% 15.14/5.84  tff(c_10069, plain, (~r1_tarski(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_10041])).
% 15.14/5.84  tff(c_9508, plain, (![B_37]: (r2_hidden('#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), B_37), k1_xboole_0) | r1_tarski(k4_tmap_1('#skF_3', '#skF_4'), B_37) | ~r1_tarski(k1_relat_1(k4_tmap_1('#skF_3', '#skF_4')), k1_relat_1(B_37)) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~v1_relat_1(k4_tmap_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_9445, c_38])).
% 15.14/5.84  tff(c_9589, plain, (![B_37]: (r2_hidden('#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), B_37), k1_xboole_0) | r1_tarski(k4_tmap_1('#skF_3', '#skF_4'), B_37) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_37)) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_9294, c_9445, c_9508])).
% 15.14/5.84  tff(c_11564, plain, (![B_37]: (r2_hidden('#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), B_37), k1_xboole_0) | r1_tarski(k4_tmap_1('#skF_3', '#skF_4'), B_37) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_37)) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37))), inference(demodulation, [status(thm), theory('equality')], [c_9839, c_9589])).
% 15.14/5.84  tff(c_7251, plain, (![B_37, A_602, B_603]: (k1_funct_1(B_37, '#skF_2'(A_602, B_603))=k1_funct_1(A_602, '#skF_2'(A_602, B_603)) | ~r1_tarski(A_602, B_37) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37) | r1_tarski(A_602, B_603) | ~r1_tarski(k1_relat_1(A_602), k1_relat_1(B_603)) | ~v1_funct_1(B_603) | ~v1_relat_1(B_603) | ~v1_funct_1(A_602) | ~v1_relat_1(A_602))), inference(resolution, [status(thm)], [c_7238, c_40])).
% 15.14/5.84  tff(c_8970, plain, (![B_37, A_602]: (k1_funct_1(B_37, '#skF_2'(A_602, '#skF_5'))=k1_funct_1(A_602, '#skF_2'(A_602, '#skF_5')) | ~r1_tarski(A_602, B_37) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37) | r1_tarski(A_602, '#skF_5') | ~r1_tarski(k1_relat_1(A_602), k1_xboole_0) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1(A_602) | ~v1_relat_1(A_602))), inference(superposition, [status(thm), theory('equality')], [c_8891, c_7251])).
% 15.14/5.84  tff(c_11987, plain, (![B_989, A_990]: (k1_funct_1(B_989, '#skF_2'(A_990, '#skF_5'))=k1_funct_1(A_990, '#skF_2'(A_990, '#skF_5')) | ~r1_tarski(A_990, B_989) | ~v1_funct_1(B_989) | ~v1_relat_1(B_989) | r1_tarski(A_990, '#skF_5') | ~r1_tarski(k1_relat_1(A_990), k1_xboole_0) | ~v1_funct_1(A_990) | ~v1_relat_1(A_990))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_62, c_8970])).
% 15.14/5.84  tff(c_12001, plain, (![B_989]: (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'))=k1_funct_1(B_989, '#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5')) | ~r1_tarski(k4_tmap_1('#skF_3', '#skF_4'), B_989) | ~v1_funct_1(B_989) | ~v1_relat_1(B_989) | r1_tarski(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5') | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~v1_relat_1(k4_tmap_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_9445, c_11987])).
% 15.14/5.84  tff(c_12015, plain, (![B_989]: (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'))=k1_funct_1(B_989, '#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5')) | ~r1_tarski(k4_tmap_1('#skF_3', '#skF_4'), B_989) | ~v1_funct_1(B_989) | ~v1_relat_1(B_989) | r1_tarski(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_9294, c_9839, c_6, c_12001])).
% 15.14/5.84  tff(c_12029, plain, (![B_994]: (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'))=k1_funct_1(B_994, '#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5')) | ~r1_tarski(k4_tmap_1('#skF_3', '#skF_4'), B_994) | ~v1_funct_1(B_994) | ~v1_relat_1(B_994))), inference(negUnitSimplification, [status(thm)], [c_10069, c_12015])).
% 15.14/5.84  tff(c_8941, plain, (![A_5, A_79]: (m1_subset_1(A_5, u1_struct_0(A_79)) | ~r2_hidden(A_5, k1_xboole_0) | ~m1_pre_topc('#skF_4', A_79) | ~l1_pre_topc(A_79))), inference(demodulation, [status(thm), theory('equality')], [c_8891, c_147])).
% 15.14/5.84  tff(c_8944, plain, (u1_struct_0('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8891, c_138])).
% 15.14/5.84  tff(c_52, plain, (![A_46, B_50, C_52]: (k1_funct_1(k4_tmap_1(A_46, B_50), C_52)=C_52 | ~r2_hidden(C_52, u1_struct_0(B_50)) | ~m1_subset_1(C_52, u1_struct_0(A_46)) | ~m1_pre_topc(B_50, A_46) | v2_struct_0(B_50) | ~l1_pre_topc(A_46) | ~v2_pre_topc(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_152])).
% 15.14/5.84  tff(c_9089, plain, (![A_46, C_52]: (k1_funct_1(k4_tmap_1(A_46, '#skF_4'), C_52)=C_52 | ~r2_hidden(C_52, k1_xboole_0) | ~m1_subset_1(C_52, u1_struct_0(A_46)) | ~m1_pre_topc('#skF_4', A_46) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_46) | ~v2_pre_topc(A_46) | v2_struct_0(A_46))), inference(superposition, [status(thm), theory('equality')], [c_8944, c_52])).
% 15.14/5.84  tff(c_10138, plain, (![A_908, C_909]: (k1_funct_1(k4_tmap_1(A_908, '#skF_4'), C_909)=C_909 | ~r2_hidden(C_909, k1_xboole_0) | ~m1_subset_1(C_909, u1_struct_0(A_908)) | ~m1_pre_topc('#skF_4', A_908) | ~l1_pre_topc(A_908) | ~v2_pre_topc(A_908) | v2_struct_0(A_908))), inference(negUnitSimplification, [status(thm)], [c_66, c_9089])).
% 15.14/5.84  tff(c_10157, plain, (![A_79, A_5]: (k1_funct_1(k4_tmap_1(A_79, '#skF_4'), A_5)=A_5 | ~v2_pre_topc(A_79) | v2_struct_0(A_79) | ~r2_hidden(A_5, k1_xboole_0) | ~m1_pre_topc('#skF_4', A_79) | ~l1_pre_topc(A_79))), inference(resolution, [status(thm)], [c_8941, c_10138])).
% 15.14/5.84  tff(c_12053, plain, (![B_994]: (k1_funct_1(B_994, '#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'))='#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r2_hidden('#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'), k1_xboole_0) | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~r1_tarski(k4_tmap_1('#skF_3', '#skF_4'), B_994) | ~v1_funct_1(B_994) | ~v1_relat_1(B_994))), inference(superposition, [status(thm), theory('equality')], [c_12029, c_10157])).
% 15.14/5.84  tff(c_12149, plain, (![B_994]: (k1_funct_1(B_994, '#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'))='#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5') | v2_struct_0('#skF_3') | ~r2_hidden('#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'), k1_xboole_0) | ~r1_tarski(k4_tmap_1('#skF_3', '#skF_4'), B_994) | ~v1_funct_1(B_994) | ~v1_relat_1(B_994))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_70, c_12053])).
% 15.14/5.84  tff(c_12150, plain, (![B_994]: (k1_funct_1(B_994, '#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'))='#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5') | ~r2_hidden('#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'), k1_xboole_0) | ~r1_tarski(k4_tmap_1('#skF_3', '#skF_4'), B_994) | ~v1_funct_1(B_994) | ~v1_relat_1(B_994))), inference(negUnitSimplification, [status(thm)], [c_72, c_12149])).
% 15.14/5.84  tff(c_12313, plain, (~r2_hidden('#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_12150])).
% 15.14/5.84  tff(c_12316, plain, (r1_tarski(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5') | ~r1_tarski(k1_xboole_0, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_11564, c_12313])).
% 15.14/5.84  tff(c_12319, plain, (r1_tarski(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_62, c_6, c_8891, c_12316])).
% 15.14/5.84  tff(c_12321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10069, c_12319])).
% 15.14/5.84  tff(c_12323, plain, (r2_hidden('#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_12150])).
% 15.14/5.84  tff(c_8974, plain, (![A_602]: (m1_subset_1('#skF_2'(A_602, '#skF_5'), k1_relat_1(A_602)) | r1_tarski(A_602, '#skF_5') | ~r1_tarski(k1_relat_1(A_602), k1_xboole_0) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1(A_602) | ~v1_relat_1(A_602))), inference(superposition, [status(thm), theory('equality')], [c_8891, c_7258])).
% 15.14/5.84  tff(c_10117, plain, (![A_907]: (m1_subset_1('#skF_2'(A_907, '#skF_5'), k1_relat_1(A_907)) | r1_tarski(A_907, '#skF_5') | ~r1_tarski(k1_relat_1(A_907), k1_xboole_0) | ~v1_funct_1(A_907) | ~v1_relat_1(A_907))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_62, c_8974])).
% 15.14/5.84  tff(c_10122, plain, (m1_subset_1('#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'), k1_xboole_0) | r1_tarski(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5') | ~r1_tarski(k1_relat_1(k4_tmap_1('#skF_3', '#skF_4')), k1_xboole_0) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~v1_relat_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_9445, c_10117])).
% 15.14/5.84  tff(c_10131, plain, (m1_subset_1('#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'), k1_xboole_0) | r1_tarski(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9294, c_9839, c_6, c_9445, c_10122])).
% 15.14/5.84  tff(c_10132, plain, (m1_subset_1('#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_10069, c_10131])).
% 15.14/5.84  tff(c_10150, plain, (![C_909]: (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), C_909)=C_909 | ~r2_hidden(C_909, k1_xboole_0) | ~m1_subset_1(C_909, k1_xboole_0) | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_8609, c_10138])).
% 15.14/5.84  tff(c_10161, plain, (![C_909]: (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), C_909)=C_909 | ~r2_hidden(C_909, k1_xboole_0) | ~m1_subset_1(C_909, k1_xboole_0) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_10150])).
% 15.14/5.84  tff(c_10162, plain, (![C_909]: (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), C_909)=C_909 | ~r2_hidden(C_909, k1_xboole_0) | ~m1_subset_1(C_909, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_72, c_10161])).
% 15.14/5.84  tff(c_12080, plain, (![B_994]: (k1_funct_1(B_994, '#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'))!=k1_funct_1('#skF_5', '#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5')) | r1_tarski(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5') | ~r1_tarski(k1_relat_1(k4_tmap_1('#skF_3', '#skF_4')), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~v1_relat_1(k4_tmap_1('#skF_3', '#skF_4')) | ~r1_tarski(k4_tmap_1('#skF_3', '#skF_4'), B_994) | ~v1_funct_1(B_994) | ~v1_relat_1(B_994))), inference(superposition, [status(thm), theory('equality')], [c_12029, c_36])).
% 15.14/5.84  tff(c_12174, plain, (![B_994]: (k1_funct_1(B_994, '#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'))!=k1_funct_1('#skF_5', '#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5')) | r1_tarski(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5') | ~r1_tarski(k4_tmap_1('#skF_3', '#skF_4'), B_994) | ~v1_funct_1(B_994) | ~v1_relat_1(B_994))), inference(demodulation, [status(thm), theory('equality')], [c_9294, c_9839, c_90, c_62, c_6, c_8891, c_9445, c_12080])).
% 15.14/5.84  tff(c_12220, plain, (![B_995]: (k1_funct_1(B_995, '#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'))!=k1_funct_1('#skF_5', '#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5')) | ~r1_tarski(k4_tmap_1('#skF_3', '#skF_4'), B_995) | ~v1_funct_1(B_995) | ~v1_relat_1(B_995))), inference(negUnitSimplification, [status(thm)], [c_10069, c_12174])).
% 15.14/5.84  tff(c_12250, plain, (k1_funct_1('#skF_5', '#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'))!='#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5') | ~r1_tarski(k4_tmap_1('#skF_3', '#skF_4'), k4_tmap_1('#skF_3', '#skF_4')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~v1_relat_1(k4_tmap_1('#skF_3', '#skF_4')) | ~r2_hidden('#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'), k1_xboole_0) | ~m1_subset_1('#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10162, c_12220])).
% 15.14/5.84  tff(c_12289, plain, (k1_funct_1('#skF_5', '#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'))!='#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5') | ~r2_hidden('#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10132, c_9294, c_9839, c_6, c_12250])).
% 15.14/5.84  tff(c_12312, plain, (~r2_hidden('#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_12289])).
% 15.14/5.84  tff(c_12339, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12323, c_12312])).
% 15.14/5.84  tff(c_12340, plain, (k1_funct_1('#skF_5', '#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'))!='#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_12289])).
% 15.14/5.84  tff(c_12341, plain, (r2_hidden('#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_12289])).
% 15.14/5.84  tff(c_8617, plain, (![D_64]: (k1_funct_1('#skF_5', D_64)=D_64 | ~r2_hidden(D_64, k1_relat_1('#skF_5')) | ~m1_subset_1(D_64, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8609, c_140])).
% 15.14/5.84  tff(c_9606, plain, (![D_64]: (k1_funct_1('#skF_5', D_64)=D_64 | ~r2_hidden(D_64, k1_xboole_0) | ~m1_subset_1(D_64, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8891, c_8617])).
% 15.14/5.84  tff(c_12346, plain, (k1_funct_1('#skF_5', '#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'))='#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5') | ~m1_subset_1('#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'), k1_xboole_0)), inference(resolution, [status(thm)], [c_12341, c_9606])).
% 15.14/5.84  tff(c_12353, plain, (k1_funct_1('#skF_5', '#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'))='#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10132, c_12346])).
% 15.14/5.84  tff(c_12379, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12340, c_12353])).
% 15.14/5.84  tff(c_12380, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_10041])).
% 15.14/5.84  tff(c_54, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_182])).
% 15.14/5.84  tff(c_142, plain, (~r2_funct_2(k1_relat_1('#skF_5'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_54])).
% 15.14/5.84  tff(c_8619, plain, (~r2_funct_2(k1_relat_1('#skF_5'), k1_xboole_0, k4_tmap_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8609, c_142])).
% 15.14/5.84  tff(c_9308, plain, (~r2_funct_2(k1_xboole_0, k1_xboole_0, k4_tmap_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8891, c_8619])).
% 15.14/5.84  tff(c_12387, plain, (~r2_funct_2(k1_xboole_0, k1_xboole_0, '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12380, c_9308])).
% 15.14/5.84  tff(c_12398, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8905, c_12387])).
% 15.14/5.84  tff(c_12400, plain, (~r1_tarski('#skF_5', k4_tmap_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_10012])).
% 15.14/5.84  tff(c_12399, plain, (m1_subset_1('#skF_2'('#skF_5', k4_tmap_1('#skF_3', '#skF_4')), k1_xboole_0)), inference(splitRight, [status(thm)], [c_10012])).
% 15.14/5.84  tff(c_8689, plain, (![B_37]: (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_2'('#skF_5', B_37))='#skF_2'('#skF_5', B_37) | ~m1_subset_1('#skF_2'('#skF_5', B_37), k1_xboole_0) | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | r1_tarski('#skF_5', B_37) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(B_37)) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37))), inference(superposition, [status(thm), theory('equality')], [c_8609, c_7278])).
% 15.14/5.84  tff(c_8794, plain, (![B_37]: (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_2'('#skF_5', B_37))='#skF_2'('#skF_5', B_37) | ~m1_subset_1('#skF_2'('#skF_5', B_37), k1_xboole_0) | v2_struct_0('#skF_3') | r1_tarski('#skF_5', B_37) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(B_37)) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_8689])).
% 15.14/5.84  tff(c_8795, plain, (![B_37]: (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_2'('#skF_5', B_37))='#skF_2'('#skF_5', B_37) | ~m1_subset_1('#skF_2'('#skF_5', B_37), k1_xboole_0) | r1_tarski('#skF_5', B_37) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(B_37)) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37))), inference(negUnitSimplification, [status(thm)], [c_72, c_8794])).
% 15.14/5.84  tff(c_13171, plain, (![B_1034]: (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_2'('#skF_5', B_1034))='#skF_2'('#skF_5', B_1034) | ~m1_subset_1('#skF_2'('#skF_5', B_1034), k1_xboole_0) | r1_tarski('#skF_5', B_1034) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_1034)) | ~v1_funct_1(B_1034) | ~v1_relat_1(B_1034))), inference(demodulation, [status(thm), theory('equality')], [c_8891, c_8795])).
% 15.14/5.84  tff(c_13187, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_5', k4_tmap_1('#skF_3', '#skF_4')))!='#skF_2'('#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | r1_tarski('#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(k4_tmap_1('#skF_3', '#skF_4'))) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~v1_relat_1(k4_tmap_1('#skF_3', '#skF_4')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~m1_subset_1('#skF_2'('#skF_5', k4_tmap_1('#skF_3', '#skF_4')), k1_xboole_0) | r1_tarski('#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~r1_tarski(k1_xboole_0, k1_relat_1(k4_tmap_1('#skF_3', '#skF_4'))) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~v1_relat_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_13171, c_36])).
% 15.14/5.84  tff(c_13210, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_5', k4_tmap_1('#skF_3', '#skF_4')))!='#skF_2'('#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | r1_tarski('#skF_5', k4_tmap_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9294, c_9839, c_6, c_9445, c_12399, c_90, c_62, c_9294, c_9839, c_6, c_8891, c_9445, c_13187])).
% 15.14/5.84  tff(c_13211, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_5', k4_tmap_1('#skF_3', '#skF_4')))!='#skF_2'('#skF_5', k4_tmap_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_12400, c_13210])).
% 15.14/5.84  tff(c_8977, plain, (![B_37]: (r2_hidden('#skF_2'('#skF_5', B_37), k1_xboole_0) | r1_tarski('#skF_5', B_37) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(B_37)) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8891, c_38])).
% 15.14/5.84  tff(c_12438, plain, (![B_1001]: (r2_hidden('#skF_2'('#skF_5', B_1001), k1_xboole_0) | r1_tarski('#skF_5', B_1001) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_1001)) | ~v1_funct_1(B_1001) | ~v1_relat_1(B_1001))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_62, c_8891, c_8977])).
% 15.14/5.84  tff(c_13957, plain, (![B_1066]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', B_1066))='#skF_2'('#skF_5', B_1066) | ~m1_subset_1('#skF_2'('#skF_5', B_1066), k1_xboole_0) | r1_tarski('#skF_5', B_1066) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_1066)) | ~v1_funct_1(B_1066) | ~v1_relat_1(B_1066))), inference(resolution, [status(thm)], [c_12438, c_9606])).
% 15.14/5.84  tff(c_13969, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_5', k4_tmap_1('#skF_3', '#skF_4')))='#skF_2'('#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_2'('#skF_5', k4_tmap_1('#skF_3', '#skF_4')), k1_xboole_0) | r1_tarski('#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~v1_relat_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_9445, c_13957])).
% 15.14/5.84  tff(c_13982, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_5', k4_tmap_1('#skF_3', '#skF_4')))='#skF_2'('#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | r1_tarski('#skF_5', k4_tmap_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9294, c_9839, c_6, c_12399, c_13969])).
% 15.14/5.84  tff(c_13984, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12400, c_13211, c_13982])).
% 15.14/5.84  tff(c_13985, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_8885])).
% 15.14/5.84  tff(c_13999, plain, (r2_funct_2(k1_relat_1('#skF_5'), '#skF_5', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_13985, c_8613])).
% 15.14/5.84  tff(c_13986, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_8885])).
% 15.14/5.84  tff(c_14063, plain, (k1_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_13985, c_13986])).
% 15.14/5.84  tff(c_14228, plain, (v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), k1_relat_1('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_13985, c_8821])).
% 15.14/5.84  tff(c_14336, plain, (m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_13985, c_8818])).
% 15.14/5.84  tff(c_14559, plain, (![C_1106, A_1107]: (C_1106='#skF_5' | ~v1_funct_2(C_1106, A_1107, '#skF_5') | A_1107='#skF_5' | ~m1_subset_1(C_1106, k1_zfmisc_1(k2_zfmisc_1(A_1107, '#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_13985, c_13985, c_13985, c_13985, c_20])).
% 15.14/5.84  tff(c_14565, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5' | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), k1_relat_1('#skF_5'), '#skF_5') | k1_relat_1('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_14336, c_14559])).
% 15.14/5.84  tff(c_14572, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5' | k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_14228, c_14565])).
% 15.14/5.84  tff(c_14573, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_14063, c_14572])).
% 15.14/5.84  tff(c_14304, plain, (~r2_funct_2(k1_relat_1('#skF_5'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_13985, c_8619])).
% 15.14/5.84  tff(c_14583, plain, (~r2_funct_2(k1_relat_1('#skF_5'), '#skF_5', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14573, c_14304])).
% 15.14/5.84  tff(c_14590, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13999, c_14583])).
% 15.14/5.84  tff(c_14591, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_8608])).
% 15.14/5.84  tff(c_14593, plain, (~r2_funct_2(k1_relat_1('#skF_5'), u1_struct_0('#skF_3'), '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14591, c_142])).
% 15.14/5.84  tff(c_14596, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7582, c_14593])).
% 15.14/5.84  tff(c_14597, plain, (u1_struct_0('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_137])).
% 15.14/5.84  tff(c_14604, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14597, c_60])).
% 15.14/5.84  tff(c_14603, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14597, c_58])).
% 15.14/5.84  tff(c_14641, plain, (k1_xboole_0='#skF_5' | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k1_xboole_0) | u1_struct_0('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_14603, c_20])).
% 15.14/5.84  tff(c_14659, plain, (k1_xboole_0='#skF_5' | u1_struct_0('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14604, c_14641])).
% 15.14/5.84  tff(c_14665, plain, (u1_struct_0('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_14659])).
% 15.14/5.84  tff(c_14598, plain, (u1_struct_0('#skF_4')!=k1_relat_1('#skF_5')), inference(splitRight, [status(thm)], [c_137])).
% 15.14/5.84  tff(c_14669, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14665, c_14598])).
% 15.14/5.84  tff(c_14668, plain, (v1_funct_2('#skF_5', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14665, c_14604])).
% 15.14/5.84  tff(c_14667, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14665, c_14603])).
% 15.14/5.84  tff(c_14702, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_5')=k1_xboole_0 | ~v1_funct_2('#skF_5', k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_14667, c_26])).
% 15.14/5.84  tff(c_14725, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14668, c_14702])).
% 15.14/5.84  tff(c_14730, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_14667, c_16])).
% 15.14/5.84  tff(c_14777, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14725, c_14730])).
% 15.14/5.84  tff(c_14778, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14669, c_14777])).
% 15.14/5.84  tff(c_14779, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_14659])).
% 15.14/5.84  tff(c_14780, plain, (u1_struct_0('#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_14659])).
% 15.14/5.84  tff(c_14797, plain, (u1_struct_0('#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_14779, c_14780])).
% 15.14/5.84  tff(c_14623, plain, (![A_1108, B_1109]: (v1_funct_2(k4_tmap_1(A_1108, B_1109), u1_struct_0(B_1109), u1_struct_0(A_1108)) | ~m1_pre_topc(B_1109, A_1108) | ~l1_pre_topc(A_1108) | ~v2_pre_topc(A_1108) | v2_struct_0(A_1108))), inference(cnfTransformation, [status(thm)], [f_125])).
% 15.14/5.84  tff(c_14629, plain, (![B_1109]: (v1_funct_2(k4_tmap_1('#skF_3', B_1109), u1_struct_0(B_1109), k1_xboole_0) | ~m1_pre_topc(B_1109, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_14597, c_14623])).
% 15.14/5.84  tff(c_14631, plain, (![B_1109]: (v1_funct_2(k4_tmap_1('#skF_3', B_1109), u1_struct_0(B_1109), k1_xboole_0) | ~m1_pre_topc(B_1109, '#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_14629])).
% 15.14/5.84  tff(c_14632, plain, (![B_1109]: (v1_funct_2(k4_tmap_1('#skF_3', B_1109), u1_struct_0(B_1109), k1_xboole_0) | ~m1_pre_topc(B_1109, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_72, c_14631])).
% 15.14/5.84  tff(c_14795, plain, (![B_1109]: (v1_funct_2(k4_tmap_1('#skF_3', B_1109), u1_struct_0(B_1109), '#skF_5') | ~m1_pre_topc(B_1109, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14779, c_14632])).
% 15.14/5.84  tff(c_14784, plain, (u1_struct_0('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_14779, c_14597])).
% 15.14/5.84  tff(c_14841, plain, (![A_1114, B_1115]: (m1_subset_1(k4_tmap_1(A_1114, B_1115), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_1115), u1_struct_0(A_1114)))) | ~m1_pre_topc(B_1115, A_1114) | ~l1_pre_topc(A_1114) | ~v2_pre_topc(A_1114) | v2_struct_0(A_1114))), inference(cnfTransformation, [status(thm)], [f_125])).
% 15.14/5.84  tff(c_14855, plain, (![B_1115]: (m1_subset_1(k4_tmap_1('#skF_3', B_1115), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_1115), '#skF_5'))) | ~m1_pre_topc(B_1115, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_14784, c_14841])).
% 15.14/5.84  tff(c_14862, plain, (![B_1115]: (m1_subset_1(k4_tmap_1('#skF_3', B_1115), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_1115), '#skF_5'))) | ~m1_pre_topc(B_1115, '#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_14855])).
% 15.14/5.84  tff(c_14863, plain, (![B_1115]: (m1_subset_1(k4_tmap_1('#skF_3', B_1115), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_1115), '#skF_5'))) | ~m1_pre_topc(B_1115, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_72, c_14862])).
% 15.14/5.84  tff(c_14972, plain, (![C_1138, A_1139]: (C_1138='#skF_5' | ~v1_funct_2(C_1138, A_1139, '#skF_5') | A_1139='#skF_5' | ~m1_subset_1(C_1138, k1_zfmisc_1(k2_zfmisc_1(A_1139, '#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_14779, c_14779, c_14779, c_14779, c_20])).
% 15.14/5.84  tff(c_15054, plain, (![B_1157]: (k4_tmap_1('#skF_3', B_1157)='#skF_5' | ~v1_funct_2(k4_tmap_1('#skF_3', B_1157), u1_struct_0(B_1157), '#skF_5') | u1_struct_0(B_1157)='#skF_5' | ~m1_pre_topc(B_1157, '#skF_3'))), inference(resolution, [status(thm)], [c_14863, c_14972])).
% 15.14/5.84  tff(c_15063, plain, (![B_1158]: (k4_tmap_1('#skF_3', B_1158)='#skF_5' | u1_struct_0(B_1158)='#skF_5' | ~m1_pre_topc(B_1158, '#skF_3'))), inference(resolution, [status(thm)], [c_14795, c_15054])).
% 15.14/5.84  tff(c_15066, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5' | u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_64, c_15063])).
% 15.14/5.84  tff(c_15069, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_14797, c_15066])).
% 15.14/5.84  tff(c_14602, plain, (~r2_funct_2(u1_struct_0('#skF_4'), k1_xboole_0, k4_tmap_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14597, c_54])).
% 15.14/5.84  tff(c_14781, plain, (~r2_funct_2(u1_struct_0('#skF_4'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14779, c_14602])).
% 15.14/5.84  tff(c_15076, plain, (~r2_funct_2(u1_struct_0('#skF_4'), '#skF_5', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_15069, c_14781])).
% 15.14/5.84  tff(c_14783, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14779, c_14604])).
% 15.14/5.84  tff(c_14782, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_14779, c_14603])).
% 15.14/5.84  tff(c_15561, plain, (![A_1214, B_1215, C_1216]: (r2_funct_2(A_1214, B_1215, C_1216, C_1216) | ~m1_subset_1(C_1216, k1_zfmisc_1(k2_zfmisc_1(A_1214, B_1215))) | ~v1_funct_2(C_1216, A_1214, B_1215) | ~v1_funct_1(C_1216) | ~m1_subset_1(C_1216, k1_zfmisc_1(k2_zfmisc_1(A_1214, B_1215))) | ~v1_funct_2(C_1216, A_1214, B_1215) | ~v1_funct_1(C_1216))), inference(reflexivity, [status(thm), theory('equality')], [c_32])).
% 15.14/5.84  tff(c_15567, plain, (r2_funct_2(u1_struct_0('#skF_4'), '#skF_5', '#skF_5', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), '#skF_5'))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), '#skF_5') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_14782, c_15561])).
% 15.14/5.84  tff(c_15574, plain, (r2_funct_2(u1_struct_0('#skF_4'), '#skF_5', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_14783, c_14782, c_15567])).
% 15.14/5.84  tff(c_15576, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15076, c_15574])).
% 15.14/5.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.14/5.84  
% 15.14/5.84  Inference rules
% 15.14/5.84  ----------------------
% 15.14/5.84  #Ref     : 10
% 15.14/5.84  #Sup     : 3447
% 15.14/5.84  #Fact    : 0
% 15.14/5.84  #Define  : 0
% 15.14/5.84  #Split   : 25
% 15.14/5.84  #Chain   : 0
% 15.14/5.84  #Close   : 0
% 15.14/5.84  
% 15.14/5.84  Ordering : KBO
% 15.14/5.84  
% 15.14/5.84  Simplification rules
% 15.14/5.84  ----------------------
% 15.14/5.84  #Subsume      : 917
% 15.14/5.84  #Demod        : 5687
% 15.14/5.84  #Tautology    : 943
% 15.14/5.84  #SimpNegUnit  : 524
% 15.14/5.84  #BackRed      : 283
% 15.14/5.84  
% 15.14/5.84  #Partial instantiations: 0
% 15.14/5.84  #Strategies tried      : 1
% 15.14/5.84  
% 15.14/5.84  Timing (in seconds)
% 15.14/5.84  ----------------------
% 15.14/5.85  Preprocessing        : 0.59
% 15.14/5.85  Parsing              : 0.30
% 15.14/5.85  CNF conversion       : 0.05
% 15.14/5.85  Main loop            : 4.30
% 15.14/5.85  Inferencing          : 1.23
% 15.14/5.85  Reduction            : 1.29
% 15.14/5.85  Demodulation         : 0.94
% 15.14/5.85  BG Simplification    : 0.14
% 15.14/5.85  Subsumption          : 1.42
% 15.14/5.85  Abstraction          : 0.18
% 15.14/5.85  MUC search           : 0.00
% 15.14/5.85  Cooper               : 0.00
% 15.14/5.85  Total                : 5.00
% 15.14/5.85  Index Insertion      : 0.00
% 15.14/5.85  Index Deletion       : 0.00
% 15.14/5.85  Index Matching       : 0.00
% 15.14/5.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
