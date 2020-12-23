%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:11 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 226 expanded)
%              Number of leaves         :   32 ( 112 expanded)
%              Depth                    :   10
%              Number of atoms          :  341 (2480 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   29 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v5_pre_topc > v1_funct_2 > r4_tsep_1 > v1_tsep_1 > r1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k2_tsep_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k10_tmap_1,type,(
    k10_tmap_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r4_tsep_1,type,(
    r4_tsep_1: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_tsep_1,type,(
    k2_tsep_1: ( $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_209,negated_conjecture,(
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
                  & v1_tsep_1(C,A)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & v1_tsep_1(D,A)
                      & m1_pre_topc(D,A) )
                   => ( ~ r1_tsep_1(C,D)
                     => ! [E] :
                          ( ( v1_funct_1(E)
                            & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                            & v5_pre_topc(E,C,B)
                            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                         => ! [F] :
                              ( ( v1_funct_1(F)
                                & v1_funct_2(F,u1_struct_0(D),u1_struct_0(B))
                                & v5_pre_topc(F,D,B)
                                & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                             => ( r2_funct_2(u1_struct_0(k2_tsep_1(A,C,D)),u1_struct_0(B),k3_tmap_1(A,B,C,k2_tsep_1(A,C,D),E),k3_tmap_1(A,B,D,k2_tsep_1(A,C,D),F))
                               => ( v1_funct_1(k10_tmap_1(A,B,C,D,E,F))
                                  & v1_funct_2(k10_tmap_1(A,B,C,D,E,F),u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                                  & v5_pre_topc(k10_tmap_1(A,B,C,D,E,F),k1_tsep_1(A,C,D),B)
                                  & m1_subset_1(k10_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_tmap_1)).

tff(f_146,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_tsep_1(B,A)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( v1_tsep_1(C,A)
                & m1_pre_topc(C,A) )
             => r4_tsep_1(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tsep_1)).

tff(f_67,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A)
        & ~ v2_struct_0(D)
        & m1_pre_topc(D,A)
        & v1_funct_1(E)
        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B))))
        & v1_funct_1(F)
        & v1_funct_2(F,u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
     => ( v1_funct_1(k10_tmap_1(A,B,C,D,E,F))
        & v1_funct_2(k10_tmap_1(A,B,C,D,E,F),u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
        & m1_subset_1(k10_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_tmap_1)).

tff(f_127,axiom,(
    ! [A] :
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
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ( ~ r1_tsep_1(C,D)
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                          & v5_pre_topc(E,C,B)
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                       => ! [F] :
                            ( ( v1_funct_1(F)
                              & v1_funct_2(F,u1_struct_0(D),u1_struct_0(B))
                              & v5_pre_topc(F,D,B)
                              & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                           => ( ( r2_funct_2(u1_struct_0(k2_tsep_1(A,C,D)),u1_struct_0(B),k3_tmap_1(A,B,C,k2_tsep_1(A,C,D),E),k3_tmap_1(A,B,D,k2_tsep_1(A,C,D),F))
                                & r4_tsep_1(A,C,D) )
                             => ( v1_funct_1(k10_tmap_1(A,B,C,D,E,F))
                                & v1_funct_2(k10_tmap_1(A,B,C,D,E,F),u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                                & v5_pre_topc(k10_tmap_1(A,B,C,D,E,F),k1_tsep_1(A,C,D),B)
                                & m1_subset_1(k10_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_tmap_1)).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_60,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_58,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_48,plain,(
    v1_tsep_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_46,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_42,plain,(
    v1_tsep_1('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_40,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_16,plain,(
    ! [A_70,B_74,C_76] :
      ( r4_tsep_1(A_70,B_74,C_76)
      | ~ m1_pre_topc(C_76,A_70)
      | ~ v1_tsep_1(C_76,A_70)
      | ~ m1_pre_topc(B_74,A_70)
      | ~ v1_tsep_1(B_74,A_70)
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_38,plain,(
    ~ r1_tsep_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_36,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_34,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_28,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_26,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_22,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_251,plain,(
    ! [B_200,A_202,E_198,D_199,C_201,F_197] :
      ( v1_funct_2(k10_tmap_1(A_202,B_200,C_201,D_199,E_198,F_197),u1_struct_0(k1_tsep_1(A_202,C_201,D_199)),u1_struct_0(B_200))
      | ~ m1_subset_1(F_197,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_199),u1_struct_0(B_200))))
      | ~ v1_funct_2(F_197,u1_struct_0(D_199),u1_struct_0(B_200))
      | ~ v1_funct_1(F_197)
      | ~ m1_subset_1(E_198,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_201),u1_struct_0(B_200))))
      | ~ v1_funct_2(E_198,u1_struct_0(C_201),u1_struct_0(B_200))
      | ~ v1_funct_1(E_198)
      | ~ m1_pre_topc(D_199,A_202)
      | v2_struct_0(D_199)
      | ~ m1_pre_topc(C_201,A_202)
      | v2_struct_0(C_201)
      | ~ l1_pre_topc(B_200)
      | ~ v2_pre_topc(B_200)
      | v2_struct_0(B_200)
      | ~ l1_pre_topc(A_202)
      | ~ v2_pre_topc(A_202)
      | v2_struct_0(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_163,plain,(
    ! [D_177,B_178,E_176,A_180,F_175,C_179] :
      ( m1_subset_1(k10_tmap_1(A_180,B_178,C_179,D_177,E_176,F_175),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_180,C_179,D_177)),u1_struct_0(B_178))))
      | ~ m1_subset_1(F_175,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_177),u1_struct_0(B_178))))
      | ~ v1_funct_2(F_175,u1_struct_0(D_177),u1_struct_0(B_178))
      | ~ v1_funct_1(F_175)
      | ~ m1_subset_1(E_176,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_179),u1_struct_0(B_178))))
      | ~ v1_funct_2(E_176,u1_struct_0(C_179),u1_struct_0(B_178))
      | ~ v1_funct_1(E_176)
      | ~ m1_pre_topc(D_177,A_180)
      | v2_struct_0(D_177)
      | ~ m1_pre_topc(C_179,A_180)
      | v2_struct_0(C_179)
      | ~ l1_pre_topc(B_178)
      | ~ v2_pre_topc(B_178)
      | v2_struct_0(B_178)
      | ~ l1_pre_topc(A_180)
      | ~ v2_pre_topc(A_180)
      | v2_struct_0(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_65,plain,(
    ! [B_140,E_138,C_141,A_142,F_137,D_139] :
      ( v1_funct_1(k10_tmap_1(A_142,B_140,C_141,D_139,E_138,F_137))
      | ~ m1_subset_1(F_137,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_139),u1_struct_0(B_140))))
      | ~ v1_funct_2(F_137,u1_struct_0(D_139),u1_struct_0(B_140))
      | ~ v1_funct_1(F_137)
      | ~ m1_subset_1(E_138,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_141),u1_struct_0(B_140))))
      | ~ v1_funct_2(E_138,u1_struct_0(C_141),u1_struct_0(B_140))
      | ~ v1_funct_1(E_138)
      | ~ m1_pre_topc(D_139,A_142)
      | v2_struct_0(D_139)
      | ~ m1_pre_topc(C_141,A_142)
      | v2_struct_0(C_141)
      | ~ l1_pre_topc(B_140)
      | ~ v2_pre_topc(B_140)
      | v2_struct_0(B_140)
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_69,plain,(
    ! [A_142,C_141,E_138] :
      ( v1_funct_1(k10_tmap_1(A_142,'#skF_2',C_141,'#skF_4',E_138,'#skF_6'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_138,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_141),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_138,u1_struct_0(C_141),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_138)
      | ~ m1_pre_topc('#skF_4',A_142)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_141,A_142)
      | v2_struct_0(C_141)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(resolution,[status(thm)],[c_22,c_65])).

tff(c_76,plain,(
    ! [A_142,C_141,E_138] :
      ( v1_funct_1(k10_tmap_1(A_142,'#skF_2',C_141,'#skF_4',E_138,'#skF_6'))
      | ~ m1_subset_1(E_138,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_141),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_138,u1_struct_0(C_141),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_138)
      | ~ m1_pre_topc('#skF_4',A_142)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_141,A_142)
      | v2_struct_0(C_141)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_28,c_26,c_69])).

tff(c_93,plain,(
    ! [A_148,C_149,E_150] :
      ( v1_funct_1(k10_tmap_1(A_148,'#skF_2',C_149,'#skF_4',E_150,'#skF_6'))
      | ~ m1_subset_1(E_150,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_149),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_150,u1_struct_0(C_149),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_150)
      | ~ m1_pre_topc('#skF_4',A_148)
      | ~ m1_pre_topc(C_149,A_148)
      | v2_struct_0(C_149)
      | ~ l1_pre_topc(A_148)
      | ~ v2_pre_topc(A_148)
      | v2_struct_0(A_148) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_44,c_76])).

tff(c_95,plain,(
    ! [A_148] :
      ( v1_funct_1(k10_tmap_1(A_148,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_148)
      | ~ m1_pre_topc('#skF_3',A_148)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_148)
      | ~ v2_pre_topc(A_148)
      | v2_struct_0(A_148) ) ),
    inference(resolution,[status(thm)],[c_30,c_93])).

tff(c_100,plain,(
    ! [A_148] :
      ( v1_funct_1(k10_tmap_1(A_148,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_148)
      | ~ m1_pre_topc('#skF_3',A_148)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_148)
      | ~ v2_pre_topc(A_148)
      | v2_struct_0(A_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_95])).

tff(c_107,plain,(
    ! [A_152] :
      ( v1_funct_1(k10_tmap_1(A_152,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_152)
      | ~ m1_pre_topc('#skF_3',A_152)
      | ~ l1_pre_topc(A_152)
      | ~ v2_pre_topc(A_152)
      | v2_struct_0(A_152) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_100])).

tff(c_18,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_64,plain,(
    ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_110,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_107,c_64])).

tff(c_113,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_46,c_40,c_110])).

tff(c_115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_113])).

tff(c_116,plain,
    ( ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_118,plain,(
    ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_174,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_163,c_118])).

tff(c_186,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_52,c_46,c_40,c_36,c_34,c_30,c_28,c_26,c_22,c_174])).

tff(c_188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_50,c_44,c_186])).

tff(c_189,plain,
    ( ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_191,plain,(
    ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_189])).

tff(c_254,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_251,c_191])).

tff(c_257,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_52,c_46,c_40,c_36,c_34,c_30,c_28,c_26,c_22,c_254])).

tff(c_259,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_50,c_44,c_257])).

tff(c_260,plain,(
    ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_32,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_24,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_20,plain,(
    r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_3',k2_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_5'),k3_tmap_1('#skF_1','#skF_2','#skF_4',k2_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_433,plain,(
    ! [A_258,F_260,E_255,C_256,D_259,B_257] :
      ( v5_pre_topc(k10_tmap_1(A_258,B_257,C_256,D_259,E_255,F_260),k1_tsep_1(A_258,C_256,D_259),B_257)
      | ~ r4_tsep_1(A_258,C_256,D_259)
      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(A_258,C_256,D_259)),u1_struct_0(B_257),k3_tmap_1(A_258,B_257,C_256,k2_tsep_1(A_258,C_256,D_259),E_255),k3_tmap_1(A_258,B_257,D_259,k2_tsep_1(A_258,C_256,D_259),F_260))
      | ~ m1_subset_1(F_260,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_259),u1_struct_0(B_257))))
      | ~ v5_pre_topc(F_260,D_259,B_257)
      | ~ v1_funct_2(F_260,u1_struct_0(D_259),u1_struct_0(B_257))
      | ~ v1_funct_1(F_260)
      | ~ m1_subset_1(E_255,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_256),u1_struct_0(B_257))))
      | ~ v5_pre_topc(E_255,C_256,B_257)
      | ~ v1_funct_2(E_255,u1_struct_0(C_256),u1_struct_0(B_257))
      | ~ v1_funct_1(E_255)
      | r1_tsep_1(C_256,D_259)
      | ~ m1_pre_topc(D_259,A_258)
      | v2_struct_0(D_259)
      | ~ m1_pre_topc(C_256,A_258)
      | v2_struct_0(C_256)
      | ~ l1_pre_topc(B_257)
      | ~ v2_pre_topc(B_257)
      | v2_struct_0(B_257)
      | ~ l1_pre_topc(A_258)
      | ~ v2_pre_topc(A_258)
      | v2_struct_0(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_436,plain,
    ( v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | r1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_433])).

tff(c_439,plain,
    ( v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
    | r1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_52,c_46,c_40,c_36,c_34,c_32,c_30,c_28,c_26,c_24,c_22,c_436])).

tff(c_440,plain,(
    ~ r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_50,c_44,c_38,c_260,c_439])).

tff(c_443,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_tsep_1('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_tsep_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_440])).

tff(c_446,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_48,c_46,c_42,c_40,c_443])).

tff(c_448,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_446])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:24:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.58/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.56  
% 3.69/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.56  %$ r2_funct_2 > v5_pre_topc > v1_funct_2 > r4_tsep_1 > v1_tsep_1 > r1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k2_tsep_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.69/1.56  
% 3.69/1.56  %Foreground sorts:
% 3.69/1.56  
% 3.69/1.56  
% 3.69/1.56  %Background operators:
% 3.69/1.56  
% 3.69/1.56  
% 3.69/1.56  %Foreground operators:
% 3.69/1.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.69/1.56  tff(k10_tmap_1, type, k10_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.69/1.56  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 3.69/1.56  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.69/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.69/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.69/1.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.69/1.56  tff(r4_tsep_1, type, r4_tsep_1: ($i * $i * $i) > $o).
% 3.69/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.69/1.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.69/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.69/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.69/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.69/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.69/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.69/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.69/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.69/1.56  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.69/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.69/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.69/1.56  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.69/1.56  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.69/1.56  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 3.69/1.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.69/1.56  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 3.69/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.69/1.56  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.69/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.69/1.56  
% 3.69/1.58  tff(f_209, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((~v2_struct_0(C) & v1_tsep_1(C, A)) & m1_pre_topc(C, A)) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, A)) & m1_pre_topc(D, A)) => (~r1_tsep_1(C, D) => (![E]: ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: ((((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (r2_funct_2(u1_struct_0(k2_tsep_1(A, C, D)), u1_struct_0(B), k3_tmap_1(A, B, C, k2_tsep_1(A, C, D), E), k3_tmap_1(A, B, D, k2_tsep_1(A, C, D), F)) => (((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(k10_tmap_1(A, B, C, D, E, F), k1_tsep_1(A, C, D), B)) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_tmap_1)).
% 3.69/1.58  tff(f_146, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) => (![C]: ((v1_tsep_1(C, A) & m1_pre_topc(C, A)) => r4_tsep_1(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tsep_1)).
% 3.69/1.58  tff(f_67, axiom, (![A, B, C, D, E, F]: ((((((((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) & ~v2_struct_0(D)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(F)) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_tmap_1)).
% 3.69/1.58  tff(f_127, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (~r1_tsep_1(C, D) => (![E]: ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: ((((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((r2_funct_2(u1_struct_0(k2_tsep_1(A, C, D)), u1_struct_0(B), k3_tmap_1(A, B, C, k2_tsep_1(A, C, D), E), k3_tmap_1(A, B, D, k2_tsep_1(A, C, D), F)) & r4_tsep_1(A, C, D)) => (((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(k10_tmap_1(A, B, C, D, E, F), k1_tsep_1(A, C, D), B)) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_tmap_1)).
% 3.69/1.58  tff(c_62, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_209])).
% 3.69/1.58  tff(c_60, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_209])).
% 3.69/1.58  tff(c_58, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_209])).
% 3.69/1.58  tff(c_48, plain, (v1_tsep_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_209])).
% 3.69/1.58  tff(c_46, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_209])).
% 3.69/1.58  tff(c_42, plain, (v1_tsep_1('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_209])).
% 3.69/1.58  tff(c_40, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_209])).
% 3.69/1.58  tff(c_16, plain, (![A_70, B_74, C_76]: (r4_tsep_1(A_70, B_74, C_76) | ~m1_pre_topc(C_76, A_70) | ~v1_tsep_1(C_76, A_70) | ~m1_pre_topc(B_74, A_70) | ~v1_tsep_1(B_74, A_70) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.69/1.58  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_209])).
% 3.69/1.58  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_209])).
% 3.69/1.58  tff(c_44, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_209])).
% 3.69/1.58  tff(c_38, plain, (~r1_tsep_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_209])).
% 3.69/1.58  tff(c_54, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_209])).
% 3.69/1.58  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_209])).
% 3.69/1.58  tff(c_36, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_209])).
% 3.69/1.58  tff(c_34, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_209])).
% 3.69/1.58  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_209])).
% 3.69/1.58  tff(c_28, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_209])).
% 3.69/1.58  tff(c_26, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_209])).
% 3.69/1.58  tff(c_22, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_209])).
% 3.69/1.58  tff(c_251, plain, (![B_200, A_202, E_198, D_199, C_201, F_197]: (v1_funct_2(k10_tmap_1(A_202, B_200, C_201, D_199, E_198, F_197), u1_struct_0(k1_tsep_1(A_202, C_201, D_199)), u1_struct_0(B_200)) | ~m1_subset_1(F_197, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_199), u1_struct_0(B_200)))) | ~v1_funct_2(F_197, u1_struct_0(D_199), u1_struct_0(B_200)) | ~v1_funct_1(F_197) | ~m1_subset_1(E_198, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_201), u1_struct_0(B_200)))) | ~v1_funct_2(E_198, u1_struct_0(C_201), u1_struct_0(B_200)) | ~v1_funct_1(E_198) | ~m1_pre_topc(D_199, A_202) | v2_struct_0(D_199) | ~m1_pre_topc(C_201, A_202) | v2_struct_0(C_201) | ~l1_pre_topc(B_200) | ~v2_pre_topc(B_200) | v2_struct_0(B_200) | ~l1_pre_topc(A_202) | ~v2_pre_topc(A_202) | v2_struct_0(A_202))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.69/1.58  tff(c_163, plain, (![D_177, B_178, E_176, A_180, F_175, C_179]: (m1_subset_1(k10_tmap_1(A_180, B_178, C_179, D_177, E_176, F_175), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_180, C_179, D_177)), u1_struct_0(B_178)))) | ~m1_subset_1(F_175, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_177), u1_struct_0(B_178)))) | ~v1_funct_2(F_175, u1_struct_0(D_177), u1_struct_0(B_178)) | ~v1_funct_1(F_175) | ~m1_subset_1(E_176, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_179), u1_struct_0(B_178)))) | ~v1_funct_2(E_176, u1_struct_0(C_179), u1_struct_0(B_178)) | ~v1_funct_1(E_176) | ~m1_pre_topc(D_177, A_180) | v2_struct_0(D_177) | ~m1_pre_topc(C_179, A_180) | v2_struct_0(C_179) | ~l1_pre_topc(B_178) | ~v2_pre_topc(B_178) | v2_struct_0(B_178) | ~l1_pre_topc(A_180) | ~v2_pre_topc(A_180) | v2_struct_0(A_180))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.69/1.58  tff(c_65, plain, (![B_140, E_138, C_141, A_142, F_137, D_139]: (v1_funct_1(k10_tmap_1(A_142, B_140, C_141, D_139, E_138, F_137)) | ~m1_subset_1(F_137, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_139), u1_struct_0(B_140)))) | ~v1_funct_2(F_137, u1_struct_0(D_139), u1_struct_0(B_140)) | ~v1_funct_1(F_137) | ~m1_subset_1(E_138, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_141), u1_struct_0(B_140)))) | ~v1_funct_2(E_138, u1_struct_0(C_141), u1_struct_0(B_140)) | ~v1_funct_1(E_138) | ~m1_pre_topc(D_139, A_142) | v2_struct_0(D_139) | ~m1_pre_topc(C_141, A_142) | v2_struct_0(C_141) | ~l1_pre_topc(B_140) | ~v2_pre_topc(B_140) | v2_struct_0(B_140) | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142) | v2_struct_0(A_142))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.69/1.58  tff(c_69, plain, (![A_142, C_141, E_138]: (v1_funct_1(k10_tmap_1(A_142, '#skF_2', C_141, '#skF_4', E_138, '#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_138, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_141), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_138, u1_struct_0(C_141), u1_struct_0('#skF_2')) | ~v1_funct_1(E_138) | ~m1_pre_topc('#skF_4', A_142) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_141, A_142) | v2_struct_0(C_141) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142) | v2_struct_0(A_142))), inference(resolution, [status(thm)], [c_22, c_65])).
% 3.69/1.58  tff(c_76, plain, (![A_142, C_141, E_138]: (v1_funct_1(k10_tmap_1(A_142, '#skF_2', C_141, '#skF_4', E_138, '#skF_6')) | ~m1_subset_1(E_138, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_141), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_138, u1_struct_0(C_141), u1_struct_0('#skF_2')) | ~v1_funct_1(E_138) | ~m1_pre_topc('#skF_4', A_142) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_141, A_142) | v2_struct_0(C_141) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142) | v2_struct_0(A_142))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_28, c_26, c_69])).
% 3.69/1.58  tff(c_93, plain, (![A_148, C_149, E_150]: (v1_funct_1(k10_tmap_1(A_148, '#skF_2', C_149, '#skF_4', E_150, '#skF_6')) | ~m1_subset_1(E_150, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_149), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_150, u1_struct_0(C_149), u1_struct_0('#skF_2')) | ~v1_funct_1(E_150) | ~m1_pre_topc('#skF_4', A_148) | ~m1_pre_topc(C_149, A_148) | v2_struct_0(C_149) | ~l1_pre_topc(A_148) | ~v2_pre_topc(A_148) | v2_struct_0(A_148))), inference(negUnitSimplification, [status(thm)], [c_56, c_44, c_76])).
% 3.69/1.58  tff(c_95, plain, (![A_148]: (v1_funct_1(k10_tmap_1(A_148, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_148) | ~m1_pre_topc('#skF_3', A_148) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_148) | ~v2_pre_topc(A_148) | v2_struct_0(A_148))), inference(resolution, [status(thm)], [c_30, c_93])).
% 3.69/1.58  tff(c_100, plain, (![A_148]: (v1_funct_1(k10_tmap_1(A_148, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', A_148) | ~m1_pre_topc('#skF_3', A_148) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_148) | ~v2_pre_topc(A_148) | v2_struct_0(A_148))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_95])).
% 3.69/1.58  tff(c_107, plain, (![A_152]: (v1_funct_1(k10_tmap_1(A_152, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', A_152) | ~m1_pre_topc('#skF_3', A_152) | ~l1_pre_topc(A_152) | ~v2_pre_topc(A_152) | v2_struct_0(A_152))), inference(negUnitSimplification, [status(thm)], [c_50, c_100])).
% 3.69/1.58  tff(c_18, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_209])).
% 3.69/1.58  tff(c_64, plain, (~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_18])).
% 3.69/1.58  tff(c_110, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_107, c_64])).
% 3.69/1.58  tff(c_113, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_46, c_40, c_110])).
% 3.69/1.58  tff(c_115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_113])).
% 3.69/1.58  tff(c_116, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_18])).
% 3.69/1.58  tff(c_118, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_116])).
% 3.69/1.58  tff(c_174, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_163, c_118])).
% 3.69/1.58  tff(c_186, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_52, c_46, c_40, c_36, c_34, c_30, c_28, c_26, c_22, c_174])).
% 3.69/1.58  tff(c_188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_50, c_44, c_186])).
% 3.69/1.58  tff(c_189, plain, (~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_116])).
% 3.69/1.58  tff(c_191, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_189])).
% 3.69/1.58  tff(c_254, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_251, c_191])).
% 3.69/1.58  tff(c_257, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_52, c_46, c_40, c_36, c_34, c_30, c_28, c_26, c_22, c_254])).
% 3.69/1.58  tff(c_259, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_50, c_44, c_257])).
% 3.69/1.58  tff(c_260, plain, (~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_189])).
% 3.69/1.58  tff(c_32, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_209])).
% 3.69/1.58  tff(c_24, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_209])).
% 3.69/1.58  tff(c_20, plain, (r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_3', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_5'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_209])).
% 3.69/1.58  tff(c_433, plain, (![A_258, F_260, E_255, C_256, D_259, B_257]: (v5_pre_topc(k10_tmap_1(A_258, B_257, C_256, D_259, E_255, F_260), k1_tsep_1(A_258, C_256, D_259), B_257) | ~r4_tsep_1(A_258, C_256, D_259) | ~r2_funct_2(u1_struct_0(k2_tsep_1(A_258, C_256, D_259)), u1_struct_0(B_257), k3_tmap_1(A_258, B_257, C_256, k2_tsep_1(A_258, C_256, D_259), E_255), k3_tmap_1(A_258, B_257, D_259, k2_tsep_1(A_258, C_256, D_259), F_260)) | ~m1_subset_1(F_260, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_259), u1_struct_0(B_257)))) | ~v5_pre_topc(F_260, D_259, B_257) | ~v1_funct_2(F_260, u1_struct_0(D_259), u1_struct_0(B_257)) | ~v1_funct_1(F_260) | ~m1_subset_1(E_255, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_256), u1_struct_0(B_257)))) | ~v5_pre_topc(E_255, C_256, B_257) | ~v1_funct_2(E_255, u1_struct_0(C_256), u1_struct_0(B_257)) | ~v1_funct_1(E_255) | r1_tsep_1(C_256, D_259) | ~m1_pre_topc(D_259, A_258) | v2_struct_0(D_259) | ~m1_pre_topc(C_256, A_258) | v2_struct_0(C_256) | ~l1_pre_topc(B_257) | ~v2_pre_topc(B_257) | v2_struct_0(B_257) | ~l1_pre_topc(A_258) | ~v2_pre_topc(A_258) | v2_struct_0(A_258))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.69/1.58  tff(c_436, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | r1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_433])).
% 3.69/1.58  tff(c_439, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | r1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_52, c_46, c_40, c_36, c_34, c_32, c_30, c_28, c_26, c_24, c_22, c_436])).
% 3.69/1.58  tff(c_440, plain, (~r4_tsep_1('#skF_1', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_50, c_44, c_38, c_260, c_439])).
% 3.69/1.58  tff(c_443, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~v1_tsep_1('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~v1_tsep_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_440])).
% 3.69/1.58  tff(c_446, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_48, c_46, c_42, c_40, c_443])).
% 3.69/1.58  tff(c_448, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_446])).
% 3.69/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.58  
% 3.69/1.58  Inference rules
% 3.69/1.58  ----------------------
% 3.69/1.58  #Ref     : 0
% 3.69/1.58  #Sup     : 55
% 3.69/1.58  #Fact    : 0
% 3.69/1.58  #Define  : 0
% 3.69/1.58  #Split   : 4
% 3.69/1.58  #Chain   : 0
% 3.69/1.58  #Close   : 0
% 3.69/1.58  
% 3.69/1.58  Ordering : KBO
% 3.69/1.58  
% 3.69/1.58  Simplification rules
% 3.69/1.58  ----------------------
% 3.69/1.58  #Subsume      : 7
% 3.69/1.58  #Demod        : 176
% 3.69/1.58  #Tautology    : 6
% 3.69/1.58  #SimpNegUnit  : 46
% 3.69/1.58  #BackRed      : 0
% 3.69/1.58  
% 3.69/1.58  #Partial instantiations: 0
% 3.69/1.58  #Strategies tried      : 1
% 3.69/1.58  
% 3.69/1.58  Timing (in seconds)
% 3.69/1.58  ----------------------
% 3.69/1.59  Preprocessing        : 0.39
% 3.69/1.59  Parsing              : 0.21
% 3.69/1.59  CNF conversion       : 0.05
% 3.69/1.59  Main loop            : 0.40
% 3.69/1.59  Inferencing          : 0.15
% 3.69/1.59  Reduction            : 0.13
% 3.69/1.59  Demodulation         : 0.10
% 3.69/1.59  BG Simplification    : 0.02
% 3.69/1.59  Subsumption          : 0.09
% 3.69/1.59  Abstraction          : 0.02
% 3.69/1.59  MUC search           : 0.00
% 3.69/1.59  Cooper               : 0.00
% 3.69/1.59  Total                : 0.84
% 3.69/1.59  Index Insertion      : 0.00
% 3.69/1.59  Index Deletion       : 0.00
% 3.69/1.59  Index Matching       : 0.00
% 3.69/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
