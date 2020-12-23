%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1818+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:28 EST 2020

% Result     : Theorem 5.23s
% Output     : CNFRefutation 5.23s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 530 expanded)
%              Number of leaves         :   26 ( 226 expanded)
%              Depth                    :   12
%              Number of atoms          :  902 (6590 expanded)
%              Number of equality atoms :   24 ( 224 expanded)
%              Maximal formula depth    :   30 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > r4_tsep_1 > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_170,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & v1_tsep_1(D,A)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( ~ v2_struct_0(E)
                          & v1_tsep_1(E,A)
                          & m1_pre_topc(E,A) )
                       => ( A = k1_tsep_1(A,D,E)
                         => ( ( v1_funct_1(C)
                              & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                              & v5_pre_topc(C,A,B)
                              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                          <=> ( v1_funct_1(k2_tmap_1(A,B,C,D))
                              & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
                              & v5_pre_topc(k2_tmap_1(A,B,C,D),D,B)
                              & m1_subset_1(k2_tmap_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B))))
                              & v1_funct_1(k2_tmap_1(A,B,C,E))
                              & v1_funct_2(k2_tmap_1(A,B,C,E),u1_struct_0(E),u1_struct_0(B))
                              & v5_pre_topc(k2_tmap_1(A,B,C,E),E,B)
                              & m1_subset_1(k2_tmap_1(A,B,C,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_tmap_1)).

tff(f_105,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tsep_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ! [E] :
                      ( ( ~ v2_struct_0(E)
                        & m1_pre_topc(E,A) )
                     => ( ( A = k1_tsep_1(A,D,E)
                          & r4_tsep_1(A,D,E) )
                       => ( ( v1_funct_1(C)
                            & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                            & v5_pre_topc(C,A,B)
                            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                        <=> ( v1_funct_1(k2_tmap_1(A,B,C,D))
                            & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
                            & v5_pre_topc(k2_tmap_1(A,B,C,D),D,B)
                            & m1_subset_1(k2_tmap_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B))))
                            & v1_funct_1(k2_tmap_1(A,B,C,E))
                            & v1_funct_2(k2_tmap_1(A,B,C,E),u1_struct_0(E),u1_struct_0(B))
                            & v5_pre_topc(k2_tmap_1(A,B,C,E),E,B)
                            & m1_subset_1(k2_tmap_1(A,B,C,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_tmap_1)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_46,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_44,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_56,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_54,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_38,plain,(
    v1_tsep_1('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_36,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_32,plain,(
    v1_tsep_1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_30,plain,(
    m1_pre_topc('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_26,plain,(
    ! [A_32,B_36,C_38] :
      ( r4_tsep_1(A_32,B_36,C_38)
      | ~ m1_pre_topc(C_38,A_32)
      | ~ v1_tsep_1(C_38,A_32)
      | ~ m1_pre_topc(B_36,A_32)
      | ~ v1_tsep_1(B_36,A_32)
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_28,plain,(
    k1_tsep_1('#skF_1','#skF_4','#skF_5') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_144,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_183,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_134,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_187,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_124,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_186,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_114,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_189,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_104,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_184,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_94,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_188,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_84,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_185,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_74,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_190,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_60,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_158,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_60])).

tff(c_168,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_158])).

tff(c_178,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_168])).

tff(c_224,plain,(
    ~ v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_187,c_186,c_189,c_184,c_188,c_185,c_190,c_178])).

tff(c_319,plain,(
    ! [D_155,E_159,A_158,C_156,B_157] :
      ( v5_pre_topc(C_156,A_158,B_157)
      | ~ m1_subset_1(k2_tmap_1(A_158,B_157,C_156,E_159),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E_159),u1_struct_0(B_157))))
      | ~ v5_pre_topc(k2_tmap_1(A_158,B_157,C_156,E_159),E_159,B_157)
      | ~ v1_funct_2(k2_tmap_1(A_158,B_157,C_156,E_159),u1_struct_0(E_159),u1_struct_0(B_157))
      | ~ v1_funct_1(k2_tmap_1(A_158,B_157,C_156,E_159))
      | ~ m1_subset_1(k2_tmap_1(A_158,B_157,C_156,D_155),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_155),u1_struct_0(B_157))))
      | ~ v5_pre_topc(k2_tmap_1(A_158,B_157,C_156,D_155),D_155,B_157)
      | ~ v1_funct_2(k2_tmap_1(A_158,B_157,C_156,D_155),u1_struct_0(D_155),u1_struct_0(B_157))
      | ~ v1_funct_1(k2_tmap_1(A_158,B_157,C_156,D_155))
      | ~ r4_tsep_1(A_158,D_155,E_159)
      | k1_tsep_1(A_158,D_155,E_159) != A_158
      | ~ m1_pre_topc(E_159,A_158)
      | v2_struct_0(E_159)
      | ~ m1_pre_topc(D_155,A_158)
      | v2_struct_0(D_155)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_158),u1_struct_0(B_157))))
      | ~ v1_funct_2(C_156,u1_struct_0(A_158),u1_struct_0(B_157))
      | ~ v1_funct_1(C_156)
      | ~ l1_pre_topc(B_157)
      | ~ v2_pre_topc(B_157)
      | v2_struct_0(B_157)
      | ~ l1_pre_topc(A_158)
      | ~ v2_pre_topc(A_158)
      | v2_struct_0(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_321,plain,(
    ! [D_155] :
      ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_155),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_155),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_155),D_155,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_155),u1_struct_0(D_155),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_155))
      | ~ r4_tsep_1('#skF_1',D_155,'#skF_5')
      | k1_tsep_1('#skF_1',D_155,'#skF_5') != '#skF_1'
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(D_155,'#skF_1')
      | v2_struct_0(D_155)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_190,c_319])).

tff(c_326,plain,(
    ! [D_155] :
      ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_155),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_155),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_155),D_155,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_155),u1_struct_0(D_155),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_155))
      | ~ r4_tsep_1('#skF_1',D_155,'#skF_5')
      | k1_tsep_1('#skF_1',D_155,'#skF_5') != '#skF_1'
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(D_155,'#skF_1')
      | v2_struct_0(D_155)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_48,c_46,c_44,c_42,c_30,c_184,c_188,c_185,c_321])).

tff(c_364,plain,(
    ! [D_163] :
      ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_163),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_163),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_163),D_163,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_163),u1_struct_0(D_163),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_163))
      | ~ r4_tsep_1('#skF_1',D_163,'#skF_5')
      | k1_tsep_1('#skF_1',D_163,'#skF_5') != '#skF_1'
      | ~ m1_pre_topc(D_163,'#skF_1')
      | v2_struct_0(D_163) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_52,c_34,c_224,c_326])).

tff(c_374,plain,
    ( ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | k1_tsep_1('#skF_1','#skF_4','#skF_5') != '#skF_1'
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_189,c_364])).

tff(c_385,plain,
    ( ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28,c_183,c_187,c_186,c_374])).

tff(c_386,plain,(
    ~ r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_385])).

tff(c_389,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ v1_tsep_1('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_tsep_1('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_386])).

tff(c_392,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_38,c_36,c_32,c_30,c_389])).

tff(c_394,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_392])).

tff(c_395,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_454,plain,(
    ! [A_214,D_211,C_212,B_213,E_215] :
      ( m1_subset_1(k2_tmap_1(A_214,B_213,C_212,E_215),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E_215),u1_struct_0(B_213))))
      | ~ v5_pre_topc(C_212,A_214,B_213)
      | ~ r4_tsep_1(A_214,D_211,E_215)
      | k1_tsep_1(A_214,D_211,E_215) != A_214
      | ~ m1_pre_topc(E_215,A_214)
      | v2_struct_0(E_215)
      | ~ m1_pre_topc(D_211,A_214)
      | v2_struct_0(D_211)
      | ~ m1_subset_1(C_212,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_214),u1_struct_0(B_213))))
      | ~ v1_funct_2(C_212,u1_struct_0(A_214),u1_struct_0(B_213))
      | ~ v1_funct_1(C_212)
      | ~ l1_pre_topc(B_213)
      | ~ v2_pre_topc(B_213)
      | v2_struct_0(B_213)
      | ~ l1_pre_topc(A_214)
      | ~ v2_pre_topc(A_214)
      | v2_struct_0(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_539,plain,(
    ! [C_264,B_265,C_261,A_262,B_263] :
      ( m1_subset_1(k2_tmap_1(A_262,B_263,C_261,C_264),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_264),u1_struct_0(B_263))))
      | ~ v5_pre_topc(C_261,A_262,B_263)
      | k1_tsep_1(A_262,B_265,C_264) != A_262
      | v2_struct_0(C_264)
      | v2_struct_0(B_265)
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_262),u1_struct_0(B_263))))
      | ~ v1_funct_2(C_261,u1_struct_0(A_262),u1_struct_0(B_263))
      | ~ v1_funct_1(C_261)
      | ~ l1_pre_topc(B_263)
      | ~ v2_pre_topc(B_263)
      | v2_struct_0(B_263)
      | ~ m1_pre_topc(C_264,A_262)
      | ~ v1_tsep_1(C_264,A_262)
      | ~ m1_pre_topc(B_265,A_262)
      | ~ v1_tsep_1(B_265,A_262)
      | ~ l1_pre_topc(A_262)
      | ~ v2_pre_topc(A_262)
      | v2_struct_0(A_262) ) ),
    inference(resolution,[status(thm)],[c_26,c_454])).

tff(c_541,plain,(
    ! [B_263,C_261] :
      ( m1_subset_1(k2_tmap_1('#skF_1',B_263,C_261,'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_263))))
      | ~ v5_pre_topc(C_261,'#skF_1',B_263)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_263))))
      | ~ v1_funct_2(C_261,u1_struct_0('#skF_1'),u1_struct_0(B_263))
      | ~ v1_funct_1(C_261)
      | ~ l1_pre_topc(B_263)
      | ~ v2_pre_topc(B_263)
      | v2_struct_0(B_263)
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | ~ v1_tsep_1('#skF_5','#skF_1')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ v1_tsep_1('#skF_4','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_539])).

tff(c_544,plain,(
    ! [B_263,C_261] :
      ( m1_subset_1(k2_tmap_1('#skF_1',B_263,C_261,'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_263))))
      | ~ v5_pre_topc(C_261,'#skF_1',B_263)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_263))))
      | ~ v1_funct_2(C_261,u1_struct_0('#skF_1'),u1_struct_0(B_263))
      | ~ v1_funct_1(C_261)
      | ~ l1_pre_topc(B_263)
      | ~ v2_pre_topc(B_263)
      | v2_struct_0(B_263)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_38,c_36,c_32,c_30,c_541])).

tff(c_546,plain,(
    ! [B_266,C_267] :
      ( m1_subset_1(k2_tmap_1('#skF_1',B_266,C_267,'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_266))))
      | ~ v5_pre_topc(C_267,'#skF_1',B_266)
      | ~ m1_subset_1(C_267,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_266))))
      | ~ v1_funct_2(C_267,u1_struct_0('#skF_1'),u1_struct_0(B_266))
      | ~ v1_funct_1(C_267)
      | ~ l1_pre_topc(B_266)
      | ~ v2_pre_topc(B_266)
      | v2_struct_0(B_266) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_40,c_34,c_544])).

tff(c_396,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_551,plain,
    ( ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_546,c_396])).

tff(c_558,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_395,c_551])).

tff(c_560,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_558])).

tff(c_561,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_621,plain,(
    ! [E_319,A_318,B_317,C_316,D_315] :
      ( m1_subset_1(k2_tmap_1(A_318,B_317,C_316,D_315),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_315),u1_struct_0(B_317))))
      | ~ v5_pre_topc(C_316,A_318,B_317)
      | ~ r4_tsep_1(A_318,D_315,E_319)
      | k1_tsep_1(A_318,D_315,E_319) != A_318
      | ~ m1_pre_topc(E_319,A_318)
      | v2_struct_0(E_319)
      | ~ m1_pre_topc(D_315,A_318)
      | v2_struct_0(D_315)
      | ~ m1_subset_1(C_316,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_318),u1_struct_0(B_317))))
      | ~ v1_funct_2(C_316,u1_struct_0(A_318),u1_struct_0(B_317))
      | ~ v1_funct_1(C_316)
      | ~ l1_pre_topc(B_317)
      | ~ v2_pre_topc(B_317)
      | v2_struct_0(B_317)
      | ~ l1_pre_topc(A_318)
      | ~ v2_pre_topc(A_318)
      | v2_struct_0(A_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_700,plain,(
    ! [C_367,C_368,B_369,B_366,A_365] :
      ( m1_subset_1(k2_tmap_1(A_365,B_366,C_367,B_369),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_369),u1_struct_0(B_366))))
      | ~ v5_pre_topc(C_367,A_365,B_366)
      | k1_tsep_1(A_365,B_369,C_368) != A_365
      | v2_struct_0(C_368)
      | v2_struct_0(B_369)
      | ~ m1_subset_1(C_367,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_365),u1_struct_0(B_366))))
      | ~ v1_funct_2(C_367,u1_struct_0(A_365),u1_struct_0(B_366))
      | ~ v1_funct_1(C_367)
      | ~ l1_pre_topc(B_366)
      | ~ v2_pre_topc(B_366)
      | v2_struct_0(B_366)
      | ~ m1_pre_topc(C_368,A_365)
      | ~ v1_tsep_1(C_368,A_365)
      | ~ m1_pre_topc(B_369,A_365)
      | ~ v1_tsep_1(B_369,A_365)
      | ~ l1_pre_topc(A_365)
      | ~ v2_pre_topc(A_365)
      | v2_struct_0(A_365) ) ),
    inference(resolution,[status(thm)],[c_26,c_621])).

tff(c_702,plain,(
    ! [B_366,C_367] :
      ( m1_subset_1(k2_tmap_1('#skF_1',B_366,C_367,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_366))))
      | ~ v5_pre_topc(C_367,'#skF_1',B_366)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_367,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_366))))
      | ~ v1_funct_2(C_367,u1_struct_0('#skF_1'),u1_struct_0(B_366))
      | ~ v1_funct_1(C_367)
      | ~ l1_pre_topc(B_366)
      | ~ v2_pre_topc(B_366)
      | v2_struct_0(B_366)
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | ~ v1_tsep_1('#skF_5','#skF_1')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ v1_tsep_1('#skF_4','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_700])).

tff(c_705,plain,(
    ! [B_366,C_367] :
      ( m1_subset_1(k2_tmap_1('#skF_1',B_366,C_367,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_366))))
      | ~ v5_pre_topc(C_367,'#skF_1',B_366)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_367,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_366))))
      | ~ v1_funct_2(C_367,u1_struct_0('#skF_1'),u1_struct_0(B_366))
      | ~ v1_funct_1(C_367)
      | ~ l1_pre_topc(B_366)
      | ~ v2_pre_topc(B_366)
      | v2_struct_0(B_366)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_38,c_36,c_32,c_30,c_702])).

tff(c_707,plain,(
    ! [B_370,C_371] :
      ( m1_subset_1(k2_tmap_1('#skF_1',B_370,C_371,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_370))))
      | ~ v5_pre_topc(C_371,'#skF_1',B_370)
      | ~ m1_subset_1(C_371,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_370))))
      | ~ v1_funct_2(C_371,u1_struct_0('#skF_1'),u1_struct_0(B_370))
      | ~ v1_funct_1(C_371)
      | ~ l1_pre_topc(B_370)
      | ~ v2_pre_topc(B_370)
      | v2_struct_0(B_370) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_40,c_34,c_705])).

tff(c_562,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_712,plain,
    ( ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_707,c_562])).

tff(c_719,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_561,c_712])).

tff(c_721,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_719])).

tff(c_723,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_722,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_752,plain,(
    ! [C_401,B_402,A_403,E_404,D_400] :
      ( v1_funct_2(k2_tmap_1(A_403,B_402,C_401,E_404),u1_struct_0(E_404),u1_struct_0(B_402))
      | ~ v5_pre_topc(C_401,A_403,B_402)
      | ~ r4_tsep_1(A_403,D_400,E_404)
      | k1_tsep_1(A_403,D_400,E_404) != A_403
      | ~ m1_pre_topc(E_404,A_403)
      | v2_struct_0(E_404)
      | ~ m1_pre_topc(D_400,A_403)
      | v2_struct_0(D_400)
      | ~ m1_subset_1(C_401,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_403),u1_struct_0(B_402))))
      | ~ v1_funct_2(C_401,u1_struct_0(A_403),u1_struct_0(B_402))
      | ~ v1_funct_1(C_401)
      | ~ l1_pre_topc(B_402)
      | ~ v2_pre_topc(B_402)
      | v2_struct_0(B_402)
      | ~ l1_pre_topc(A_403)
      | ~ v2_pre_topc(A_403)
      | v2_struct_0(A_403) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_819,plain,(
    ! [C_443,C_446,B_445,A_444,B_447] :
      ( v1_funct_2(k2_tmap_1(A_444,B_445,C_443,C_446),u1_struct_0(C_446),u1_struct_0(B_445))
      | ~ v5_pre_topc(C_443,A_444,B_445)
      | k1_tsep_1(A_444,B_447,C_446) != A_444
      | v2_struct_0(C_446)
      | v2_struct_0(B_447)
      | ~ m1_subset_1(C_443,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_444),u1_struct_0(B_445))))
      | ~ v1_funct_2(C_443,u1_struct_0(A_444),u1_struct_0(B_445))
      | ~ v1_funct_1(C_443)
      | ~ l1_pre_topc(B_445)
      | ~ v2_pre_topc(B_445)
      | v2_struct_0(B_445)
      | ~ m1_pre_topc(C_446,A_444)
      | ~ v1_tsep_1(C_446,A_444)
      | ~ m1_pre_topc(B_447,A_444)
      | ~ v1_tsep_1(B_447,A_444)
      | ~ l1_pre_topc(A_444)
      | ~ v2_pre_topc(A_444)
      | v2_struct_0(A_444) ) ),
    inference(resolution,[status(thm)],[c_26,c_752])).

tff(c_821,plain,(
    ! [B_445,C_443] :
      ( v1_funct_2(k2_tmap_1('#skF_1',B_445,C_443,'#skF_5'),u1_struct_0('#skF_5'),u1_struct_0(B_445))
      | ~ v5_pre_topc(C_443,'#skF_1',B_445)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_443,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_445))))
      | ~ v1_funct_2(C_443,u1_struct_0('#skF_1'),u1_struct_0(B_445))
      | ~ v1_funct_1(C_443)
      | ~ l1_pre_topc(B_445)
      | ~ v2_pre_topc(B_445)
      | v2_struct_0(B_445)
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | ~ v1_tsep_1('#skF_5','#skF_1')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ v1_tsep_1('#skF_4','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_819])).

tff(c_824,plain,(
    ! [B_445,C_443] :
      ( v1_funct_2(k2_tmap_1('#skF_1',B_445,C_443,'#skF_5'),u1_struct_0('#skF_5'),u1_struct_0(B_445))
      | ~ v5_pre_topc(C_443,'#skF_1',B_445)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_443,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_445))))
      | ~ v1_funct_2(C_443,u1_struct_0('#skF_1'),u1_struct_0(B_445))
      | ~ v1_funct_1(C_443)
      | ~ l1_pre_topc(B_445)
      | ~ v2_pre_topc(B_445)
      | v2_struct_0(B_445)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_38,c_36,c_32,c_30,c_821])).

tff(c_826,plain,(
    ! [B_448,C_449] :
      ( v1_funct_2(k2_tmap_1('#skF_1',B_448,C_449,'#skF_5'),u1_struct_0('#skF_5'),u1_struct_0(B_448))
      | ~ v5_pre_topc(C_449,'#skF_1',B_448)
      | ~ m1_subset_1(C_449,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_448))))
      | ~ v1_funct_2(C_449,u1_struct_0('#skF_1'),u1_struct_0(B_448))
      | ~ v1_funct_1(C_449)
      | ~ l1_pre_topc(B_448)
      | ~ v2_pre_topc(B_448)
      | v2_struct_0(B_448) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_40,c_34,c_824])).

tff(c_828,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_826])).

tff(c_831,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_722,c_828])).

tff(c_833,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_723,c_831])).

tff(c_835,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_834,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_886,plain,(
    ! [C_488,B_489,D_487,E_491,A_490] :
      ( v1_funct_2(k2_tmap_1(A_490,B_489,C_488,D_487),u1_struct_0(D_487),u1_struct_0(B_489))
      | ~ v5_pre_topc(C_488,A_490,B_489)
      | ~ r4_tsep_1(A_490,D_487,E_491)
      | k1_tsep_1(A_490,D_487,E_491) != A_490
      | ~ m1_pre_topc(E_491,A_490)
      | v2_struct_0(E_491)
      | ~ m1_pre_topc(D_487,A_490)
      | v2_struct_0(D_487)
      | ~ m1_subset_1(C_488,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_490),u1_struct_0(B_489))))
      | ~ v1_funct_2(C_488,u1_struct_0(A_490),u1_struct_0(B_489))
      | ~ v1_funct_1(C_488)
      | ~ l1_pre_topc(B_489)
      | ~ v2_pre_topc(B_489)
      | v2_struct_0(B_489)
      | ~ l1_pre_topc(A_490)
      | ~ v2_pre_topc(A_490)
      | v2_struct_0(A_490) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_946,plain,(
    ! [B_532,C_531,A_530,B_529,C_528] :
      ( v1_funct_2(k2_tmap_1(A_530,B_529,C_528,B_532),u1_struct_0(B_532),u1_struct_0(B_529))
      | ~ v5_pre_topc(C_528,A_530,B_529)
      | k1_tsep_1(A_530,B_532,C_531) != A_530
      | v2_struct_0(C_531)
      | v2_struct_0(B_532)
      | ~ m1_subset_1(C_528,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_530),u1_struct_0(B_529))))
      | ~ v1_funct_2(C_528,u1_struct_0(A_530),u1_struct_0(B_529))
      | ~ v1_funct_1(C_528)
      | ~ l1_pre_topc(B_529)
      | ~ v2_pre_topc(B_529)
      | v2_struct_0(B_529)
      | ~ m1_pre_topc(C_531,A_530)
      | ~ v1_tsep_1(C_531,A_530)
      | ~ m1_pre_topc(B_532,A_530)
      | ~ v1_tsep_1(B_532,A_530)
      | ~ l1_pre_topc(A_530)
      | ~ v2_pre_topc(A_530)
      | v2_struct_0(A_530) ) ),
    inference(resolution,[status(thm)],[c_26,c_886])).

tff(c_948,plain,(
    ! [B_529,C_528] :
      ( v1_funct_2(k2_tmap_1('#skF_1',B_529,C_528,'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(B_529))
      | ~ v5_pre_topc(C_528,'#skF_1',B_529)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_528,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_529))))
      | ~ v1_funct_2(C_528,u1_struct_0('#skF_1'),u1_struct_0(B_529))
      | ~ v1_funct_1(C_528)
      | ~ l1_pre_topc(B_529)
      | ~ v2_pre_topc(B_529)
      | v2_struct_0(B_529)
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | ~ v1_tsep_1('#skF_5','#skF_1')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ v1_tsep_1('#skF_4','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_946])).

tff(c_951,plain,(
    ! [B_529,C_528] :
      ( v1_funct_2(k2_tmap_1('#skF_1',B_529,C_528,'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(B_529))
      | ~ v5_pre_topc(C_528,'#skF_1',B_529)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_528,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_529))))
      | ~ v1_funct_2(C_528,u1_struct_0('#skF_1'),u1_struct_0(B_529))
      | ~ v1_funct_1(C_528)
      | ~ l1_pre_topc(B_529)
      | ~ v2_pre_topc(B_529)
      | v2_struct_0(B_529)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_38,c_36,c_32,c_30,c_948])).

tff(c_954,plain,(
    ! [B_538,C_539] :
      ( v1_funct_2(k2_tmap_1('#skF_1',B_538,C_539,'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(B_538))
      | ~ v5_pre_topc(C_539,'#skF_1',B_538)
      | ~ m1_subset_1(C_539,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_538))))
      | ~ v1_funct_2(C_539,u1_struct_0('#skF_1'),u1_struct_0(B_538))
      | ~ v1_funct_1(C_539)
      | ~ l1_pre_topc(B_538)
      | ~ v2_pre_topc(B_538)
      | v2_struct_0(B_538) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_40,c_34,c_951])).

tff(c_956,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_954])).

tff(c_959,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_834,c_956])).

tff(c_961,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_835,c_959])).

tff(c_963,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_962,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_977,plain,(
    ! [C_554,A_556,B_555,E_557,D_553] :
      ( v5_pre_topc(k2_tmap_1(A_556,B_555,C_554,D_553),D_553,B_555)
      | ~ v5_pre_topc(C_554,A_556,B_555)
      | ~ r4_tsep_1(A_556,D_553,E_557)
      | k1_tsep_1(A_556,D_553,E_557) != A_556
      | ~ m1_pre_topc(E_557,A_556)
      | v2_struct_0(E_557)
      | ~ m1_pre_topc(D_553,A_556)
      | v2_struct_0(D_553)
      | ~ m1_subset_1(C_554,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_556),u1_struct_0(B_555))))
      | ~ v1_funct_2(C_554,u1_struct_0(A_556),u1_struct_0(B_555))
      | ~ v1_funct_1(C_554)
      | ~ l1_pre_topc(B_555)
      | ~ v2_pre_topc(B_555)
      | v2_struct_0(B_555)
      | ~ l1_pre_topc(A_556)
      | ~ v2_pre_topc(A_556)
      | v2_struct_0(A_556) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1041,plain,(
    ! [C_600,C_602,A_601,B_599,B_603] :
      ( v5_pre_topc(k2_tmap_1(A_601,B_599,C_600,B_603),B_603,B_599)
      | ~ v5_pre_topc(C_600,A_601,B_599)
      | k1_tsep_1(A_601,B_603,C_602) != A_601
      | v2_struct_0(C_602)
      | v2_struct_0(B_603)
      | ~ m1_subset_1(C_600,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_601),u1_struct_0(B_599))))
      | ~ v1_funct_2(C_600,u1_struct_0(A_601),u1_struct_0(B_599))
      | ~ v1_funct_1(C_600)
      | ~ l1_pre_topc(B_599)
      | ~ v2_pre_topc(B_599)
      | v2_struct_0(B_599)
      | ~ m1_pre_topc(C_602,A_601)
      | ~ v1_tsep_1(C_602,A_601)
      | ~ m1_pre_topc(B_603,A_601)
      | ~ v1_tsep_1(B_603,A_601)
      | ~ l1_pre_topc(A_601)
      | ~ v2_pre_topc(A_601)
      | v2_struct_0(A_601) ) ),
    inference(resolution,[status(thm)],[c_26,c_977])).

tff(c_1043,plain,(
    ! [B_599,C_600] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_599,C_600,'#skF_4'),'#skF_4',B_599)
      | ~ v5_pre_topc(C_600,'#skF_1',B_599)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_600,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_599))))
      | ~ v1_funct_2(C_600,u1_struct_0('#skF_1'),u1_struct_0(B_599))
      | ~ v1_funct_1(C_600)
      | ~ l1_pre_topc(B_599)
      | ~ v2_pre_topc(B_599)
      | v2_struct_0(B_599)
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | ~ v1_tsep_1('#skF_5','#skF_1')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ v1_tsep_1('#skF_4','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1041])).

tff(c_1046,plain,(
    ! [B_599,C_600] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_599,C_600,'#skF_4'),'#skF_4',B_599)
      | ~ v5_pre_topc(C_600,'#skF_1',B_599)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_600,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_599))))
      | ~ v1_funct_2(C_600,u1_struct_0('#skF_1'),u1_struct_0(B_599))
      | ~ v1_funct_1(C_600)
      | ~ l1_pre_topc(B_599)
      | ~ v2_pre_topc(B_599)
      | v2_struct_0(B_599)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_38,c_36,c_32,c_30,c_1043])).

tff(c_1048,plain,(
    ! [B_604,C_605] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_604,C_605,'#skF_4'),'#skF_4',B_604)
      | ~ v5_pre_topc(C_605,'#skF_1',B_604)
      | ~ m1_subset_1(C_605,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_604))))
      | ~ v1_funct_2(C_605,u1_struct_0('#skF_1'),u1_struct_0(B_604))
      | ~ v1_funct_1(C_605)
      | ~ l1_pre_topc(B_604)
      | ~ v2_pre_topc(B_604)
      | v2_struct_0(B_604) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_40,c_34,c_1046])).

tff(c_1050,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_1048])).

tff(c_1053,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_962,c_1050])).

tff(c_1055,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_963,c_1053])).

tff(c_1057,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_1056,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_1074,plain,(
    ! [A_622,D_619,C_620,B_621,E_623] :
      ( v5_pre_topc(k2_tmap_1(A_622,B_621,C_620,E_623),E_623,B_621)
      | ~ v5_pre_topc(C_620,A_622,B_621)
      | ~ r4_tsep_1(A_622,D_619,E_623)
      | k1_tsep_1(A_622,D_619,E_623) != A_622
      | ~ m1_pre_topc(E_623,A_622)
      | v2_struct_0(E_623)
      | ~ m1_pre_topc(D_619,A_622)
      | v2_struct_0(D_619)
      | ~ m1_subset_1(C_620,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_622),u1_struct_0(B_621))))
      | ~ v1_funct_2(C_620,u1_struct_0(A_622),u1_struct_0(B_621))
      | ~ v1_funct_1(C_620)
      | ~ l1_pre_topc(B_621)
      | ~ v2_pre_topc(B_621)
      | v2_struct_0(B_621)
      | ~ l1_pre_topc(A_622)
      | ~ v2_pre_topc(A_622)
      | v2_struct_0(A_622) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1134,plain,(
    ! [C_663,B_660,B_664,C_661,A_662] :
      ( v5_pre_topc(k2_tmap_1(A_662,B_660,C_661,C_663),C_663,B_660)
      | ~ v5_pre_topc(C_661,A_662,B_660)
      | k1_tsep_1(A_662,B_664,C_663) != A_662
      | v2_struct_0(C_663)
      | v2_struct_0(B_664)
      | ~ m1_subset_1(C_661,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_662),u1_struct_0(B_660))))
      | ~ v1_funct_2(C_661,u1_struct_0(A_662),u1_struct_0(B_660))
      | ~ v1_funct_1(C_661)
      | ~ l1_pre_topc(B_660)
      | ~ v2_pre_topc(B_660)
      | v2_struct_0(B_660)
      | ~ m1_pre_topc(C_663,A_662)
      | ~ v1_tsep_1(C_663,A_662)
      | ~ m1_pre_topc(B_664,A_662)
      | ~ v1_tsep_1(B_664,A_662)
      | ~ l1_pre_topc(A_662)
      | ~ v2_pre_topc(A_662)
      | v2_struct_0(A_662) ) ),
    inference(resolution,[status(thm)],[c_26,c_1074])).

tff(c_1136,plain,(
    ! [B_660,C_661] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_660,C_661,'#skF_5'),'#skF_5',B_660)
      | ~ v5_pre_topc(C_661,'#skF_1',B_660)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_661,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_660))))
      | ~ v1_funct_2(C_661,u1_struct_0('#skF_1'),u1_struct_0(B_660))
      | ~ v1_funct_1(C_661)
      | ~ l1_pre_topc(B_660)
      | ~ v2_pre_topc(B_660)
      | v2_struct_0(B_660)
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | ~ v1_tsep_1('#skF_5','#skF_1')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ v1_tsep_1('#skF_4','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1134])).

tff(c_1139,plain,(
    ! [B_660,C_661] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_660,C_661,'#skF_5'),'#skF_5',B_660)
      | ~ v5_pre_topc(C_661,'#skF_1',B_660)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_661,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_660))))
      | ~ v1_funct_2(C_661,u1_struct_0('#skF_1'),u1_struct_0(B_660))
      | ~ v1_funct_1(C_661)
      | ~ l1_pre_topc(B_660)
      | ~ v2_pre_topc(B_660)
      | v2_struct_0(B_660)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_38,c_36,c_32,c_30,c_1136])).

tff(c_1141,plain,(
    ! [B_665,C_666] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_665,C_666,'#skF_5'),'#skF_5',B_665)
      | ~ v5_pre_topc(C_666,'#skF_1',B_665)
      | ~ m1_subset_1(C_666,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_665))))
      | ~ v1_funct_2(C_666,u1_struct_0('#skF_1'),u1_struct_0(B_665))
      | ~ v1_funct_1(C_666)
      | ~ l1_pre_topc(B_665)
      | ~ v2_pre_topc(B_665)
      | v2_struct_0(B_665) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_40,c_34,c_1139])).

tff(c_1143,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_1141])).

tff(c_1146,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_1056,c_1143])).

tff(c_1148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1057,c_1146])).

tff(c_1150,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_1149,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_1158,plain,(
    ! [D_670,E_674,C_671,B_672,A_673] :
      ( v1_funct_1(k2_tmap_1(A_673,B_672,C_671,E_674))
      | ~ v5_pre_topc(C_671,A_673,B_672)
      | ~ r4_tsep_1(A_673,D_670,E_674)
      | k1_tsep_1(A_673,D_670,E_674) != A_673
      | ~ m1_pre_topc(E_674,A_673)
      | v2_struct_0(E_674)
      | ~ m1_pre_topc(D_670,A_673)
      | v2_struct_0(D_670)
      | ~ m1_subset_1(C_671,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_673),u1_struct_0(B_672))))
      | ~ v1_funct_2(C_671,u1_struct_0(A_673),u1_struct_0(B_672))
      | ~ v1_funct_1(C_671)
      | ~ l1_pre_topc(B_672)
      | ~ v2_pre_topc(B_672)
      | v2_struct_0(B_672)
      | ~ l1_pre_topc(A_673)
      | ~ v2_pre_topc(A_673)
      | v2_struct_0(A_673) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1174,plain,(
    ! [B_693,A_690,C_692,C_691,B_694] :
      ( v1_funct_1(k2_tmap_1(A_690,B_694,C_691,C_692))
      | ~ v5_pre_topc(C_691,A_690,B_694)
      | k1_tsep_1(A_690,B_693,C_692) != A_690
      | v2_struct_0(C_692)
      | v2_struct_0(B_693)
      | ~ m1_subset_1(C_691,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_690),u1_struct_0(B_694))))
      | ~ v1_funct_2(C_691,u1_struct_0(A_690),u1_struct_0(B_694))
      | ~ v1_funct_1(C_691)
      | ~ l1_pre_topc(B_694)
      | ~ v2_pre_topc(B_694)
      | v2_struct_0(B_694)
      | ~ m1_pre_topc(C_692,A_690)
      | ~ v1_tsep_1(C_692,A_690)
      | ~ m1_pre_topc(B_693,A_690)
      | ~ v1_tsep_1(B_693,A_690)
      | ~ l1_pre_topc(A_690)
      | ~ v2_pre_topc(A_690)
      | v2_struct_0(A_690) ) ),
    inference(resolution,[status(thm)],[c_26,c_1158])).

tff(c_1176,plain,(
    ! [B_694,C_691] :
      ( v1_funct_1(k2_tmap_1('#skF_1',B_694,C_691,'#skF_5'))
      | ~ v5_pre_topc(C_691,'#skF_1',B_694)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_691,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_694))))
      | ~ v1_funct_2(C_691,u1_struct_0('#skF_1'),u1_struct_0(B_694))
      | ~ v1_funct_1(C_691)
      | ~ l1_pre_topc(B_694)
      | ~ v2_pre_topc(B_694)
      | v2_struct_0(B_694)
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | ~ v1_tsep_1('#skF_5','#skF_1')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ v1_tsep_1('#skF_4','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1174])).

tff(c_1179,plain,(
    ! [B_694,C_691] :
      ( v1_funct_1(k2_tmap_1('#skF_1',B_694,C_691,'#skF_5'))
      | ~ v5_pre_topc(C_691,'#skF_1',B_694)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_691,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_694))))
      | ~ v1_funct_2(C_691,u1_struct_0('#skF_1'),u1_struct_0(B_694))
      | ~ v1_funct_1(C_691)
      | ~ l1_pre_topc(B_694)
      | ~ v2_pre_topc(B_694)
      | v2_struct_0(B_694)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_38,c_36,c_32,c_30,c_1176])).

tff(c_1181,plain,(
    ! [B_695,C_696] :
      ( v1_funct_1(k2_tmap_1('#skF_1',B_695,C_696,'#skF_5'))
      | ~ v5_pre_topc(C_696,'#skF_1',B_695)
      | ~ m1_subset_1(C_696,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_695))))
      | ~ v1_funct_2(C_696,u1_struct_0('#skF_1'),u1_struct_0(B_695))
      | ~ v1_funct_1(C_696)
      | ~ l1_pre_topc(B_695)
      | ~ v2_pre_topc(B_695)
      | v2_struct_0(B_695) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_40,c_34,c_1179])).

tff(c_1184,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_1181])).

tff(c_1187,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_1149,c_1184])).

tff(c_1189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1150,c_1187])).

tff(c_1191,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_1190,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_1202,plain,(
    ! [D_700,C_701,E_704,B_702,A_703] :
      ( v1_funct_1(k2_tmap_1(A_703,B_702,C_701,D_700))
      | ~ v5_pre_topc(C_701,A_703,B_702)
      | ~ r4_tsep_1(A_703,D_700,E_704)
      | k1_tsep_1(A_703,D_700,E_704) != A_703
      | ~ m1_pre_topc(E_704,A_703)
      | v2_struct_0(E_704)
      | ~ m1_pre_topc(D_700,A_703)
      | v2_struct_0(D_700)
      | ~ m1_subset_1(C_701,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_703),u1_struct_0(B_702))))
      | ~ v1_funct_2(C_701,u1_struct_0(A_703),u1_struct_0(B_702))
      | ~ v1_funct_1(C_701)
      | ~ l1_pre_topc(B_702)
      | ~ v2_pre_topc(B_702)
      | v2_struct_0(B_702)
      | ~ l1_pre_topc(A_703)
      | ~ v2_pre_topc(A_703)
      | v2_struct_0(A_703) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1222,plain,(
    ! [C_727,B_728,C_726,A_725,B_729] :
      ( v1_funct_1(k2_tmap_1(A_725,B_728,C_726,B_729))
      | ~ v5_pre_topc(C_726,A_725,B_728)
      | k1_tsep_1(A_725,B_729,C_727) != A_725
      | v2_struct_0(C_727)
      | v2_struct_0(B_729)
      | ~ m1_subset_1(C_726,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_725),u1_struct_0(B_728))))
      | ~ v1_funct_2(C_726,u1_struct_0(A_725),u1_struct_0(B_728))
      | ~ v1_funct_1(C_726)
      | ~ l1_pre_topc(B_728)
      | ~ v2_pre_topc(B_728)
      | v2_struct_0(B_728)
      | ~ m1_pre_topc(C_727,A_725)
      | ~ v1_tsep_1(C_727,A_725)
      | ~ m1_pre_topc(B_729,A_725)
      | ~ v1_tsep_1(B_729,A_725)
      | ~ l1_pre_topc(A_725)
      | ~ v2_pre_topc(A_725)
      | v2_struct_0(A_725) ) ),
    inference(resolution,[status(thm)],[c_26,c_1202])).

tff(c_1224,plain,(
    ! [B_728,C_726] :
      ( v1_funct_1(k2_tmap_1('#skF_1',B_728,C_726,'#skF_4'))
      | ~ v5_pre_topc(C_726,'#skF_1',B_728)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_726,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_728))))
      | ~ v1_funct_2(C_726,u1_struct_0('#skF_1'),u1_struct_0(B_728))
      | ~ v1_funct_1(C_726)
      | ~ l1_pre_topc(B_728)
      | ~ v2_pre_topc(B_728)
      | v2_struct_0(B_728)
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | ~ v1_tsep_1('#skF_5','#skF_1')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ v1_tsep_1('#skF_4','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1222])).

tff(c_1227,plain,(
    ! [B_728,C_726] :
      ( v1_funct_1(k2_tmap_1('#skF_1',B_728,C_726,'#skF_4'))
      | ~ v5_pre_topc(C_726,'#skF_1',B_728)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_726,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_728))))
      | ~ v1_funct_2(C_726,u1_struct_0('#skF_1'),u1_struct_0(B_728))
      | ~ v1_funct_1(C_726)
      | ~ l1_pre_topc(B_728)
      | ~ v2_pre_topc(B_728)
      | v2_struct_0(B_728)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_38,c_36,c_32,c_30,c_1224])).

tff(c_1229,plain,(
    ! [B_730,C_731] :
      ( v1_funct_1(k2_tmap_1('#skF_1',B_730,C_731,'#skF_4'))
      | ~ v5_pre_topc(C_731,'#skF_1',B_730)
      | ~ m1_subset_1(C_731,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_730))))
      | ~ v1_funct_2(C_731,u1_struct_0('#skF_1'),u1_struct_0(B_730))
      | ~ v1_funct_1(C_731)
      | ~ l1_pre_topc(B_730)
      | ~ v2_pre_topc(B_730)
      | v2_struct_0(B_730) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_40,c_34,c_1227])).

tff(c_1232,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_1229])).

tff(c_1235,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_1190,c_1232])).

tff(c_1237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1191,c_1235])).

%------------------------------------------------------------------------------
