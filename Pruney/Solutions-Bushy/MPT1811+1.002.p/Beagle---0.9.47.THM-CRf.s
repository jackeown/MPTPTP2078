%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1811+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:27 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 652 expanded)
%              Number of leaves         :   26 ( 287 expanded)
%              Depth                    :    9
%              Number of atoms          :  644 (7888 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   29 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > r4_tsep_1 > v1_borsuk_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v1_borsuk_1,type,(
    v1_borsuk_1: ( $i * $i ) > $o )).

tff(f_166,negated_conjecture,(
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
                  & v1_borsuk_1(C,A)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & v1_borsuk_1(D,A)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) )
                       => ( ( v1_funct_1(E)
                            & v1_funct_2(E,u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                            & v5_pre_topc(E,k1_tsep_1(A,C,D),B)
                            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) )
                        <=> ( v1_funct_1(k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,E))
                            & v1_funct_2(k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,E),u1_struct_0(C),u1_struct_0(B))
                            & v5_pre_topc(k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,E),C,B)
                            & m1_subset_1(k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B))))
                            & v1_funct_1(k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,E))
                            & v1_funct_2(k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,E),u1_struct_0(D),u1_struct_0(B))
                            & v5_pre_topc(k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,E),D,B)
                            & m1_subset_1(k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_tmap_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_borsuk_1(B,A)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( v1_borsuk_1(C,A)
                & m1_pre_topc(C,A) )
             => r4_tsep_1(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_tsep_1)).

tff(f_84,axiom,(
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
                 => ( r4_tsep_1(A,C,D)
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) )
                       => ( ( v1_funct_1(E)
                            & v1_funct_2(E,u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                            & v5_pre_topc(E,k1_tsep_1(A,C,D),B)
                            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) )
                        <=> ( v1_funct_1(k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,E))
                            & v1_funct_2(k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,E),u1_struct_0(C),u1_struct_0(B))
                            & v5_pre_topc(k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,E),C,B)
                            & m1_subset_1(k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B))))
                            & v1_funct_1(k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,E))
                            & v1_funct_2(k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,E),u1_struct_0(D),u1_struct_0(B))
                            & v5_pre_topc(k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,E),D,B)
                            & m1_subset_1(k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_tmap_1)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_42,plain,(
    v1_borsuk_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_40,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_36,plain,(
    v1_borsuk_1('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_34,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_26,plain,(
    ! [A_32,B_36,C_38] :
      ( r4_tsep_1(A_32,B_36,C_38)
      | ~ m1_pre_topc(C_38,A_32)
      | ~ v1_borsuk_1(C_38,A_32)
      | ~ m1_pre_topc(B_36,A_32)
      | ~ v1_borsuk_1(B_36,A_32)
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_32,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_30,plain,(
    v1_funct_2('#skF_5',u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_142,plain,
    ( v5_pre_topc('#skF_5',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_178,plain,(
    v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_132,plain,
    ( v5_pre_topc('#skF_5',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_182,plain,(
    v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_122,plain,
    ( v5_pre_topc('#skF_5',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | v5_pre_topc(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'),'#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_179,plain,(
    v5_pre_topc(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'),'#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_112,plain,
    ( v5_pre_topc('#skF_5',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_184,plain,(
    m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_102,plain,
    ( v5_pre_topc('#skF_5',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_177,plain,(
    v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_92,plain,
    ( v5_pre_topc('#skF_5',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_181,plain,(
    v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_82,plain,
    ( v5_pre_topc('#skF_5',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | v5_pre_topc(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'),'#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_180,plain,(
    v5_pre_topc(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'),'#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_72,plain,
    ( v5_pre_topc('#skF_5',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_185,plain,(
    m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_58,plain,
    ( ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'),'#skF_3','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc('#skF_5',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_2('#skF_5',u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_155,plain,
    ( ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'),'#skF_3','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc('#skF_5',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_2('#skF_5',u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_58])).

tff(c_166,plain,
    ( ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'),'#skF_3','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc('#skF_5',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_155])).

tff(c_176,plain,
    ( ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'),'#skF_3','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'))
    | ~ v5_pre_topc('#skF_5',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_166])).

tff(c_254,plain,(
    ~ v5_pre_topc('#skF_5',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_182,c_179,c_184,c_177,c_181,c_180,c_185,c_176])).

tff(c_280,plain,(
    ! [D_108,B_110,A_111,C_109,E_112] :
      ( v5_pre_topc(E_112,k1_tsep_1(A_111,C_109,D_108),B_110)
      | ~ m1_subset_1(k3_tmap_1(A_111,B_110,k1_tsep_1(A_111,C_109,D_108),D_108,E_112),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_108),u1_struct_0(B_110))))
      | ~ v5_pre_topc(k3_tmap_1(A_111,B_110,k1_tsep_1(A_111,C_109,D_108),D_108,E_112),D_108,B_110)
      | ~ v1_funct_2(k3_tmap_1(A_111,B_110,k1_tsep_1(A_111,C_109,D_108),D_108,E_112),u1_struct_0(D_108),u1_struct_0(B_110))
      | ~ v1_funct_1(k3_tmap_1(A_111,B_110,k1_tsep_1(A_111,C_109,D_108),D_108,E_112))
      | ~ m1_subset_1(k3_tmap_1(A_111,B_110,k1_tsep_1(A_111,C_109,D_108),C_109,E_112),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_109),u1_struct_0(B_110))))
      | ~ v5_pre_topc(k3_tmap_1(A_111,B_110,k1_tsep_1(A_111,C_109,D_108),C_109,E_112),C_109,B_110)
      | ~ v1_funct_2(k3_tmap_1(A_111,B_110,k1_tsep_1(A_111,C_109,D_108),C_109,E_112),u1_struct_0(C_109),u1_struct_0(B_110))
      | ~ v1_funct_1(k3_tmap_1(A_111,B_110,k1_tsep_1(A_111,C_109,D_108),C_109,E_112))
      | ~ m1_subset_1(E_112,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_111,C_109,D_108)),u1_struct_0(B_110))))
      | ~ v1_funct_2(E_112,u1_struct_0(k1_tsep_1(A_111,C_109,D_108)),u1_struct_0(B_110))
      | ~ v1_funct_1(E_112)
      | ~ r4_tsep_1(A_111,C_109,D_108)
      | ~ m1_pre_topc(D_108,A_111)
      | v2_struct_0(D_108)
      | ~ m1_pre_topc(C_109,A_111)
      | v2_struct_0(C_109)
      | ~ l1_pre_topc(B_110)
      | ~ v2_pre_topc(B_110)
      | v2_struct_0(B_110)
      | ~ l1_pre_topc(A_111)
      | ~ v2_pre_topc(A_111)
      | v2_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_287,plain,
    ( v5_pre_topc('#skF_5',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'),'#skF_3','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
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
    inference(resolution,[status(thm)],[c_185,c_280])).

tff(c_292,plain,
    ( v5_pre_topc('#skF_5',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_46,c_40,c_34,c_32,c_30,c_28,c_178,c_182,c_179,c_184,c_177,c_181,c_180,c_287])).

tff(c_293,plain,(
    ~ r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_44,c_38,c_254,c_292])).

tff(c_296,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_borsuk_1('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_borsuk_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_293])).

tff(c_299,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_42,c_40,c_36,c_34,c_296])).

tff(c_301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_299])).

tff(c_302,plain,(
    v5_pre_topc('#skF_5',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_348,plain,(
    ! [C_144,D_143,E_147,A_146,B_145] :
      ( m1_subset_1(k3_tmap_1(A_146,B_145,k1_tsep_1(A_146,C_144,D_143),D_143,E_147),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_143),u1_struct_0(B_145))))
      | ~ v5_pre_topc(E_147,k1_tsep_1(A_146,C_144,D_143),B_145)
      | ~ m1_subset_1(E_147,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_146,C_144,D_143)),u1_struct_0(B_145))))
      | ~ v1_funct_2(E_147,u1_struct_0(k1_tsep_1(A_146,C_144,D_143)),u1_struct_0(B_145))
      | ~ v1_funct_1(E_147)
      | ~ r4_tsep_1(A_146,C_144,D_143)
      | ~ m1_pre_topc(D_143,A_146)
      | v2_struct_0(D_143)
      | ~ m1_pre_topc(C_144,A_146)
      | v2_struct_0(C_144)
      | ~ l1_pre_topc(B_145)
      | ~ v2_pre_topc(B_145)
      | v2_struct_0(B_145)
      | ~ l1_pre_topc(A_146)
      | ~ v2_pre_topc(A_146)
      | v2_struct_0(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_303,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_369,plain,
    ( ~ v5_pre_topc('#skF_5',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
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
    inference(resolution,[status(thm)],[c_348,c_303])).

tff(c_378,plain,
    ( ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_46,c_40,c_34,c_32,c_30,c_28,c_302,c_369])).

tff(c_379,plain,(
    ~ r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_44,c_38,c_378])).

tff(c_382,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_borsuk_1('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_borsuk_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_379])).

tff(c_385,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_42,c_40,c_36,c_34,c_382])).

tff(c_387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_385])).

tff(c_388,plain,(
    v5_pre_topc('#skF_5',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_435,plain,(
    ! [B_180,A_181,D_178,E_182,C_179] :
      ( m1_subset_1(k3_tmap_1(A_181,B_180,k1_tsep_1(A_181,C_179,D_178),C_179,E_182),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_179),u1_struct_0(B_180))))
      | ~ v5_pre_topc(E_182,k1_tsep_1(A_181,C_179,D_178),B_180)
      | ~ m1_subset_1(E_182,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_181,C_179,D_178)),u1_struct_0(B_180))))
      | ~ v1_funct_2(E_182,u1_struct_0(k1_tsep_1(A_181,C_179,D_178)),u1_struct_0(B_180))
      | ~ v1_funct_1(E_182)
      | ~ r4_tsep_1(A_181,C_179,D_178)
      | ~ m1_pre_topc(D_178,A_181)
      | v2_struct_0(D_178)
      | ~ m1_pre_topc(C_179,A_181)
      | v2_struct_0(C_179)
      | ~ l1_pre_topc(B_180)
      | ~ v2_pre_topc(B_180)
      | v2_struct_0(B_180)
      | ~ l1_pre_topc(A_181)
      | ~ v2_pre_topc(A_181)
      | v2_struct_0(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_389,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_456,plain,
    ( ~ v5_pre_topc('#skF_5',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
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
    inference(resolution,[status(thm)],[c_435,c_389])).

tff(c_465,plain,
    ( ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_46,c_40,c_34,c_32,c_30,c_28,c_388,c_456])).

tff(c_466,plain,(
    ~ r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_44,c_38,c_465])).

tff(c_469,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_borsuk_1('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_borsuk_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_466])).

tff(c_472,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_42,c_40,c_36,c_34,c_469])).

tff(c_474,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_472])).

tff(c_476,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_475,plain,(
    v5_pre_topc('#skF_5',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_508,plain,(
    ! [B_208,A_209,C_207,E_210,D_206] :
      ( v1_funct_2(k3_tmap_1(A_209,B_208,k1_tsep_1(A_209,C_207,D_206),C_207,E_210),u1_struct_0(C_207),u1_struct_0(B_208))
      | ~ v5_pre_topc(E_210,k1_tsep_1(A_209,C_207,D_206),B_208)
      | ~ m1_subset_1(E_210,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_209,C_207,D_206)),u1_struct_0(B_208))))
      | ~ v1_funct_2(E_210,u1_struct_0(k1_tsep_1(A_209,C_207,D_206)),u1_struct_0(B_208))
      | ~ v1_funct_1(E_210)
      | ~ r4_tsep_1(A_209,C_207,D_206)
      | ~ m1_pre_topc(D_206,A_209)
      | v2_struct_0(D_206)
      | ~ m1_pre_topc(C_207,A_209)
      | v2_struct_0(C_207)
      | ~ l1_pre_topc(B_208)
      | ~ v2_pre_topc(B_208)
      | v2_struct_0(B_208)
      | ~ l1_pre_topc(A_209)
      | ~ v2_pre_topc(A_209)
      | v2_struct_0(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_510,plain,
    ( v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc('#skF_5',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_2('#skF_5',u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
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
    inference(resolution,[status(thm)],[c_28,c_508])).

tff(c_513,plain,
    ( v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_46,c_40,c_34,c_32,c_30,c_475,c_510])).

tff(c_514,plain,(
    ~ r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_44,c_38,c_476,c_513])).

tff(c_517,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_borsuk_1('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_borsuk_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_514])).

tff(c_520,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_42,c_40,c_36,c_34,c_517])).

tff(c_522,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_520])).

tff(c_524,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_523,plain,(
    v5_pre_topc('#skF_5',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_557,plain,(
    ! [E_238,D_234,C_235,B_236,A_237] :
      ( v1_funct_2(k3_tmap_1(A_237,B_236,k1_tsep_1(A_237,C_235,D_234),D_234,E_238),u1_struct_0(D_234),u1_struct_0(B_236))
      | ~ v5_pre_topc(E_238,k1_tsep_1(A_237,C_235,D_234),B_236)
      | ~ m1_subset_1(E_238,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_237,C_235,D_234)),u1_struct_0(B_236))))
      | ~ v1_funct_2(E_238,u1_struct_0(k1_tsep_1(A_237,C_235,D_234)),u1_struct_0(B_236))
      | ~ v1_funct_1(E_238)
      | ~ r4_tsep_1(A_237,C_235,D_234)
      | ~ m1_pre_topc(D_234,A_237)
      | v2_struct_0(D_234)
      | ~ m1_pre_topc(C_235,A_237)
      | v2_struct_0(C_235)
      | ~ l1_pre_topc(B_236)
      | ~ v2_pre_topc(B_236)
      | v2_struct_0(B_236)
      | ~ l1_pre_topc(A_237)
      | ~ v2_pre_topc(A_237)
      | v2_struct_0(A_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_559,plain,
    ( v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc('#skF_5',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_2('#skF_5',u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
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
    inference(resolution,[status(thm)],[c_28,c_557])).

tff(c_562,plain,
    ( v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_46,c_40,c_34,c_32,c_30,c_523,c_559])).

tff(c_563,plain,(
    ~ r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_44,c_38,c_524,c_562])).

tff(c_566,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_borsuk_1('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_borsuk_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_563])).

tff(c_569,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_42,c_40,c_36,c_34,c_566])).

tff(c_571,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_569])).

tff(c_573,plain,(
    ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'),'#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_572,plain,(
    v5_pre_topc('#skF_5',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_595,plain,(
    ! [E_256,A_255,C_253,B_254,D_252] :
      ( v5_pre_topc(k3_tmap_1(A_255,B_254,k1_tsep_1(A_255,C_253,D_252),D_252,E_256),D_252,B_254)
      | ~ v5_pre_topc(E_256,k1_tsep_1(A_255,C_253,D_252),B_254)
      | ~ m1_subset_1(E_256,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_255,C_253,D_252)),u1_struct_0(B_254))))
      | ~ v1_funct_2(E_256,u1_struct_0(k1_tsep_1(A_255,C_253,D_252)),u1_struct_0(B_254))
      | ~ v1_funct_1(E_256)
      | ~ r4_tsep_1(A_255,C_253,D_252)
      | ~ m1_pre_topc(D_252,A_255)
      | v2_struct_0(D_252)
      | ~ m1_pre_topc(C_253,A_255)
      | v2_struct_0(C_253)
      | ~ l1_pre_topc(B_254)
      | ~ v2_pre_topc(B_254)
      | v2_struct_0(B_254)
      | ~ l1_pre_topc(A_255)
      | ~ v2_pre_topc(A_255)
      | v2_struct_0(A_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_597,plain,
    ( v5_pre_topc(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'),'#skF_4','#skF_2')
    | ~ v5_pre_topc('#skF_5',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_2('#skF_5',u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
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
    inference(resolution,[status(thm)],[c_28,c_595])).

tff(c_600,plain,
    ( v5_pre_topc(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'),'#skF_4','#skF_2')
    | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_46,c_40,c_34,c_32,c_30,c_572,c_597])).

tff(c_601,plain,(
    ~ r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_44,c_38,c_573,c_600])).

tff(c_604,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_borsuk_1('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_borsuk_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_601])).

tff(c_607,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_42,c_40,c_36,c_34,c_604])).

tff(c_609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_607])).

tff(c_610,plain,(
    v5_pre_topc('#skF_5',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_632,plain,(
    ! [E_274,C_271,D_270,A_273,B_272] :
      ( v5_pre_topc(k3_tmap_1(A_273,B_272,k1_tsep_1(A_273,C_271,D_270),D_270,E_274),D_270,B_272)
      | ~ v5_pre_topc(E_274,k1_tsep_1(A_273,C_271,D_270),B_272)
      | ~ m1_subset_1(E_274,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_273,C_271,D_270)),u1_struct_0(B_272))))
      | ~ v1_funct_2(E_274,u1_struct_0(k1_tsep_1(A_273,C_271,D_270)),u1_struct_0(B_272))
      | ~ v1_funct_1(E_274)
      | ~ r4_tsep_1(A_273,C_271,D_270)
      | ~ m1_pre_topc(D_270,A_273)
      | v2_struct_0(D_270)
      | ~ m1_pre_topc(C_271,A_273)
      | v2_struct_0(C_271)
      | ~ l1_pre_topc(B_272)
      | ~ v2_pre_topc(B_272)
      | v2_struct_0(B_272)
      | ~ l1_pre_topc(A_273)
      | ~ v2_pre_topc(A_273)
      | v2_struct_0(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_634,plain,
    ( v5_pre_topc(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'),'#skF_4','#skF_2')
    | ~ v5_pre_topc('#skF_5',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_2('#skF_5',u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
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
    inference(resolution,[status(thm)],[c_28,c_632])).

tff(c_637,plain,
    ( v5_pre_topc(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'),'#skF_4','#skF_2')
    | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_46,c_40,c_34,c_32,c_30,c_610,c_634])).

tff(c_638,plain,
    ( v5_pre_topc(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'),'#skF_4','#skF_2')
    | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_44,c_38,c_637])).

tff(c_639,plain,(
    ~ r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_638])).

tff(c_642,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_borsuk_1('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_borsuk_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_639])).

tff(c_645,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_42,c_40,c_36,c_34,c_642])).

tff(c_647,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_645])).

tff(c_649,plain,(
    r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_638])).

tff(c_611,plain,(
    ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_650,plain,(
    ! [A_278,D_275,B_277,E_279,C_276] :
      ( v5_pre_topc(k3_tmap_1(A_278,B_277,k1_tsep_1(A_278,C_276,D_275),C_276,E_279),C_276,B_277)
      | ~ v5_pre_topc(E_279,k1_tsep_1(A_278,C_276,D_275),B_277)
      | ~ m1_subset_1(E_279,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_278,C_276,D_275)),u1_struct_0(B_277))))
      | ~ v1_funct_2(E_279,u1_struct_0(k1_tsep_1(A_278,C_276,D_275)),u1_struct_0(B_277))
      | ~ v1_funct_1(E_279)
      | ~ r4_tsep_1(A_278,C_276,D_275)
      | ~ m1_pre_topc(D_275,A_278)
      | v2_struct_0(D_275)
      | ~ m1_pre_topc(C_276,A_278)
      | v2_struct_0(C_276)
      | ~ l1_pre_topc(B_277)
      | ~ v2_pre_topc(B_277)
      | v2_struct_0(B_277)
      | ~ l1_pre_topc(A_278)
      | ~ v2_pre_topc(A_278)
      | v2_struct_0(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_652,plain,
    ( v5_pre_topc(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'),'#skF_3','#skF_2')
    | ~ v5_pre_topc('#skF_5',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_2('#skF_5',u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
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
    inference(resolution,[status(thm)],[c_28,c_650])).

tff(c_655,plain,
    ( v5_pre_topc(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'),'#skF_3','#skF_2')
    | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_46,c_40,c_34,c_32,c_30,c_610,c_652])).

tff(c_656,plain,(
    ~ r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_44,c_38,c_611,c_655])).

tff(c_658,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_649,c_656])).

tff(c_660,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_659,plain,(
    v5_pre_topc('#skF_5',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_675,plain,(
    ! [E_292,A_291,C_289,D_288,B_290] :
      ( v1_funct_1(k3_tmap_1(A_291,B_290,k1_tsep_1(A_291,C_289,D_288),C_289,E_292))
      | ~ v5_pre_topc(E_292,k1_tsep_1(A_291,C_289,D_288),B_290)
      | ~ m1_subset_1(E_292,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_291,C_289,D_288)),u1_struct_0(B_290))))
      | ~ v1_funct_2(E_292,u1_struct_0(k1_tsep_1(A_291,C_289,D_288)),u1_struct_0(B_290))
      | ~ v1_funct_1(E_292)
      | ~ r4_tsep_1(A_291,C_289,D_288)
      | ~ m1_pre_topc(D_288,A_291)
      | v2_struct_0(D_288)
      | ~ m1_pre_topc(C_289,A_291)
      | v2_struct_0(C_289)
      | ~ l1_pre_topc(B_290)
      | ~ v2_pre_topc(B_290)
      | v2_struct_0(B_290)
      | ~ l1_pre_topc(A_291)
      | ~ v2_pre_topc(A_291)
      | v2_struct_0(A_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_677,plain,
    ( v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'))
    | ~ v5_pre_topc('#skF_5',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_2('#skF_5',u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
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
    inference(resolution,[status(thm)],[c_28,c_675])).

tff(c_680,plain,
    ( v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3','#skF_5'))
    | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_46,c_40,c_34,c_32,c_30,c_659,c_677])).

tff(c_681,plain,(
    ~ r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_44,c_38,c_660,c_680])).

tff(c_684,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_borsuk_1('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_borsuk_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_681])).

tff(c_687,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_42,c_40,c_36,c_34,c_684])).

tff(c_689,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_687])).

tff(c_691,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_690,plain,(
    v5_pre_topc('#skF_5',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_700,plain,(
    ! [D_296,C_297,A_299,B_298,E_300] :
      ( v1_funct_1(k3_tmap_1(A_299,B_298,k1_tsep_1(A_299,C_297,D_296),D_296,E_300))
      | ~ v5_pre_topc(E_300,k1_tsep_1(A_299,C_297,D_296),B_298)
      | ~ m1_subset_1(E_300,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_299,C_297,D_296)),u1_struct_0(B_298))))
      | ~ v1_funct_2(E_300,u1_struct_0(k1_tsep_1(A_299,C_297,D_296)),u1_struct_0(B_298))
      | ~ v1_funct_1(E_300)
      | ~ r4_tsep_1(A_299,C_297,D_296)
      | ~ m1_pre_topc(D_296,A_299)
      | v2_struct_0(D_296)
      | ~ m1_pre_topc(C_297,A_299)
      | v2_struct_0(C_297)
      | ~ l1_pre_topc(B_298)
      | ~ v2_pre_topc(B_298)
      | v2_struct_0(B_298)
      | ~ l1_pre_topc(A_299)
      | ~ v2_pre_topc(A_299)
      | v2_struct_0(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_702,plain,
    ( v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'))
    | ~ v5_pre_topc('#skF_5',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_2('#skF_5',u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
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
    inference(resolution,[status(thm)],[c_28,c_700])).

tff(c_705,plain,
    ( v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4','#skF_5'))
    | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_46,c_40,c_34,c_32,c_30,c_690,c_702])).

tff(c_706,plain,(
    ~ r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_44,c_38,c_691,c_705])).

tff(c_709,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_borsuk_1('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_borsuk_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_706])).

tff(c_712,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_42,c_40,c_36,c_34,c_709])).

tff(c_714,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_712])).

%------------------------------------------------------------------------------
