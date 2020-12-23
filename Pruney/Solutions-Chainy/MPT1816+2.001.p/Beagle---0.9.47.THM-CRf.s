%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:06 EST 2020

% Result     : Theorem 22.54s
% Output     : CNFRefutation 22.74s
% Verified   : 
% Statistics : Number of formulae       :  210 (1140 expanded)
%              Number of leaves         :   41 ( 469 expanded)
%              Depth                    :   10
%              Number of atoms          :  865 (11952 expanded)
%              Number of equality atoms :   35 ( 524 expanded)
%              Maximal formula depth    :   29 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > r4_tsep_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_352,negated_conjecture,(
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

tff(f_137,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k1_tsep_1(A,B,C))
        & v1_pre_topc(k1_tsep_1(A,B,C))
        & m1_pre_topc(k1_tsep_1(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_115,axiom,(
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
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_170,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & v1_funct_1(C)
        & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
        & v5_pre_topc(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B))))
        & ~ v2_struct_0(D)
        & m1_pre_topc(D,A) )
     => ( v1_funct_1(k2_tmap_1(A,B,C,D))
        & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
        & v5_pre_topc(k2_tmap_1(A,B,C,D),D,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tmap_1)).

tff(f_230,axiom,(
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
                          & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                       => ( ( v1_funct_1(k2_tmap_1(A,B,E,k1_tsep_1(A,C,D)))
                            & v1_funct_2(k2_tmap_1(A,B,E,k1_tsep_1(A,C,D)),u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                            & v5_pre_topc(k2_tmap_1(A,B,E,k1_tsep_1(A,C,D)),k1_tsep_1(A,C,D),B)
                            & m1_subset_1(k2_tmap_1(A,B,E,k1_tsep_1(A,C,D)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) )
                        <=> ( v1_funct_1(k2_tmap_1(A,B,E,C))
                            & v1_funct_2(k2_tmap_1(A,B,E,C),u1_struct_0(C),u1_struct_0(B))
                            & v5_pre_topc(k2_tmap_1(A,B,E,C),C,B)
                            & m1_subset_1(k2_tmap_1(A,B,E,C),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B))))
                            & v1_funct_1(k2_tmap_1(A,B,E,D))
                            & v1_funct_2(k2_tmap_1(A,B,E,D),u1_struct_0(D),u1_struct_0(B))
                            & v5_pre_topc(k2_tmap_1(A,B,E,D),D,B)
                            & m1_subset_1(k2_tmap_1(A,B,E,D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_tmap_1)).

tff(c_88,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_352])).

tff(c_86,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_352])).

tff(c_106,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_352])).

tff(c_100,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_352])).

tff(c_104,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_352])).

tff(c_102,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_352])).

tff(c_98,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_352])).

tff(c_96,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_352])).

tff(c_94,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_352])).

tff(c_92,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_352])).

tff(c_84,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_352])).

tff(c_82,plain,(
    m1_pre_topc('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_352])).

tff(c_90,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_352])).

tff(c_80,plain,(
    k1_tsep_1('#skF_1','#skF_4','#skF_5') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_352])).

tff(c_14799,plain,(
    ! [A_577,B_578,C_579] :
      ( m1_pre_topc(k1_tsep_1(A_577,B_578,C_579),A_577)
      | ~ m1_pre_topc(C_579,A_577)
      | v2_struct_0(C_579)
      | ~ m1_pre_topc(B_578,A_577)
      | v2_struct_0(B_578)
      | ~ l1_pre_topc(A_577)
      | v2_struct_0(A_577) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_14824,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_14799])).

tff(c_14841,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_86,c_82,c_14824])).

tff(c_14842,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_88,c_84,c_14841])).

tff(c_14316,plain,(
    ! [A_534,B_535,C_536,D_537] :
      ( k2_partfun1(A_534,B_535,C_536,D_537) = k7_relat_1(C_536,D_537)
      | ~ m1_subset_1(C_536,k1_zfmisc_1(k2_zfmisc_1(A_534,B_535)))
      | ~ v1_funct_1(C_536) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14320,plain,(
    ! [D_537] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_537) = k7_relat_1('#skF_3',D_537)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_90,c_14316])).

tff(c_14329,plain,(
    ! [D_537] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_537) = k7_relat_1('#skF_3',D_537) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_14320])).

tff(c_15719,plain,(
    ! [A_603,B_604,C_605,D_606] :
      ( k2_partfun1(u1_struct_0(A_603),u1_struct_0(B_604),C_605,u1_struct_0(D_606)) = k2_tmap_1(A_603,B_604,C_605,D_606)
      | ~ m1_pre_topc(D_606,A_603)
      | ~ m1_subset_1(C_605,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_603),u1_struct_0(B_604))))
      | ~ v1_funct_2(C_605,u1_struct_0(A_603),u1_struct_0(B_604))
      | ~ v1_funct_1(C_605)
      | ~ l1_pre_topc(B_604)
      | ~ v2_pre_topc(B_604)
      | v2_struct_0(B_604)
      | ~ l1_pre_topc(A_603)
      | ~ v2_pre_topc(A_603)
      | v2_struct_0(A_603) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_15727,plain,(
    ! [D_606] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_606)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_606)
      | ~ m1_pre_topc(D_606,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_90,c_15719])).

tff(c_15743,plain,(
    ! [D_606] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_606)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_606)
      | ~ m1_pre_topc(D_606,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_98,c_96,c_94,c_92,c_14329,c_15727])).

tff(c_15746,plain,(
    ! [D_607] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_607)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_607)
      | ~ m1_pre_topc(D_607,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_100,c_15743])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_272,plain,(
    ! [B_144,A_145] :
      ( v1_relat_1(B_144)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(A_145))
      | ~ v1_relat_1(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_275,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_90,c_272])).

tff(c_281,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_275])).

tff(c_294,plain,(
    ! [C_148,A_149,B_150] :
      ( v4_relat_1(C_148,A_149)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_302,plain,(
    v4_relat_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_90,c_294])).

tff(c_357,plain,(
    ! [B_166,A_167] :
      ( k7_relat_1(B_166,A_167) = B_166
      | ~ v4_relat_1(B_166,A_167)
      | ~ v1_relat_1(B_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_363,plain,
    ( k7_relat_1('#skF_3',u1_struct_0('#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_302,c_357])).

tff(c_369,plain,(
    k7_relat_1('#skF_3',u1_struct_0('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_363])).

tff(c_15752,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_15746,c_369])).

tff(c_15764,plain,(
    k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14842,c_15752])).

tff(c_1523,plain,(
    ! [A_243,B_244,C_245,D_246] :
      ( v1_funct_1(k2_tmap_1(A_243,B_244,C_245,D_246))
      | ~ m1_pre_topc(D_246,A_243)
      | v2_struct_0(D_246)
      | ~ m1_subset_1(C_245,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_243),u1_struct_0(B_244))))
      | ~ v5_pre_topc(C_245,A_243,B_244)
      | ~ v1_funct_2(C_245,u1_struct_0(A_243),u1_struct_0(B_244))
      | ~ v1_funct_1(C_245)
      | ~ l1_pre_topc(B_244)
      | ~ v2_pre_topc(B_244)
      | v2_struct_0(B_244)
      | ~ l1_pre_topc(A_243)
      | ~ v2_pre_topc(A_243)
      | v2_struct_0(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_1529,plain,(
    ! [D_246] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_246))
      | ~ m1_pre_topc(D_246,'#skF_1')
      | v2_struct_0(D_246)
      | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_90,c_1523])).

tff(c_1543,plain,(
    ! [D_246] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_246))
      | ~ m1_pre_topc(D_246,'#skF_1')
      | v2_struct_0(D_246)
      | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_98,c_96,c_94,c_92,c_1529])).

tff(c_1544,plain,(
    ! [D_246] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_246))
      | ~ m1_pre_topc(D_246,'#skF_1')
      | v2_struct_0(D_246)
      | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_100,c_1543])).

tff(c_1860,plain,(
    ~ v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1544])).

tff(c_78,plain,(
    r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_352])).

tff(c_192,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_352])).

tff(c_304,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_192])).

tff(c_182,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_352])).

tff(c_413,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_182])).

tff(c_172,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_352])).

tff(c_402,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_1080,plain,(
    ! [A_231,B_232,C_233] :
      ( m1_pre_topc(k1_tsep_1(A_231,B_232,C_233),A_231)
      | ~ m1_pre_topc(C_233,A_231)
      | v2_struct_0(C_233)
      | ~ m1_pre_topc(B_232,A_231)
      | v2_struct_0(B_232)
      | ~ l1_pre_topc(A_231)
      | v2_struct_0(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1103,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_1080])).

tff(c_1119,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_86,c_82,c_1103])).

tff(c_1120,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_88,c_84,c_1119])).

tff(c_592,plain,(
    ! [A_191,B_192,C_193,D_194] :
      ( k2_partfun1(A_191,B_192,C_193,D_194) = k7_relat_1(C_193,D_194)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(A_191,B_192)))
      | ~ v1_funct_1(C_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_598,plain,(
    ! [D_194] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_194) = k7_relat_1('#skF_3',D_194)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_90,c_592])).

tff(c_610,plain,(
    ! [D_194] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_194) = k7_relat_1('#skF_3',D_194) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_598])).

tff(c_1643,plain,(
    ! [A_247,B_248,C_249,D_250] :
      ( k2_partfun1(u1_struct_0(A_247),u1_struct_0(B_248),C_249,u1_struct_0(D_250)) = k2_tmap_1(A_247,B_248,C_249,D_250)
      | ~ m1_pre_topc(D_250,A_247)
      | ~ m1_subset_1(C_249,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_247),u1_struct_0(B_248))))
      | ~ v1_funct_2(C_249,u1_struct_0(A_247),u1_struct_0(B_248))
      | ~ v1_funct_1(C_249)
      | ~ l1_pre_topc(B_248)
      | ~ v2_pre_topc(B_248)
      | v2_struct_0(B_248)
      | ~ l1_pre_topc(A_247)
      | ~ v2_pre_topc(A_247)
      | v2_struct_0(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1649,plain,(
    ! [D_250] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_250)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_250)
      | ~ m1_pre_topc(D_250,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_90,c_1643])).

tff(c_1663,plain,(
    ! [D_250] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_250)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_250)
      | ~ m1_pre_topc(D_250,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_98,c_96,c_94,c_92,c_610,c_1649])).

tff(c_1748,plain,(
    ! [D_251] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_251)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_251)
      | ~ m1_pre_topc(D_251,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_100,c_1663])).

tff(c_1754,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1748,c_369])).

tff(c_1763,plain,(
    k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1120,c_1754])).

tff(c_162,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_352])).

tff(c_479,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_152,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_352])).

tff(c_344,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_142,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_352])).

tff(c_436,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_132,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_352])).

tff(c_401,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_122,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_352])).

tff(c_504,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_5015,plain,(
    ! [E_374,A_372,B_371,D_370,C_373] :
      ( v5_pre_topc(k2_tmap_1(A_372,B_371,E_374,k1_tsep_1(A_372,C_373,D_370)),k1_tsep_1(A_372,C_373,D_370),B_371)
      | ~ m1_subset_1(k2_tmap_1(A_372,B_371,E_374,D_370),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_370),u1_struct_0(B_371))))
      | ~ v5_pre_topc(k2_tmap_1(A_372,B_371,E_374,D_370),D_370,B_371)
      | ~ v1_funct_2(k2_tmap_1(A_372,B_371,E_374,D_370),u1_struct_0(D_370),u1_struct_0(B_371))
      | ~ v1_funct_1(k2_tmap_1(A_372,B_371,E_374,D_370))
      | ~ m1_subset_1(k2_tmap_1(A_372,B_371,E_374,C_373),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_373),u1_struct_0(B_371))))
      | ~ v5_pre_topc(k2_tmap_1(A_372,B_371,E_374,C_373),C_373,B_371)
      | ~ v1_funct_2(k2_tmap_1(A_372,B_371,E_374,C_373),u1_struct_0(C_373),u1_struct_0(B_371))
      | ~ v1_funct_1(k2_tmap_1(A_372,B_371,E_374,C_373))
      | ~ m1_subset_1(E_374,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_372),u1_struct_0(B_371))))
      | ~ v1_funct_2(E_374,u1_struct_0(A_372),u1_struct_0(B_371))
      | ~ v1_funct_1(E_374)
      | ~ r4_tsep_1(A_372,C_373,D_370)
      | ~ m1_pre_topc(D_370,A_372)
      | v2_struct_0(D_370)
      | ~ m1_pre_topc(C_373,A_372)
      | v2_struct_0(C_373)
      | ~ l1_pre_topc(B_371)
      | ~ v2_pre_topc(B_371)
      | v2_struct_0(B_371)
      | ~ l1_pre_topc(A_372)
      | ~ v2_pre_topc(A_372)
      | v2_struct_0(A_372) ) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_5023,plain,(
    ! [C_373] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',C_373,'#skF_5')),k1_tsep_1('#skF_1',C_373,'#skF_5'),'#skF_2')
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_373),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_373),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_373),C_373,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_373),u1_struct_0(C_373),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_373))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ r4_tsep_1('#skF_1',C_373,'#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(C_373,'#skF_1')
      | v2_struct_0(C_373)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_504,c_5015])).

tff(c_5039,plain,(
    ! [C_373] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',C_373,'#skF_5')),k1_tsep_1('#skF_1',C_373,'#skF_5'),'#skF_2')
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_373),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_373),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_373),C_373,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_373),u1_struct_0(C_373),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_373))
      | ~ r4_tsep_1('#skF_1',C_373,'#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(C_373,'#skF_1')
      | v2_struct_0(C_373)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_98,c_96,c_82,c_94,c_92,c_90,c_344,c_436,c_401,c_5023])).

tff(c_13860,plain,(
    ! [C_516] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',C_516,'#skF_5')),k1_tsep_1('#skF_1',C_516,'#skF_5'),'#skF_2')
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_516),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_516),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_516),C_516,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_516),u1_struct_0(C_516),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_516))
      | ~ r4_tsep_1('#skF_1',C_516,'#skF_5')
      | ~ m1_pre_topc(C_516,'#skF_1')
      | v2_struct_0(C_516) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_100,c_84,c_5039])).

tff(c_13885,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2')
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_479,c_13860])).

tff(c_13912,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_78,c_304,c_413,c_402,c_80,c_1763,c_80,c_13885])).

tff(c_13914,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_1860,c_13912])).

tff(c_13916,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1544])).

tff(c_108,plain,
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
    inference(cnfTransformation,[status(thm)],[f_352])).

tff(c_206,plain,
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
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_108])).

tff(c_216,plain,
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
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_206])).

tff(c_226,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_216])).

tff(c_14231,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13916,c_304,c_413,c_402,c_479,c_344,c_436,c_401,c_504,c_226])).

tff(c_14232,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_18180,plain,(
    ! [B_693,C_695,E_696,A_694,D_692] :
      ( m1_subset_1(k2_tmap_1(A_694,B_693,E_696,D_692),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_692),u1_struct_0(B_693))))
      | ~ m1_subset_1(k2_tmap_1(A_694,B_693,E_696,k1_tsep_1(A_694,C_695,D_692)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_694,C_695,D_692)),u1_struct_0(B_693))))
      | ~ v5_pre_topc(k2_tmap_1(A_694,B_693,E_696,k1_tsep_1(A_694,C_695,D_692)),k1_tsep_1(A_694,C_695,D_692),B_693)
      | ~ v1_funct_2(k2_tmap_1(A_694,B_693,E_696,k1_tsep_1(A_694,C_695,D_692)),u1_struct_0(k1_tsep_1(A_694,C_695,D_692)),u1_struct_0(B_693))
      | ~ v1_funct_1(k2_tmap_1(A_694,B_693,E_696,k1_tsep_1(A_694,C_695,D_692)))
      | ~ m1_subset_1(E_696,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_694),u1_struct_0(B_693))))
      | ~ v1_funct_2(E_696,u1_struct_0(A_694),u1_struct_0(B_693))
      | ~ v1_funct_1(E_696)
      | ~ r4_tsep_1(A_694,C_695,D_692)
      | ~ m1_pre_topc(D_692,A_694)
      | v2_struct_0(D_692)
      | ~ m1_pre_topc(C_695,A_694)
      | v2_struct_0(C_695)
      | ~ l1_pre_topc(B_693)
      | ~ v2_pre_topc(B_693)
      | v2_struct_0(B_693)
      | ~ l1_pre_topc(A_694)
      | ~ v2_pre_topc(A_694)
      | v2_struct_0(A_694) ) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_18222,plain,(
    ! [B_693,E_696] :
      ( m1_subset_1(k2_tmap_1('#skF_1',B_693,E_696,'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_693))))
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_693,E_696,'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_693))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_693,E_696,k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_693)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_693,E_696,k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_693))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_693,E_696,k1_tsep_1('#skF_1','#skF_4','#skF_5')))
      | ~ m1_subset_1(E_696,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_693))))
      | ~ v1_funct_2(E_696,u1_struct_0('#skF_1'),u1_struct_0(B_693))
      | ~ v1_funct_1(E_696)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_693)
      | ~ v2_pre_topc(B_693)
      | v2_struct_0(B_693)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_18180])).

tff(c_18258,plain,(
    ! [B_693,E_696] :
      ( m1_subset_1(k2_tmap_1('#skF_1',B_693,E_696,'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_693))))
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_693,E_696,'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_693))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_693,E_696,'#skF_1'),'#skF_1',B_693)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_693,E_696,'#skF_1'),u1_struct_0('#skF_1'),u1_struct_0(B_693))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_693,E_696,'#skF_1'))
      | ~ m1_subset_1(E_696,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_693))))
      | ~ v1_funct_2(E_696,u1_struct_0('#skF_1'),u1_struct_0(B_693))
      | ~ v1_funct_1(E_696)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_693)
      | ~ v2_pre_topc(B_693)
      | v2_struct_0(B_693)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_86,c_82,c_78,c_80,c_80,c_80,c_80,c_80,c_80,c_18222])).

tff(c_33446,plain,(
    ! [B_925,E_926] :
      ( m1_subset_1(k2_tmap_1('#skF_1',B_925,E_926,'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_925))))
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_925,E_926,'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_925))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_925,E_926,'#skF_1'),'#skF_1',B_925)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_925,E_926,'#skF_1'),u1_struct_0('#skF_1'),u1_struct_0(B_925))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_925,E_926,'#skF_1'))
      | ~ m1_subset_1(E_926,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_925))))
      | ~ v1_funct_2(E_926,u1_struct_0('#skF_1'),u1_struct_0(B_925))
      | ~ v1_funct_1(E_926)
      | ~ l1_pre_topc(B_925)
      | ~ v2_pre_topc(B_925)
      | v2_struct_0(B_925) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_88,c_84,c_18258])).

tff(c_14233,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_33471,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),'#skF_1','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_33446,c_14233])).

tff(c_33537,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_94,c_92,c_90,c_94,c_15764,c_92,c_15764,c_14232,c_15764,c_90,c_15764,c_33471])).

tff(c_33539,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_33537])).

tff(c_33541,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_33944,plain,(
    ! [A_968,B_969,C_970] :
      ( m1_pre_topc(k1_tsep_1(A_968,B_969,C_970),A_968)
      | ~ m1_pre_topc(C_970,A_968)
      | v2_struct_0(C_970)
      | ~ m1_pre_topc(B_969,A_968)
      | v2_struct_0(B_969)
      | ~ l1_pre_topc(A_968)
      | v2_struct_0(A_968) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_33967,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_33944])).

tff(c_33983,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_86,c_82,c_33967])).

tff(c_33984,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_88,c_84,c_33983])).

tff(c_33602,plain,(
    ! [A_932,B_933,C_934,D_935] :
      ( k2_partfun1(A_932,B_933,C_934,D_935) = k7_relat_1(C_934,D_935)
      | ~ m1_subset_1(C_934,k1_zfmisc_1(k2_zfmisc_1(A_932,B_933)))
      | ~ v1_funct_1(C_934) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_33604,plain,(
    ! [D_935] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_935) = k7_relat_1('#skF_3',D_935)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_90,c_33602])).

tff(c_33610,plain,(
    ! [D_935] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_935) = k7_relat_1('#skF_3',D_935) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_33604])).

tff(c_34830,plain,(
    ! [A_990,B_991,C_992,D_993] :
      ( k2_partfun1(u1_struct_0(A_990),u1_struct_0(B_991),C_992,u1_struct_0(D_993)) = k2_tmap_1(A_990,B_991,C_992,D_993)
      | ~ m1_pre_topc(D_993,A_990)
      | ~ m1_subset_1(C_992,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_990),u1_struct_0(B_991))))
      | ~ v1_funct_2(C_992,u1_struct_0(A_990),u1_struct_0(B_991))
      | ~ v1_funct_1(C_992)
      | ~ l1_pre_topc(B_991)
      | ~ v2_pre_topc(B_991)
      | v2_struct_0(B_991)
      | ~ l1_pre_topc(A_990)
      | ~ v2_pre_topc(A_990)
      | v2_struct_0(A_990) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_34836,plain,(
    ! [D_993] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_993)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_993)
      | ~ m1_pre_topc(D_993,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_90,c_34830])).

tff(c_34848,plain,(
    ! [D_993] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_993)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_993)
      | ~ m1_pre_topc(D_993,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_98,c_96,c_94,c_92,c_33610,c_34836])).

tff(c_34986,plain,(
    ! [D_997] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_997)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_997)
      | ~ m1_pre_topc(D_997,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_100,c_34848])).

tff(c_34992,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_34986,c_369])).

tff(c_35004,plain,(
    k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33984,c_34992])).

tff(c_33540,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_37218,plain,(
    ! [B_1061,E_1064,D_1060,C_1063,A_1062] :
      ( m1_subset_1(k2_tmap_1(A_1062,B_1061,E_1064,C_1063),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1063),u1_struct_0(B_1061))))
      | ~ m1_subset_1(k2_tmap_1(A_1062,B_1061,E_1064,k1_tsep_1(A_1062,C_1063,D_1060)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_1062,C_1063,D_1060)),u1_struct_0(B_1061))))
      | ~ v5_pre_topc(k2_tmap_1(A_1062,B_1061,E_1064,k1_tsep_1(A_1062,C_1063,D_1060)),k1_tsep_1(A_1062,C_1063,D_1060),B_1061)
      | ~ v1_funct_2(k2_tmap_1(A_1062,B_1061,E_1064,k1_tsep_1(A_1062,C_1063,D_1060)),u1_struct_0(k1_tsep_1(A_1062,C_1063,D_1060)),u1_struct_0(B_1061))
      | ~ v1_funct_1(k2_tmap_1(A_1062,B_1061,E_1064,k1_tsep_1(A_1062,C_1063,D_1060)))
      | ~ m1_subset_1(E_1064,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1062),u1_struct_0(B_1061))))
      | ~ v1_funct_2(E_1064,u1_struct_0(A_1062),u1_struct_0(B_1061))
      | ~ v1_funct_1(E_1064)
      | ~ r4_tsep_1(A_1062,C_1063,D_1060)
      | ~ m1_pre_topc(D_1060,A_1062)
      | v2_struct_0(D_1060)
      | ~ m1_pre_topc(C_1063,A_1062)
      | v2_struct_0(C_1063)
      | ~ l1_pre_topc(B_1061)
      | ~ v2_pre_topc(B_1061)
      | v2_struct_0(B_1061)
      | ~ l1_pre_topc(A_1062)
      | ~ v2_pre_topc(A_1062)
      | v2_struct_0(A_1062) ) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_37278,plain,(
    ! [B_1061,E_1064] :
      ( m1_subset_1(k2_tmap_1('#skF_1',B_1061,E_1064,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_1061))))
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_1061,E_1064,'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_1061))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_1061,E_1064,k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_1061)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_1061,E_1064,k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_1061))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_1061,E_1064,k1_tsep_1('#skF_1','#skF_4','#skF_5')))
      | ~ m1_subset_1(E_1064,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1061))))
      | ~ v1_funct_2(E_1064,u1_struct_0('#skF_1'),u1_struct_0(B_1061))
      | ~ v1_funct_1(E_1064)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_1061)
      | ~ v2_pre_topc(B_1061)
      | v2_struct_0(B_1061)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_37218])).

tff(c_37332,plain,(
    ! [B_1061,E_1064] :
      ( m1_subset_1(k2_tmap_1('#skF_1',B_1061,E_1064,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_1061))))
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_1061,E_1064,'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1061))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_1061,E_1064,'#skF_1'),'#skF_1',B_1061)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_1061,E_1064,'#skF_1'),u1_struct_0('#skF_1'),u1_struct_0(B_1061))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_1061,E_1064,'#skF_1'))
      | ~ m1_subset_1(E_1064,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1061))))
      | ~ v1_funct_2(E_1064,u1_struct_0('#skF_1'),u1_struct_0(B_1061))
      | ~ v1_funct_1(E_1064)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_1061)
      | ~ v2_pre_topc(B_1061)
      | v2_struct_0(B_1061)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_86,c_82,c_78,c_80,c_80,c_80,c_80,c_80,c_80,c_37278])).

tff(c_52345,plain,(
    ! [B_1307,E_1308] :
      ( m1_subset_1(k2_tmap_1('#skF_1',B_1307,E_1308,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_1307))))
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_1307,E_1308,'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1307))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_1307,E_1308,'#skF_1'),'#skF_1',B_1307)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_1307,E_1308,'#skF_1'),u1_struct_0('#skF_1'),u1_struct_0(B_1307))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_1307,E_1308,'#skF_1'))
      | ~ m1_subset_1(E_1308,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1307))))
      | ~ v1_funct_2(E_1308,u1_struct_0('#skF_1'),u1_struct_0(B_1307))
      | ~ v1_funct_1(E_1308)
      | ~ l1_pre_topc(B_1307)
      | ~ v2_pre_topc(B_1307)
      | v2_struct_0(B_1307) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_88,c_84,c_37332])).

tff(c_52363,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),'#skF_1','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_35004,c_52345])).

tff(c_52380,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_94,c_92,c_90,c_94,c_35004,c_92,c_35004,c_33540,c_35004,c_90,c_52363])).

tff(c_52382,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_33541,c_52380])).

tff(c_52383,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_54277,plain,(
    ! [A_1411,B_1412,C_1413,D_1414] :
      ( v1_funct_2(k2_tmap_1(A_1411,B_1412,C_1413,D_1414),u1_struct_0(D_1414),u1_struct_0(B_1412))
      | ~ m1_pre_topc(D_1414,A_1411)
      | v2_struct_0(D_1414)
      | ~ m1_subset_1(C_1413,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1411),u1_struct_0(B_1412))))
      | ~ v5_pre_topc(C_1413,A_1411,B_1412)
      | ~ v1_funct_2(C_1413,u1_struct_0(A_1411),u1_struct_0(B_1412))
      | ~ v1_funct_1(C_1413)
      | ~ l1_pre_topc(B_1412)
      | ~ v2_pre_topc(B_1412)
      | v2_struct_0(B_1412)
      | ~ l1_pre_topc(A_1411)
      | ~ v2_pre_topc(A_1411)
      | v2_struct_0(A_1411) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_54283,plain,(
    ! [D_1414] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_1414),u1_struct_0(D_1414),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_1414,'#skF_1')
      | v2_struct_0(D_1414)
      | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_90,c_54277])).

tff(c_54295,plain,(
    ! [D_1414] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_1414),u1_struct_0(D_1414),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_1414,'#skF_1')
      | v2_struct_0(D_1414)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_98,c_96,c_94,c_92,c_52383,c_54283])).

tff(c_54812,plain,(
    ! [D_1434] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_1434),u1_struct_0(D_1434),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_1434,'#skF_1')
      | v2_struct_0(D_1434) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_100,c_54295])).

tff(c_52384,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_54815,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_54812,c_52384])).

tff(c_54824,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_54815])).

tff(c_54826,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_54824])).

tff(c_54827,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_56574,plain,(
    ! [A_1525,B_1526,C_1527,D_1528] :
      ( v1_funct_2(k2_tmap_1(A_1525,B_1526,C_1527,D_1528),u1_struct_0(D_1528),u1_struct_0(B_1526))
      | ~ m1_pre_topc(D_1528,A_1525)
      | v2_struct_0(D_1528)
      | ~ m1_subset_1(C_1527,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1525),u1_struct_0(B_1526))))
      | ~ v5_pre_topc(C_1527,A_1525,B_1526)
      | ~ v1_funct_2(C_1527,u1_struct_0(A_1525),u1_struct_0(B_1526))
      | ~ v1_funct_1(C_1527)
      | ~ l1_pre_topc(B_1526)
      | ~ v2_pre_topc(B_1526)
      | v2_struct_0(B_1526)
      | ~ l1_pre_topc(A_1525)
      | ~ v2_pre_topc(A_1525)
      | v2_struct_0(A_1525) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_56580,plain,(
    ! [D_1528] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_1528),u1_struct_0(D_1528),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_1528,'#skF_1')
      | v2_struct_0(D_1528)
      | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_90,c_56574])).

tff(c_56592,plain,(
    ! [D_1528] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_1528),u1_struct_0(D_1528),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_1528,'#skF_1')
      | v2_struct_0(D_1528)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_98,c_96,c_94,c_92,c_54827,c_56580])).

tff(c_56622,plain,(
    ! [D_1531] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_1531),u1_struct_0(D_1531),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_1531,'#skF_1')
      | v2_struct_0(D_1531) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_100,c_56592])).

tff(c_54828,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_56625,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56622,c_54828])).

tff(c_56634,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_56625])).

tff(c_56636,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_56634])).

tff(c_56637,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_58213,plain,(
    ! [A_1632,B_1633,C_1634,D_1635] :
      ( v5_pre_topc(k2_tmap_1(A_1632,B_1633,C_1634,D_1635),D_1635,B_1633)
      | ~ m1_pre_topc(D_1635,A_1632)
      | v2_struct_0(D_1635)
      | ~ m1_subset_1(C_1634,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1632),u1_struct_0(B_1633))))
      | ~ v5_pre_topc(C_1634,A_1632,B_1633)
      | ~ v1_funct_2(C_1634,u1_struct_0(A_1632),u1_struct_0(B_1633))
      | ~ v1_funct_1(C_1634)
      | ~ l1_pre_topc(B_1633)
      | ~ v2_pre_topc(B_1633)
      | v2_struct_0(B_1633)
      | ~ l1_pre_topc(A_1632)
      | ~ v2_pre_topc(A_1632)
      | v2_struct_0(A_1632) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_58215,plain,(
    ! [D_1635] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_1635),D_1635,'#skF_2')
      | ~ m1_pre_topc(D_1635,'#skF_1')
      | v2_struct_0(D_1635)
      | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_90,c_58213])).

tff(c_58221,plain,(
    ! [D_1635] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_1635),D_1635,'#skF_2')
      | ~ m1_pre_topc(D_1635,'#skF_1')
      | v2_struct_0(D_1635)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_98,c_96,c_94,c_92,c_56637,c_58215])).

tff(c_58947,plain,(
    ! [D_1653] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_1653),D_1653,'#skF_2')
      | ~ m1_pre_topc(D_1653,'#skF_1')
      | v2_struct_0(D_1653) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_100,c_58221])).

tff(c_56638,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_58950,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_58947,c_56638])).

tff(c_58956,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_58950])).

tff(c_58958,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_58956])).

tff(c_58959,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_60448,plain,(
    ! [A_1737,B_1738,C_1739,D_1740] :
      ( v5_pre_topc(k2_tmap_1(A_1737,B_1738,C_1739,D_1740),D_1740,B_1738)
      | ~ m1_pre_topc(D_1740,A_1737)
      | v2_struct_0(D_1740)
      | ~ m1_subset_1(C_1739,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1737),u1_struct_0(B_1738))))
      | ~ v5_pre_topc(C_1739,A_1737,B_1738)
      | ~ v1_funct_2(C_1739,u1_struct_0(A_1737),u1_struct_0(B_1738))
      | ~ v1_funct_1(C_1739)
      | ~ l1_pre_topc(B_1738)
      | ~ v2_pre_topc(B_1738)
      | v2_struct_0(B_1738)
      | ~ l1_pre_topc(A_1737)
      | ~ v2_pre_topc(A_1737)
      | v2_struct_0(A_1737) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_60450,plain,(
    ! [D_1740] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_1740),D_1740,'#skF_2')
      | ~ m1_pre_topc(D_1740,'#skF_1')
      | v2_struct_0(D_1740)
      | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_90,c_60448])).

tff(c_60456,plain,(
    ! [D_1740] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_1740),D_1740,'#skF_2')
      | ~ m1_pre_topc(D_1740,'#skF_1')
      | v2_struct_0(D_1740)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_98,c_96,c_94,c_92,c_58959,c_60450])).

tff(c_60643,plain,(
    ! [D_1741] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_1741),D_1741,'#skF_2')
      | ~ m1_pre_topc(D_1741,'#skF_1')
      | v2_struct_0(D_1741) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_100,c_60456])).

tff(c_58960,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_60646,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_60643,c_58960])).

tff(c_60652,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_60646])).

tff(c_60654,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_60652])).

tff(c_60655,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_62031,plain,(
    ! [A_1849,B_1850,C_1851,D_1852] :
      ( v1_funct_1(k2_tmap_1(A_1849,B_1850,C_1851,D_1852))
      | ~ m1_pre_topc(D_1852,A_1849)
      | v2_struct_0(D_1852)
      | ~ m1_subset_1(C_1851,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1849),u1_struct_0(B_1850))))
      | ~ v5_pre_topc(C_1851,A_1849,B_1850)
      | ~ v1_funct_2(C_1851,u1_struct_0(A_1849),u1_struct_0(B_1850))
      | ~ v1_funct_1(C_1851)
      | ~ l1_pre_topc(B_1850)
      | ~ v2_pre_topc(B_1850)
      | v2_struct_0(B_1850)
      | ~ l1_pre_topc(A_1849)
      | ~ v2_pre_topc(A_1849)
      | v2_struct_0(A_1849) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_62033,plain,(
    ! [D_1852] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_1852))
      | ~ m1_pre_topc(D_1852,'#skF_1')
      | v2_struct_0(D_1852)
      | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_90,c_62031])).

tff(c_62039,plain,(
    ! [D_1852] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_1852))
      | ~ m1_pre_topc(D_1852,'#skF_1')
      | v2_struct_0(D_1852)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_98,c_96,c_94,c_92,c_60655,c_62033])).

tff(c_62555,plain,(
    ! [D_1861] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_1861))
      | ~ m1_pre_topc(D_1861,'#skF_1')
      | v2_struct_0(D_1861) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_100,c_62039])).

tff(c_60656,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_62558,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_62555,c_60656])).

tff(c_62561,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_62558])).

tff(c_62563,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_62561])).

tff(c_62564,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_63980,plain,(
    ! [A_1979,B_1980,C_1981,D_1982] :
      ( v1_funct_1(k2_tmap_1(A_1979,B_1980,C_1981,D_1982))
      | ~ m1_pre_topc(D_1982,A_1979)
      | v2_struct_0(D_1982)
      | ~ m1_subset_1(C_1981,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1979),u1_struct_0(B_1980))))
      | ~ v5_pre_topc(C_1981,A_1979,B_1980)
      | ~ v1_funct_2(C_1981,u1_struct_0(A_1979),u1_struct_0(B_1980))
      | ~ v1_funct_1(C_1981)
      | ~ l1_pre_topc(B_1980)
      | ~ v2_pre_topc(B_1980)
      | v2_struct_0(B_1980)
      | ~ l1_pre_topc(A_1979)
      | ~ v2_pre_topc(A_1979)
      | v2_struct_0(A_1979) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_63982,plain,(
    ! [D_1982] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_1982))
      | ~ m1_pre_topc(D_1982,'#skF_1')
      | v2_struct_0(D_1982)
      | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_90,c_63980])).

tff(c_63988,plain,(
    ! [D_1982] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_1982))
      | ~ m1_pre_topc(D_1982,'#skF_1')
      | v2_struct_0(D_1982)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_98,c_96,c_94,c_92,c_62564,c_63982])).

tff(c_64504,plain,(
    ! [D_1991] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_1991))
      | ~ m1_pre_topc(D_1991,'#skF_1')
      | v2_struct_0(D_1991) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_100,c_63988])).

tff(c_62565,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_64507,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_64504,c_62565])).

tff(c_64510,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_64507])).

tff(c_64512,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_64510])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:28:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.54/11.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.54/11.82  
% 22.54/11.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.54/11.82  %$ v5_pre_topc > v1_funct_2 > r4_tsep_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 22.54/11.82  
% 22.54/11.82  %Foreground sorts:
% 22.54/11.82  
% 22.54/11.82  
% 22.54/11.82  %Background operators:
% 22.54/11.82  
% 22.54/11.82  
% 22.54/11.82  %Foreground operators:
% 22.54/11.82  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 22.54/11.82  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 22.54/11.82  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 22.54/11.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 22.54/11.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.54/11.82  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 22.54/11.82  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 22.54/11.82  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 22.54/11.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 22.54/11.82  tff(r4_tsep_1, type, r4_tsep_1: ($i * $i * $i) > $o).
% 22.54/11.82  tff('#skF_5', type, '#skF_5': $i).
% 22.54/11.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 22.54/11.82  tff('#skF_2', type, '#skF_2': $i).
% 22.54/11.82  tff('#skF_3', type, '#skF_3': $i).
% 22.54/11.82  tff('#skF_1', type, '#skF_1': $i).
% 22.54/11.82  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 22.54/11.82  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 22.54/11.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 22.54/11.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.54/11.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 22.54/11.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 22.54/11.82  tff('#skF_4', type, '#skF_4': $i).
% 22.54/11.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.54/11.82  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 22.54/11.82  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 22.54/11.82  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 22.54/11.82  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 22.54/11.82  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 22.54/11.82  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 22.54/11.82  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 22.54/11.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 22.54/11.82  
% 22.74/11.85  tff(f_352, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => (((A = k1_tsep_1(A, D, E)) & r4_tsep_1(A, D, E)) => ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) <=> (((((((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, C, D), D, B)) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) & v1_funct_1(k2_tmap_1(A, B, C, E))) & v1_funct_2(k2_tmap_1(A, B, C, E), u1_struct_0(E), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, C, E), E, B)) & m1_subset_1(k2_tmap_1(A, B, C, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E), u1_struct_0(B))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_tmap_1)).
% 22.74/11.85  tff(f_137, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 22.74/11.85  tff(f_62, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 22.74/11.85  tff(f_115, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 22.74/11.85  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 22.74/11.85  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 22.74/11.85  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 22.74/11.85  tff(f_50, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 22.74/11.85  tff(f_170, axiom, (![A, B, C, D]: ((((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & ~v2_struct_0(D)) & m1_pre_topc(D, A)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, C, D), D, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_tmap_1)).
% 22.74/11.85  tff(f_230, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (r4_tsep_1(A, C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => ((((v1_funct_1(k2_tmap_1(A, B, E, k1_tsep_1(A, C, D))) & v1_funct_2(k2_tmap_1(A, B, E, k1_tsep_1(A, C, D)), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, E, k1_tsep_1(A, C, D)), k1_tsep_1(A, C, D), B)) & m1_subset_1(k2_tmap_1(A, B, E, k1_tsep_1(A, C, D)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) <=> (((((((v1_funct_1(k2_tmap_1(A, B, E, C)) & v1_funct_2(k2_tmap_1(A, B, E, C), u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, E, C), C, B)) & m1_subset_1(k2_tmap_1(A, B, E, C), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(k2_tmap_1(A, B, E, D))) & v1_funct_2(k2_tmap_1(A, B, E, D), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, E, D), D, B)) & m1_subset_1(k2_tmap_1(A, B, E, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_tmap_1)).
% 22.74/11.85  tff(c_88, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_352])).
% 22.74/11.85  tff(c_86, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_352])).
% 22.74/11.85  tff(c_106, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_352])).
% 22.74/11.85  tff(c_100, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_352])).
% 22.74/11.85  tff(c_104, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_352])).
% 22.74/11.85  tff(c_102, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_352])).
% 22.74/11.85  tff(c_98, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_352])).
% 22.74/11.85  tff(c_96, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_352])).
% 22.74/11.85  tff(c_94, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_352])).
% 22.74/11.85  tff(c_92, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_352])).
% 22.74/11.85  tff(c_84, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_352])).
% 22.74/11.85  tff(c_82, plain, (m1_pre_topc('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_352])).
% 22.74/11.85  tff(c_90, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_352])).
% 22.74/11.85  tff(c_80, plain, (k1_tsep_1('#skF_1', '#skF_4', '#skF_5')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_352])).
% 22.74/11.85  tff(c_14799, plain, (![A_577, B_578, C_579]: (m1_pre_topc(k1_tsep_1(A_577, B_578, C_579), A_577) | ~m1_pre_topc(C_579, A_577) | v2_struct_0(C_579) | ~m1_pre_topc(B_578, A_577) | v2_struct_0(B_578) | ~l1_pre_topc(A_577) | v2_struct_0(A_577))), inference(cnfTransformation, [status(thm)], [f_137])).
% 22.74/11.85  tff(c_14824, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_80, c_14799])).
% 22.74/11.85  tff(c_14841, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_86, c_82, c_14824])).
% 22.74/11.85  tff(c_14842, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_106, c_88, c_84, c_14841])).
% 22.74/11.85  tff(c_14316, plain, (![A_534, B_535, C_536, D_537]: (k2_partfun1(A_534, B_535, C_536, D_537)=k7_relat_1(C_536, D_537) | ~m1_subset_1(C_536, k1_zfmisc_1(k2_zfmisc_1(A_534, B_535))) | ~v1_funct_1(C_536))), inference(cnfTransformation, [status(thm)], [f_62])).
% 22.74/11.85  tff(c_14320, plain, (![D_537]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_537)=k7_relat_1('#skF_3', D_537) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_90, c_14316])).
% 22.74/11.85  tff(c_14329, plain, (![D_537]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_537)=k7_relat_1('#skF_3', D_537))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_14320])).
% 22.74/11.85  tff(c_15719, plain, (![A_603, B_604, C_605, D_606]: (k2_partfun1(u1_struct_0(A_603), u1_struct_0(B_604), C_605, u1_struct_0(D_606))=k2_tmap_1(A_603, B_604, C_605, D_606) | ~m1_pre_topc(D_606, A_603) | ~m1_subset_1(C_605, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_603), u1_struct_0(B_604)))) | ~v1_funct_2(C_605, u1_struct_0(A_603), u1_struct_0(B_604)) | ~v1_funct_1(C_605) | ~l1_pre_topc(B_604) | ~v2_pre_topc(B_604) | v2_struct_0(B_604) | ~l1_pre_topc(A_603) | ~v2_pre_topc(A_603) | v2_struct_0(A_603))), inference(cnfTransformation, [status(thm)], [f_115])).
% 22.74/11.85  tff(c_15727, plain, (![D_606]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_606))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_606) | ~m1_pre_topc(D_606, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_90, c_15719])).
% 22.74/11.85  tff(c_15743, plain, (![D_606]: (k7_relat_1('#skF_3', u1_struct_0(D_606))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_606) | ~m1_pre_topc(D_606, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_98, c_96, c_94, c_92, c_14329, c_15727])).
% 22.74/11.85  tff(c_15746, plain, (![D_607]: (k7_relat_1('#skF_3', u1_struct_0(D_607))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_607) | ~m1_pre_topc(D_607, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_106, c_100, c_15743])).
% 22.74/11.85  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 22.74/11.85  tff(c_272, plain, (![B_144, A_145]: (v1_relat_1(B_144) | ~m1_subset_1(B_144, k1_zfmisc_1(A_145)) | ~v1_relat_1(A_145))), inference(cnfTransformation, [status(thm)], [f_42])).
% 22.74/11.85  tff(c_275, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_90, c_272])).
% 22.74/11.85  tff(c_281, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_275])).
% 22.74/11.85  tff(c_294, plain, (![C_148, A_149, B_150]: (v4_relat_1(C_148, A_149) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 22.74/11.85  tff(c_302, plain, (v4_relat_1('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_90, c_294])).
% 22.74/11.85  tff(c_357, plain, (![B_166, A_167]: (k7_relat_1(B_166, A_167)=B_166 | ~v4_relat_1(B_166, A_167) | ~v1_relat_1(B_166))), inference(cnfTransformation, [status(thm)], [f_50])).
% 22.74/11.85  tff(c_363, plain, (k7_relat_1('#skF_3', u1_struct_0('#skF_1'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_302, c_357])).
% 22.74/11.85  tff(c_369, plain, (k7_relat_1('#skF_3', u1_struct_0('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_281, c_363])).
% 22.74/11.85  tff(c_15752, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_15746, c_369])).
% 22.74/11.85  tff(c_15764, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14842, c_15752])).
% 22.74/11.85  tff(c_1523, plain, (![A_243, B_244, C_245, D_246]: (v1_funct_1(k2_tmap_1(A_243, B_244, C_245, D_246)) | ~m1_pre_topc(D_246, A_243) | v2_struct_0(D_246) | ~m1_subset_1(C_245, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_243), u1_struct_0(B_244)))) | ~v5_pre_topc(C_245, A_243, B_244) | ~v1_funct_2(C_245, u1_struct_0(A_243), u1_struct_0(B_244)) | ~v1_funct_1(C_245) | ~l1_pre_topc(B_244) | ~v2_pre_topc(B_244) | v2_struct_0(B_244) | ~l1_pre_topc(A_243) | ~v2_pre_topc(A_243) | v2_struct_0(A_243))), inference(cnfTransformation, [status(thm)], [f_170])).
% 22.74/11.85  tff(c_1529, plain, (![D_246]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_246)) | ~m1_pre_topc(D_246, '#skF_1') | v2_struct_0(D_246) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_90, c_1523])).
% 22.74/11.85  tff(c_1543, plain, (![D_246]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_246)) | ~m1_pre_topc(D_246, '#skF_1') | v2_struct_0(D_246) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_98, c_96, c_94, c_92, c_1529])).
% 22.74/11.85  tff(c_1544, plain, (![D_246]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_246)) | ~m1_pre_topc(D_246, '#skF_1') | v2_struct_0(D_246) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_106, c_100, c_1543])).
% 22.74/11.85  tff(c_1860, plain, (~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_1544])).
% 22.74/11.85  tff(c_78, plain, (r4_tsep_1('#skF_1', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_352])).
% 22.74/11.85  tff(c_192, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_352])).
% 22.74/11.85  tff(c_304, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_192])).
% 22.74/11.85  tff(c_182, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_352])).
% 22.74/11.85  tff(c_413, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_182])).
% 22.74/11.85  tff(c_172, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_352])).
% 22.74/11.85  tff(c_402, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_172])).
% 22.74/11.85  tff(c_1080, plain, (![A_231, B_232, C_233]: (m1_pre_topc(k1_tsep_1(A_231, B_232, C_233), A_231) | ~m1_pre_topc(C_233, A_231) | v2_struct_0(C_233) | ~m1_pre_topc(B_232, A_231) | v2_struct_0(B_232) | ~l1_pre_topc(A_231) | v2_struct_0(A_231))), inference(cnfTransformation, [status(thm)], [f_137])).
% 22.74/11.85  tff(c_1103, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_80, c_1080])).
% 22.74/11.85  tff(c_1119, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_86, c_82, c_1103])).
% 22.74/11.85  tff(c_1120, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_106, c_88, c_84, c_1119])).
% 22.74/11.85  tff(c_592, plain, (![A_191, B_192, C_193, D_194]: (k2_partfun1(A_191, B_192, C_193, D_194)=k7_relat_1(C_193, D_194) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(A_191, B_192))) | ~v1_funct_1(C_193))), inference(cnfTransformation, [status(thm)], [f_62])).
% 22.74/11.85  tff(c_598, plain, (![D_194]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_194)=k7_relat_1('#skF_3', D_194) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_90, c_592])).
% 22.74/11.85  tff(c_610, plain, (![D_194]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_194)=k7_relat_1('#skF_3', D_194))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_598])).
% 22.74/11.85  tff(c_1643, plain, (![A_247, B_248, C_249, D_250]: (k2_partfun1(u1_struct_0(A_247), u1_struct_0(B_248), C_249, u1_struct_0(D_250))=k2_tmap_1(A_247, B_248, C_249, D_250) | ~m1_pre_topc(D_250, A_247) | ~m1_subset_1(C_249, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_247), u1_struct_0(B_248)))) | ~v1_funct_2(C_249, u1_struct_0(A_247), u1_struct_0(B_248)) | ~v1_funct_1(C_249) | ~l1_pre_topc(B_248) | ~v2_pre_topc(B_248) | v2_struct_0(B_248) | ~l1_pre_topc(A_247) | ~v2_pre_topc(A_247) | v2_struct_0(A_247))), inference(cnfTransformation, [status(thm)], [f_115])).
% 22.74/11.85  tff(c_1649, plain, (![D_250]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_250))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_250) | ~m1_pre_topc(D_250, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_90, c_1643])).
% 22.74/11.85  tff(c_1663, plain, (![D_250]: (k7_relat_1('#skF_3', u1_struct_0(D_250))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_250) | ~m1_pre_topc(D_250, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_98, c_96, c_94, c_92, c_610, c_1649])).
% 22.74/11.85  tff(c_1748, plain, (![D_251]: (k7_relat_1('#skF_3', u1_struct_0(D_251))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_251) | ~m1_pre_topc(D_251, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_106, c_100, c_1663])).
% 22.74/11.85  tff(c_1754, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1748, c_369])).
% 22.74/11.85  tff(c_1763, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1120, c_1754])).
% 22.74/11.85  tff(c_162, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_352])).
% 22.74/11.85  tff(c_479, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_162])).
% 22.74/11.85  tff(c_152, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_352])).
% 22.74/11.85  tff(c_344, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_152])).
% 22.74/11.85  tff(c_142, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_352])).
% 22.74/11.85  tff(c_436, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_142])).
% 22.74/11.85  tff(c_132, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_352])).
% 22.74/11.85  tff(c_401, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2')), inference(splitLeft, [status(thm)], [c_132])).
% 22.74/11.85  tff(c_122, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_352])).
% 22.74/11.85  tff(c_504, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_122])).
% 22.74/11.85  tff(c_5015, plain, (![E_374, A_372, B_371, D_370, C_373]: (v5_pre_topc(k2_tmap_1(A_372, B_371, E_374, k1_tsep_1(A_372, C_373, D_370)), k1_tsep_1(A_372, C_373, D_370), B_371) | ~m1_subset_1(k2_tmap_1(A_372, B_371, E_374, D_370), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_370), u1_struct_0(B_371)))) | ~v5_pre_topc(k2_tmap_1(A_372, B_371, E_374, D_370), D_370, B_371) | ~v1_funct_2(k2_tmap_1(A_372, B_371, E_374, D_370), u1_struct_0(D_370), u1_struct_0(B_371)) | ~v1_funct_1(k2_tmap_1(A_372, B_371, E_374, D_370)) | ~m1_subset_1(k2_tmap_1(A_372, B_371, E_374, C_373), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_373), u1_struct_0(B_371)))) | ~v5_pre_topc(k2_tmap_1(A_372, B_371, E_374, C_373), C_373, B_371) | ~v1_funct_2(k2_tmap_1(A_372, B_371, E_374, C_373), u1_struct_0(C_373), u1_struct_0(B_371)) | ~v1_funct_1(k2_tmap_1(A_372, B_371, E_374, C_373)) | ~m1_subset_1(E_374, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_372), u1_struct_0(B_371)))) | ~v1_funct_2(E_374, u1_struct_0(A_372), u1_struct_0(B_371)) | ~v1_funct_1(E_374) | ~r4_tsep_1(A_372, C_373, D_370) | ~m1_pre_topc(D_370, A_372) | v2_struct_0(D_370) | ~m1_pre_topc(C_373, A_372) | v2_struct_0(C_373) | ~l1_pre_topc(B_371) | ~v2_pre_topc(B_371) | v2_struct_0(B_371) | ~l1_pre_topc(A_372) | ~v2_pre_topc(A_372) | v2_struct_0(A_372))), inference(cnfTransformation, [status(thm)], [f_230])).
% 22.74/11.85  tff(c_5023, plain, (![C_373]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', C_373, '#skF_5')), k1_tsep_1('#skF_1', C_373, '#skF_5'), '#skF_2') | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_373), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_373), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_373), C_373, '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_373), u1_struct_0(C_373), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_373)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~r4_tsep_1('#skF_1', C_373, '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc(C_373, '#skF_1') | v2_struct_0(C_373) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_504, c_5015])).
% 22.74/11.85  tff(c_5039, plain, (![C_373]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', C_373, '#skF_5')), k1_tsep_1('#skF_1', C_373, '#skF_5'), '#skF_2') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_373), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_373), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_373), C_373, '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_373), u1_struct_0(C_373), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_373)) | ~r4_tsep_1('#skF_1', C_373, '#skF_5') | v2_struct_0('#skF_5') | ~m1_pre_topc(C_373, '#skF_1') | v2_struct_0(C_373) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_98, c_96, c_82, c_94, c_92, c_90, c_344, c_436, c_401, c_5023])).
% 22.74/11.85  tff(c_13860, plain, (![C_516]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', C_516, '#skF_5')), k1_tsep_1('#skF_1', C_516, '#skF_5'), '#skF_2') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_516), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_516), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_516), C_516, '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_516), u1_struct_0(C_516), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_516)) | ~r4_tsep_1('#skF_1', C_516, '#skF_5') | ~m1_pre_topc(C_516, '#skF_1') | v2_struct_0(C_516))), inference(negUnitSimplification, [status(thm)], [c_106, c_100, c_84, c_5039])).
% 22.74/11.85  tff(c_13885, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_2') | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_479, c_13860])).
% 22.74/11.85  tff(c_13912, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_78, c_304, c_413, c_402, c_80, c_1763, c_80, c_13885])).
% 22.74/11.85  tff(c_13914, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_1860, c_13912])).
% 22.74/11.85  tff(c_13916, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_1544])).
% 22.74/11.85  tff(c_108, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_352])).
% 22.74/11.85  tff(c_206, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_108])).
% 22.74/11.85  tff(c_216, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_206])).
% 22.74/11.85  tff(c_226, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_216])).
% 22.74/11.85  tff(c_14231, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13916, c_304, c_413, c_402, c_479, c_344, c_436, c_401, c_504, c_226])).
% 22.74/11.85  tff(c_14232, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_122])).
% 22.74/11.85  tff(c_18180, plain, (![B_693, C_695, E_696, A_694, D_692]: (m1_subset_1(k2_tmap_1(A_694, B_693, E_696, D_692), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_692), u1_struct_0(B_693)))) | ~m1_subset_1(k2_tmap_1(A_694, B_693, E_696, k1_tsep_1(A_694, C_695, D_692)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_694, C_695, D_692)), u1_struct_0(B_693)))) | ~v5_pre_topc(k2_tmap_1(A_694, B_693, E_696, k1_tsep_1(A_694, C_695, D_692)), k1_tsep_1(A_694, C_695, D_692), B_693) | ~v1_funct_2(k2_tmap_1(A_694, B_693, E_696, k1_tsep_1(A_694, C_695, D_692)), u1_struct_0(k1_tsep_1(A_694, C_695, D_692)), u1_struct_0(B_693)) | ~v1_funct_1(k2_tmap_1(A_694, B_693, E_696, k1_tsep_1(A_694, C_695, D_692))) | ~m1_subset_1(E_696, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_694), u1_struct_0(B_693)))) | ~v1_funct_2(E_696, u1_struct_0(A_694), u1_struct_0(B_693)) | ~v1_funct_1(E_696) | ~r4_tsep_1(A_694, C_695, D_692) | ~m1_pre_topc(D_692, A_694) | v2_struct_0(D_692) | ~m1_pre_topc(C_695, A_694) | v2_struct_0(C_695) | ~l1_pre_topc(B_693) | ~v2_pre_topc(B_693) | v2_struct_0(B_693) | ~l1_pre_topc(A_694) | ~v2_pre_topc(A_694) | v2_struct_0(A_694))), inference(cnfTransformation, [status(thm)], [f_230])).
% 22.74/11.85  tff(c_18222, plain, (![B_693, E_696]: (m1_subset_1(k2_tmap_1('#skF_1', B_693, E_696, '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_693)))) | ~m1_subset_1(k2_tmap_1('#skF_1', B_693, E_696, '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_693)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_693, E_696, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_693) | ~v1_funct_2(k2_tmap_1('#skF_1', B_693, E_696, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_693)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_693, E_696, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'))) | ~m1_subset_1(E_696, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_693)))) | ~v1_funct_2(E_696, u1_struct_0('#skF_1'), u1_struct_0(B_693)) | ~v1_funct_1(E_696) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_693) | ~v2_pre_topc(B_693) | v2_struct_0(B_693) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_80, c_18180])).
% 22.74/11.85  tff(c_18258, plain, (![B_693, E_696]: (m1_subset_1(k2_tmap_1('#skF_1', B_693, E_696, '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_693)))) | ~m1_subset_1(k2_tmap_1('#skF_1', B_693, E_696, '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_693)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_693, E_696, '#skF_1'), '#skF_1', B_693) | ~v1_funct_2(k2_tmap_1('#skF_1', B_693, E_696, '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0(B_693)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_693, E_696, '#skF_1')) | ~m1_subset_1(E_696, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_693)))) | ~v1_funct_2(E_696, u1_struct_0('#skF_1'), u1_struct_0(B_693)) | ~v1_funct_1(E_696) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_693) | ~v2_pre_topc(B_693) | v2_struct_0(B_693) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_86, c_82, c_78, c_80, c_80, c_80, c_80, c_80, c_80, c_18222])).
% 22.74/11.85  tff(c_33446, plain, (![B_925, E_926]: (m1_subset_1(k2_tmap_1('#skF_1', B_925, E_926, '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_925)))) | ~m1_subset_1(k2_tmap_1('#skF_1', B_925, E_926, '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_925)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_925, E_926, '#skF_1'), '#skF_1', B_925) | ~v1_funct_2(k2_tmap_1('#skF_1', B_925, E_926, '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0(B_925)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_925, E_926, '#skF_1')) | ~m1_subset_1(E_926, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_925)))) | ~v1_funct_2(E_926, u1_struct_0('#skF_1'), u1_struct_0(B_925)) | ~v1_funct_1(E_926) | ~l1_pre_topc(B_925) | ~v2_pre_topc(B_925) | v2_struct_0(B_925))), inference(negUnitSimplification, [status(thm)], [c_106, c_88, c_84, c_18258])).
% 22.74/11.85  tff(c_14233, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_122])).
% 22.74/11.85  tff(c_33471, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), '#skF_1', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_33446, c_14233])).
% 22.74/11.85  tff(c_33537, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_94, c_92, c_90, c_94, c_15764, c_92, c_15764, c_14232, c_15764, c_90, c_15764, c_33471])).
% 22.74/11.85  tff(c_33539, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_33537])).
% 22.74/11.85  tff(c_33541, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_162])).
% 22.74/11.85  tff(c_33944, plain, (![A_968, B_969, C_970]: (m1_pre_topc(k1_tsep_1(A_968, B_969, C_970), A_968) | ~m1_pre_topc(C_970, A_968) | v2_struct_0(C_970) | ~m1_pre_topc(B_969, A_968) | v2_struct_0(B_969) | ~l1_pre_topc(A_968) | v2_struct_0(A_968))), inference(cnfTransformation, [status(thm)], [f_137])).
% 22.74/11.85  tff(c_33967, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_80, c_33944])).
% 22.74/11.85  tff(c_33983, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_86, c_82, c_33967])).
% 22.74/11.85  tff(c_33984, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_106, c_88, c_84, c_33983])).
% 22.74/11.85  tff(c_33602, plain, (![A_932, B_933, C_934, D_935]: (k2_partfun1(A_932, B_933, C_934, D_935)=k7_relat_1(C_934, D_935) | ~m1_subset_1(C_934, k1_zfmisc_1(k2_zfmisc_1(A_932, B_933))) | ~v1_funct_1(C_934))), inference(cnfTransformation, [status(thm)], [f_62])).
% 22.74/11.85  tff(c_33604, plain, (![D_935]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_935)=k7_relat_1('#skF_3', D_935) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_90, c_33602])).
% 22.74/11.85  tff(c_33610, plain, (![D_935]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_935)=k7_relat_1('#skF_3', D_935))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_33604])).
% 22.74/11.85  tff(c_34830, plain, (![A_990, B_991, C_992, D_993]: (k2_partfun1(u1_struct_0(A_990), u1_struct_0(B_991), C_992, u1_struct_0(D_993))=k2_tmap_1(A_990, B_991, C_992, D_993) | ~m1_pre_topc(D_993, A_990) | ~m1_subset_1(C_992, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_990), u1_struct_0(B_991)))) | ~v1_funct_2(C_992, u1_struct_0(A_990), u1_struct_0(B_991)) | ~v1_funct_1(C_992) | ~l1_pre_topc(B_991) | ~v2_pre_topc(B_991) | v2_struct_0(B_991) | ~l1_pre_topc(A_990) | ~v2_pre_topc(A_990) | v2_struct_0(A_990))), inference(cnfTransformation, [status(thm)], [f_115])).
% 22.74/11.85  tff(c_34836, plain, (![D_993]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_993))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_993) | ~m1_pre_topc(D_993, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_90, c_34830])).
% 22.74/11.85  tff(c_34848, plain, (![D_993]: (k7_relat_1('#skF_3', u1_struct_0(D_993))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_993) | ~m1_pre_topc(D_993, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_98, c_96, c_94, c_92, c_33610, c_34836])).
% 22.74/11.85  tff(c_34986, plain, (![D_997]: (k7_relat_1('#skF_3', u1_struct_0(D_997))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_997) | ~m1_pre_topc(D_997, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_106, c_100, c_34848])).
% 22.74/11.85  tff(c_34992, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_34986, c_369])).
% 22.74/11.85  tff(c_35004, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_33984, c_34992])).
% 22.74/11.85  tff(c_33540, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_162])).
% 22.74/11.85  tff(c_37218, plain, (![B_1061, E_1064, D_1060, C_1063, A_1062]: (m1_subset_1(k2_tmap_1(A_1062, B_1061, E_1064, C_1063), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1063), u1_struct_0(B_1061)))) | ~m1_subset_1(k2_tmap_1(A_1062, B_1061, E_1064, k1_tsep_1(A_1062, C_1063, D_1060)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_1062, C_1063, D_1060)), u1_struct_0(B_1061)))) | ~v5_pre_topc(k2_tmap_1(A_1062, B_1061, E_1064, k1_tsep_1(A_1062, C_1063, D_1060)), k1_tsep_1(A_1062, C_1063, D_1060), B_1061) | ~v1_funct_2(k2_tmap_1(A_1062, B_1061, E_1064, k1_tsep_1(A_1062, C_1063, D_1060)), u1_struct_0(k1_tsep_1(A_1062, C_1063, D_1060)), u1_struct_0(B_1061)) | ~v1_funct_1(k2_tmap_1(A_1062, B_1061, E_1064, k1_tsep_1(A_1062, C_1063, D_1060))) | ~m1_subset_1(E_1064, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1062), u1_struct_0(B_1061)))) | ~v1_funct_2(E_1064, u1_struct_0(A_1062), u1_struct_0(B_1061)) | ~v1_funct_1(E_1064) | ~r4_tsep_1(A_1062, C_1063, D_1060) | ~m1_pre_topc(D_1060, A_1062) | v2_struct_0(D_1060) | ~m1_pre_topc(C_1063, A_1062) | v2_struct_0(C_1063) | ~l1_pre_topc(B_1061) | ~v2_pre_topc(B_1061) | v2_struct_0(B_1061) | ~l1_pre_topc(A_1062) | ~v2_pre_topc(A_1062) | v2_struct_0(A_1062))), inference(cnfTransformation, [status(thm)], [f_230])).
% 22.74/11.85  tff(c_37278, plain, (![B_1061, E_1064]: (m1_subset_1(k2_tmap_1('#skF_1', B_1061, E_1064, '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_1061)))) | ~m1_subset_1(k2_tmap_1('#skF_1', B_1061, E_1064, '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_1061)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_1061, E_1064, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_1061) | ~v1_funct_2(k2_tmap_1('#skF_1', B_1061, E_1064, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_1061)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_1061, E_1064, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'))) | ~m1_subset_1(E_1064, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_1061)))) | ~v1_funct_2(E_1064, u1_struct_0('#skF_1'), u1_struct_0(B_1061)) | ~v1_funct_1(E_1064) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_1061) | ~v2_pre_topc(B_1061) | v2_struct_0(B_1061) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_80, c_37218])).
% 22.74/11.85  tff(c_37332, plain, (![B_1061, E_1064]: (m1_subset_1(k2_tmap_1('#skF_1', B_1061, E_1064, '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_1061)))) | ~m1_subset_1(k2_tmap_1('#skF_1', B_1061, E_1064, '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_1061)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_1061, E_1064, '#skF_1'), '#skF_1', B_1061) | ~v1_funct_2(k2_tmap_1('#skF_1', B_1061, E_1064, '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0(B_1061)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_1061, E_1064, '#skF_1')) | ~m1_subset_1(E_1064, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_1061)))) | ~v1_funct_2(E_1064, u1_struct_0('#skF_1'), u1_struct_0(B_1061)) | ~v1_funct_1(E_1064) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_1061) | ~v2_pre_topc(B_1061) | v2_struct_0(B_1061) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_86, c_82, c_78, c_80, c_80, c_80, c_80, c_80, c_80, c_37278])).
% 22.74/11.85  tff(c_52345, plain, (![B_1307, E_1308]: (m1_subset_1(k2_tmap_1('#skF_1', B_1307, E_1308, '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_1307)))) | ~m1_subset_1(k2_tmap_1('#skF_1', B_1307, E_1308, '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_1307)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_1307, E_1308, '#skF_1'), '#skF_1', B_1307) | ~v1_funct_2(k2_tmap_1('#skF_1', B_1307, E_1308, '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0(B_1307)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_1307, E_1308, '#skF_1')) | ~m1_subset_1(E_1308, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_1307)))) | ~v1_funct_2(E_1308, u1_struct_0('#skF_1'), u1_struct_0(B_1307)) | ~v1_funct_1(E_1308) | ~l1_pre_topc(B_1307) | ~v2_pre_topc(B_1307) | v2_struct_0(B_1307))), inference(negUnitSimplification, [status(thm)], [c_106, c_88, c_84, c_37332])).
% 22.74/11.85  tff(c_52363, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), '#skF_1', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_35004, c_52345])).
% 22.74/11.85  tff(c_52380, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_94, c_92, c_90, c_94, c_35004, c_92, c_35004, c_33540, c_35004, c_90, c_52363])).
% 22.74/11.85  tff(c_52382, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_33541, c_52380])).
% 22.74/11.85  tff(c_52383, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_142])).
% 22.74/11.85  tff(c_54277, plain, (![A_1411, B_1412, C_1413, D_1414]: (v1_funct_2(k2_tmap_1(A_1411, B_1412, C_1413, D_1414), u1_struct_0(D_1414), u1_struct_0(B_1412)) | ~m1_pre_topc(D_1414, A_1411) | v2_struct_0(D_1414) | ~m1_subset_1(C_1413, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1411), u1_struct_0(B_1412)))) | ~v5_pre_topc(C_1413, A_1411, B_1412) | ~v1_funct_2(C_1413, u1_struct_0(A_1411), u1_struct_0(B_1412)) | ~v1_funct_1(C_1413) | ~l1_pre_topc(B_1412) | ~v2_pre_topc(B_1412) | v2_struct_0(B_1412) | ~l1_pre_topc(A_1411) | ~v2_pre_topc(A_1411) | v2_struct_0(A_1411))), inference(cnfTransformation, [status(thm)], [f_170])).
% 22.74/11.85  tff(c_54283, plain, (![D_1414]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_1414), u1_struct_0(D_1414), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_1414, '#skF_1') | v2_struct_0(D_1414) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_90, c_54277])).
% 22.74/11.85  tff(c_54295, plain, (![D_1414]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_1414), u1_struct_0(D_1414), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_1414, '#skF_1') | v2_struct_0(D_1414) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_98, c_96, c_94, c_92, c_52383, c_54283])).
% 22.74/11.85  tff(c_54812, plain, (![D_1434]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_1434), u1_struct_0(D_1434), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_1434, '#skF_1') | v2_struct_0(D_1434))), inference(negUnitSimplification, [status(thm)], [c_106, c_100, c_54295])).
% 22.74/11.85  tff(c_52384, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_142])).
% 22.74/11.85  tff(c_54815, plain, (~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_54812, c_52384])).
% 22.74/11.85  tff(c_54824, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_54815])).
% 22.74/11.85  tff(c_54826, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_54824])).
% 22.74/11.85  tff(c_54827, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_182])).
% 22.74/11.85  tff(c_56574, plain, (![A_1525, B_1526, C_1527, D_1528]: (v1_funct_2(k2_tmap_1(A_1525, B_1526, C_1527, D_1528), u1_struct_0(D_1528), u1_struct_0(B_1526)) | ~m1_pre_topc(D_1528, A_1525) | v2_struct_0(D_1528) | ~m1_subset_1(C_1527, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1525), u1_struct_0(B_1526)))) | ~v5_pre_topc(C_1527, A_1525, B_1526) | ~v1_funct_2(C_1527, u1_struct_0(A_1525), u1_struct_0(B_1526)) | ~v1_funct_1(C_1527) | ~l1_pre_topc(B_1526) | ~v2_pre_topc(B_1526) | v2_struct_0(B_1526) | ~l1_pre_topc(A_1525) | ~v2_pre_topc(A_1525) | v2_struct_0(A_1525))), inference(cnfTransformation, [status(thm)], [f_170])).
% 22.74/11.85  tff(c_56580, plain, (![D_1528]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_1528), u1_struct_0(D_1528), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_1528, '#skF_1') | v2_struct_0(D_1528) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_90, c_56574])).
% 22.74/11.85  tff(c_56592, plain, (![D_1528]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_1528), u1_struct_0(D_1528), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_1528, '#skF_1') | v2_struct_0(D_1528) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_98, c_96, c_94, c_92, c_54827, c_56580])).
% 22.74/11.85  tff(c_56622, plain, (![D_1531]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_1531), u1_struct_0(D_1531), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_1531, '#skF_1') | v2_struct_0(D_1531))), inference(negUnitSimplification, [status(thm)], [c_106, c_100, c_56592])).
% 22.74/11.85  tff(c_54828, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_182])).
% 22.74/11.85  tff(c_56625, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56622, c_54828])).
% 22.74/11.85  tff(c_56634, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_56625])).
% 22.74/11.85  tff(c_56636, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_56634])).
% 22.74/11.85  tff(c_56637, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_172])).
% 22.74/11.85  tff(c_58213, plain, (![A_1632, B_1633, C_1634, D_1635]: (v5_pre_topc(k2_tmap_1(A_1632, B_1633, C_1634, D_1635), D_1635, B_1633) | ~m1_pre_topc(D_1635, A_1632) | v2_struct_0(D_1635) | ~m1_subset_1(C_1634, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1632), u1_struct_0(B_1633)))) | ~v5_pre_topc(C_1634, A_1632, B_1633) | ~v1_funct_2(C_1634, u1_struct_0(A_1632), u1_struct_0(B_1633)) | ~v1_funct_1(C_1634) | ~l1_pre_topc(B_1633) | ~v2_pre_topc(B_1633) | v2_struct_0(B_1633) | ~l1_pre_topc(A_1632) | ~v2_pre_topc(A_1632) | v2_struct_0(A_1632))), inference(cnfTransformation, [status(thm)], [f_170])).
% 22.74/11.85  tff(c_58215, plain, (![D_1635]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_1635), D_1635, '#skF_2') | ~m1_pre_topc(D_1635, '#skF_1') | v2_struct_0(D_1635) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_90, c_58213])).
% 22.74/11.85  tff(c_58221, plain, (![D_1635]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_1635), D_1635, '#skF_2') | ~m1_pre_topc(D_1635, '#skF_1') | v2_struct_0(D_1635) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_98, c_96, c_94, c_92, c_56637, c_58215])).
% 22.74/11.85  tff(c_58947, plain, (![D_1653]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_1653), D_1653, '#skF_2') | ~m1_pre_topc(D_1653, '#skF_1') | v2_struct_0(D_1653))), inference(negUnitSimplification, [status(thm)], [c_106, c_100, c_58221])).
% 22.74/11.85  tff(c_56638, plain, (~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_172])).
% 22.74/11.85  tff(c_58950, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_58947, c_56638])).
% 22.74/11.85  tff(c_58956, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_58950])).
% 22.74/11.85  tff(c_58958, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_58956])).
% 22.74/11.85  tff(c_58959, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_132])).
% 22.74/11.85  tff(c_60448, plain, (![A_1737, B_1738, C_1739, D_1740]: (v5_pre_topc(k2_tmap_1(A_1737, B_1738, C_1739, D_1740), D_1740, B_1738) | ~m1_pre_topc(D_1740, A_1737) | v2_struct_0(D_1740) | ~m1_subset_1(C_1739, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1737), u1_struct_0(B_1738)))) | ~v5_pre_topc(C_1739, A_1737, B_1738) | ~v1_funct_2(C_1739, u1_struct_0(A_1737), u1_struct_0(B_1738)) | ~v1_funct_1(C_1739) | ~l1_pre_topc(B_1738) | ~v2_pre_topc(B_1738) | v2_struct_0(B_1738) | ~l1_pre_topc(A_1737) | ~v2_pre_topc(A_1737) | v2_struct_0(A_1737))), inference(cnfTransformation, [status(thm)], [f_170])).
% 22.74/11.85  tff(c_60450, plain, (![D_1740]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_1740), D_1740, '#skF_2') | ~m1_pre_topc(D_1740, '#skF_1') | v2_struct_0(D_1740) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_90, c_60448])).
% 22.74/11.85  tff(c_60456, plain, (![D_1740]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_1740), D_1740, '#skF_2') | ~m1_pre_topc(D_1740, '#skF_1') | v2_struct_0(D_1740) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_98, c_96, c_94, c_92, c_58959, c_60450])).
% 22.74/11.85  tff(c_60643, plain, (![D_1741]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_1741), D_1741, '#skF_2') | ~m1_pre_topc(D_1741, '#skF_1') | v2_struct_0(D_1741))), inference(negUnitSimplification, [status(thm)], [c_106, c_100, c_60456])).
% 22.74/11.85  tff(c_58960, plain, (~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_132])).
% 22.74/11.85  tff(c_60646, plain, (~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_60643, c_58960])).
% 22.74/11.85  tff(c_60652, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_60646])).
% 22.74/11.85  tff(c_60654, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_60652])).
% 22.74/11.85  tff(c_60655, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_152])).
% 22.74/11.85  tff(c_62031, plain, (![A_1849, B_1850, C_1851, D_1852]: (v1_funct_1(k2_tmap_1(A_1849, B_1850, C_1851, D_1852)) | ~m1_pre_topc(D_1852, A_1849) | v2_struct_0(D_1852) | ~m1_subset_1(C_1851, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1849), u1_struct_0(B_1850)))) | ~v5_pre_topc(C_1851, A_1849, B_1850) | ~v1_funct_2(C_1851, u1_struct_0(A_1849), u1_struct_0(B_1850)) | ~v1_funct_1(C_1851) | ~l1_pre_topc(B_1850) | ~v2_pre_topc(B_1850) | v2_struct_0(B_1850) | ~l1_pre_topc(A_1849) | ~v2_pre_topc(A_1849) | v2_struct_0(A_1849))), inference(cnfTransformation, [status(thm)], [f_170])).
% 22.74/11.85  tff(c_62033, plain, (![D_1852]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_1852)) | ~m1_pre_topc(D_1852, '#skF_1') | v2_struct_0(D_1852) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_90, c_62031])).
% 22.74/11.85  tff(c_62039, plain, (![D_1852]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_1852)) | ~m1_pre_topc(D_1852, '#skF_1') | v2_struct_0(D_1852) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_98, c_96, c_94, c_92, c_60655, c_62033])).
% 22.74/11.85  tff(c_62555, plain, (![D_1861]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_1861)) | ~m1_pre_topc(D_1861, '#skF_1') | v2_struct_0(D_1861))), inference(negUnitSimplification, [status(thm)], [c_106, c_100, c_62039])).
% 22.74/11.85  tff(c_60656, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_152])).
% 22.74/11.85  tff(c_62558, plain, (~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_62555, c_60656])).
% 22.74/11.85  tff(c_62561, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_62558])).
% 22.74/11.85  tff(c_62563, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_62561])).
% 22.74/11.85  tff(c_62564, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_192])).
% 22.74/11.85  tff(c_63980, plain, (![A_1979, B_1980, C_1981, D_1982]: (v1_funct_1(k2_tmap_1(A_1979, B_1980, C_1981, D_1982)) | ~m1_pre_topc(D_1982, A_1979) | v2_struct_0(D_1982) | ~m1_subset_1(C_1981, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1979), u1_struct_0(B_1980)))) | ~v5_pre_topc(C_1981, A_1979, B_1980) | ~v1_funct_2(C_1981, u1_struct_0(A_1979), u1_struct_0(B_1980)) | ~v1_funct_1(C_1981) | ~l1_pre_topc(B_1980) | ~v2_pre_topc(B_1980) | v2_struct_0(B_1980) | ~l1_pre_topc(A_1979) | ~v2_pre_topc(A_1979) | v2_struct_0(A_1979))), inference(cnfTransformation, [status(thm)], [f_170])).
% 22.74/11.85  tff(c_63982, plain, (![D_1982]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_1982)) | ~m1_pre_topc(D_1982, '#skF_1') | v2_struct_0(D_1982) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_90, c_63980])).
% 22.74/11.85  tff(c_63988, plain, (![D_1982]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_1982)) | ~m1_pre_topc(D_1982, '#skF_1') | v2_struct_0(D_1982) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_98, c_96, c_94, c_92, c_62564, c_63982])).
% 22.74/11.85  tff(c_64504, plain, (![D_1991]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_1991)) | ~m1_pre_topc(D_1991, '#skF_1') | v2_struct_0(D_1991))), inference(negUnitSimplification, [status(thm)], [c_106, c_100, c_63988])).
% 22.74/11.85  tff(c_62565, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_192])).
% 22.74/11.85  tff(c_64507, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_64504, c_62565])).
% 22.74/11.85  tff(c_64510, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_64507])).
% 22.74/11.85  tff(c_64512, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_64510])).
% 22.74/11.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.74/11.85  
% 22.74/11.85  Inference rules
% 22.74/11.85  ----------------------
% 22.74/11.85  #Ref     : 0
% 22.74/11.85  #Sup     : 12569
% 22.74/11.85  #Fact    : 0
% 22.74/11.85  #Define  : 0
% 22.74/11.85  #Split   : 137
% 22.74/11.85  #Chain   : 0
% 22.74/11.85  #Close   : 0
% 22.74/11.85  
% 22.74/11.85  Ordering : KBO
% 22.74/11.85  
% 22.74/11.85  Simplification rules
% 22.74/11.85  ----------------------
% 22.74/11.85  #Subsume      : 5347
% 22.74/11.85  #Demod        : 26681
% 22.74/11.85  #Tautology    : 2178
% 22.74/11.85  #SimpNegUnit  : 2799
% 22.74/11.85  #BackRed      : 55
% 22.74/11.85  
% 22.74/11.85  #Partial instantiations: 0
% 22.74/11.85  #Strategies tried      : 1
% 22.74/11.85  
% 22.74/11.85  Timing (in seconds)
% 22.74/11.85  ----------------------
% 22.74/11.86  Preprocessing        : 0.48
% 22.74/11.86  Parsing              : 0.24
% 22.74/11.86  CNF conversion       : 0.06
% 22.74/11.86  Main loop            : 10.51
% 22.74/11.86  Inferencing          : 2.17
% 22.74/11.86  Reduction            : 5.03
% 22.74/11.86  Demodulation         : 4.13
% 22.74/11.86  BG Simplification    : 0.20
% 22.74/11.86  Subsumption          : 2.72
% 22.74/11.86  Abstraction          : 0.40
% 22.74/11.86  MUC search           : 0.00
% 22.74/11.86  Cooper               : 0.00
% 22.74/11.86  Total                : 11.06
% 22.74/11.86  Index Insertion      : 0.00
% 22.74/11.86  Index Deletion       : 0.00
% 22.74/11.86  Index Matching       : 0.00
% 22.74/11.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
