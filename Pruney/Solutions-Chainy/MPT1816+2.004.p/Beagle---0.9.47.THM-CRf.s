%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:07 EST 2020

% Result     : Theorem 8.74s
% Output     : CNFRefutation 8.74s
% Verified   : 
% Statistics : Number of formulae       :  256 (1482 expanded)
%              Number of leaves         :   39 ( 571 expanded)
%              Depth                    :   11
%              Number of atoms          :  798 (13826 expanded)
%              Number of equality atoms :   36 ( 656 expanded)
%              Maximal formula depth    :   29 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > r4_tsep_1 > v5_relat_1 > v4_relat_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(f_230,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_tmap_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_103,axiom,(
    ! [A,B,C,D] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B))))
        & l1_struct_0(D) )
     => ( v1_funct_1(k2_tmap_1(A,B,C,D))
        & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k2_tmap_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).

tff(f_167,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_85,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_163,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_tmap_1)).

tff(c_74,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_54,plain,(
    m1_pre_topc('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_205,plain,(
    ! [B_96,A_97] :
      ( l1_pre_topc(B_96)
      | ~ m1_pre_topc(B_96,A_97)
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_214,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_205])).

tff(c_221,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_214])).

tff(c_12,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_66,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_64,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_5404,plain,(
    ! [A_734,B_735,C_736,D_737] :
      ( v1_funct_1(k2_tmap_1(A_734,B_735,C_736,D_737))
      | ~ l1_struct_0(D_737)
      | ~ m1_subset_1(C_736,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_734),u1_struct_0(B_735))))
      | ~ v1_funct_2(C_736,u1_struct_0(A_734),u1_struct_0(B_735))
      | ~ v1_funct_1(C_736)
      | ~ l1_struct_0(B_735)
      | ~ l1_struct_0(A_734) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_5406,plain,(
    ! [D_737] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_737))
      | ~ l1_struct_0(D_737)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_62,c_5404])).

tff(c_5409,plain,(
    ! [D_737] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_737))
      | ~ l1_struct_0(D_737)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_5406])).

tff(c_5410,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_5409])).

tff(c_5413,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_5410])).

tff(c_5417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_5413])).

tff(c_5418,plain,(
    ! [D_737] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_737))
      | ~ l1_struct_0(D_737) ) ),
    inference(splitRight,[status(thm)],[c_5409])).

tff(c_5420,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_5418])).

tff(c_5423,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_5420])).

tff(c_5427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_5423])).

tff(c_5436,plain,(
    ! [D_742] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_742))
      | ~ l1_struct_0(D_742) ) ),
    inference(splitRight,[status(thm)],[c_5418])).

tff(c_58,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_211,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_205])).

tff(c_218,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_211])).

tff(c_5306,plain,(
    ! [A_716,B_717,C_718,D_719] :
      ( v1_funct_1(k2_tmap_1(A_716,B_717,C_718,D_719))
      | ~ l1_struct_0(D_719)
      | ~ m1_subset_1(C_718,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_716),u1_struct_0(B_717))))
      | ~ v1_funct_2(C_718,u1_struct_0(A_716),u1_struct_0(B_717))
      | ~ v1_funct_1(C_718)
      | ~ l1_struct_0(B_717)
      | ~ l1_struct_0(A_716) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_5308,plain,(
    ! [D_719] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_719))
      | ~ l1_struct_0(D_719)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_62,c_5306])).

tff(c_5311,plain,(
    ! [D_719] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_719))
      | ~ l1_struct_0(D_719)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_5308])).

tff(c_5312,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_5311])).

tff(c_5315,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_5312])).

tff(c_5319,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_5315])).

tff(c_5320,plain,(
    ! [D_719] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_719))
      | ~ l1_struct_0(D_719) ) ),
    inference(splitRight,[status(thm)],[c_5311])).

tff(c_5328,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_5320])).

tff(c_5331,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_5328])).

tff(c_5335,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_5331])).

tff(c_5346,plain,(
    ! [D_724] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_724))
      | ~ l1_struct_0(D_724) ) ),
    inference(splitRight,[status(thm)],[c_5320])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_3744,plain,(
    ! [A_425,B_426,C_427,D_428] :
      ( v1_funct_1(k2_tmap_1(A_425,B_426,C_427,D_428))
      | ~ l1_struct_0(D_428)
      | ~ m1_subset_1(C_427,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_425),u1_struct_0(B_426))))
      | ~ v1_funct_2(C_427,u1_struct_0(A_425),u1_struct_0(B_426))
      | ~ v1_funct_1(C_427)
      | ~ l1_struct_0(B_426)
      | ~ l1_struct_0(A_425) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3746,plain,(
    ! [D_428] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_428))
      | ~ l1_struct_0(D_428)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_62,c_3744])).

tff(c_3749,plain,(
    ! [D_428] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_428))
      | ~ l1_struct_0(D_428)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_3746])).

tff(c_3750,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3749])).

tff(c_3753,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_3750])).

tff(c_3757,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3753])).

tff(c_3759,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3749])).

tff(c_3758,plain,(
    ! [D_428] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_428))
      | ~ l1_struct_0(D_428) ) ),
    inference(splitRight,[status(thm)],[c_3749])).

tff(c_3760,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3758])).

tff(c_3763,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_3760])).

tff(c_3767,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3763])).

tff(c_3769,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3758])).

tff(c_3771,plain,(
    ! [A_430,B_431,C_432,D_433] :
      ( v1_funct_2(k2_tmap_1(A_430,B_431,C_432,D_433),u1_struct_0(D_433),u1_struct_0(B_431))
      | ~ l1_struct_0(D_433)
      | ~ m1_subset_1(C_432,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_430),u1_struct_0(B_431))))
      | ~ v1_funct_2(C_432,u1_struct_0(A_430),u1_struct_0(B_431))
      | ~ v1_funct_1(C_432)
      | ~ l1_struct_0(B_431)
      | ~ l1_struct_0(A_430) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3773,plain,(
    ! [D_433] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_433),u1_struct_0(D_433),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_433)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_62,c_3771])).

tff(c_3777,plain,(
    ! [D_434] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_434),u1_struct_0(D_434),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_434) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3759,c_3769,c_66,c_64,c_3773])).

tff(c_3648,plain,(
    ! [A_405,B_406,C_407,D_408] :
      ( v1_funct_1(k2_tmap_1(A_405,B_406,C_407,D_408))
      | ~ l1_struct_0(D_408)
      | ~ m1_subset_1(C_407,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_405),u1_struct_0(B_406))))
      | ~ v1_funct_2(C_407,u1_struct_0(A_405),u1_struct_0(B_406))
      | ~ v1_funct_1(C_407)
      | ~ l1_struct_0(B_406)
      | ~ l1_struct_0(A_405) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3650,plain,(
    ! [D_408] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_408))
      | ~ l1_struct_0(D_408)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_62,c_3648])).

tff(c_3653,plain,(
    ! [D_408] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_408))
      | ~ l1_struct_0(D_408)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_3650])).

tff(c_3663,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3653])).

tff(c_3666,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_3663])).

tff(c_3670,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3666])).

tff(c_3672,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3653])).

tff(c_3671,plain,(
    ! [D_408] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_408))
      | ~ l1_struct_0(D_408) ) ),
    inference(splitRight,[status(thm)],[c_3653])).

tff(c_3673,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3671])).

tff(c_3676,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_3673])).

tff(c_3680,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3676])).

tff(c_3682,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3671])).

tff(c_3684,plain,(
    ! [A_411,B_412,C_413,D_414] :
      ( v1_funct_2(k2_tmap_1(A_411,B_412,C_413,D_414),u1_struct_0(D_414),u1_struct_0(B_412))
      | ~ l1_struct_0(D_414)
      | ~ m1_subset_1(C_413,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_411),u1_struct_0(B_412))))
      | ~ v1_funct_2(C_413,u1_struct_0(A_411),u1_struct_0(B_412))
      | ~ v1_funct_1(C_413)
      | ~ l1_struct_0(B_412)
      | ~ l1_struct_0(A_411) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3686,plain,(
    ! [D_414] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_414),u1_struct_0(D_414),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_414)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_62,c_3684])).

tff(c_3712,plain,(
    ! [D_419] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_419),u1_struct_0(D_419),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_419) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3672,c_3682,c_66,c_64,c_3686])).

tff(c_3569,plain,(
    ! [A_387,B_388,C_389,D_390] :
      ( v1_funct_1(k2_tmap_1(A_387,B_388,C_389,D_390))
      | ~ l1_struct_0(D_390)
      | ~ m1_subset_1(C_389,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_387),u1_struct_0(B_388))))
      | ~ v1_funct_2(C_389,u1_struct_0(A_387),u1_struct_0(B_388))
      | ~ v1_funct_1(C_389)
      | ~ l1_struct_0(B_388)
      | ~ l1_struct_0(A_387) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3571,plain,(
    ! [D_390] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_390))
      | ~ l1_struct_0(D_390)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_62,c_3569])).

tff(c_3574,plain,(
    ! [D_390] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_390))
      | ~ l1_struct_0(D_390)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_3571])).

tff(c_3575,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3574])).

tff(c_3578,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_3575])).

tff(c_3582,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3578])).

tff(c_3584,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3574])).

tff(c_3583,plain,(
    ! [D_390] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_390))
      | ~ l1_struct_0(D_390) ) ),
    inference(splitRight,[status(thm)],[c_3574])).

tff(c_3585,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3583])).

tff(c_3588,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_3585])).

tff(c_3592,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3588])).

tff(c_3594,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3583])).

tff(c_3603,plain,(
    ! [A_397,B_398,C_399,D_400] :
      ( m1_subset_1(k2_tmap_1(A_397,B_398,C_399,D_400),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_400),u1_struct_0(B_398))))
      | ~ l1_struct_0(D_400)
      | ~ m1_subset_1(C_399,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_397),u1_struct_0(B_398))))
      | ~ v1_funct_2(C_399,u1_struct_0(A_397),u1_struct_0(B_398))
      | ~ v1_funct_1(C_399)
      | ~ l1_struct_0(B_398)
      | ~ l1_struct_0(A_397) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3444,plain,(
    ! [A_362,B_363,C_364,D_365] :
      ( v1_funct_1(k2_tmap_1(A_362,B_363,C_364,D_365))
      | ~ l1_struct_0(D_365)
      | ~ m1_subset_1(C_364,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_362),u1_struct_0(B_363))))
      | ~ v1_funct_2(C_364,u1_struct_0(A_362),u1_struct_0(B_363))
      | ~ v1_funct_1(C_364)
      | ~ l1_struct_0(B_363)
      | ~ l1_struct_0(A_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3448,plain,(
    ! [D_365] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_365))
      | ~ l1_struct_0(D_365)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_62,c_3444])).

tff(c_3454,plain,(
    ! [D_365] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_365))
      | ~ l1_struct_0(D_365)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_3448])).

tff(c_3455,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3454])).

tff(c_3469,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_3455])).

tff(c_3473,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3469])).

tff(c_3475,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3454])).

tff(c_3474,plain,(
    ! [D_365] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_365))
      | ~ l1_struct_0(D_365) ) ),
    inference(splitRight,[status(thm)],[c_3454])).

tff(c_3476,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3474])).

tff(c_3480,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_3476])).

tff(c_3484,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3480])).

tff(c_3486,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3474])).

tff(c_3516,plain,(
    ! [A_378,B_379,C_380,D_381] :
      ( m1_subset_1(k2_tmap_1(A_378,B_379,C_380,D_381),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_381),u1_struct_0(B_379))))
      | ~ l1_struct_0(D_381)
      | ~ m1_subset_1(C_380,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_378),u1_struct_0(B_379))))
      | ~ v1_funct_2(C_380,u1_struct_0(A_378),u1_struct_0(B_379))
      | ~ v1_funct_1(C_380)
      | ~ l1_struct_0(B_379)
      | ~ l1_struct_0(A_378) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_164,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_249,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_154,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_253,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_144,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_250,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_134,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_254,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_124,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_248,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_114,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_252,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_104,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_251,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_94,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_297,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_80,plain,
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
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_178,plain,
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
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_80])).

tff(c_188,plain,
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
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_178])).

tff(c_198,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_188])).

tff(c_631,plain,(
    ~ v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_253,c_250,c_254,c_248,c_252,c_251,c_297,c_198])).

tff(c_50,plain,(
    r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_48,plain,(
    ! [A_67] :
      ( m1_pre_topc(A_67,A_67)
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_76,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_70,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_273,plain,(
    ! [A_109,B_110,C_111,D_112] :
      ( k2_partfun1(A_109,B_110,C_111,D_112) = k7_relat_1(C_111,D_112)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110)))
      | ~ v1_funct_1(C_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_277,plain,(
    ! [D_112] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_112) = k7_relat_1('#skF_3',D_112)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_62,c_273])).

tff(c_283,plain,(
    ! [D_112] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_112) = k7_relat_1('#skF_3',D_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_277])).

tff(c_507,plain,(
    ! [A_148,B_149,C_150,D_151] :
      ( k2_partfun1(u1_struct_0(A_148),u1_struct_0(B_149),C_150,u1_struct_0(D_151)) = k2_tmap_1(A_148,B_149,C_150,D_151)
      | ~ m1_pre_topc(D_151,A_148)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_148),u1_struct_0(B_149))))
      | ~ v1_funct_2(C_150,u1_struct_0(A_148),u1_struct_0(B_149))
      | ~ v1_funct_1(C_150)
      | ~ l1_pre_topc(B_149)
      | ~ v2_pre_topc(B_149)
      | v2_struct_0(B_149)
      | ~ l1_pre_topc(A_148)
      | ~ v2_pre_topc(A_148)
      | v2_struct_0(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_515,plain,(
    ! [D_151] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_151)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_151)
      | ~ m1_pre_topc(D_151,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_62,c_507])).

tff(c_527,plain,(
    ! [D_151] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_151)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_151)
      | ~ m1_pre_topc(D_151,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_68,c_66,c_64,c_283,c_515])).

tff(c_529,plain,(
    ! [D_152] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_152)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_152)
      | ~ m1_pre_topc(D_152,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_72,c_527])).

tff(c_222,plain,(
    ! [C_98,A_99,B_100] :
      ( v1_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_226,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_222])).

tff(c_232,plain,(
    ! [C_104,A_105,B_106] :
      ( v4_relat_1(C_104,A_105)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_236,plain,(
    v4_relat_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_232])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k7_relat_1(B_2,A_1) = B_2
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_240,plain,
    ( k7_relat_1('#skF_3',u1_struct_0('#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_236,c_2])).

tff(c_243,plain,(
    k7_relat_1('#skF_3',u1_struct_0('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_240])).

tff(c_535,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_529,c_243])).

tff(c_544,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_535])).

tff(c_547,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_544])).

tff(c_551,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_547])).

tff(c_552,plain,(
    k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_535])).

tff(c_52,plain,(
    k1_tsep_1('#skF_1','#skF_4','#skF_5') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_2955,plain,(
    ! [C_345,B_341,E_342,A_343,D_344] :
      ( v5_pre_topc(k2_tmap_1(A_343,B_341,E_342,k1_tsep_1(A_343,C_345,D_344)),k1_tsep_1(A_343,C_345,D_344),B_341)
      | ~ m1_subset_1(k2_tmap_1(A_343,B_341,E_342,D_344),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_344),u1_struct_0(B_341))))
      | ~ v5_pre_topc(k2_tmap_1(A_343,B_341,E_342,D_344),D_344,B_341)
      | ~ v1_funct_2(k2_tmap_1(A_343,B_341,E_342,D_344),u1_struct_0(D_344),u1_struct_0(B_341))
      | ~ v1_funct_1(k2_tmap_1(A_343,B_341,E_342,D_344))
      | ~ m1_subset_1(k2_tmap_1(A_343,B_341,E_342,C_345),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_345),u1_struct_0(B_341))))
      | ~ v5_pre_topc(k2_tmap_1(A_343,B_341,E_342,C_345),C_345,B_341)
      | ~ v1_funct_2(k2_tmap_1(A_343,B_341,E_342,C_345),u1_struct_0(C_345),u1_struct_0(B_341))
      | ~ v1_funct_1(k2_tmap_1(A_343,B_341,E_342,C_345))
      | ~ m1_subset_1(E_342,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_343),u1_struct_0(B_341))))
      | ~ v1_funct_2(E_342,u1_struct_0(A_343),u1_struct_0(B_341))
      | ~ v1_funct_1(E_342)
      | ~ r4_tsep_1(A_343,C_345,D_344)
      | ~ m1_pre_topc(D_344,A_343)
      | v2_struct_0(D_344)
      | ~ m1_pre_topc(C_345,A_343)
      | v2_struct_0(C_345)
      | ~ l1_pre_topc(B_341)
      | ~ v2_pre_topc(B_341)
      | v2_struct_0(B_341)
      | ~ l1_pre_topc(A_343)
      | ~ v2_pre_topc(A_343)
      | v2_struct_0(A_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_2967,plain,(
    ! [C_345] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',C_345,'#skF_5')),k1_tsep_1('#skF_1',C_345,'#skF_5'),'#skF_2')
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_345),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_345),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_345),C_345,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_345),u1_struct_0(C_345),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_345))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ r4_tsep_1('#skF_1',C_345,'#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(C_345,'#skF_1')
      | v2_struct_0(C_345)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_297,c_2955])).

tff(c_2985,plain,(
    ! [C_345] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',C_345,'#skF_5')),k1_tsep_1('#skF_1',C_345,'#skF_5'),'#skF_2')
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_345),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_345),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_345),C_345,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_345),u1_struct_0(C_345),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_345))
      | ~ r4_tsep_1('#skF_1',C_345,'#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(C_345,'#skF_1')
      | v2_struct_0(C_345)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_68,c_54,c_66,c_64,c_62,c_248,c_252,c_251,c_2967])).

tff(c_3404,plain,(
    ! [C_360] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',C_360,'#skF_5')),k1_tsep_1('#skF_1',C_360,'#skF_5'),'#skF_2')
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_360),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_360),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_360),C_360,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_360),u1_struct_0(C_360),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_360))
      | ~ r4_tsep_1('#skF_1',C_360,'#skF_5')
      | ~ m1_pre_topc(C_360,'#skF_1')
      | v2_struct_0(C_360) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_72,c_56,c_2985])).

tff(c_3417,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2')
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_254,c_3404])).

tff(c_3430,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50,c_249,c_253,c_250,c_552,c_52,c_52,c_3417])).

tff(c_3432,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_631,c_3430])).

tff(c_3434,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_3523,plain,
    ( ~ l1_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_3516,c_3434])).

tff(c_3539,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3475,c_3486,c_66,c_64,c_62,c_3523])).

tff(c_3546,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_3539])).

tff(c_3550,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_3546])).

tff(c_3552,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_3612,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_3603,c_3552])).

tff(c_3627,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3584,c_3594,c_66,c_64,c_62,c_3612])).

tff(c_3633,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_3627])).

tff(c_3637,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_3633])).

tff(c_3639,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_3716,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_3712,c_3639])).

tff(c_3719,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_3716])).

tff(c_3723,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_3719])).

tff(c_3725,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_3781,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_3777,c_3725])).

tff(c_3806,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_3781])).

tff(c_3810,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_3806])).

tff(c_3812,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_3815,plain,(
    ! [A_439,B_440,C_441,D_442] :
      ( k2_partfun1(A_439,B_440,C_441,D_442) = k7_relat_1(C_441,D_442)
      | ~ m1_subset_1(C_441,k1_zfmisc_1(k2_zfmisc_1(A_439,B_440)))
      | ~ v1_funct_1(C_441) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3817,plain,(
    ! [D_442] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_442) = k7_relat_1('#skF_3',D_442)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_62,c_3815])).

tff(c_3820,plain,(
    ! [D_442] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_442) = k7_relat_1('#skF_3',D_442) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3817])).

tff(c_3931,plain,(
    ! [A_474,B_475,C_476,D_477] :
      ( k2_partfun1(u1_struct_0(A_474),u1_struct_0(B_475),C_476,u1_struct_0(D_477)) = k2_tmap_1(A_474,B_475,C_476,D_477)
      | ~ m1_pre_topc(D_477,A_474)
      | ~ m1_subset_1(C_476,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_474),u1_struct_0(B_475))))
      | ~ v1_funct_2(C_476,u1_struct_0(A_474),u1_struct_0(B_475))
      | ~ v1_funct_1(C_476)
      | ~ l1_pre_topc(B_475)
      | ~ v2_pre_topc(B_475)
      | v2_struct_0(B_475)
      | ~ l1_pre_topc(A_474)
      | ~ v2_pre_topc(A_474)
      | v2_struct_0(A_474) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3935,plain,(
    ! [D_477] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_477)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_477)
      | ~ m1_pre_topc(D_477,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_62,c_3931])).

tff(c_3939,plain,(
    ! [D_477] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_477)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_477)
      | ~ m1_pre_topc(D_477,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_68,c_66,c_64,c_3820,c_3935])).

tff(c_3941,plain,(
    ! [D_478] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_478)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_478)
      | ~ m1_pre_topc(D_478,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_72,c_3939])).

tff(c_3947,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3941,c_243])).

tff(c_3958,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3947])).

tff(c_3961,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_3958])).

tff(c_3965,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3961])).

tff(c_3967,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_3947])).

tff(c_3953,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_3941])).

tff(c_3975,plain,(
    k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3967,c_3953])).

tff(c_3811,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_4510,plain,(
    ! [E_569,B_568,C_572,D_571,A_570] :
      ( v5_pre_topc(k2_tmap_1(A_570,B_568,E_569,D_571),D_571,B_568)
      | ~ m1_subset_1(k2_tmap_1(A_570,B_568,E_569,k1_tsep_1(A_570,C_572,D_571)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_570,C_572,D_571)),u1_struct_0(B_568))))
      | ~ v5_pre_topc(k2_tmap_1(A_570,B_568,E_569,k1_tsep_1(A_570,C_572,D_571)),k1_tsep_1(A_570,C_572,D_571),B_568)
      | ~ v1_funct_2(k2_tmap_1(A_570,B_568,E_569,k1_tsep_1(A_570,C_572,D_571)),u1_struct_0(k1_tsep_1(A_570,C_572,D_571)),u1_struct_0(B_568))
      | ~ v1_funct_1(k2_tmap_1(A_570,B_568,E_569,k1_tsep_1(A_570,C_572,D_571)))
      | ~ m1_subset_1(E_569,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_570),u1_struct_0(B_568))))
      | ~ v1_funct_2(E_569,u1_struct_0(A_570),u1_struct_0(B_568))
      | ~ v1_funct_1(E_569)
      | ~ r4_tsep_1(A_570,C_572,D_571)
      | ~ m1_pre_topc(D_571,A_570)
      | v2_struct_0(D_571)
      | ~ m1_pre_topc(C_572,A_570)
      | v2_struct_0(C_572)
      | ~ l1_pre_topc(B_568)
      | ~ v2_pre_topc(B_568)
      | v2_struct_0(B_568)
      | ~ l1_pre_topc(A_570)
      | ~ v2_pre_topc(A_570)
      | v2_struct_0(A_570) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_4521,plain,(
    ! [B_568,E_569] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_568,E_569,'#skF_5'),'#skF_5',B_568)
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_568,E_569,'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_568))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_568,E_569,k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_568)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_568,E_569,k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_568))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_568,E_569,k1_tsep_1('#skF_1','#skF_4','#skF_5')))
      | ~ m1_subset_1(E_569,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_568))))
      | ~ v1_funct_2(E_569,u1_struct_0('#skF_1'),u1_struct_0(B_568))
      | ~ v1_funct_1(E_569)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_568)
      | ~ v2_pre_topc(B_568)
      | v2_struct_0(B_568)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_4510])).

tff(c_4530,plain,(
    ! [B_568,E_569] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_568,E_569,'#skF_5'),'#skF_5',B_568)
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_568,E_569,'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_568))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_568,E_569,'#skF_1'),'#skF_1',B_568)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_568,E_569,'#skF_1'),u1_struct_0('#skF_1'),u1_struct_0(B_568))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_568,E_569,'#skF_1'))
      | ~ m1_subset_1(E_569,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_568))))
      | ~ v1_funct_2(E_569,u1_struct_0('#skF_1'),u1_struct_0(B_568))
      | ~ v1_funct_1(E_569)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_568)
      | ~ v2_pre_topc(B_568)
      | v2_struct_0(B_568)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_58,c_54,c_50,c_52,c_52,c_52,c_52,c_52,c_52,c_4521])).

tff(c_4584,plain,(
    ! [B_575,E_576] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_575,E_576,'#skF_5'),'#skF_5',B_575)
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_575,E_576,'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_575))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_575,E_576,'#skF_1'),'#skF_1',B_575)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_575,E_576,'#skF_1'),u1_struct_0('#skF_1'),u1_struct_0(B_575))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_575,E_576,'#skF_1'))
      | ~ m1_subset_1(E_576,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_575))))
      | ~ v1_funct_2(E_576,u1_struct_0('#skF_1'),u1_struct_0(B_575))
      | ~ v1_funct_1(E_576)
      | ~ l1_pre_topc(B_575)
      | ~ v2_pre_topc(B_575)
      | v2_struct_0(B_575) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_60,c_56,c_4530])).

tff(c_4587,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
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
    inference(superposition,[status(thm),theory(equality)],[c_3975,c_4584])).

tff(c_4593,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_62,c_66,c_3975,c_64,c_3975,c_3811,c_3975,c_62,c_4587])).

tff(c_4595,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3812,c_4593])).

tff(c_4597,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_4601,plain,(
    ! [A_577,B_578,C_579,D_580] :
      ( k2_partfun1(A_577,B_578,C_579,D_580) = k7_relat_1(C_579,D_580)
      | ~ m1_subset_1(C_579,k1_zfmisc_1(k2_zfmisc_1(A_577,B_578)))
      | ~ v1_funct_1(C_579) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4603,plain,(
    ! [D_580] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_580) = k7_relat_1('#skF_3',D_580)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_62,c_4601])).

tff(c_4606,plain,(
    ! [D_580] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_580) = k7_relat_1('#skF_3',D_580) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4603])).

tff(c_4701,plain,(
    ! [A_609,B_610,C_611,D_612] :
      ( k2_partfun1(u1_struct_0(A_609),u1_struct_0(B_610),C_611,u1_struct_0(D_612)) = k2_tmap_1(A_609,B_610,C_611,D_612)
      | ~ m1_pre_topc(D_612,A_609)
      | ~ m1_subset_1(C_611,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_609),u1_struct_0(B_610))))
      | ~ v1_funct_2(C_611,u1_struct_0(A_609),u1_struct_0(B_610))
      | ~ v1_funct_1(C_611)
      | ~ l1_pre_topc(B_610)
      | ~ v2_pre_topc(B_610)
      | v2_struct_0(B_610)
      | ~ l1_pre_topc(A_609)
      | ~ v2_pre_topc(A_609)
      | v2_struct_0(A_609) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4705,plain,(
    ! [D_612] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_612)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_612)
      | ~ m1_pre_topc(D_612,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_62,c_4701])).

tff(c_4709,plain,(
    ! [D_612] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_612)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_612)
      | ~ m1_pre_topc(D_612,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_68,c_66,c_64,c_4606,c_4705])).

tff(c_4716,plain,(
    ! [D_614] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_614)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_614)
      | ~ m1_pre_topc(D_614,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_72,c_4709])).

tff(c_4722,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4716,c_243])).

tff(c_4731,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4722])).

tff(c_4735,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_4731])).

tff(c_4739,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_4735])).

tff(c_4740,plain,(
    k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4722])).

tff(c_4596,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_5125,plain,(
    ! [A_701,B_699,C_703,E_700,D_702] :
      ( v5_pre_topc(k2_tmap_1(A_701,B_699,E_700,C_703),C_703,B_699)
      | ~ m1_subset_1(k2_tmap_1(A_701,B_699,E_700,k1_tsep_1(A_701,C_703,D_702)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_701,C_703,D_702)),u1_struct_0(B_699))))
      | ~ v5_pre_topc(k2_tmap_1(A_701,B_699,E_700,k1_tsep_1(A_701,C_703,D_702)),k1_tsep_1(A_701,C_703,D_702),B_699)
      | ~ v1_funct_2(k2_tmap_1(A_701,B_699,E_700,k1_tsep_1(A_701,C_703,D_702)),u1_struct_0(k1_tsep_1(A_701,C_703,D_702)),u1_struct_0(B_699))
      | ~ v1_funct_1(k2_tmap_1(A_701,B_699,E_700,k1_tsep_1(A_701,C_703,D_702)))
      | ~ m1_subset_1(E_700,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_701),u1_struct_0(B_699))))
      | ~ v1_funct_2(E_700,u1_struct_0(A_701),u1_struct_0(B_699))
      | ~ v1_funct_1(E_700)
      | ~ r4_tsep_1(A_701,C_703,D_702)
      | ~ m1_pre_topc(D_702,A_701)
      | v2_struct_0(D_702)
      | ~ m1_pre_topc(C_703,A_701)
      | v2_struct_0(C_703)
      | ~ l1_pre_topc(B_699)
      | ~ v2_pre_topc(B_699)
      | v2_struct_0(B_699)
      | ~ l1_pre_topc(A_701)
      | ~ v2_pre_topc(A_701)
      | v2_struct_0(A_701) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_5135,plain,(
    ! [B_699,E_700] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_699,E_700,'#skF_4'),'#skF_4',B_699)
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_699,E_700,k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_699))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_699,E_700,k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_699)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_699,E_700,k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_699))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_699,E_700,k1_tsep_1('#skF_1','#skF_4','#skF_5')))
      | ~ m1_subset_1(E_700,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_699))))
      | ~ v1_funct_2(E_700,u1_struct_0('#skF_1'),u1_struct_0(B_699))
      | ~ v1_funct_1(E_700)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_699)
      | ~ v2_pre_topc(B_699)
      | v2_struct_0(B_699)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_5125])).

tff(c_5141,plain,(
    ! [B_699,E_700] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_699,E_700,'#skF_4'),'#skF_4',B_699)
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_699,E_700,'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_699))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_699,E_700,'#skF_1'),'#skF_1',B_699)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_699,E_700,'#skF_1'),u1_struct_0('#skF_1'),u1_struct_0(B_699))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_699,E_700,'#skF_1'))
      | ~ m1_subset_1(E_700,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_699))))
      | ~ v1_funct_2(E_700,u1_struct_0('#skF_1'),u1_struct_0(B_699))
      | ~ v1_funct_1(E_700)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_699)
      | ~ v2_pre_topc(B_699)
      | v2_struct_0(B_699)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_58,c_54,c_50,c_52,c_52,c_52,c_52,c_52,c_52,c_5135])).

tff(c_5269,plain,(
    ! [B_709,E_710] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_709,E_710,'#skF_4'),'#skF_4',B_709)
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_709,E_710,'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_709))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_709,E_710,'#skF_1'),'#skF_1',B_709)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_709,E_710,'#skF_1'),u1_struct_0('#skF_1'),u1_struct_0(B_709))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_709,E_710,'#skF_1'))
      | ~ m1_subset_1(E_710,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_709))))
      | ~ v1_funct_2(E_710,u1_struct_0('#skF_1'),u1_struct_0(B_709))
      | ~ v1_funct_1(E_710)
      | ~ l1_pre_topc(B_709)
      | ~ v2_pre_topc(B_709)
      | v2_struct_0(B_709) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_60,c_56,c_5141])).

tff(c_5272,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
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
    inference(superposition,[status(thm),theory(equality)],[c_4740,c_5269])).

tff(c_5278,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_62,c_66,c_4740,c_64,c_4740,c_4596,c_4740,c_62,c_5272])).

tff(c_5280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_4597,c_5278])).

tff(c_5282,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_5350,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_5346,c_5282])).

tff(c_5375,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_5350])).

tff(c_5379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_5375])).

tff(c_5381,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_5440,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_5436,c_5381])).

tff(c_5443,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_5440])).

tff(c_5447,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_5443])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:31:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.74/2.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.74/2.82  
% 8.74/2.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.74/2.82  %$ v5_pre_topc > v1_funct_2 > r4_tsep_1 > v5_relat_1 > v4_relat_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.74/2.82  
% 8.74/2.82  %Foreground sorts:
% 8.74/2.82  
% 8.74/2.82  
% 8.74/2.82  %Background operators:
% 8.74/2.82  
% 8.74/2.82  
% 8.74/2.82  %Foreground operators:
% 8.74/2.82  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.74/2.82  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 8.74/2.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.74/2.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.74/2.82  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.74/2.82  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.74/2.82  tff(r4_tsep_1, type, r4_tsep_1: ($i * $i * $i) > $o).
% 8.74/2.82  tff('#skF_5', type, '#skF_5': $i).
% 8.74/2.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.74/2.82  tff('#skF_2', type, '#skF_2': $i).
% 8.74/2.82  tff('#skF_3', type, '#skF_3': $i).
% 8.74/2.82  tff('#skF_1', type, '#skF_1': $i).
% 8.74/2.82  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.74/2.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.74/2.82  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.74/2.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.74/2.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.74/2.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.74/2.82  tff('#skF_4', type, '#skF_4': $i).
% 8.74/2.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.74/2.82  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 8.74/2.82  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.74/2.82  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 8.74/2.82  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.74/2.82  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.74/2.82  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 8.74/2.82  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.74/2.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.74/2.82  
% 8.74/2.85  tff(f_230, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => (((A = k1_tsep_1(A, D, E)) & r4_tsep_1(A, D, E)) => ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) <=> (((((((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, C, D), D, B)) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) & v1_funct_1(k2_tmap_1(A, B, C, E))) & v1_funct_2(k2_tmap_1(A, B, C, E), u1_struct_0(E), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, C, E), E, B)) & m1_subset_1(k2_tmap_1(A, B, C, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E), u1_struct_0(B))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_tmap_1)).
% 8.74/2.85  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 8.74/2.85  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 8.74/2.85  tff(f_103, axiom, (![A, B, C, D]: ((((((l1_struct_0(A) & l1_struct_0(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & l1_struct_0(D)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 8.74/2.85  tff(f_167, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 8.74/2.85  tff(f_47, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 8.74/2.85  tff(f_85, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 8.74/2.85  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.74/2.85  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.74/2.85  tff(f_31, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 8.74/2.85  tff(f_163, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (r4_tsep_1(A, C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => ((((v1_funct_1(k2_tmap_1(A, B, E, k1_tsep_1(A, C, D))) & v1_funct_2(k2_tmap_1(A, B, E, k1_tsep_1(A, C, D)), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, E, k1_tsep_1(A, C, D)), k1_tsep_1(A, C, D), B)) & m1_subset_1(k2_tmap_1(A, B, E, k1_tsep_1(A, C, D)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) <=> (((((((v1_funct_1(k2_tmap_1(A, B, E, C)) & v1_funct_2(k2_tmap_1(A, B, E, C), u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, E, C), C, B)) & m1_subset_1(k2_tmap_1(A, B, E, C), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(k2_tmap_1(A, B, E, D))) & v1_funct_2(k2_tmap_1(A, B, E, D), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, E, D), D, B)) & m1_subset_1(k2_tmap_1(A, B, E, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_tmap_1)).
% 8.74/2.85  tff(c_74, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.74/2.85  tff(c_54, plain, (m1_pre_topc('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.74/2.85  tff(c_205, plain, (![B_96, A_97]: (l1_pre_topc(B_96) | ~m1_pre_topc(B_96, A_97) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.74/2.85  tff(c_214, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_205])).
% 8.74/2.85  tff(c_221, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_214])).
% 8.74/2.85  tff(c_12, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.74/2.85  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.74/2.85  tff(c_66, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.74/2.85  tff(c_64, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.74/2.85  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.74/2.85  tff(c_5404, plain, (![A_734, B_735, C_736, D_737]: (v1_funct_1(k2_tmap_1(A_734, B_735, C_736, D_737)) | ~l1_struct_0(D_737) | ~m1_subset_1(C_736, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_734), u1_struct_0(B_735)))) | ~v1_funct_2(C_736, u1_struct_0(A_734), u1_struct_0(B_735)) | ~v1_funct_1(C_736) | ~l1_struct_0(B_735) | ~l1_struct_0(A_734))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.74/2.85  tff(c_5406, plain, (![D_737]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_737)) | ~l1_struct_0(D_737) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_5404])).
% 8.74/2.85  tff(c_5409, plain, (![D_737]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_737)) | ~l1_struct_0(D_737) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_5406])).
% 8.74/2.85  tff(c_5410, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_5409])).
% 8.74/2.85  tff(c_5413, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_5410])).
% 8.74/2.85  tff(c_5417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_5413])).
% 8.74/2.85  tff(c_5418, plain, (![D_737]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_737)) | ~l1_struct_0(D_737))), inference(splitRight, [status(thm)], [c_5409])).
% 8.74/2.85  tff(c_5420, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_5418])).
% 8.74/2.85  tff(c_5423, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_5420])).
% 8.74/2.85  tff(c_5427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_5423])).
% 8.74/2.85  tff(c_5436, plain, (![D_742]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_742)) | ~l1_struct_0(D_742))), inference(splitRight, [status(thm)], [c_5418])).
% 8.74/2.85  tff(c_58, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.74/2.85  tff(c_211, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_205])).
% 8.74/2.85  tff(c_218, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_211])).
% 8.74/2.85  tff(c_5306, plain, (![A_716, B_717, C_718, D_719]: (v1_funct_1(k2_tmap_1(A_716, B_717, C_718, D_719)) | ~l1_struct_0(D_719) | ~m1_subset_1(C_718, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_716), u1_struct_0(B_717)))) | ~v1_funct_2(C_718, u1_struct_0(A_716), u1_struct_0(B_717)) | ~v1_funct_1(C_718) | ~l1_struct_0(B_717) | ~l1_struct_0(A_716))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.74/2.85  tff(c_5308, plain, (![D_719]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_719)) | ~l1_struct_0(D_719) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_5306])).
% 8.74/2.85  tff(c_5311, plain, (![D_719]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_719)) | ~l1_struct_0(D_719) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_5308])).
% 8.74/2.85  tff(c_5312, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_5311])).
% 8.74/2.85  tff(c_5315, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_5312])).
% 8.74/2.85  tff(c_5319, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_5315])).
% 8.74/2.85  tff(c_5320, plain, (![D_719]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_719)) | ~l1_struct_0(D_719))), inference(splitRight, [status(thm)], [c_5311])).
% 8.74/2.85  tff(c_5328, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_5320])).
% 8.74/2.85  tff(c_5331, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_5328])).
% 8.74/2.85  tff(c_5335, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_5331])).
% 8.74/2.85  tff(c_5346, plain, (![D_724]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_724)) | ~l1_struct_0(D_724))), inference(splitRight, [status(thm)], [c_5320])).
% 8.74/2.85  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.74/2.85  tff(c_3744, plain, (![A_425, B_426, C_427, D_428]: (v1_funct_1(k2_tmap_1(A_425, B_426, C_427, D_428)) | ~l1_struct_0(D_428) | ~m1_subset_1(C_427, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_425), u1_struct_0(B_426)))) | ~v1_funct_2(C_427, u1_struct_0(A_425), u1_struct_0(B_426)) | ~v1_funct_1(C_427) | ~l1_struct_0(B_426) | ~l1_struct_0(A_425))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.74/2.85  tff(c_3746, plain, (![D_428]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_428)) | ~l1_struct_0(D_428) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_3744])).
% 8.74/2.85  tff(c_3749, plain, (![D_428]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_428)) | ~l1_struct_0(D_428) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_3746])).
% 8.74/2.85  tff(c_3750, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_3749])).
% 8.74/2.85  tff(c_3753, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_3750])).
% 8.74/2.85  tff(c_3757, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_3753])).
% 8.74/2.85  tff(c_3759, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_3749])).
% 8.74/2.85  tff(c_3758, plain, (![D_428]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_428)) | ~l1_struct_0(D_428))), inference(splitRight, [status(thm)], [c_3749])).
% 8.74/2.85  tff(c_3760, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_3758])).
% 8.74/2.85  tff(c_3763, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_3760])).
% 8.74/2.85  tff(c_3767, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_3763])).
% 8.74/2.85  tff(c_3769, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_3758])).
% 8.74/2.85  tff(c_3771, plain, (![A_430, B_431, C_432, D_433]: (v1_funct_2(k2_tmap_1(A_430, B_431, C_432, D_433), u1_struct_0(D_433), u1_struct_0(B_431)) | ~l1_struct_0(D_433) | ~m1_subset_1(C_432, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_430), u1_struct_0(B_431)))) | ~v1_funct_2(C_432, u1_struct_0(A_430), u1_struct_0(B_431)) | ~v1_funct_1(C_432) | ~l1_struct_0(B_431) | ~l1_struct_0(A_430))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.74/2.85  tff(c_3773, plain, (![D_433]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_433), u1_struct_0(D_433), u1_struct_0('#skF_2')) | ~l1_struct_0(D_433) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_3771])).
% 8.74/2.85  tff(c_3777, plain, (![D_434]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_434), u1_struct_0(D_434), u1_struct_0('#skF_2')) | ~l1_struct_0(D_434))), inference(demodulation, [status(thm), theory('equality')], [c_3759, c_3769, c_66, c_64, c_3773])).
% 8.74/2.85  tff(c_3648, plain, (![A_405, B_406, C_407, D_408]: (v1_funct_1(k2_tmap_1(A_405, B_406, C_407, D_408)) | ~l1_struct_0(D_408) | ~m1_subset_1(C_407, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_405), u1_struct_0(B_406)))) | ~v1_funct_2(C_407, u1_struct_0(A_405), u1_struct_0(B_406)) | ~v1_funct_1(C_407) | ~l1_struct_0(B_406) | ~l1_struct_0(A_405))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.74/2.85  tff(c_3650, plain, (![D_408]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_408)) | ~l1_struct_0(D_408) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_3648])).
% 8.74/2.85  tff(c_3653, plain, (![D_408]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_408)) | ~l1_struct_0(D_408) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_3650])).
% 8.74/2.85  tff(c_3663, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_3653])).
% 8.74/2.85  tff(c_3666, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_3663])).
% 8.74/2.85  tff(c_3670, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_3666])).
% 8.74/2.85  tff(c_3672, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_3653])).
% 8.74/2.85  tff(c_3671, plain, (![D_408]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_408)) | ~l1_struct_0(D_408))), inference(splitRight, [status(thm)], [c_3653])).
% 8.74/2.85  tff(c_3673, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_3671])).
% 8.74/2.85  tff(c_3676, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_3673])).
% 8.74/2.85  tff(c_3680, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_3676])).
% 8.74/2.85  tff(c_3682, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_3671])).
% 8.74/2.85  tff(c_3684, plain, (![A_411, B_412, C_413, D_414]: (v1_funct_2(k2_tmap_1(A_411, B_412, C_413, D_414), u1_struct_0(D_414), u1_struct_0(B_412)) | ~l1_struct_0(D_414) | ~m1_subset_1(C_413, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_411), u1_struct_0(B_412)))) | ~v1_funct_2(C_413, u1_struct_0(A_411), u1_struct_0(B_412)) | ~v1_funct_1(C_413) | ~l1_struct_0(B_412) | ~l1_struct_0(A_411))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.74/2.85  tff(c_3686, plain, (![D_414]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_414), u1_struct_0(D_414), u1_struct_0('#skF_2')) | ~l1_struct_0(D_414) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_3684])).
% 8.74/2.85  tff(c_3712, plain, (![D_419]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_419), u1_struct_0(D_419), u1_struct_0('#skF_2')) | ~l1_struct_0(D_419))), inference(demodulation, [status(thm), theory('equality')], [c_3672, c_3682, c_66, c_64, c_3686])).
% 8.74/2.85  tff(c_3569, plain, (![A_387, B_388, C_389, D_390]: (v1_funct_1(k2_tmap_1(A_387, B_388, C_389, D_390)) | ~l1_struct_0(D_390) | ~m1_subset_1(C_389, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_387), u1_struct_0(B_388)))) | ~v1_funct_2(C_389, u1_struct_0(A_387), u1_struct_0(B_388)) | ~v1_funct_1(C_389) | ~l1_struct_0(B_388) | ~l1_struct_0(A_387))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.74/2.85  tff(c_3571, plain, (![D_390]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_390)) | ~l1_struct_0(D_390) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_3569])).
% 8.74/2.85  tff(c_3574, plain, (![D_390]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_390)) | ~l1_struct_0(D_390) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_3571])).
% 8.74/2.85  tff(c_3575, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_3574])).
% 8.74/2.85  tff(c_3578, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_3575])).
% 8.74/2.85  tff(c_3582, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_3578])).
% 8.74/2.85  tff(c_3584, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_3574])).
% 8.74/2.85  tff(c_3583, plain, (![D_390]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_390)) | ~l1_struct_0(D_390))), inference(splitRight, [status(thm)], [c_3574])).
% 8.74/2.85  tff(c_3585, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_3583])).
% 8.74/2.85  tff(c_3588, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_3585])).
% 8.74/2.85  tff(c_3592, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_3588])).
% 8.74/2.85  tff(c_3594, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_3583])).
% 8.74/2.85  tff(c_3603, plain, (![A_397, B_398, C_399, D_400]: (m1_subset_1(k2_tmap_1(A_397, B_398, C_399, D_400), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_400), u1_struct_0(B_398)))) | ~l1_struct_0(D_400) | ~m1_subset_1(C_399, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_397), u1_struct_0(B_398)))) | ~v1_funct_2(C_399, u1_struct_0(A_397), u1_struct_0(B_398)) | ~v1_funct_1(C_399) | ~l1_struct_0(B_398) | ~l1_struct_0(A_397))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.74/2.85  tff(c_3444, plain, (![A_362, B_363, C_364, D_365]: (v1_funct_1(k2_tmap_1(A_362, B_363, C_364, D_365)) | ~l1_struct_0(D_365) | ~m1_subset_1(C_364, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_362), u1_struct_0(B_363)))) | ~v1_funct_2(C_364, u1_struct_0(A_362), u1_struct_0(B_363)) | ~v1_funct_1(C_364) | ~l1_struct_0(B_363) | ~l1_struct_0(A_362))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.74/2.85  tff(c_3448, plain, (![D_365]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_365)) | ~l1_struct_0(D_365) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_3444])).
% 8.74/2.85  tff(c_3454, plain, (![D_365]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_365)) | ~l1_struct_0(D_365) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_3448])).
% 8.74/2.85  tff(c_3455, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_3454])).
% 8.74/2.85  tff(c_3469, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_3455])).
% 8.74/2.85  tff(c_3473, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_3469])).
% 8.74/2.85  tff(c_3475, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_3454])).
% 8.74/2.85  tff(c_3474, plain, (![D_365]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_365)) | ~l1_struct_0(D_365))), inference(splitRight, [status(thm)], [c_3454])).
% 8.74/2.85  tff(c_3476, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_3474])).
% 8.74/2.85  tff(c_3480, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_3476])).
% 8.74/2.85  tff(c_3484, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_3480])).
% 8.74/2.85  tff(c_3486, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_3474])).
% 8.74/2.85  tff(c_3516, plain, (![A_378, B_379, C_380, D_381]: (m1_subset_1(k2_tmap_1(A_378, B_379, C_380, D_381), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_381), u1_struct_0(B_379)))) | ~l1_struct_0(D_381) | ~m1_subset_1(C_380, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_378), u1_struct_0(B_379)))) | ~v1_funct_2(C_380, u1_struct_0(A_378), u1_struct_0(B_379)) | ~v1_funct_1(C_380) | ~l1_struct_0(B_379) | ~l1_struct_0(A_378))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.74/2.85  tff(c_60, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.74/2.85  tff(c_164, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.74/2.85  tff(c_249, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_164])).
% 8.74/2.85  tff(c_154, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.74/2.85  tff(c_253, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_154])).
% 8.74/2.85  tff(c_144, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.74/2.85  tff(c_250, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_144])).
% 8.74/2.85  tff(c_134, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.74/2.85  tff(c_254, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_134])).
% 8.74/2.85  tff(c_124, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.74/2.85  tff(c_248, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_124])).
% 8.74/2.85  tff(c_114, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.74/2.85  tff(c_252, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_114])).
% 8.74/2.85  tff(c_104, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.74/2.85  tff(c_251, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2')), inference(splitLeft, [status(thm)], [c_104])).
% 8.74/2.85  tff(c_94, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.74/2.85  tff(c_297, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_94])).
% 8.74/2.85  tff(c_80, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.74/2.85  tff(c_178, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_80])).
% 8.74/2.85  tff(c_188, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_178])).
% 8.74/2.85  tff(c_198, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_188])).
% 8.74/2.85  tff(c_631, plain, (~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_249, c_253, c_250, c_254, c_248, c_252, c_251, c_297, c_198])).
% 8.74/2.85  tff(c_50, plain, (r4_tsep_1('#skF_1', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.74/2.85  tff(c_48, plain, (![A_67]: (m1_pre_topc(A_67, A_67) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_167])).
% 8.74/2.85  tff(c_78, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.74/2.85  tff(c_76, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.74/2.85  tff(c_70, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.74/2.85  tff(c_273, plain, (![A_109, B_110, C_111, D_112]: (k2_partfun1(A_109, B_110, C_111, D_112)=k7_relat_1(C_111, D_112) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))) | ~v1_funct_1(C_111))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.74/2.85  tff(c_277, plain, (![D_112]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_112)=k7_relat_1('#skF_3', D_112) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_62, c_273])).
% 8.74/2.85  tff(c_283, plain, (![D_112]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_112)=k7_relat_1('#skF_3', D_112))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_277])).
% 8.74/2.85  tff(c_507, plain, (![A_148, B_149, C_150, D_151]: (k2_partfun1(u1_struct_0(A_148), u1_struct_0(B_149), C_150, u1_struct_0(D_151))=k2_tmap_1(A_148, B_149, C_150, D_151) | ~m1_pre_topc(D_151, A_148) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_148), u1_struct_0(B_149)))) | ~v1_funct_2(C_150, u1_struct_0(A_148), u1_struct_0(B_149)) | ~v1_funct_1(C_150) | ~l1_pre_topc(B_149) | ~v2_pre_topc(B_149) | v2_struct_0(B_149) | ~l1_pre_topc(A_148) | ~v2_pre_topc(A_148) | v2_struct_0(A_148))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.74/2.85  tff(c_515, plain, (![D_151]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_151))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_151) | ~m1_pre_topc(D_151, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_507])).
% 8.74/2.85  tff(c_527, plain, (![D_151]: (k7_relat_1('#skF_3', u1_struct_0(D_151))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_151) | ~m1_pre_topc(D_151, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_70, c_68, c_66, c_64, c_283, c_515])).
% 8.74/2.85  tff(c_529, plain, (![D_152]: (k7_relat_1('#skF_3', u1_struct_0(D_152))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_152) | ~m1_pre_topc(D_152, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_78, c_72, c_527])).
% 8.74/2.85  tff(c_222, plain, (![C_98, A_99, B_100]: (v1_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.74/2.85  tff(c_226, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_222])).
% 8.74/2.85  tff(c_232, plain, (![C_104, A_105, B_106]: (v4_relat_1(C_104, A_105) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.74/2.85  tff(c_236, plain, (v4_relat_1('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_232])).
% 8.74/2.85  tff(c_2, plain, (![B_2, A_1]: (k7_relat_1(B_2, A_1)=B_2 | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.74/2.85  tff(c_240, plain, (k7_relat_1('#skF_3', u1_struct_0('#skF_1'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_236, c_2])).
% 8.74/2.85  tff(c_243, plain, (k7_relat_1('#skF_3', u1_struct_0('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_226, c_240])).
% 8.74/2.85  tff(c_535, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_529, c_243])).
% 8.74/2.85  tff(c_544, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_535])).
% 8.74/2.85  tff(c_547, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_544])).
% 8.74/2.85  tff(c_551, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_547])).
% 8.74/2.85  tff(c_552, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_535])).
% 8.74/2.85  tff(c_52, plain, (k1_tsep_1('#skF_1', '#skF_4', '#skF_5')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.74/2.85  tff(c_56, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_230])).
% 8.74/2.85  tff(c_2955, plain, (![C_345, B_341, E_342, A_343, D_344]: (v5_pre_topc(k2_tmap_1(A_343, B_341, E_342, k1_tsep_1(A_343, C_345, D_344)), k1_tsep_1(A_343, C_345, D_344), B_341) | ~m1_subset_1(k2_tmap_1(A_343, B_341, E_342, D_344), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_344), u1_struct_0(B_341)))) | ~v5_pre_topc(k2_tmap_1(A_343, B_341, E_342, D_344), D_344, B_341) | ~v1_funct_2(k2_tmap_1(A_343, B_341, E_342, D_344), u1_struct_0(D_344), u1_struct_0(B_341)) | ~v1_funct_1(k2_tmap_1(A_343, B_341, E_342, D_344)) | ~m1_subset_1(k2_tmap_1(A_343, B_341, E_342, C_345), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_345), u1_struct_0(B_341)))) | ~v5_pre_topc(k2_tmap_1(A_343, B_341, E_342, C_345), C_345, B_341) | ~v1_funct_2(k2_tmap_1(A_343, B_341, E_342, C_345), u1_struct_0(C_345), u1_struct_0(B_341)) | ~v1_funct_1(k2_tmap_1(A_343, B_341, E_342, C_345)) | ~m1_subset_1(E_342, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_343), u1_struct_0(B_341)))) | ~v1_funct_2(E_342, u1_struct_0(A_343), u1_struct_0(B_341)) | ~v1_funct_1(E_342) | ~r4_tsep_1(A_343, C_345, D_344) | ~m1_pre_topc(D_344, A_343) | v2_struct_0(D_344) | ~m1_pre_topc(C_345, A_343) | v2_struct_0(C_345) | ~l1_pre_topc(B_341) | ~v2_pre_topc(B_341) | v2_struct_0(B_341) | ~l1_pre_topc(A_343) | ~v2_pre_topc(A_343) | v2_struct_0(A_343))), inference(cnfTransformation, [status(thm)], [f_163])).
% 8.74/2.85  tff(c_2967, plain, (![C_345]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', C_345, '#skF_5')), k1_tsep_1('#skF_1', C_345, '#skF_5'), '#skF_2') | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_345), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_345), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_345), C_345, '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_345), u1_struct_0(C_345), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_345)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~r4_tsep_1('#skF_1', C_345, '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc(C_345, '#skF_1') | v2_struct_0(C_345) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_297, c_2955])).
% 8.74/2.85  tff(c_2985, plain, (![C_345]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', C_345, '#skF_5')), k1_tsep_1('#skF_1', C_345, '#skF_5'), '#skF_2') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_345), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_345), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_345), C_345, '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_345), u1_struct_0(C_345), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_345)) | ~r4_tsep_1('#skF_1', C_345, '#skF_5') | v2_struct_0('#skF_5') | ~m1_pre_topc(C_345, '#skF_1') | v2_struct_0(C_345) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_70, c_68, c_54, c_66, c_64, c_62, c_248, c_252, c_251, c_2967])).
% 8.74/2.85  tff(c_3404, plain, (![C_360]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', C_360, '#skF_5')), k1_tsep_1('#skF_1', C_360, '#skF_5'), '#skF_2') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_360), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_360), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_360), C_360, '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_360), u1_struct_0(C_360), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_360)) | ~r4_tsep_1('#skF_1', C_360, '#skF_5') | ~m1_pre_topc(C_360, '#skF_1') | v2_struct_0(C_360))), inference(negUnitSimplification, [status(thm)], [c_78, c_72, c_56, c_2985])).
% 8.74/2.85  tff(c_3417, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_2') | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_254, c_3404])).
% 8.74/2.85  tff(c_3430, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_50, c_249, c_253, c_250, c_552, c_52, c_52, c_3417])).
% 8.74/2.85  tff(c_3432, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_631, c_3430])).
% 8.74/2.85  tff(c_3434, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_94])).
% 8.74/2.85  tff(c_3523, plain, (~l1_struct_0('#skF_5') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_3516, c_3434])).
% 8.74/2.85  tff(c_3539, plain, (~l1_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3475, c_3486, c_66, c_64, c_62, c_3523])).
% 8.74/2.85  tff(c_3546, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_12, c_3539])).
% 8.74/2.85  tff(c_3550, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_221, c_3546])).
% 8.74/2.85  tff(c_3552, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_134])).
% 8.74/2.85  tff(c_3612, plain, (~l1_struct_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_3603, c_3552])).
% 8.74/2.85  tff(c_3627, plain, (~l1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3584, c_3594, c_66, c_64, c_62, c_3612])).
% 8.74/2.85  tff(c_3633, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_12, c_3627])).
% 8.74/2.85  tff(c_3637, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_218, c_3633])).
% 8.74/2.85  tff(c_3639, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_154])).
% 8.74/2.85  tff(c_3716, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_3712, c_3639])).
% 8.74/2.85  tff(c_3719, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_12, c_3716])).
% 8.74/2.85  tff(c_3723, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_218, c_3719])).
% 8.74/2.85  tff(c_3725, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_114])).
% 8.74/2.85  tff(c_3781, plain, (~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_3777, c_3725])).
% 8.74/2.85  tff(c_3806, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_12, c_3781])).
% 8.74/2.85  tff(c_3810, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_221, c_3806])).
% 8.74/2.85  tff(c_3812, plain, (~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_104])).
% 8.74/2.85  tff(c_3815, plain, (![A_439, B_440, C_441, D_442]: (k2_partfun1(A_439, B_440, C_441, D_442)=k7_relat_1(C_441, D_442) | ~m1_subset_1(C_441, k1_zfmisc_1(k2_zfmisc_1(A_439, B_440))) | ~v1_funct_1(C_441))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.74/2.85  tff(c_3817, plain, (![D_442]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_442)=k7_relat_1('#skF_3', D_442) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_62, c_3815])).
% 8.74/2.85  tff(c_3820, plain, (![D_442]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_442)=k7_relat_1('#skF_3', D_442))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3817])).
% 8.74/2.85  tff(c_3931, plain, (![A_474, B_475, C_476, D_477]: (k2_partfun1(u1_struct_0(A_474), u1_struct_0(B_475), C_476, u1_struct_0(D_477))=k2_tmap_1(A_474, B_475, C_476, D_477) | ~m1_pre_topc(D_477, A_474) | ~m1_subset_1(C_476, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_474), u1_struct_0(B_475)))) | ~v1_funct_2(C_476, u1_struct_0(A_474), u1_struct_0(B_475)) | ~v1_funct_1(C_476) | ~l1_pre_topc(B_475) | ~v2_pre_topc(B_475) | v2_struct_0(B_475) | ~l1_pre_topc(A_474) | ~v2_pre_topc(A_474) | v2_struct_0(A_474))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.74/2.85  tff(c_3935, plain, (![D_477]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_477))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_477) | ~m1_pre_topc(D_477, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_3931])).
% 8.74/2.85  tff(c_3939, plain, (![D_477]: (k7_relat_1('#skF_3', u1_struct_0(D_477))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_477) | ~m1_pre_topc(D_477, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_70, c_68, c_66, c_64, c_3820, c_3935])).
% 8.74/2.85  tff(c_3941, plain, (![D_478]: (k7_relat_1('#skF_3', u1_struct_0(D_478))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_478) | ~m1_pre_topc(D_478, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_78, c_72, c_3939])).
% 8.74/2.85  tff(c_3947, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3941, c_243])).
% 8.74/2.85  tff(c_3958, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_3947])).
% 8.74/2.85  tff(c_3961, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_3958])).
% 8.74/2.85  tff(c_3965, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_3961])).
% 8.74/2.85  tff(c_3967, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_3947])).
% 8.74/2.85  tff(c_3953, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_243, c_3941])).
% 8.74/2.85  tff(c_3975, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3967, c_3953])).
% 8.74/2.85  tff(c_3811, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_104])).
% 8.74/2.85  tff(c_4510, plain, (![E_569, B_568, C_572, D_571, A_570]: (v5_pre_topc(k2_tmap_1(A_570, B_568, E_569, D_571), D_571, B_568) | ~m1_subset_1(k2_tmap_1(A_570, B_568, E_569, k1_tsep_1(A_570, C_572, D_571)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_570, C_572, D_571)), u1_struct_0(B_568)))) | ~v5_pre_topc(k2_tmap_1(A_570, B_568, E_569, k1_tsep_1(A_570, C_572, D_571)), k1_tsep_1(A_570, C_572, D_571), B_568) | ~v1_funct_2(k2_tmap_1(A_570, B_568, E_569, k1_tsep_1(A_570, C_572, D_571)), u1_struct_0(k1_tsep_1(A_570, C_572, D_571)), u1_struct_0(B_568)) | ~v1_funct_1(k2_tmap_1(A_570, B_568, E_569, k1_tsep_1(A_570, C_572, D_571))) | ~m1_subset_1(E_569, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_570), u1_struct_0(B_568)))) | ~v1_funct_2(E_569, u1_struct_0(A_570), u1_struct_0(B_568)) | ~v1_funct_1(E_569) | ~r4_tsep_1(A_570, C_572, D_571) | ~m1_pre_topc(D_571, A_570) | v2_struct_0(D_571) | ~m1_pre_topc(C_572, A_570) | v2_struct_0(C_572) | ~l1_pre_topc(B_568) | ~v2_pre_topc(B_568) | v2_struct_0(B_568) | ~l1_pre_topc(A_570) | ~v2_pre_topc(A_570) | v2_struct_0(A_570))), inference(cnfTransformation, [status(thm)], [f_163])).
% 8.74/2.85  tff(c_4521, plain, (![B_568, E_569]: (v5_pre_topc(k2_tmap_1('#skF_1', B_568, E_569, '#skF_5'), '#skF_5', B_568) | ~m1_subset_1(k2_tmap_1('#skF_1', B_568, E_569, '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_568)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_568, E_569, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_568) | ~v1_funct_2(k2_tmap_1('#skF_1', B_568, E_569, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_568)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_568, E_569, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'))) | ~m1_subset_1(E_569, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_568)))) | ~v1_funct_2(E_569, u1_struct_0('#skF_1'), u1_struct_0(B_568)) | ~v1_funct_1(E_569) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_568) | ~v2_pre_topc(B_568) | v2_struct_0(B_568) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_4510])).
% 8.74/2.85  tff(c_4530, plain, (![B_568, E_569]: (v5_pre_topc(k2_tmap_1('#skF_1', B_568, E_569, '#skF_5'), '#skF_5', B_568) | ~m1_subset_1(k2_tmap_1('#skF_1', B_568, E_569, '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_568)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_568, E_569, '#skF_1'), '#skF_1', B_568) | ~v1_funct_2(k2_tmap_1('#skF_1', B_568, E_569, '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0(B_568)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_568, E_569, '#skF_1')) | ~m1_subset_1(E_569, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_568)))) | ~v1_funct_2(E_569, u1_struct_0('#skF_1'), u1_struct_0(B_568)) | ~v1_funct_1(E_569) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_568) | ~v2_pre_topc(B_568) | v2_struct_0(B_568) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_58, c_54, c_50, c_52, c_52, c_52, c_52, c_52, c_52, c_4521])).
% 8.74/2.85  tff(c_4584, plain, (![B_575, E_576]: (v5_pre_topc(k2_tmap_1('#skF_1', B_575, E_576, '#skF_5'), '#skF_5', B_575) | ~m1_subset_1(k2_tmap_1('#skF_1', B_575, E_576, '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_575)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_575, E_576, '#skF_1'), '#skF_1', B_575) | ~v1_funct_2(k2_tmap_1('#skF_1', B_575, E_576, '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0(B_575)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_575, E_576, '#skF_1')) | ~m1_subset_1(E_576, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_575)))) | ~v1_funct_2(E_576, u1_struct_0('#skF_1'), u1_struct_0(B_575)) | ~v1_funct_1(E_576) | ~l1_pre_topc(B_575) | ~v2_pre_topc(B_575) | v2_struct_0(B_575))), inference(negUnitSimplification, [status(thm)], [c_78, c_60, c_56, c_4530])).
% 8.74/2.85  tff(c_4587, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), '#skF_1', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3975, c_4584])).
% 8.74/2.85  tff(c_4593, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_62, c_66, c_3975, c_64, c_3975, c_3811, c_3975, c_62, c_4587])).
% 8.74/2.85  tff(c_4595, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_3812, c_4593])).
% 8.74/2.85  tff(c_4597, plain, (~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_144])).
% 8.74/2.85  tff(c_4601, plain, (![A_577, B_578, C_579, D_580]: (k2_partfun1(A_577, B_578, C_579, D_580)=k7_relat_1(C_579, D_580) | ~m1_subset_1(C_579, k1_zfmisc_1(k2_zfmisc_1(A_577, B_578))) | ~v1_funct_1(C_579))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.74/2.85  tff(c_4603, plain, (![D_580]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_580)=k7_relat_1('#skF_3', D_580) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_62, c_4601])).
% 8.74/2.85  tff(c_4606, plain, (![D_580]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_580)=k7_relat_1('#skF_3', D_580))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_4603])).
% 8.74/2.85  tff(c_4701, plain, (![A_609, B_610, C_611, D_612]: (k2_partfun1(u1_struct_0(A_609), u1_struct_0(B_610), C_611, u1_struct_0(D_612))=k2_tmap_1(A_609, B_610, C_611, D_612) | ~m1_pre_topc(D_612, A_609) | ~m1_subset_1(C_611, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_609), u1_struct_0(B_610)))) | ~v1_funct_2(C_611, u1_struct_0(A_609), u1_struct_0(B_610)) | ~v1_funct_1(C_611) | ~l1_pre_topc(B_610) | ~v2_pre_topc(B_610) | v2_struct_0(B_610) | ~l1_pre_topc(A_609) | ~v2_pre_topc(A_609) | v2_struct_0(A_609))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.74/2.85  tff(c_4705, plain, (![D_612]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_612))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_612) | ~m1_pre_topc(D_612, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_4701])).
% 8.74/2.85  tff(c_4709, plain, (![D_612]: (k7_relat_1('#skF_3', u1_struct_0(D_612))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_612) | ~m1_pre_topc(D_612, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_70, c_68, c_66, c_64, c_4606, c_4705])).
% 8.74/2.85  tff(c_4716, plain, (![D_614]: (k7_relat_1('#skF_3', u1_struct_0(D_614))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_614) | ~m1_pre_topc(D_614, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_78, c_72, c_4709])).
% 8.74/2.85  tff(c_4722, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4716, c_243])).
% 8.74/2.85  tff(c_4731, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_4722])).
% 8.74/2.85  tff(c_4735, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_4731])).
% 8.74/2.85  tff(c_4739, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_4735])).
% 8.74/2.85  tff(c_4740, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_4722])).
% 8.74/2.85  tff(c_4596, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_144])).
% 8.74/2.85  tff(c_5125, plain, (![A_701, B_699, C_703, E_700, D_702]: (v5_pre_topc(k2_tmap_1(A_701, B_699, E_700, C_703), C_703, B_699) | ~m1_subset_1(k2_tmap_1(A_701, B_699, E_700, k1_tsep_1(A_701, C_703, D_702)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_701, C_703, D_702)), u1_struct_0(B_699)))) | ~v5_pre_topc(k2_tmap_1(A_701, B_699, E_700, k1_tsep_1(A_701, C_703, D_702)), k1_tsep_1(A_701, C_703, D_702), B_699) | ~v1_funct_2(k2_tmap_1(A_701, B_699, E_700, k1_tsep_1(A_701, C_703, D_702)), u1_struct_0(k1_tsep_1(A_701, C_703, D_702)), u1_struct_0(B_699)) | ~v1_funct_1(k2_tmap_1(A_701, B_699, E_700, k1_tsep_1(A_701, C_703, D_702))) | ~m1_subset_1(E_700, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_701), u1_struct_0(B_699)))) | ~v1_funct_2(E_700, u1_struct_0(A_701), u1_struct_0(B_699)) | ~v1_funct_1(E_700) | ~r4_tsep_1(A_701, C_703, D_702) | ~m1_pre_topc(D_702, A_701) | v2_struct_0(D_702) | ~m1_pre_topc(C_703, A_701) | v2_struct_0(C_703) | ~l1_pre_topc(B_699) | ~v2_pre_topc(B_699) | v2_struct_0(B_699) | ~l1_pre_topc(A_701) | ~v2_pre_topc(A_701) | v2_struct_0(A_701))), inference(cnfTransformation, [status(thm)], [f_163])).
% 8.74/2.85  tff(c_5135, plain, (![B_699, E_700]: (v5_pre_topc(k2_tmap_1('#skF_1', B_699, E_700, '#skF_4'), '#skF_4', B_699) | ~m1_subset_1(k2_tmap_1('#skF_1', B_699, E_700, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_699)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_699, E_700, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_699) | ~v1_funct_2(k2_tmap_1('#skF_1', B_699, E_700, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_699)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_699, E_700, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'))) | ~m1_subset_1(E_700, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_699)))) | ~v1_funct_2(E_700, u1_struct_0('#skF_1'), u1_struct_0(B_699)) | ~v1_funct_1(E_700) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_699) | ~v2_pre_topc(B_699) | v2_struct_0(B_699) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_5125])).
% 8.74/2.85  tff(c_5141, plain, (![B_699, E_700]: (v5_pre_topc(k2_tmap_1('#skF_1', B_699, E_700, '#skF_4'), '#skF_4', B_699) | ~m1_subset_1(k2_tmap_1('#skF_1', B_699, E_700, '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_699)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_699, E_700, '#skF_1'), '#skF_1', B_699) | ~v1_funct_2(k2_tmap_1('#skF_1', B_699, E_700, '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0(B_699)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_699, E_700, '#skF_1')) | ~m1_subset_1(E_700, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_699)))) | ~v1_funct_2(E_700, u1_struct_0('#skF_1'), u1_struct_0(B_699)) | ~v1_funct_1(E_700) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_699) | ~v2_pre_topc(B_699) | v2_struct_0(B_699) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_58, c_54, c_50, c_52, c_52, c_52, c_52, c_52, c_52, c_5135])).
% 8.74/2.85  tff(c_5269, plain, (![B_709, E_710]: (v5_pre_topc(k2_tmap_1('#skF_1', B_709, E_710, '#skF_4'), '#skF_4', B_709) | ~m1_subset_1(k2_tmap_1('#skF_1', B_709, E_710, '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_709)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_709, E_710, '#skF_1'), '#skF_1', B_709) | ~v1_funct_2(k2_tmap_1('#skF_1', B_709, E_710, '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0(B_709)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_709, E_710, '#skF_1')) | ~m1_subset_1(E_710, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_709)))) | ~v1_funct_2(E_710, u1_struct_0('#skF_1'), u1_struct_0(B_709)) | ~v1_funct_1(E_710) | ~l1_pre_topc(B_709) | ~v2_pre_topc(B_709) | v2_struct_0(B_709))), inference(negUnitSimplification, [status(thm)], [c_78, c_60, c_56, c_5141])).
% 8.74/2.85  tff(c_5272, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), '#skF_1', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4740, c_5269])).
% 8.74/2.85  tff(c_5278, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_62, c_66, c_4740, c_64, c_4740, c_4596, c_4740, c_62, c_5272])).
% 8.74/2.85  tff(c_5280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_4597, c_5278])).
% 8.74/2.85  tff(c_5282, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_164])).
% 8.74/2.85  tff(c_5350, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_5346, c_5282])).
% 8.74/2.85  tff(c_5375, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_12, c_5350])).
% 8.74/2.85  tff(c_5379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_218, c_5375])).
% 8.74/2.85  tff(c_5381, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_124])).
% 8.74/2.85  tff(c_5440, plain, (~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_5436, c_5381])).
% 8.74/2.85  tff(c_5443, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_12, c_5440])).
% 8.74/2.85  tff(c_5447, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_221, c_5443])).
% 8.74/2.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.74/2.85  
% 8.74/2.85  Inference rules
% 8.74/2.85  ----------------------
% 8.74/2.85  #Ref     : 0
% 8.74/2.85  #Sup     : 1007
% 8.74/2.85  #Fact    : 0
% 8.74/2.85  #Define  : 0
% 8.74/2.85  #Split   : 40
% 8.74/2.85  #Chain   : 0
% 8.74/2.85  #Close   : 0
% 8.74/2.85  
% 8.74/2.85  Ordering : KBO
% 8.74/2.85  
% 8.74/2.85  Simplification rules
% 8.74/2.85  ----------------------
% 8.74/2.85  #Subsume      : 325
% 8.74/2.85  #Demod        : 3366
% 8.74/2.85  #Tautology    : 300
% 8.74/2.85  #SimpNegUnit  : 283
% 8.74/2.85  #BackRed      : 0
% 8.74/2.85  
% 8.74/2.85  #Partial instantiations: 0
% 8.74/2.85  #Strategies tried      : 1
% 8.74/2.85  
% 8.74/2.85  Timing (in seconds)
% 8.74/2.85  ----------------------
% 8.74/2.86  Preprocessing        : 0.42
% 8.74/2.86  Parsing              : 0.19
% 8.74/2.86  CNF conversion       : 0.05
% 8.74/2.86  Main loop            : 1.59
% 8.74/2.86  Inferencing          : 0.54
% 8.74/2.86  Reduction            : 0.60
% 8.74/2.86  Demodulation         : 0.47
% 8.74/2.86  BG Simplification    : 0.08
% 8.74/2.86  Subsumption          : 0.31
% 8.74/2.86  Abstraction          : 0.07
% 8.74/2.86  MUC search           : 0.00
% 8.74/2.86  Cooper               : 0.00
% 8.74/2.86  Total                : 2.09
% 8.74/2.86  Index Insertion      : 0.00
% 8.74/2.86  Index Deletion       : 0.00
% 8.74/2.86  Index Matching       : 0.00
% 9.18/2.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
