%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:07 EST 2020

% Result     : Theorem 9.86s
% Output     : CNFRefutation 9.86s
% Verified   : 
% Statistics : Number of formulae       :  268 (1363 expanded)
%              Number of leaves         :   44 ( 532 expanded)
%              Depth                    :   10
%              Number of atoms          :  869 (12837 expanded)
%              Number of equality atoms :   39 ( 545 expanded)
%              Maximal formula depth    :   29 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > r4_tsep_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_275,negated_conjecture,(
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

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_152,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

tff(f_134,axiom,(
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

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_112,axiom,(
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

tff(f_56,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_212,axiom,(
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

tff(c_96,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_80,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_239,plain,(
    ! [B_115,A_116] :
      ( l1_pre_topc(B_115)
      | ~ m1_pre_topc(B_115,A_116)
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_242,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_239])).

tff(c_248,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_242])).

tff(c_30,plain,(
    ! [A_24] :
      ( l1_struct_0(A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_90,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_88,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_86,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_84,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_14138,plain,(
    ! [A_1776,B_1777,C_1778,D_1779] :
      ( v1_funct_1(k2_tmap_1(A_1776,B_1777,C_1778,D_1779))
      | ~ l1_struct_0(D_1779)
      | ~ m1_subset_1(C_1778,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1776),u1_struct_0(B_1777))))
      | ~ v1_funct_2(C_1778,u1_struct_0(A_1776),u1_struct_0(B_1777))
      | ~ v1_funct_1(C_1778)
      | ~ l1_struct_0(B_1777)
      | ~ l1_struct_0(A_1776) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_14140,plain,(
    ! [D_1779] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_1779))
      | ~ l1_struct_0(D_1779)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_84,c_14138])).

tff(c_14146,plain,(
    ! [D_1779] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_1779))
      | ~ l1_struct_0(D_1779)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_14140])).

tff(c_14192,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_14146])).

tff(c_14195,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_14192])).

tff(c_14199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_14195])).

tff(c_14200,plain,(
    ! [D_1779] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_1779))
      | ~ l1_struct_0(D_1779) ) ),
    inference(splitRight,[status(thm)],[c_14146])).

tff(c_14202,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_14200])).

tff(c_14205,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_14202])).

tff(c_14209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_14205])).

tff(c_14212,plain,(
    ! [D_1785] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_1785))
      | ~ l1_struct_0(D_1785) ) ),
    inference(splitRight,[status(thm)],[c_14200])).

tff(c_76,plain,(
    m1_pre_topc('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_245,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_239])).

tff(c_251,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_245])).

tff(c_13250,plain,(
    ! [A_1647,B_1648,C_1649,D_1650] :
      ( v1_funct_1(k2_tmap_1(A_1647,B_1648,C_1649,D_1650))
      | ~ l1_struct_0(D_1650)
      | ~ m1_subset_1(C_1649,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1647),u1_struct_0(B_1648))))
      | ~ v1_funct_2(C_1649,u1_struct_0(A_1647),u1_struct_0(B_1648))
      | ~ v1_funct_1(C_1649)
      | ~ l1_struct_0(B_1648)
      | ~ l1_struct_0(A_1647) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_13252,plain,(
    ! [D_1650] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_1650))
      | ~ l1_struct_0(D_1650)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_84,c_13250])).

tff(c_13258,plain,(
    ! [D_1650] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_1650))
      | ~ l1_struct_0(D_1650)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_13252])).

tff(c_13261,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_13258])).

tff(c_13264,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_13261])).

tff(c_13268,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_13264])).

tff(c_13269,plain,(
    ! [D_1650] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_1650))
      | ~ l1_struct_0(D_1650) ) ),
    inference(splitRight,[status(thm)],[c_13258])).

tff(c_13271,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_13269])).

tff(c_13274,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_13271])).

tff(c_13278,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_13274])).

tff(c_13281,plain,(
    ! [D_1654] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_1654))
      | ~ l1_struct_0(D_1654) ) ),
    inference(splitRight,[status(thm)],[c_13269])).

tff(c_94,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_7491,plain,(
    ! [A_943,B_944,C_945,D_946] :
      ( v1_funct_1(k2_tmap_1(A_943,B_944,C_945,D_946))
      | ~ l1_struct_0(D_946)
      | ~ m1_subset_1(C_945,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_943),u1_struct_0(B_944))))
      | ~ v1_funct_2(C_945,u1_struct_0(A_943),u1_struct_0(B_944))
      | ~ v1_funct_1(C_945)
      | ~ l1_struct_0(B_944)
      | ~ l1_struct_0(A_943) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_7493,plain,(
    ! [D_946] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_946))
      | ~ l1_struct_0(D_946)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_84,c_7491])).

tff(c_7499,plain,(
    ! [D_946] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_946))
      | ~ l1_struct_0(D_946)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_7493])).

tff(c_7501,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_7499])).

tff(c_7504,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_7501])).

tff(c_7508,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_7504])).

tff(c_7510,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_7499])).

tff(c_7509,plain,(
    ! [D_946] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_946))
      | ~ l1_struct_0(D_946) ) ),
    inference(splitRight,[status(thm)],[c_7499])).

tff(c_7511,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_7509])).

tff(c_7514,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_7511])).

tff(c_7518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_7514])).

tff(c_7520,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_7509])).

tff(c_7613,plain,(
    ! [A_956,B_957,C_958,D_959] :
      ( v1_funct_2(k2_tmap_1(A_956,B_957,C_958,D_959),u1_struct_0(D_959),u1_struct_0(B_957))
      | ~ l1_struct_0(D_959)
      | ~ m1_subset_1(C_958,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_956),u1_struct_0(B_957))))
      | ~ v1_funct_2(C_958,u1_struct_0(A_956),u1_struct_0(B_957))
      | ~ v1_funct_1(C_958)
      | ~ l1_struct_0(B_957)
      | ~ l1_struct_0(A_956) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_7615,plain,(
    ! [D_959] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_959),u1_struct_0(D_959),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_959)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_84,c_7613])).

tff(c_7667,plain,(
    ! [D_967] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_967),u1_struct_0(D_967),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_967) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7510,c_7520,c_88,c_86,c_7615])).

tff(c_6632,plain,(
    ! [A_820,B_821,C_822,D_823] :
      ( v1_funct_1(k2_tmap_1(A_820,B_821,C_822,D_823))
      | ~ l1_struct_0(D_823)
      | ~ m1_subset_1(C_822,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_820),u1_struct_0(B_821))))
      | ~ v1_funct_2(C_822,u1_struct_0(A_820),u1_struct_0(B_821))
      | ~ v1_funct_1(C_822)
      | ~ l1_struct_0(B_821)
      | ~ l1_struct_0(A_820) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_6634,plain,(
    ! [D_823] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_823))
      | ~ l1_struct_0(D_823)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_84,c_6632])).

tff(c_6640,plain,(
    ! [D_823] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_823))
      | ~ l1_struct_0(D_823)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_6634])).

tff(c_6678,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_6640])).

tff(c_6681,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_6678])).

tff(c_6685,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_6681])).

tff(c_6687,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_6640])).

tff(c_6686,plain,(
    ! [D_823] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_823))
      | ~ l1_struct_0(D_823) ) ),
    inference(splitRight,[status(thm)],[c_6640])).

tff(c_6688,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_6686])).

tff(c_6691,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_6688])).

tff(c_6695,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_6691])).

tff(c_6697,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_6686])).

tff(c_6698,plain,(
    ! [A_834,B_835,C_836,D_837] :
      ( v1_funct_2(k2_tmap_1(A_834,B_835,C_836,D_837),u1_struct_0(D_837),u1_struct_0(B_835))
      | ~ l1_struct_0(D_837)
      | ~ m1_subset_1(C_836,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_834),u1_struct_0(B_835))))
      | ~ v1_funct_2(C_836,u1_struct_0(A_834),u1_struct_0(B_835))
      | ~ v1_funct_1(C_836)
      | ~ l1_struct_0(B_835)
      | ~ l1_struct_0(A_834) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_6700,plain,(
    ! [D_837] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_837),u1_struct_0(D_837),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_837)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_84,c_6698])).

tff(c_6711,plain,(
    ! [D_839] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_839),u1_struct_0(D_839),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_839) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6687,c_6697,c_88,c_86,c_6700])).

tff(c_5772,plain,(
    ! [A_711,B_712,C_713,D_714] :
      ( v1_funct_1(k2_tmap_1(A_711,B_712,C_713,D_714))
      | ~ l1_struct_0(D_714)
      | ~ m1_subset_1(C_713,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_711),u1_struct_0(B_712))))
      | ~ v1_funct_2(C_713,u1_struct_0(A_711),u1_struct_0(B_712))
      | ~ v1_funct_1(C_713)
      | ~ l1_struct_0(B_712)
      | ~ l1_struct_0(A_711) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_5774,plain,(
    ! [D_714] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_714))
      | ~ l1_struct_0(D_714)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_84,c_5772])).

tff(c_5780,plain,(
    ! [D_714] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_714))
      | ~ l1_struct_0(D_714)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_5774])).

tff(c_5782,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_5780])).

tff(c_5785,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_5782])).

tff(c_5789,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_5785])).

tff(c_5791,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_5780])).

tff(c_5790,plain,(
    ! [D_714] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_714))
      | ~ l1_struct_0(D_714) ) ),
    inference(splitRight,[status(thm)],[c_5780])).

tff(c_5792,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_5790])).

tff(c_5795,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_5792])).

tff(c_5799,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_5795])).

tff(c_5801,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_5790])).

tff(c_6031,plain,(
    ! [A_742,B_743,C_744,D_745] :
      ( m1_subset_1(k2_tmap_1(A_742,B_743,C_744,D_745),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_745),u1_struct_0(B_743))))
      | ~ l1_struct_0(D_745)
      | ~ m1_subset_1(C_744,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_742),u1_struct_0(B_743))))
      | ~ v1_funct_2(C_744,u1_struct_0(A_742),u1_struct_0(B_743))
      | ~ v1_funct_1(C_744)
      | ~ l1_struct_0(B_743)
      | ~ l1_struct_0(A_742) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_4711,plain,(
    ! [A_571,B_572,C_573,D_574] :
      ( v1_funct_1(k2_tmap_1(A_571,B_572,C_573,D_574))
      | ~ l1_struct_0(D_574)
      | ~ m1_subset_1(C_573,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_571),u1_struct_0(B_572))))
      | ~ v1_funct_2(C_573,u1_struct_0(A_571),u1_struct_0(B_572))
      | ~ v1_funct_1(C_573)
      | ~ l1_struct_0(B_572)
      | ~ l1_struct_0(A_571) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_4715,plain,(
    ! [D_574] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_574))
      | ~ l1_struct_0(D_574)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_84,c_4711])).

tff(c_4724,plain,(
    ! [D_574] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_574))
      | ~ l1_struct_0(D_574)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_4715])).

tff(c_4767,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4724])).

tff(c_4770,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_4767])).

tff(c_4774,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_4770])).

tff(c_4776,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_4724])).

tff(c_4775,plain,(
    ! [D_574] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_574))
      | ~ l1_struct_0(D_574) ) ),
    inference(splitRight,[status(thm)],[c_4724])).

tff(c_4777,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_4775])).

tff(c_4780,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_4777])).

tff(c_4784,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_4780])).

tff(c_4786,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_4775])).

tff(c_4959,plain,(
    ! [A_605,B_606,C_607,D_608] :
      ( m1_subset_1(k2_tmap_1(A_605,B_606,C_607,D_608),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_608),u1_struct_0(B_606))))
      | ~ l1_struct_0(D_608)
      | ~ m1_subset_1(C_607,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_605),u1_struct_0(B_606))))
      | ~ v1_funct_2(C_607,u1_struct_0(A_605),u1_struct_0(B_606))
      | ~ v1_funct_1(C_607)
      | ~ l1_struct_0(B_606)
      | ~ l1_struct_0(A_605) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_186,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_290,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_176,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_463,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_166,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_406,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_156,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_534,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_146,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_335,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_136,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_471,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_126,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_379,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_116,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_490,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_102,plain,
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
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_200,plain,
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
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_102])).

tff(c_210,plain,
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
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_200])).

tff(c_220,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_210])).

tff(c_1656,plain,(
    ~ v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_463,c_406,c_534,c_335,c_471,c_379,c_490,c_220])).

tff(c_72,plain,(
    r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_100,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_74,plain,(
    k1_tsep_1('#skF_1','#skF_4','#skF_5') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_933,plain,(
    ! [A_208,B_209,C_210] :
      ( m1_pre_topc(k1_tsep_1(A_208,B_209,C_210),A_208)
      | ~ m1_pre_topc(C_210,A_208)
      | v2_struct_0(C_210)
      | ~ m1_pre_topc(B_209,A_208)
      | v2_struct_0(B_209)
      | ~ l1_pre_topc(A_208)
      | v2_struct_0(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_939,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_933])).

tff(c_942,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_80,c_76,c_939])).

tff(c_943,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_82,c_78,c_942])).

tff(c_98,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_92,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_619,plain,(
    ! [A_176,B_177,C_178,D_179] :
      ( k2_partfun1(A_176,B_177,C_178,D_179) = k7_relat_1(C_178,D_179)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177)))
      | ~ v1_funct_1(C_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_625,plain,(
    ! [D_179] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_179) = k7_relat_1('#skF_3',D_179)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_84,c_619])).

tff(c_637,plain,(
    ! [D_179] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_179) = k7_relat_1('#skF_3',D_179) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_625])).

tff(c_1573,plain,(
    ! [A_271,B_272,C_273,D_274] :
      ( k2_partfun1(u1_struct_0(A_271),u1_struct_0(B_272),C_273,u1_struct_0(D_274)) = k2_tmap_1(A_271,B_272,C_273,D_274)
      | ~ m1_pre_topc(D_274,A_271)
      | ~ m1_subset_1(C_273,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_271),u1_struct_0(B_272))))
      | ~ v1_funct_2(C_273,u1_struct_0(A_271),u1_struct_0(B_272))
      | ~ v1_funct_1(C_273)
      | ~ l1_pre_topc(B_272)
      | ~ v2_pre_topc(B_272)
      | v2_struct_0(B_272)
      | ~ l1_pre_topc(A_271)
      | ~ v2_pre_topc(A_271)
      | v2_struct_0(A_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1581,plain,(
    ! [D_274] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_274)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_274)
      | ~ m1_pre_topc(D_274,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_84,c_1573])).

tff(c_1596,plain,(
    ! [D_274] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_274)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_274)
      | ~ m1_pre_topc(D_274,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_92,c_90,c_88,c_86,c_637,c_1581])).

tff(c_1600,plain,(
    ! [D_275] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_275)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_275)
      | ~ m1_pre_topc(D_275,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_94,c_1596])).

tff(c_20,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_262,plain,(
    ! [B_119,A_120] :
      ( v1_relat_1(B_119)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(A_120))
      | ~ v1_relat_1(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_265,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_84,c_262])).

tff(c_271,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_265])).

tff(c_292,plain,(
    ! [C_126,A_127,B_128] :
      ( v4_relat_1(C_126,A_127)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_300,plain,(
    v4_relat_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_84,c_292])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(B_12),A_11)
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_369,plain,(
    ! [B_147,A_148] :
      ( k7_relat_1(B_147,A_148) = B_147
      | ~ r1_tarski(k1_relat_1(B_147),A_148)
      | ~ v1_relat_1(B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_389,plain,(
    ! [B_150,A_151] :
      ( k7_relat_1(B_150,A_151) = B_150
      | ~ v4_relat_1(B_150,A_151)
      | ~ v1_relat_1(B_150) ) ),
    inference(resolution,[status(thm)],[c_18,c_369])).

tff(c_395,plain,
    ( k7_relat_1('#skF_3',u1_struct_0('#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_300,c_389])).

tff(c_404,plain,(
    k7_relat_1('#skF_3',u1_struct_0('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_395])).

tff(c_1610,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1600,c_404])).

tff(c_1625,plain,(
    k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_943,c_1610])).

tff(c_3864,plain,(
    ! [E_479,B_482,D_480,A_478,C_481] :
      ( v5_pre_topc(k2_tmap_1(A_478,B_482,E_479,k1_tsep_1(A_478,C_481,D_480)),k1_tsep_1(A_478,C_481,D_480),B_482)
      | ~ m1_subset_1(k2_tmap_1(A_478,B_482,E_479,D_480),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_480),u1_struct_0(B_482))))
      | ~ v5_pre_topc(k2_tmap_1(A_478,B_482,E_479,D_480),D_480,B_482)
      | ~ v1_funct_2(k2_tmap_1(A_478,B_482,E_479,D_480),u1_struct_0(D_480),u1_struct_0(B_482))
      | ~ v1_funct_1(k2_tmap_1(A_478,B_482,E_479,D_480))
      | ~ m1_subset_1(k2_tmap_1(A_478,B_482,E_479,C_481),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_481),u1_struct_0(B_482))))
      | ~ v5_pre_topc(k2_tmap_1(A_478,B_482,E_479,C_481),C_481,B_482)
      | ~ v1_funct_2(k2_tmap_1(A_478,B_482,E_479,C_481),u1_struct_0(C_481),u1_struct_0(B_482))
      | ~ v1_funct_1(k2_tmap_1(A_478,B_482,E_479,C_481))
      | ~ m1_subset_1(E_479,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_478),u1_struct_0(B_482))))
      | ~ v1_funct_2(E_479,u1_struct_0(A_478),u1_struct_0(B_482))
      | ~ v1_funct_1(E_479)
      | ~ r4_tsep_1(A_478,C_481,D_480)
      | ~ m1_pre_topc(D_480,A_478)
      | v2_struct_0(D_480)
      | ~ m1_pre_topc(C_481,A_478)
      | v2_struct_0(C_481)
      | ~ l1_pre_topc(B_482)
      | ~ v2_pre_topc(B_482)
      | v2_struct_0(B_482)
      | ~ l1_pre_topc(A_478)
      | ~ v2_pre_topc(A_478)
      | v2_struct_0(A_478) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_3870,plain,(
    ! [C_481] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',C_481,'#skF_5')),k1_tsep_1('#skF_1',C_481,'#skF_5'),'#skF_2')
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_481),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_481),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_481),C_481,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_481),u1_struct_0(C_481),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_481))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ r4_tsep_1('#skF_1',C_481,'#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(C_481,'#skF_1')
      | v2_struct_0(C_481)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_490,c_3864])).

tff(c_3882,plain,(
    ! [C_481] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',C_481,'#skF_5')),k1_tsep_1('#skF_1',C_481,'#skF_5'),'#skF_2')
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_481),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_481),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_481),C_481,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_481),u1_struct_0(C_481),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_481))
      | ~ r4_tsep_1('#skF_1',C_481,'#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(C_481,'#skF_1')
      | v2_struct_0(C_481)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_92,c_90,c_76,c_88,c_86,c_84,c_335,c_471,c_379,c_3870])).

tff(c_3981,plain,(
    ! [C_497] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',C_497,'#skF_5')),k1_tsep_1('#skF_1',C_497,'#skF_5'),'#skF_2')
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_497),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_497),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_497),C_497,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_497),u1_struct_0(C_497),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_497))
      | ~ r4_tsep_1('#skF_1',C_497,'#skF_5')
      | ~ m1_pre_topc(C_497,'#skF_1')
      | v2_struct_0(C_497) ) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_94,c_78,c_3882])).

tff(c_3994,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2')
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_534,c_3981])).

tff(c_4010,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_72,c_290,c_463,c_406,c_1625,c_74,c_74,c_3994])).

tff(c_4012,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1656,c_4010])).

tff(c_4014,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_4968,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_4959,c_4014])).

tff(c_4986,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4776,c_4786,c_88,c_86,c_84,c_4968])).

tff(c_4995,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_4986])).

tff(c_4999,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_4995])).

tff(c_5001,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_6040,plain,
    ( ~ l1_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_6031,c_5001])).

tff(c_6058,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5791,c_5801,c_88,c_86,c_84,c_6040])).

tff(c_6067,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_6058])).

tff(c_6071,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_6067])).

tff(c_6073,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_6715,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_6711,c_6073])).

tff(c_6718,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_6715])).

tff(c_6722,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_6718])).

tff(c_6724,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_7671,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_7667,c_6724])).

tff(c_7674,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_7671])).

tff(c_7678,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_7674])).

tff(c_7680,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_8288,plain,(
    ! [A_1050,B_1051,C_1052] :
      ( m1_pre_topc(k1_tsep_1(A_1050,B_1051,C_1052),A_1050)
      | ~ m1_pre_topc(C_1052,A_1050)
      | v2_struct_0(C_1052)
      | ~ m1_pre_topc(B_1051,A_1050)
      | v2_struct_0(B_1051)
      | ~ l1_pre_topc(A_1050)
      | v2_struct_0(A_1050) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_8294,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_8288])).

tff(c_8297,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_80,c_76,c_8294])).

tff(c_8298,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_82,c_78,c_8297])).

tff(c_7854,plain,(
    ! [A_997,B_998,C_999,D_1000] :
      ( k2_partfun1(A_997,B_998,C_999,D_1000) = k7_relat_1(C_999,D_1000)
      | ~ m1_subset_1(C_999,k1_zfmisc_1(k2_zfmisc_1(A_997,B_998)))
      | ~ v1_funct_1(C_999) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_7856,plain,(
    ! [D_1000] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_1000) = k7_relat_1('#skF_3',D_1000)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_84,c_7854])).

tff(c_7862,plain,(
    ! [D_1000] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_1000) = k7_relat_1('#skF_3',D_1000) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_7856])).

tff(c_8856,plain,(
    ! [A_1121,B_1122,C_1123,D_1124] :
      ( k2_partfun1(u1_struct_0(A_1121),u1_struct_0(B_1122),C_1123,u1_struct_0(D_1124)) = k2_tmap_1(A_1121,B_1122,C_1123,D_1124)
      | ~ m1_pre_topc(D_1124,A_1121)
      | ~ m1_subset_1(C_1123,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1121),u1_struct_0(B_1122))))
      | ~ v1_funct_2(C_1123,u1_struct_0(A_1121),u1_struct_0(B_1122))
      | ~ v1_funct_1(C_1123)
      | ~ l1_pre_topc(B_1122)
      | ~ v2_pre_topc(B_1122)
      | v2_struct_0(B_1122)
      | ~ l1_pre_topc(A_1121)
      | ~ v2_pre_topc(A_1121)
      | v2_struct_0(A_1121) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_8860,plain,(
    ! [D_1124] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_1124)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_1124)
      | ~ m1_pre_topc(D_1124,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_84,c_8856])).

tff(c_8867,plain,(
    ! [D_1124] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_1124)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_1124)
      | ~ m1_pre_topc(D_1124,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_92,c_90,c_88,c_86,c_7862,c_8860])).

tff(c_8870,plain,(
    ! [D_1125] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_1125)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_1125)
      | ~ m1_pre_topc(D_1125,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_94,c_8867])).

tff(c_8880,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8870,c_404])).

tff(c_8895,plain,(
    k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8298,c_8880])).

tff(c_7679,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_9387,plain,(
    ! [B_1188,C_1187,D_1186,E_1185,A_1184] :
      ( v5_pre_topc(k2_tmap_1(A_1184,B_1188,E_1185,C_1187),C_1187,B_1188)
      | ~ m1_subset_1(k2_tmap_1(A_1184,B_1188,E_1185,k1_tsep_1(A_1184,C_1187,D_1186)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_1184,C_1187,D_1186)),u1_struct_0(B_1188))))
      | ~ v5_pre_topc(k2_tmap_1(A_1184,B_1188,E_1185,k1_tsep_1(A_1184,C_1187,D_1186)),k1_tsep_1(A_1184,C_1187,D_1186),B_1188)
      | ~ v1_funct_2(k2_tmap_1(A_1184,B_1188,E_1185,k1_tsep_1(A_1184,C_1187,D_1186)),u1_struct_0(k1_tsep_1(A_1184,C_1187,D_1186)),u1_struct_0(B_1188))
      | ~ v1_funct_1(k2_tmap_1(A_1184,B_1188,E_1185,k1_tsep_1(A_1184,C_1187,D_1186)))
      | ~ m1_subset_1(E_1185,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1184),u1_struct_0(B_1188))))
      | ~ v1_funct_2(E_1185,u1_struct_0(A_1184),u1_struct_0(B_1188))
      | ~ v1_funct_1(E_1185)
      | ~ r4_tsep_1(A_1184,C_1187,D_1186)
      | ~ m1_pre_topc(D_1186,A_1184)
      | v2_struct_0(D_1186)
      | ~ m1_pre_topc(C_1187,A_1184)
      | v2_struct_0(C_1187)
      | ~ l1_pre_topc(B_1188)
      | ~ v2_pre_topc(B_1188)
      | v2_struct_0(B_1188)
      | ~ l1_pre_topc(A_1184)
      | ~ v2_pre_topc(A_1184)
      | v2_struct_0(A_1184) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_9400,plain,(
    ! [B_1188,E_1185] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_1188,E_1185,'#skF_4'),'#skF_4',B_1188)
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_1188,E_1185,k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1188))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_1188,E_1185,k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_1188)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_1188,E_1185,k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_1188))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_1188,E_1185,k1_tsep_1('#skF_1','#skF_4','#skF_5')))
      | ~ m1_subset_1(E_1185,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1188))))
      | ~ v1_funct_2(E_1185,u1_struct_0('#skF_1'),u1_struct_0(B_1188))
      | ~ v1_funct_1(E_1185)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_1188)
      | ~ v2_pre_topc(B_1188)
      | v2_struct_0(B_1188)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_9387])).

tff(c_9407,plain,(
    ! [B_1188,E_1185] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_1188,E_1185,'#skF_4'),'#skF_4',B_1188)
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_1188,E_1185,'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1188))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_1188,E_1185,'#skF_1'),'#skF_1',B_1188)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_1188,E_1185,'#skF_1'),u1_struct_0('#skF_1'),u1_struct_0(B_1188))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_1188,E_1185,'#skF_1'))
      | ~ m1_subset_1(E_1185,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1188))))
      | ~ v1_funct_2(E_1185,u1_struct_0('#skF_1'),u1_struct_0(B_1188))
      | ~ v1_funct_1(E_1185)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_1188)
      | ~ v2_pre_topc(B_1188)
      | v2_struct_0(B_1188)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_80,c_76,c_72,c_74,c_74,c_74,c_74,c_74,c_74,c_9400])).

tff(c_9929,plain,(
    ! [B_1238,E_1239] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_1238,E_1239,'#skF_4'),'#skF_4',B_1238)
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_1238,E_1239,'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1238))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_1238,E_1239,'#skF_1'),'#skF_1',B_1238)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_1238,E_1239,'#skF_1'),u1_struct_0('#skF_1'),u1_struct_0(B_1238))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_1238,E_1239,'#skF_1'))
      | ~ m1_subset_1(E_1239,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1238))))
      | ~ v1_funct_2(E_1239,u1_struct_0('#skF_1'),u1_struct_0(B_1238))
      | ~ v1_funct_1(E_1239)
      | ~ l1_pre_topc(B_1238)
      | ~ v2_pre_topc(B_1238)
      | v2_struct_0(B_1238) ) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_82,c_78,c_9407])).

tff(c_9932,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_8895,c_9929])).

tff(c_9941,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_86,c_84,c_88,c_8895,c_86,c_8895,c_7679,c_8895,c_84,c_9932])).

tff(c_9943,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_7680,c_9941])).

tff(c_9945,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_10568,plain,(
    ! [A_1320,B_1321,C_1322] :
      ( m1_pre_topc(k1_tsep_1(A_1320,B_1321,C_1322),A_1320)
      | ~ m1_pre_topc(C_1322,A_1320)
      | v2_struct_0(C_1322)
      | ~ m1_pre_topc(B_1321,A_1320)
      | v2_struct_0(B_1321)
      | ~ l1_pre_topc(A_1320)
      | v2_struct_0(A_1320) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_10574,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_10568])).

tff(c_10577,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_80,c_76,c_10574])).

tff(c_10578,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_82,c_78,c_10577])).

tff(c_10133,plain,(
    ! [A_1270,B_1271,C_1272,D_1273] :
      ( k2_partfun1(A_1270,B_1271,C_1272,D_1273) = k7_relat_1(C_1272,D_1273)
      | ~ m1_subset_1(C_1272,k1_zfmisc_1(k2_zfmisc_1(A_1270,B_1271)))
      | ~ v1_funct_1(C_1272) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10135,plain,(
    ! [D_1273] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_1273) = k7_relat_1('#skF_3',D_1273)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_84,c_10133])).

tff(c_10141,plain,(
    ! [D_1273] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_1273) = k7_relat_1('#skF_3',D_1273) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_10135])).

tff(c_11111,plain,(
    ! [A_1393,B_1394,C_1395,D_1396] :
      ( k2_partfun1(u1_struct_0(A_1393),u1_struct_0(B_1394),C_1395,u1_struct_0(D_1396)) = k2_tmap_1(A_1393,B_1394,C_1395,D_1396)
      | ~ m1_pre_topc(D_1396,A_1393)
      | ~ m1_subset_1(C_1395,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1393),u1_struct_0(B_1394))))
      | ~ v1_funct_2(C_1395,u1_struct_0(A_1393),u1_struct_0(B_1394))
      | ~ v1_funct_1(C_1395)
      | ~ l1_pre_topc(B_1394)
      | ~ v2_pre_topc(B_1394)
      | v2_struct_0(B_1394)
      | ~ l1_pre_topc(A_1393)
      | ~ v2_pre_topc(A_1393)
      | v2_struct_0(A_1393) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_11115,plain,(
    ! [D_1396] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_1396)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_1396)
      | ~ m1_pre_topc(D_1396,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_84,c_11111])).

tff(c_11122,plain,(
    ! [D_1396] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_1396)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_1396)
      | ~ m1_pre_topc(D_1396,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_92,c_90,c_88,c_86,c_10141,c_11115])).

tff(c_11125,plain,(
    ! [D_1397] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_1397)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_1397)
      | ~ m1_pre_topc(D_1397,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_94,c_11122])).

tff(c_9955,plain,(
    ! [B_1241,A_1242] :
      ( k7_relat_1(B_1241,A_1242) = B_1241
      | ~ v4_relat_1(B_1241,A_1242)
      | ~ v1_relat_1(B_1241) ) ),
    inference(resolution,[status(thm)],[c_18,c_369])).

tff(c_9961,plain,
    ( k7_relat_1('#skF_3',u1_struct_0('#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_300,c_9955])).

tff(c_9970,plain,(
    k7_relat_1('#skF_3',u1_struct_0('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_9961])).

tff(c_11135,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_11125,c_9970])).

tff(c_11150,plain,(
    k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10578,c_11135])).

tff(c_9944,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_11561,plain,(
    ! [E_1452,B_1455,C_1454,D_1453,A_1451] :
      ( v5_pre_topc(k2_tmap_1(A_1451,B_1455,E_1452,D_1453),D_1453,B_1455)
      | ~ m1_subset_1(k2_tmap_1(A_1451,B_1455,E_1452,k1_tsep_1(A_1451,C_1454,D_1453)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_1451,C_1454,D_1453)),u1_struct_0(B_1455))))
      | ~ v5_pre_topc(k2_tmap_1(A_1451,B_1455,E_1452,k1_tsep_1(A_1451,C_1454,D_1453)),k1_tsep_1(A_1451,C_1454,D_1453),B_1455)
      | ~ v1_funct_2(k2_tmap_1(A_1451,B_1455,E_1452,k1_tsep_1(A_1451,C_1454,D_1453)),u1_struct_0(k1_tsep_1(A_1451,C_1454,D_1453)),u1_struct_0(B_1455))
      | ~ v1_funct_1(k2_tmap_1(A_1451,B_1455,E_1452,k1_tsep_1(A_1451,C_1454,D_1453)))
      | ~ m1_subset_1(E_1452,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1451),u1_struct_0(B_1455))))
      | ~ v1_funct_2(E_1452,u1_struct_0(A_1451),u1_struct_0(B_1455))
      | ~ v1_funct_1(E_1452)
      | ~ r4_tsep_1(A_1451,C_1454,D_1453)
      | ~ m1_pre_topc(D_1453,A_1451)
      | v2_struct_0(D_1453)
      | ~ m1_pre_topc(C_1454,A_1451)
      | v2_struct_0(C_1454)
      | ~ l1_pre_topc(B_1455)
      | ~ v2_pre_topc(B_1455)
      | v2_struct_0(B_1455)
      | ~ l1_pre_topc(A_1451)
      | ~ v2_pre_topc(A_1451)
      | v2_struct_0(A_1451) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_11571,plain,(
    ! [B_1455,E_1452] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_1455,E_1452,'#skF_5'),'#skF_5',B_1455)
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_1455,E_1452,'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_1455))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_1455,E_1452,k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_1455)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_1455,E_1452,k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_1455))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_1455,E_1452,k1_tsep_1('#skF_1','#skF_4','#skF_5')))
      | ~ m1_subset_1(E_1452,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1455))))
      | ~ v1_funct_2(E_1452,u1_struct_0('#skF_1'),u1_struct_0(B_1455))
      | ~ v1_funct_1(E_1452)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_1455)
      | ~ v2_pre_topc(B_1455)
      | v2_struct_0(B_1455)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_11561])).

tff(c_11578,plain,(
    ! [B_1455,E_1452] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_1455,E_1452,'#skF_5'),'#skF_5',B_1455)
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_1455,E_1452,'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1455))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_1455,E_1452,'#skF_1'),'#skF_1',B_1455)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_1455,E_1452,'#skF_1'),u1_struct_0('#skF_1'),u1_struct_0(B_1455))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_1455,E_1452,'#skF_1'))
      | ~ m1_subset_1(E_1452,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1455))))
      | ~ v1_funct_2(E_1452,u1_struct_0('#skF_1'),u1_struct_0(B_1455))
      | ~ v1_funct_1(E_1452)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_1455)
      | ~ v2_pre_topc(B_1455)
      | v2_struct_0(B_1455)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_80,c_76,c_72,c_74,c_74,c_74,c_74,c_74,c_74,c_11571])).

tff(c_12153,plain,(
    ! [B_1509,E_1510] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_1509,E_1510,'#skF_5'),'#skF_5',B_1509)
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_1509,E_1510,'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1509))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_1509,E_1510,'#skF_1'),'#skF_1',B_1509)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_1509,E_1510,'#skF_1'),u1_struct_0('#skF_1'),u1_struct_0(B_1509))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_1509,E_1510,'#skF_1'))
      | ~ m1_subset_1(E_1510,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1509))))
      | ~ v1_funct_2(E_1510,u1_struct_0('#skF_1'),u1_struct_0(B_1509))
      | ~ v1_funct_1(E_1510)
      | ~ l1_pre_topc(B_1509)
      | ~ v2_pre_topc(B_1509)
      | v2_struct_0(B_1509) ) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_82,c_78,c_11578])).

tff(c_12156,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_11150,c_12153])).

tff(c_12165,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_86,c_84,c_88,c_11150,c_86,c_11150,c_9944,c_11150,c_84,c_12156])).

tff(c_12167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_9945,c_12165])).

tff(c_12169,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_13285,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_13281,c_12169])).

tff(c_13288,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_13285])).

tff(c_13292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_13288])).

tff(c_13294,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_14216,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_14212,c_13294])).

tff(c_14229,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_14216])).

tff(c_14233,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_14229])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:05:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.86/3.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.86/3.53  
% 9.86/3.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.86/3.53  %$ v5_pre_topc > v1_funct_2 > r4_tsep_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.86/3.53  
% 9.86/3.53  %Foreground sorts:
% 9.86/3.53  
% 9.86/3.53  
% 9.86/3.53  %Background operators:
% 9.86/3.53  
% 9.86/3.53  
% 9.86/3.53  %Foreground operators:
% 9.86/3.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.86/3.53  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 9.86/3.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.86/3.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.86/3.53  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.86/3.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.86/3.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.86/3.53  tff(r4_tsep_1, type, r4_tsep_1: ($i * $i * $i) > $o).
% 9.86/3.53  tff('#skF_5', type, '#skF_5': $i).
% 9.86/3.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.86/3.53  tff('#skF_2', type, '#skF_2': $i).
% 9.86/3.53  tff('#skF_3', type, '#skF_3': $i).
% 9.86/3.53  tff('#skF_1', type, '#skF_1': $i).
% 9.86/3.53  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 9.86/3.53  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.86/3.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.86/3.53  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 9.86/3.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.86/3.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.86/3.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.86/3.53  tff('#skF_4', type, '#skF_4': $i).
% 9.86/3.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.86/3.53  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 9.86/3.53  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 9.86/3.53  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 9.86/3.53  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.86/3.53  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.86/3.53  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 9.86/3.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.86/3.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.86/3.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.86/3.53  
% 9.86/3.57  tff(f_275, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => (((A = k1_tsep_1(A, D, E)) & r4_tsep_1(A, D, E)) => ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) <=> (((((((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, C, D), D, B)) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) & v1_funct_1(k2_tmap_1(A, B, C, E))) & v1_funct_2(k2_tmap_1(A, B, C, E), u1_struct_0(E), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, C, E), E, B)) & m1_subset_1(k2_tmap_1(A, B, C, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E), u1_struct_0(B))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_tmap_1)).
% 9.86/3.57  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 9.86/3.57  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 9.86/3.57  tff(f_152, axiom, (![A, B, C, D]: ((((((l1_struct_0(A) & l1_struct_0(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & l1_struct_0(D)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 9.86/3.57  tff(f_134, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 9.86/3.57  tff(f_74, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 9.86/3.57  tff(f_112, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 9.86/3.57  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.86/3.57  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.86/3.57  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.86/3.57  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 9.86/3.57  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 9.86/3.57  tff(f_212, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (r4_tsep_1(A, C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => ((((v1_funct_1(k2_tmap_1(A, B, E, k1_tsep_1(A, C, D))) & v1_funct_2(k2_tmap_1(A, B, E, k1_tsep_1(A, C, D)), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, E, k1_tsep_1(A, C, D)), k1_tsep_1(A, C, D), B)) & m1_subset_1(k2_tmap_1(A, B, E, k1_tsep_1(A, C, D)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) <=> (((((((v1_funct_1(k2_tmap_1(A, B, E, C)) & v1_funct_2(k2_tmap_1(A, B, E, C), u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, E, C), C, B)) & m1_subset_1(k2_tmap_1(A, B, E, C), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(k2_tmap_1(A, B, E, D))) & v1_funct_2(k2_tmap_1(A, B, E, D), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, E, D), D, B)) & m1_subset_1(k2_tmap_1(A, B, E, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_tmap_1)).
% 9.86/3.57  tff(c_96, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_275])).
% 9.86/3.57  tff(c_80, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_275])).
% 9.86/3.57  tff(c_239, plain, (![B_115, A_116]: (l1_pre_topc(B_115) | ~m1_pre_topc(B_115, A_116) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.86/3.57  tff(c_242, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_80, c_239])).
% 9.86/3.57  tff(c_248, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_242])).
% 9.86/3.57  tff(c_30, plain, (![A_24]: (l1_struct_0(A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.86/3.57  tff(c_90, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_275])).
% 9.86/3.57  tff(c_88, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_275])).
% 9.86/3.57  tff(c_86, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_275])).
% 9.86/3.57  tff(c_84, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_275])).
% 9.86/3.57  tff(c_14138, plain, (![A_1776, B_1777, C_1778, D_1779]: (v1_funct_1(k2_tmap_1(A_1776, B_1777, C_1778, D_1779)) | ~l1_struct_0(D_1779) | ~m1_subset_1(C_1778, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1776), u1_struct_0(B_1777)))) | ~v1_funct_2(C_1778, u1_struct_0(A_1776), u1_struct_0(B_1777)) | ~v1_funct_1(C_1778) | ~l1_struct_0(B_1777) | ~l1_struct_0(A_1776))), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.86/3.57  tff(c_14140, plain, (![D_1779]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_1779)) | ~l1_struct_0(D_1779) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_84, c_14138])).
% 9.86/3.57  tff(c_14146, plain, (![D_1779]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_1779)) | ~l1_struct_0(D_1779) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_14140])).
% 9.86/3.57  tff(c_14192, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_14146])).
% 9.86/3.57  tff(c_14195, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_14192])).
% 9.86/3.57  tff(c_14199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_14195])).
% 9.86/3.57  tff(c_14200, plain, (![D_1779]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_1779)) | ~l1_struct_0(D_1779))), inference(splitRight, [status(thm)], [c_14146])).
% 9.86/3.57  tff(c_14202, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_14200])).
% 9.86/3.57  tff(c_14205, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_14202])).
% 9.86/3.57  tff(c_14209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_14205])).
% 9.86/3.57  tff(c_14212, plain, (![D_1785]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_1785)) | ~l1_struct_0(D_1785))), inference(splitRight, [status(thm)], [c_14200])).
% 9.86/3.57  tff(c_76, plain, (m1_pre_topc('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_275])).
% 9.86/3.57  tff(c_245, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_76, c_239])).
% 9.86/3.57  tff(c_251, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_245])).
% 9.86/3.57  tff(c_13250, plain, (![A_1647, B_1648, C_1649, D_1650]: (v1_funct_1(k2_tmap_1(A_1647, B_1648, C_1649, D_1650)) | ~l1_struct_0(D_1650) | ~m1_subset_1(C_1649, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1647), u1_struct_0(B_1648)))) | ~v1_funct_2(C_1649, u1_struct_0(A_1647), u1_struct_0(B_1648)) | ~v1_funct_1(C_1649) | ~l1_struct_0(B_1648) | ~l1_struct_0(A_1647))), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.86/3.57  tff(c_13252, plain, (![D_1650]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_1650)) | ~l1_struct_0(D_1650) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_84, c_13250])).
% 9.86/3.57  tff(c_13258, plain, (![D_1650]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_1650)) | ~l1_struct_0(D_1650) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_13252])).
% 9.86/3.57  tff(c_13261, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_13258])).
% 9.86/3.57  tff(c_13264, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_13261])).
% 9.86/3.57  tff(c_13268, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_13264])).
% 9.86/3.57  tff(c_13269, plain, (![D_1650]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_1650)) | ~l1_struct_0(D_1650))), inference(splitRight, [status(thm)], [c_13258])).
% 9.86/3.57  tff(c_13271, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_13269])).
% 9.86/3.57  tff(c_13274, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_13271])).
% 9.86/3.57  tff(c_13278, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_13274])).
% 9.86/3.57  tff(c_13281, plain, (![D_1654]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_1654)) | ~l1_struct_0(D_1654))), inference(splitRight, [status(thm)], [c_13269])).
% 9.86/3.57  tff(c_94, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_275])).
% 9.86/3.57  tff(c_7491, plain, (![A_943, B_944, C_945, D_946]: (v1_funct_1(k2_tmap_1(A_943, B_944, C_945, D_946)) | ~l1_struct_0(D_946) | ~m1_subset_1(C_945, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_943), u1_struct_0(B_944)))) | ~v1_funct_2(C_945, u1_struct_0(A_943), u1_struct_0(B_944)) | ~v1_funct_1(C_945) | ~l1_struct_0(B_944) | ~l1_struct_0(A_943))), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.86/3.57  tff(c_7493, plain, (![D_946]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_946)) | ~l1_struct_0(D_946) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_84, c_7491])).
% 9.86/3.57  tff(c_7499, plain, (![D_946]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_946)) | ~l1_struct_0(D_946) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_7493])).
% 9.86/3.57  tff(c_7501, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_7499])).
% 9.86/3.57  tff(c_7504, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_7501])).
% 9.86/3.57  tff(c_7508, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_7504])).
% 9.86/3.57  tff(c_7510, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_7499])).
% 9.86/3.57  tff(c_7509, plain, (![D_946]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_946)) | ~l1_struct_0(D_946))), inference(splitRight, [status(thm)], [c_7499])).
% 9.86/3.57  tff(c_7511, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_7509])).
% 9.86/3.57  tff(c_7514, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_7511])).
% 9.86/3.57  tff(c_7518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_7514])).
% 9.86/3.57  tff(c_7520, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_7509])).
% 9.86/3.57  tff(c_7613, plain, (![A_956, B_957, C_958, D_959]: (v1_funct_2(k2_tmap_1(A_956, B_957, C_958, D_959), u1_struct_0(D_959), u1_struct_0(B_957)) | ~l1_struct_0(D_959) | ~m1_subset_1(C_958, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_956), u1_struct_0(B_957)))) | ~v1_funct_2(C_958, u1_struct_0(A_956), u1_struct_0(B_957)) | ~v1_funct_1(C_958) | ~l1_struct_0(B_957) | ~l1_struct_0(A_956))), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.86/3.57  tff(c_7615, plain, (![D_959]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_959), u1_struct_0(D_959), u1_struct_0('#skF_2')) | ~l1_struct_0(D_959) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_84, c_7613])).
% 9.86/3.57  tff(c_7667, plain, (![D_967]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_967), u1_struct_0(D_967), u1_struct_0('#skF_2')) | ~l1_struct_0(D_967))), inference(demodulation, [status(thm), theory('equality')], [c_7510, c_7520, c_88, c_86, c_7615])).
% 9.86/3.57  tff(c_6632, plain, (![A_820, B_821, C_822, D_823]: (v1_funct_1(k2_tmap_1(A_820, B_821, C_822, D_823)) | ~l1_struct_0(D_823) | ~m1_subset_1(C_822, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_820), u1_struct_0(B_821)))) | ~v1_funct_2(C_822, u1_struct_0(A_820), u1_struct_0(B_821)) | ~v1_funct_1(C_822) | ~l1_struct_0(B_821) | ~l1_struct_0(A_820))), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.86/3.57  tff(c_6634, plain, (![D_823]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_823)) | ~l1_struct_0(D_823) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_84, c_6632])).
% 9.86/3.57  tff(c_6640, plain, (![D_823]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_823)) | ~l1_struct_0(D_823) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_6634])).
% 9.86/3.57  tff(c_6678, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_6640])).
% 9.86/3.57  tff(c_6681, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_6678])).
% 9.86/3.57  tff(c_6685, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_6681])).
% 9.86/3.57  tff(c_6687, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_6640])).
% 9.86/3.57  tff(c_6686, plain, (![D_823]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_823)) | ~l1_struct_0(D_823))), inference(splitRight, [status(thm)], [c_6640])).
% 9.86/3.57  tff(c_6688, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_6686])).
% 9.86/3.57  tff(c_6691, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_6688])).
% 9.86/3.57  tff(c_6695, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_6691])).
% 9.86/3.57  tff(c_6697, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_6686])).
% 9.86/3.57  tff(c_6698, plain, (![A_834, B_835, C_836, D_837]: (v1_funct_2(k2_tmap_1(A_834, B_835, C_836, D_837), u1_struct_0(D_837), u1_struct_0(B_835)) | ~l1_struct_0(D_837) | ~m1_subset_1(C_836, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_834), u1_struct_0(B_835)))) | ~v1_funct_2(C_836, u1_struct_0(A_834), u1_struct_0(B_835)) | ~v1_funct_1(C_836) | ~l1_struct_0(B_835) | ~l1_struct_0(A_834))), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.86/3.57  tff(c_6700, plain, (![D_837]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_837), u1_struct_0(D_837), u1_struct_0('#skF_2')) | ~l1_struct_0(D_837) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_84, c_6698])).
% 9.86/3.57  tff(c_6711, plain, (![D_839]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_839), u1_struct_0(D_839), u1_struct_0('#skF_2')) | ~l1_struct_0(D_839))), inference(demodulation, [status(thm), theory('equality')], [c_6687, c_6697, c_88, c_86, c_6700])).
% 9.86/3.57  tff(c_5772, plain, (![A_711, B_712, C_713, D_714]: (v1_funct_1(k2_tmap_1(A_711, B_712, C_713, D_714)) | ~l1_struct_0(D_714) | ~m1_subset_1(C_713, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_711), u1_struct_0(B_712)))) | ~v1_funct_2(C_713, u1_struct_0(A_711), u1_struct_0(B_712)) | ~v1_funct_1(C_713) | ~l1_struct_0(B_712) | ~l1_struct_0(A_711))), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.86/3.57  tff(c_5774, plain, (![D_714]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_714)) | ~l1_struct_0(D_714) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_84, c_5772])).
% 9.86/3.57  tff(c_5780, plain, (![D_714]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_714)) | ~l1_struct_0(D_714) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_5774])).
% 9.86/3.57  tff(c_5782, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_5780])).
% 9.86/3.57  tff(c_5785, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_5782])).
% 9.86/3.57  tff(c_5789, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_5785])).
% 9.86/3.57  tff(c_5791, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_5780])).
% 9.86/3.57  tff(c_5790, plain, (![D_714]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_714)) | ~l1_struct_0(D_714))), inference(splitRight, [status(thm)], [c_5780])).
% 9.86/3.57  tff(c_5792, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_5790])).
% 9.86/3.57  tff(c_5795, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_5792])).
% 9.86/3.57  tff(c_5799, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_5795])).
% 9.86/3.57  tff(c_5801, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_5790])).
% 9.86/3.57  tff(c_6031, plain, (![A_742, B_743, C_744, D_745]: (m1_subset_1(k2_tmap_1(A_742, B_743, C_744, D_745), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_745), u1_struct_0(B_743)))) | ~l1_struct_0(D_745) | ~m1_subset_1(C_744, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_742), u1_struct_0(B_743)))) | ~v1_funct_2(C_744, u1_struct_0(A_742), u1_struct_0(B_743)) | ~v1_funct_1(C_744) | ~l1_struct_0(B_743) | ~l1_struct_0(A_742))), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.86/3.57  tff(c_4711, plain, (![A_571, B_572, C_573, D_574]: (v1_funct_1(k2_tmap_1(A_571, B_572, C_573, D_574)) | ~l1_struct_0(D_574) | ~m1_subset_1(C_573, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_571), u1_struct_0(B_572)))) | ~v1_funct_2(C_573, u1_struct_0(A_571), u1_struct_0(B_572)) | ~v1_funct_1(C_573) | ~l1_struct_0(B_572) | ~l1_struct_0(A_571))), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.86/3.57  tff(c_4715, plain, (![D_574]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_574)) | ~l1_struct_0(D_574) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_84, c_4711])).
% 9.86/3.57  tff(c_4724, plain, (![D_574]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_574)) | ~l1_struct_0(D_574) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_4715])).
% 9.86/3.57  tff(c_4767, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_4724])).
% 9.86/3.57  tff(c_4770, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_4767])).
% 9.86/3.57  tff(c_4774, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_4770])).
% 9.86/3.57  tff(c_4776, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_4724])).
% 9.86/3.57  tff(c_4775, plain, (![D_574]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_574)) | ~l1_struct_0(D_574))), inference(splitRight, [status(thm)], [c_4724])).
% 9.86/3.57  tff(c_4777, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_4775])).
% 9.86/3.57  tff(c_4780, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_4777])).
% 9.86/3.57  tff(c_4784, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_4780])).
% 9.86/3.57  tff(c_4786, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_4775])).
% 9.86/3.57  tff(c_4959, plain, (![A_605, B_606, C_607, D_608]: (m1_subset_1(k2_tmap_1(A_605, B_606, C_607, D_608), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_608), u1_struct_0(B_606)))) | ~l1_struct_0(D_608) | ~m1_subset_1(C_607, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_605), u1_struct_0(B_606)))) | ~v1_funct_2(C_607, u1_struct_0(A_605), u1_struct_0(B_606)) | ~v1_funct_1(C_607) | ~l1_struct_0(B_606) | ~l1_struct_0(A_605))), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.86/3.57  tff(c_82, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_275])).
% 9.86/3.57  tff(c_186, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_275])).
% 9.86/3.57  tff(c_290, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_186])).
% 9.86/3.57  tff(c_176, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_275])).
% 9.86/3.57  tff(c_463, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_176])).
% 9.86/3.57  tff(c_166, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_275])).
% 9.86/3.57  tff(c_406, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_166])).
% 9.86/3.57  tff(c_156, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_275])).
% 9.86/3.57  tff(c_534, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_156])).
% 9.86/3.57  tff(c_146, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_275])).
% 9.86/3.57  tff(c_335, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_146])).
% 9.86/3.57  tff(c_136, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_275])).
% 9.86/3.57  tff(c_471, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_136])).
% 9.86/3.57  tff(c_126, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_275])).
% 9.86/3.57  tff(c_379, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2')), inference(splitLeft, [status(thm)], [c_126])).
% 9.86/3.57  tff(c_116, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_275])).
% 9.86/3.57  tff(c_490, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_116])).
% 9.86/3.57  tff(c_102, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_275])).
% 9.86/3.57  tff(c_200, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_102])).
% 9.86/3.57  tff(c_210, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_200])).
% 9.86/3.57  tff(c_220, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_210])).
% 9.86/3.57  tff(c_1656, plain, (~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_290, c_463, c_406, c_534, c_335, c_471, c_379, c_490, c_220])).
% 9.86/3.57  tff(c_72, plain, (r4_tsep_1('#skF_1', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_275])).
% 9.86/3.57  tff(c_100, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_275])).
% 9.86/3.57  tff(c_78, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_275])).
% 9.86/3.57  tff(c_74, plain, (k1_tsep_1('#skF_1', '#skF_4', '#skF_5')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_275])).
% 9.86/3.57  tff(c_933, plain, (![A_208, B_209, C_210]: (m1_pre_topc(k1_tsep_1(A_208, B_209, C_210), A_208) | ~m1_pre_topc(C_210, A_208) | v2_struct_0(C_210) | ~m1_pre_topc(B_209, A_208) | v2_struct_0(B_209) | ~l1_pre_topc(A_208) | v2_struct_0(A_208))), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.86/3.57  tff(c_939, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_74, c_933])).
% 9.86/3.57  tff(c_942, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_80, c_76, c_939])).
% 9.86/3.57  tff(c_943, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_100, c_82, c_78, c_942])).
% 9.86/3.57  tff(c_98, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_275])).
% 9.86/3.57  tff(c_92, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_275])).
% 9.86/3.57  tff(c_619, plain, (![A_176, B_177, C_178, D_179]: (k2_partfun1(A_176, B_177, C_178, D_179)=k7_relat_1(C_178, D_179) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))) | ~v1_funct_1(C_178))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.86/3.57  tff(c_625, plain, (![D_179]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_179)=k7_relat_1('#skF_3', D_179) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_84, c_619])).
% 9.86/3.57  tff(c_637, plain, (![D_179]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_179)=k7_relat_1('#skF_3', D_179))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_625])).
% 9.86/3.57  tff(c_1573, plain, (![A_271, B_272, C_273, D_274]: (k2_partfun1(u1_struct_0(A_271), u1_struct_0(B_272), C_273, u1_struct_0(D_274))=k2_tmap_1(A_271, B_272, C_273, D_274) | ~m1_pre_topc(D_274, A_271) | ~m1_subset_1(C_273, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_271), u1_struct_0(B_272)))) | ~v1_funct_2(C_273, u1_struct_0(A_271), u1_struct_0(B_272)) | ~v1_funct_1(C_273) | ~l1_pre_topc(B_272) | ~v2_pre_topc(B_272) | v2_struct_0(B_272) | ~l1_pre_topc(A_271) | ~v2_pre_topc(A_271) | v2_struct_0(A_271))), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.86/3.57  tff(c_1581, plain, (![D_274]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_274))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_274) | ~m1_pre_topc(D_274, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_84, c_1573])).
% 9.86/3.57  tff(c_1596, plain, (![D_274]: (k7_relat_1('#skF_3', u1_struct_0(D_274))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_274) | ~m1_pre_topc(D_274, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_92, c_90, c_88, c_86, c_637, c_1581])).
% 9.86/3.57  tff(c_1600, plain, (![D_275]: (k7_relat_1('#skF_3', u1_struct_0(D_275))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_275) | ~m1_pre_topc(D_275, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_100, c_94, c_1596])).
% 9.86/3.57  tff(c_20, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.86/3.57  tff(c_262, plain, (![B_119, A_120]: (v1_relat_1(B_119) | ~m1_subset_1(B_119, k1_zfmisc_1(A_120)) | ~v1_relat_1(A_120))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.86/3.57  tff(c_265, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_84, c_262])).
% 9.86/3.57  tff(c_271, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_265])).
% 9.86/3.57  tff(c_292, plain, (![C_126, A_127, B_128]: (v4_relat_1(C_126, A_127) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.86/3.57  tff(c_300, plain, (v4_relat_1('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_84, c_292])).
% 9.86/3.57  tff(c_18, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(B_12), A_11) | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.86/3.57  tff(c_369, plain, (![B_147, A_148]: (k7_relat_1(B_147, A_148)=B_147 | ~r1_tarski(k1_relat_1(B_147), A_148) | ~v1_relat_1(B_147))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.86/3.57  tff(c_389, plain, (![B_150, A_151]: (k7_relat_1(B_150, A_151)=B_150 | ~v4_relat_1(B_150, A_151) | ~v1_relat_1(B_150))), inference(resolution, [status(thm)], [c_18, c_369])).
% 9.86/3.57  tff(c_395, plain, (k7_relat_1('#skF_3', u1_struct_0('#skF_1'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_300, c_389])).
% 9.86/3.57  tff(c_404, plain, (k7_relat_1('#skF_3', u1_struct_0('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_271, c_395])).
% 9.86/3.57  tff(c_1610, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1600, c_404])).
% 9.86/3.57  tff(c_1625, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_943, c_1610])).
% 9.86/3.57  tff(c_3864, plain, (![E_479, B_482, D_480, A_478, C_481]: (v5_pre_topc(k2_tmap_1(A_478, B_482, E_479, k1_tsep_1(A_478, C_481, D_480)), k1_tsep_1(A_478, C_481, D_480), B_482) | ~m1_subset_1(k2_tmap_1(A_478, B_482, E_479, D_480), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_480), u1_struct_0(B_482)))) | ~v5_pre_topc(k2_tmap_1(A_478, B_482, E_479, D_480), D_480, B_482) | ~v1_funct_2(k2_tmap_1(A_478, B_482, E_479, D_480), u1_struct_0(D_480), u1_struct_0(B_482)) | ~v1_funct_1(k2_tmap_1(A_478, B_482, E_479, D_480)) | ~m1_subset_1(k2_tmap_1(A_478, B_482, E_479, C_481), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_481), u1_struct_0(B_482)))) | ~v5_pre_topc(k2_tmap_1(A_478, B_482, E_479, C_481), C_481, B_482) | ~v1_funct_2(k2_tmap_1(A_478, B_482, E_479, C_481), u1_struct_0(C_481), u1_struct_0(B_482)) | ~v1_funct_1(k2_tmap_1(A_478, B_482, E_479, C_481)) | ~m1_subset_1(E_479, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_478), u1_struct_0(B_482)))) | ~v1_funct_2(E_479, u1_struct_0(A_478), u1_struct_0(B_482)) | ~v1_funct_1(E_479) | ~r4_tsep_1(A_478, C_481, D_480) | ~m1_pre_topc(D_480, A_478) | v2_struct_0(D_480) | ~m1_pre_topc(C_481, A_478) | v2_struct_0(C_481) | ~l1_pre_topc(B_482) | ~v2_pre_topc(B_482) | v2_struct_0(B_482) | ~l1_pre_topc(A_478) | ~v2_pre_topc(A_478) | v2_struct_0(A_478))), inference(cnfTransformation, [status(thm)], [f_212])).
% 9.86/3.57  tff(c_3870, plain, (![C_481]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', C_481, '#skF_5')), k1_tsep_1('#skF_1', C_481, '#skF_5'), '#skF_2') | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_481), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_481), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_481), C_481, '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_481), u1_struct_0(C_481), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_481)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~r4_tsep_1('#skF_1', C_481, '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc(C_481, '#skF_1') | v2_struct_0(C_481) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_490, c_3864])).
% 9.86/3.57  tff(c_3882, plain, (![C_481]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', C_481, '#skF_5')), k1_tsep_1('#skF_1', C_481, '#skF_5'), '#skF_2') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_481), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_481), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_481), C_481, '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_481), u1_struct_0(C_481), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_481)) | ~r4_tsep_1('#skF_1', C_481, '#skF_5') | v2_struct_0('#skF_5') | ~m1_pre_topc(C_481, '#skF_1') | v2_struct_0(C_481) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_92, c_90, c_76, c_88, c_86, c_84, c_335, c_471, c_379, c_3870])).
% 9.86/3.57  tff(c_3981, plain, (![C_497]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', C_497, '#skF_5')), k1_tsep_1('#skF_1', C_497, '#skF_5'), '#skF_2') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_497), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_497), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_497), C_497, '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_497), u1_struct_0(C_497), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_497)) | ~r4_tsep_1('#skF_1', C_497, '#skF_5') | ~m1_pre_topc(C_497, '#skF_1') | v2_struct_0(C_497))), inference(negUnitSimplification, [status(thm)], [c_100, c_94, c_78, c_3882])).
% 9.86/3.57  tff(c_3994, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_2') | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_534, c_3981])).
% 9.86/3.57  tff(c_4010, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_72, c_290, c_463, c_406, c_1625, c_74, c_74, c_3994])).
% 9.86/3.57  tff(c_4012, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_1656, c_4010])).
% 9.86/3.57  tff(c_4014, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_156])).
% 9.86/3.57  tff(c_4968, plain, (~l1_struct_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_4959, c_4014])).
% 9.86/3.57  tff(c_4986, plain, (~l1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4776, c_4786, c_88, c_86, c_84, c_4968])).
% 9.86/3.57  tff(c_4995, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_30, c_4986])).
% 9.86/3.57  tff(c_4999, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_248, c_4995])).
% 9.86/3.57  tff(c_5001, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_116])).
% 9.86/3.57  tff(c_6040, plain, (~l1_struct_0('#skF_5') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_6031, c_5001])).
% 9.86/3.57  tff(c_6058, plain, (~l1_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5791, c_5801, c_88, c_86, c_84, c_6040])).
% 9.86/3.57  tff(c_6067, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_30, c_6058])).
% 9.86/3.57  tff(c_6071, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_251, c_6067])).
% 9.86/3.57  tff(c_6073, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_136])).
% 9.86/3.57  tff(c_6715, plain, (~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_6711, c_6073])).
% 9.86/3.57  tff(c_6718, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_30, c_6715])).
% 9.86/3.57  tff(c_6722, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_251, c_6718])).
% 9.86/3.57  tff(c_6724, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_176])).
% 9.86/3.57  tff(c_7671, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_7667, c_6724])).
% 9.86/3.57  tff(c_7674, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_30, c_7671])).
% 9.86/3.57  tff(c_7678, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_248, c_7674])).
% 9.86/3.57  tff(c_7680, plain, (~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_166])).
% 9.86/3.57  tff(c_8288, plain, (![A_1050, B_1051, C_1052]: (m1_pre_topc(k1_tsep_1(A_1050, B_1051, C_1052), A_1050) | ~m1_pre_topc(C_1052, A_1050) | v2_struct_0(C_1052) | ~m1_pre_topc(B_1051, A_1050) | v2_struct_0(B_1051) | ~l1_pre_topc(A_1050) | v2_struct_0(A_1050))), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.86/3.57  tff(c_8294, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_74, c_8288])).
% 9.86/3.57  tff(c_8297, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_80, c_76, c_8294])).
% 9.86/3.57  tff(c_8298, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_100, c_82, c_78, c_8297])).
% 9.86/3.57  tff(c_7854, plain, (![A_997, B_998, C_999, D_1000]: (k2_partfun1(A_997, B_998, C_999, D_1000)=k7_relat_1(C_999, D_1000) | ~m1_subset_1(C_999, k1_zfmisc_1(k2_zfmisc_1(A_997, B_998))) | ~v1_funct_1(C_999))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.86/3.57  tff(c_7856, plain, (![D_1000]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_1000)=k7_relat_1('#skF_3', D_1000) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_84, c_7854])).
% 9.86/3.57  tff(c_7862, plain, (![D_1000]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_1000)=k7_relat_1('#skF_3', D_1000))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_7856])).
% 9.86/3.57  tff(c_8856, plain, (![A_1121, B_1122, C_1123, D_1124]: (k2_partfun1(u1_struct_0(A_1121), u1_struct_0(B_1122), C_1123, u1_struct_0(D_1124))=k2_tmap_1(A_1121, B_1122, C_1123, D_1124) | ~m1_pre_topc(D_1124, A_1121) | ~m1_subset_1(C_1123, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1121), u1_struct_0(B_1122)))) | ~v1_funct_2(C_1123, u1_struct_0(A_1121), u1_struct_0(B_1122)) | ~v1_funct_1(C_1123) | ~l1_pre_topc(B_1122) | ~v2_pre_topc(B_1122) | v2_struct_0(B_1122) | ~l1_pre_topc(A_1121) | ~v2_pre_topc(A_1121) | v2_struct_0(A_1121))), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.86/3.57  tff(c_8860, plain, (![D_1124]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_1124))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_1124) | ~m1_pre_topc(D_1124, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_84, c_8856])).
% 9.86/3.57  tff(c_8867, plain, (![D_1124]: (k7_relat_1('#skF_3', u1_struct_0(D_1124))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_1124) | ~m1_pre_topc(D_1124, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_92, c_90, c_88, c_86, c_7862, c_8860])).
% 9.86/3.57  tff(c_8870, plain, (![D_1125]: (k7_relat_1('#skF_3', u1_struct_0(D_1125))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_1125) | ~m1_pre_topc(D_1125, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_100, c_94, c_8867])).
% 9.86/3.57  tff(c_8880, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8870, c_404])).
% 9.86/3.57  tff(c_8895, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8298, c_8880])).
% 9.86/3.57  tff(c_7679, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_166])).
% 9.86/3.57  tff(c_9387, plain, (![B_1188, C_1187, D_1186, E_1185, A_1184]: (v5_pre_topc(k2_tmap_1(A_1184, B_1188, E_1185, C_1187), C_1187, B_1188) | ~m1_subset_1(k2_tmap_1(A_1184, B_1188, E_1185, k1_tsep_1(A_1184, C_1187, D_1186)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_1184, C_1187, D_1186)), u1_struct_0(B_1188)))) | ~v5_pre_topc(k2_tmap_1(A_1184, B_1188, E_1185, k1_tsep_1(A_1184, C_1187, D_1186)), k1_tsep_1(A_1184, C_1187, D_1186), B_1188) | ~v1_funct_2(k2_tmap_1(A_1184, B_1188, E_1185, k1_tsep_1(A_1184, C_1187, D_1186)), u1_struct_0(k1_tsep_1(A_1184, C_1187, D_1186)), u1_struct_0(B_1188)) | ~v1_funct_1(k2_tmap_1(A_1184, B_1188, E_1185, k1_tsep_1(A_1184, C_1187, D_1186))) | ~m1_subset_1(E_1185, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1184), u1_struct_0(B_1188)))) | ~v1_funct_2(E_1185, u1_struct_0(A_1184), u1_struct_0(B_1188)) | ~v1_funct_1(E_1185) | ~r4_tsep_1(A_1184, C_1187, D_1186) | ~m1_pre_topc(D_1186, A_1184) | v2_struct_0(D_1186) | ~m1_pre_topc(C_1187, A_1184) | v2_struct_0(C_1187) | ~l1_pre_topc(B_1188) | ~v2_pre_topc(B_1188) | v2_struct_0(B_1188) | ~l1_pre_topc(A_1184) | ~v2_pre_topc(A_1184) | v2_struct_0(A_1184))), inference(cnfTransformation, [status(thm)], [f_212])).
% 9.86/3.57  tff(c_9400, plain, (![B_1188, E_1185]: (v5_pre_topc(k2_tmap_1('#skF_1', B_1188, E_1185, '#skF_4'), '#skF_4', B_1188) | ~m1_subset_1(k2_tmap_1('#skF_1', B_1188, E_1185, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_1188)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_1188, E_1185, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_1188) | ~v1_funct_2(k2_tmap_1('#skF_1', B_1188, E_1185, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_1188)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_1188, E_1185, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'))) | ~m1_subset_1(E_1185, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_1188)))) | ~v1_funct_2(E_1185, u1_struct_0('#skF_1'), u1_struct_0(B_1188)) | ~v1_funct_1(E_1185) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_1188) | ~v2_pre_topc(B_1188) | v2_struct_0(B_1188) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_9387])).
% 9.86/3.57  tff(c_9407, plain, (![B_1188, E_1185]: (v5_pre_topc(k2_tmap_1('#skF_1', B_1188, E_1185, '#skF_4'), '#skF_4', B_1188) | ~m1_subset_1(k2_tmap_1('#skF_1', B_1188, E_1185, '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_1188)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_1188, E_1185, '#skF_1'), '#skF_1', B_1188) | ~v1_funct_2(k2_tmap_1('#skF_1', B_1188, E_1185, '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0(B_1188)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_1188, E_1185, '#skF_1')) | ~m1_subset_1(E_1185, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_1188)))) | ~v1_funct_2(E_1185, u1_struct_0('#skF_1'), u1_struct_0(B_1188)) | ~v1_funct_1(E_1185) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_1188) | ~v2_pre_topc(B_1188) | v2_struct_0(B_1188) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_80, c_76, c_72, c_74, c_74, c_74, c_74, c_74, c_74, c_9400])).
% 9.86/3.57  tff(c_9929, plain, (![B_1238, E_1239]: (v5_pre_topc(k2_tmap_1('#skF_1', B_1238, E_1239, '#skF_4'), '#skF_4', B_1238) | ~m1_subset_1(k2_tmap_1('#skF_1', B_1238, E_1239, '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_1238)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_1238, E_1239, '#skF_1'), '#skF_1', B_1238) | ~v1_funct_2(k2_tmap_1('#skF_1', B_1238, E_1239, '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0(B_1238)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_1238, E_1239, '#skF_1')) | ~m1_subset_1(E_1239, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_1238)))) | ~v1_funct_2(E_1239, u1_struct_0('#skF_1'), u1_struct_0(B_1238)) | ~v1_funct_1(E_1239) | ~l1_pre_topc(B_1238) | ~v2_pre_topc(B_1238) | v2_struct_0(B_1238))), inference(negUnitSimplification, [status(thm)], [c_100, c_82, c_78, c_9407])).
% 9.86/3.57  tff(c_9932, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), '#skF_1', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8895, c_9929])).
% 9.86/3.57  tff(c_9941, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_86, c_84, c_88, c_8895, c_86, c_8895, c_7679, c_8895, c_84, c_9932])).
% 9.86/3.57  tff(c_9943, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_7680, c_9941])).
% 9.86/3.57  tff(c_9945, plain, (~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_126])).
% 9.86/3.57  tff(c_10568, plain, (![A_1320, B_1321, C_1322]: (m1_pre_topc(k1_tsep_1(A_1320, B_1321, C_1322), A_1320) | ~m1_pre_topc(C_1322, A_1320) | v2_struct_0(C_1322) | ~m1_pre_topc(B_1321, A_1320) | v2_struct_0(B_1321) | ~l1_pre_topc(A_1320) | v2_struct_0(A_1320))), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.86/3.57  tff(c_10574, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_74, c_10568])).
% 9.86/3.57  tff(c_10577, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_80, c_76, c_10574])).
% 9.86/3.57  tff(c_10578, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_100, c_82, c_78, c_10577])).
% 9.86/3.57  tff(c_10133, plain, (![A_1270, B_1271, C_1272, D_1273]: (k2_partfun1(A_1270, B_1271, C_1272, D_1273)=k7_relat_1(C_1272, D_1273) | ~m1_subset_1(C_1272, k1_zfmisc_1(k2_zfmisc_1(A_1270, B_1271))) | ~v1_funct_1(C_1272))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.86/3.57  tff(c_10135, plain, (![D_1273]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_1273)=k7_relat_1('#skF_3', D_1273) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_84, c_10133])).
% 9.86/3.57  tff(c_10141, plain, (![D_1273]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_1273)=k7_relat_1('#skF_3', D_1273))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_10135])).
% 9.86/3.57  tff(c_11111, plain, (![A_1393, B_1394, C_1395, D_1396]: (k2_partfun1(u1_struct_0(A_1393), u1_struct_0(B_1394), C_1395, u1_struct_0(D_1396))=k2_tmap_1(A_1393, B_1394, C_1395, D_1396) | ~m1_pre_topc(D_1396, A_1393) | ~m1_subset_1(C_1395, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1393), u1_struct_0(B_1394)))) | ~v1_funct_2(C_1395, u1_struct_0(A_1393), u1_struct_0(B_1394)) | ~v1_funct_1(C_1395) | ~l1_pre_topc(B_1394) | ~v2_pre_topc(B_1394) | v2_struct_0(B_1394) | ~l1_pre_topc(A_1393) | ~v2_pre_topc(A_1393) | v2_struct_0(A_1393))), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.86/3.57  tff(c_11115, plain, (![D_1396]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_1396))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_1396) | ~m1_pre_topc(D_1396, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_84, c_11111])).
% 9.86/3.57  tff(c_11122, plain, (![D_1396]: (k7_relat_1('#skF_3', u1_struct_0(D_1396))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_1396) | ~m1_pre_topc(D_1396, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_92, c_90, c_88, c_86, c_10141, c_11115])).
% 9.86/3.57  tff(c_11125, plain, (![D_1397]: (k7_relat_1('#skF_3', u1_struct_0(D_1397))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_1397) | ~m1_pre_topc(D_1397, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_100, c_94, c_11122])).
% 9.86/3.57  tff(c_9955, plain, (![B_1241, A_1242]: (k7_relat_1(B_1241, A_1242)=B_1241 | ~v4_relat_1(B_1241, A_1242) | ~v1_relat_1(B_1241))), inference(resolution, [status(thm)], [c_18, c_369])).
% 9.86/3.57  tff(c_9961, plain, (k7_relat_1('#skF_3', u1_struct_0('#skF_1'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_300, c_9955])).
% 9.86/3.57  tff(c_9970, plain, (k7_relat_1('#skF_3', u1_struct_0('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_271, c_9961])).
% 9.86/3.57  tff(c_11135, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_11125, c_9970])).
% 9.86/3.57  tff(c_11150, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10578, c_11135])).
% 9.86/3.57  tff(c_9944, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_126])).
% 9.86/3.57  tff(c_11561, plain, (![E_1452, B_1455, C_1454, D_1453, A_1451]: (v5_pre_topc(k2_tmap_1(A_1451, B_1455, E_1452, D_1453), D_1453, B_1455) | ~m1_subset_1(k2_tmap_1(A_1451, B_1455, E_1452, k1_tsep_1(A_1451, C_1454, D_1453)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_1451, C_1454, D_1453)), u1_struct_0(B_1455)))) | ~v5_pre_topc(k2_tmap_1(A_1451, B_1455, E_1452, k1_tsep_1(A_1451, C_1454, D_1453)), k1_tsep_1(A_1451, C_1454, D_1453), B_1455) | ~v1_funct_2(k2_tmap_1(A_1451, B_1455, E_1452, k1_tsep_1(A_1451, C_1454, D_1453)), u1_struct_0(k1_tsep_1(A_1451, C_1454, D_1453)), u1_struct_0(B_1455)) | ~v1_funct_1(k2_tmap_1(A_1451, B_1455, E_1452, k1_tsep_1(A_1451, C_1454, D_1453))) | ~m1_subset_1(E_1452, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1451), u1_struct_0(B_1455)))) | ~v1_funct_2(E_1452, u1_struct_0(A_1451), u1_struct_0(B_1455)) | ~v1_funct_1(E_1452) | ~r4_tsep_1(A_1451, C_1454, D_1453) | ~m1_pre_topc(D_1453, A_1451) | v2_struct_0(D_1453) | ~m1_pre_topc(C_1454, A_1451) | v2_struct_0(C_1454) | ~l1_pre_topc(B_1455) | ~v2_pre_topc(B_1455) | v2_struct_0(B_1455) | ~l1_pre_topc(A_1451) | ~v2_pre_topc(A_1451) | v2_struct_0(A_1451))), inference(cnfTransformation, [status(thm)], [f_212])).
% 9.86/3.57  tff(c_11571, plain, (![B_1455, E_1452]: (v5_pre_topc(k2_tmap_1('#skF_1', B_1455, E_1452, '#skF_5'), '#skF_5', B_1455) | ~m1_subset_1(k2_tmap_1('#skF_1', B_1455, E_1452, '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_1455)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_1455, E_1452, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_1455) | ~v1_funct_2(k2_tmap_1('#skF_1', B_1455, E_1452, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_1455)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_1455, E_1452, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'))) | ~m1_subset_1(E_1452, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_1455)))) | ~v1_funct_2(E_1452, u1_struct_0('#skF_1'), u1_struct_0(B_1455)) | ~v1_funct_1(E_1452) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_1455) | ~v2_pre_topc(B_1455) | v2_struct_0(B_1455) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_11561])).
% 9.86/3.57  tff(c_11578, plain, (![B_1455, E_1452]: (v5_pre_topc(k2_tmap_1('#skF_1', B_1455, E_1452, '#skF_5'), '#skF_5', B_1455) | ~m1_subset_1(k2_tmap_1('#skF_1', B_1455, E_1452, '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_1455)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_1455, E_1452, '#skF_1'), '#skF_1', B_1455) | ~v1_funct_2(k2_tmap_1('#skF_1', B_1455, E_1452, '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0(B_1455)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_1455, E_1452, '#skF_1')) | ~m1_subset_1(E_1452, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_1455)))) | ~v1_funct_2(E_1452, u1_struct_0('#skF_1'), u1_struct_0(B_1455)) | ~v1_funct_1(E_1452) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_1455) | ~v2_pre_topc(B_1455) | v2_struct_0(B_1455) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_80, c_76, c_72, c_74, c_74, c_74, c_74, c_74, c_74, c_11571])).
% 9.86/3.57  tff(c_12153, plain, (![B_1509, E_1510]: (v5_pre_topc(k2_tmap_1('#skF_1', B_1509, E_1510, '#skF_5'), '#skF_5', B_1509) | ~m1_subset_1(k2_tmap_1('#skF_1', B_1509, E_1510, '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_1509)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_1509, E_1510, '#skF_1'), '#skF_1', B_1509) | ~v1_funct_2(k2_tmap_1('#skF_1', B_1509, E_1510, '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0(B_1509)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_1509, E_1510, '#skF_1')) | ~m1_subset_1(E_1510, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_1509)))) | ~v1_funct_2(E_1510, u1_struct_0('#skF_1'), u1_struct_0(B_1509)) | ~v1_funct_1(E_1510) | ~l1_pre_topc(B_1509) | ~v2_pre_topc(B_1509) | v2_struct_0(B_1509))), inference(negUnitSimplification, [status(thm)], [c_100, c_82, c_78, c_11578])).
% 9.86/3.57  tff(c_12156, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), '#skF_1', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_11150, c_12153])).
% 9.86/3.57  tff(c_12165, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_86, c_84, c_88, c_11150, c_86, c_11150, c_9944, c_11150, c_84, c_12156])).
% 9.86/3.57  tff(c_12167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_9945, c_12165])).
% 9.86/3.57  tff(c_12169, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_146])).
% 9.86/3.57  tff(c_13285, plain, (~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_13281, c_12169])).
% 9.86/3.57  tff(c_13288, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_30, c_13285])).
% 9.86/3.57  tff(c_13292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_251, c_13288])).
% 9.86/3.57  tff(c_13294, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_186])).
% 9.86/3.57  tff(c_14216, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_14212, c_13294])).
% 9.86/3.57  tff(c_14229, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_30, c_14216])).
% 9.86/3.57  tff(c_14233, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_248, c_14229])).
% 9.86/3.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.86/3.57  
% 9.86/3.57  Inference rules
% 9.86/3.57  ----------------------
% 9.86/3.57  #Ref     : 0
% 9.86/3.57  #Sup     : 2741
% 9.86/3.57  #Fact    : 0
% 9.86/3.57  #Define  : 0
% 9.86/3.57  #Split   : 51
% 9.86/3.57  #Chain   : 0
% 9.86/3.57  #Close   : 0
% 9.86/3.57  
% 9.86/3.57  Ordering : KBO
% 9.86/3.57  
% 9.86/3.57  Simplification rules
% 9.86/3.57  ----------------------
% 9.86/3.57  #Subsume      : 352
% 9.86/3.57  #Demod        : 2154
% 9.86/3.57  #Tautology    : 625
% 9.86/3.57  #SimpNegUnit  : 95
% 9.86/3.57  #BackRed      : 0
% 9.86/3.57  
% 9.86/3.57  #Partial instantiations: 0
% 9.86/3.57  #Strategies tried      : 1
% 9.86/3.57  
% 9.86/3.57  Timing (in seconds)
% 9.86/3.57  ----------------------
% 9.86/3.57  Preprocessing        : 0.46
% 9.86/3.57  Parsing              : 0.22
% 9.86/3.57  CNF conversion       : 0.06
% 9.86/3.57  Main loop            : 2.29
% 9.86/3.57  Inferencing          : 0.75
% 9.86/3.57  Reduction            : 0.82
% 9.86/3.57  Demodulation         : 0.61
% 9.86/3.57  BG Simplification    : 0.09
% 9.86/3.57  Subsumption          : 0.49
% 9.86/3.57  Abstraction          : 0.10
% 9.86/3.57  MUC search           : 0.00
% 9.86/3.57  Cooper               : 0.00
% 9.86/3.57  Total                : 2.83
% 9.86/3.57  Index Insertion      : 0.00
% 9.86/3.57  Index Deletion       : 0.00
% 9.86/3.57  Index Matching       : 0.00
% 9.86/3.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
