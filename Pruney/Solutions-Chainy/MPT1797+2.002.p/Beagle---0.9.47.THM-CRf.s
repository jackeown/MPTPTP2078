%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:56 EST 2020

% Result     : Theorem 29.98s
% Output     : CNFRefutation 30.20s
% Verified   : 
% Statistics : Number of formulae       :  343 (11619 expanded)
%              Number of leaves         :   46 (4071 expanded)
%              Depth                    :   19
%              Number of atoms          : 1063 (39306 expanded)
%              Number of equality atoms :  146 (5414 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k7_tmap_1 > k6_tmap_1 > k5_tmap_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > u1_pre_topc > k6_partfun1 > k3_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k7_tmap_1,type,(
    k7_tmap_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k3_struct_0,type,(
    k3_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_206,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> ( v1_funct_1(k7_tmap_1(A,B))
                & v1_funct_2(k7_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B)))
                & v5_pre_topc(k7_tmap_1(A,B),A,k6_tmap_1(A,B))
                & m1_subset_1(k7_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B))))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_tmap_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_168,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_112,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_185,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(k6_tmap_1(A,B))))
             => ( C = B
               => v3_pre_topc(C,k6_tmap_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_tmap_1)).

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_97,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k7_tmap_1(A,B) = k6_partfun1(u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_tmap_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( ( k2_struct_0(B) = k1_xboole_0
                 => k2_struct_0(A) = k1_xboole_0 )
               => ( v5_pre_topc(C,A,B)
                <=> ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                     => ( v3_pre_topc(D,B)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D),A) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_2)).

tff(f_127,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_funct_1(k7_tmap_1(A,B))
        & v1_funct_2(k7_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B)))
        & m1_subset_1(k7_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_154,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,u1_pre_topc(A))
          <=> u1_pre_topc(A) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_72,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_22,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_100,plain,(
    ! [A_62] :
      ( u1_struct_0(A_62) = k2_struct_0(A_62)
      | ~ l1_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_105,plain,(
    ! [A_63] :
      ( u1_struct_0(A_63) = k2_struct_0(A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(resolution,[status(thm)],[c_22,c_100])).

tff(c_109,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_105])).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_110,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_70])).

tff(c_74,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_13997,plain,(
    ! [A_594,B_595] :
      ( u1_struct_0(k6_tmap_1(A_594,B_595)) = u1_struct_0(A_594)
      | ~ m1_subset_1(B_595,k1_zfmisc_1(u1_struct_0(A_594)))
      | ~ l1_pre_topc(A_594)
      | ~ v2_pre_topc(A_594)
      | v2_struct_0(A_594) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_14010,plain,(
    ! [B_595] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_595)) = u1_struct_0('#skF_2')
      | ~ m1_subset_1(B_595,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_13997])).

tff(c_14017,plain,(
    ! [B_595] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_595)) = k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_595,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_109,c_14010])).

tff(c_14019,plain,(
    ! [B_596] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_596)) = k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_596,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_14017])).

tff(c_14028,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_110,c_14019])).

tff(c_13627,plain,(
    ! [A_569,B_570] :
      ( l1_pre_topc(k6_tmap_1(A_569,B_570))
      | ~ m1_subset_1(B_570,k1_zfmisc_1(u1_struct_0(A_569)))
      | ~ l1_pre_topc(A_569)
      | ~ v2_pre_topc(A_569)
      | v2_struct_0(A_569) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_13634,plain,(
    ! [B_570] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_570))
      | ~ m1_subset_1(B_570,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_13627])).

tff(c_13637,plain,(
    ! [B_570] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_570))
      | ~ m1_subset_1(B_570,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_13634])).

tff(c_13650,plain,(
    ! [B_572] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_572))
      | ~ m1_subset_1(B_572,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_13637])).

tff(c_13659,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_110,c_13650])).

tff(c_104,plain,(
    ! [A_15] :
      ( u1_struct_0(A_15) = k2_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(resolution,[status(thm)],[c_22,c_100])).

tff(c_13663,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_13659,c_104])).

tff(c_14029,plain,(
    k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14028,c_13663])).

tff(c_12694,plain,(
    ! [A_498,B_499] :
      ( u1_struct_0(k6_tmap_1(A_498,B_499)) = u1_struct_0(A_498)
      | ~ m1_subset_1(B_499,k1_zfmisc_1(u1_struct_0(A_498)))
      | ~ l1_pre_topc(A_498)
      | ~ v2_pre_topc(A_498)
      | v2_struct_0(A_498) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_12707,plain,(
    ! [B_499] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_499)) = u1_struct_0('#skF_2')
      | ~ m1_subset_1(B_499,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_12694])).

tff(c_12714,plain,(
    ! [B_499] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_499)) = k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_499,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_109,c_12707])).

tff(c_12716,plain,(
    ! [B_500] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_500)) = k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_500,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_12714])).

tff(c_12725,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_110,c_12716])).

tff(c_12379,plain,(
    ! [A_476,B_477] :
      ( l1_pre_topc(k6_tmap_1(A_476,B_477))
      | ~ m1_subset_1(B_477,k1_zfmisc_1(u1_struct_0(A_476)))
      | ~ l1_pre_topc(A_476)
      | ~ v2_pre_topc(A_476)
      | v2_struct_0(A_476) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_12386,plain,(
    ! [B_477] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_477))
      | ~ m1_subset_1(B_477,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_12379])).

tff(c_12389,plain,(
    ! [B_477] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_477))
      | ~ m1_subset_1(B_477,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_12386])).

tff(c_12403,plain,(
    ! [B_480] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_480))
      | ~ m1_subset_1(B_480,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_12389])).

tff(c_12412,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_110,c_12403])).

tff(c_12416,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_12412,c_104])).

tff(c_12726,plain,(
    k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12725,c_12416])).

tff(c_96,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_115,plain,(
    v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_92,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_186,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_92])).

tff(c_187,plain,(
    v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_88,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2',k6_tmap_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_138,plain,(
    v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2',k6_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_84,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))))) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_188,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_84])).

tff(c_189,plain,(
    m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_78,plain,
    ( ~ m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))))
    | ~ v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_248,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_187,c_109,c_138,c_189,c_109,c_78])).

tff(c_677,plain,(
    ! [A_125,B_126] :
      ( u1_struct_0(k6_tmap_1(A_125,B_126)) = u1_struct_0(A_125)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125)
      | ~ v2_pre_topc(A_125)
      | v2_struct_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_690,plain,(
    ! [B_126] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_126)) = u1_struct_0('#skF_2')
      | ~ m1_subset_1(B_126,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_677])).

tff(c_697,plain,(
    ! [B_126] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_126)) = k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_126,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_109,c_690])).

tff(c_710,plain,(
    ! [B_128] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_128)) = k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_128,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_697])).

tff(c_719,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_110,c_710])).

tff(c_1428,plain,(
    ! [C_163,A_164] :
      ( v3_pre_topc(C_163,k6_tmap_1(A_164,C_163))
      | ~ m1_subset_1(C_163,k1_zfmisc_1(u1_struct_0(k6_tmap_1(A_164,C_163))))
      | ~ m1_subset_1(C_163,k1_zfmisc_1(u1_struct_0(A_164)))
      | ~ l1_pre_topc(A_164)
      | ~ v2_pre_topc(A_164)
      | v2_struct_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_1434,plain,
    ( v3_pre_topc('#skF_3',k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_719,c_1428])).

tff(c_1443,plain,
    ( v3_pre_topc('#skF_3',k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_110,c_109,c_110,c_1434])).

tff(c_1444,plain,(
    v3_pre_topc('#skF_3',k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1443])).

tff(c_273,plain,(
    ! [A_97,B_98] :
      ( l1_pre_topc(k6_tmap_1(A_97,B_98))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97)
      | ~ v2_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_280,plain,(
    ! [B_98] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_98))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_273])).

tff(c_283,plain,(
    ! [B_98] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_98))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_280])).

tff(c_285,plain,(
    ! [B_99] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_99))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_283])).

tff(c_294,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_110,c_285])).

tff(c_298,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_294,c_104])).

tff(c_720,plain,(
    k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_298])).

tff(c_200,plain,(
    ! [A_77,B_78,C_79,D_80] :
      ( k8_relset_1(A_77,B_78,C_79,D_80) = k10_relat_1(C_79,D_80)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_206,plain,(
    ! [D_80] : k8_relset_1(k2_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')),k7_tmap_1('#skF_2','#skF_3'),D_80) = k10_relat_1(k7_tmap_1('#skF_2','#skF_3'),D_80) ),
    inference(resolution,[status(thm)],[c_189,c_200])).

tff(c_579,plain,(
    ! [D_80] : k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0(k6_tmap_1('#skF_2','#skF_3')),k7_tmap_1('#skF_2','#skF_3'),D_80) = k10_relat_1(k7_tmap_1('#skF_2','#skF_3'),D_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_206])).

tff(c_1320,plain,(
    ! [D_158] : k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k7_tmap_1('#skF_2','#skF_3'),D_158) = k10_relat_1(k7_tmap_1('#skF_2','#skF_3'),D_158) ),
    inference(demodulation,[status(thm),theory(equality)],[c_720,c_579])).

tff(c_825,plain,(
    ! [A_130,B_131] :
      ( k7_tmap_1(A_130,B_131) = k6_partfun1(u1_struct_0(A_130))
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130)
      | ~ v2_pre_topc(A_130)
      | v2_struct_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_838,plain,(
    ! [B_131] :
      ( k7_tmap_1('#skF_2',B_131) = k6_partfun1(u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_131,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_825])).

tff(c_845,plain,(
    ! [B_131] :
      ( k7_tmap_1('#skF_2',B_131) = k6_partfun1(k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_131,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_109,c_838])).

tff(c_947,plain,(
    ! [B_132] :
      ( k7_tmap_1('#skF_2',B_132) = k6_partfun1(k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_132,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_845])).

tff(c_956,plain,(
    k6_partfun1(k2_struct_0('#skF_2')) = k7_tmap_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_110,c_947])).

tff(c_140,plain,(
    ! [A_72,B_73] :
      ( k8_relset_1(A_72,A_72,k6_partfun1(A_72),B_73) = B_73
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_146,plain,(
    k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k6_partfun1(k2_struct_0('#skF_2')),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_110,c_140])).

tff(c_958,plain,(
    k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k7_tmap_1('#skF_2','#skF_3'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_956,c_146])).

tff(c_1326,plain,(
    k10_relat_1(k7_tmap_1('#skF_2','#skF_3'),'#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1320,c_958])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1545,plain,(
    ! [B_165,A_166,C_167] :
      ( k2_struct_0(B_165) = k1_xboole_0
      | v3_pre_topc('#skF_1'(A_166,B_165,C_167),B_165)
      | v5_pre_topc(C_167,A_166,B_165)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_166),u1_struct_0(B_165))))
      | ~ v1_funct_2(C_167,u1_struct_0(A_166),u1_struct_0(B_165))
      | ~ v1_funct_1(C_167)
      | ~ l1_pre_topc(B_165)
      | ~ l1_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3191,plain,(
    ! [B_231,A_232,A_233] :
      ( k2_struct_0(B_231) = k1_xboole_0
      | v3_pre_topc('#skF_1'(A_232,B_231,A_233),B_231)
      | v5_pre_topc(A_233,A_232,B_231)
      | ~ v1_funct_2(A_233,u1_struct_0(A_232),u1_struct_0(B_231))
      | ~ v1_funct_1(A_233)
      | ~ l1_pre_topc(B_231)
      | ~ l1_pre_topc(A_232)
      | ~ r1_tarski(A_233,k2_zfmisc_1(u1_struct_0(A_232),u1_struct_0(B_231))) ) ),
    inference(resolution,[status(thm)],[c_10,c_1545])).

tff(c_3213,plain,(
    ! [A_232,A_233] :
      ( k2_struct_0('#skF_2') = k1_xboole_0
      | v3_pre_topc('#skF_1'(A_232,'#skF_2',A_233),'#skF_2')
      | v5_pre_topc(A_233,A_232,'#skF_2')
      | ~ v1_funct_2(A_233,u1_struct_0(A_232),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(A_233)
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_232)
      | ~ r1_tarski(A_233,k2_zfmisc_1(u1_struct_0(A_232),k2_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_3191])).

tff(c_3229,plain,(
    ! [A_232,A_233] :
      ( k2_struct_0('#skF_2') = k1_xboole_0
      | v3_pre_topc('#skF_1'(A_232,'#skF_2',A_233),'#skF_2')
      | v5_pre_topc(A_233,A_232,'#skF_2')
      | ~ v1_funct_2(A_233,u1_struct_0(A_232),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(A_233)
      | ~ l1_pre_topc(A_232)
      | ~ r1_tarski(A_233,k2_zfmisc_1(u1_struct_0(A_232),k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_109,c_3213])).

tff(c_3864,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3229])).

tff(c_3934,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3864,c_110])).

tff(c_3906,plain,(
    k7_tmap_1('#skF_2','#skF_3') = k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3864,c_956])).

tff(c_4987,plain,(
    k10_relat_1(k6_partfun1(k1_xboole_0),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3906,c_1326])).

tff(c_3935,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3864,c_109])).

tff(c_3914,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3864,c_719])).

tff(c_1335,plain,(
    ! [A_159,B_160] :
      ( m1_subset_1(k7_tmap_1(A_159,B_160),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_159),u1_struct_0(k6_tmap_1(A_159,B_160)))))
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ l1_pre_topc(A_159)
      | ~ v2_pre_topc(A_159)
      | v2_struct_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_12,plain,(
    ! [A_5,B_6,C_7,D_8] :
      ( k8_relset_1(A_5,B_6,C_7,D_8) = k10_relat_1(C_7,D_8)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1361,plain,(
    ! [A_159,B_160,D_8] :
      ( k8_relset_1(u1_struct_0(A_159),u1_struct_0(k6_tmap_1(A_159,B_160)),k7_tmap_1(A_159,B_160),D_8) = k10_relat_1(k7_tmap_1(A_159,B_160),D_8)
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ l1_pre_topc(A_159)
      | ~ v2_pre_topc(A_159)
      | v2_struct_0(A_159) ) ),
    inference(resolution,[status(thm)],[c_1335,c_12])).

tff(c_5220,plain,(
    ! [D_8] :
      ( k8_relset_1(u1_struct_0('#skF_2'),k1_xboole_0,k7_tmap_1('#skF_2','#skF_3'),D_8) = k10_relat_1(k7_tmap_1('#skF_2','#skF_3'),D_8)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3914,c_1361])).

tff(c_5465,plain,(
    ! [D_8] :
      ( k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),D_8) = k10_relat_1(k6_partfun1(k1_xboole_0),D_8)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_3934,c_3935,c_3906,c_3906,c_3935,c_5220])).

tff(c_5466,plain,(
    ! [D_8] : k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),D_8) = k10_relat_1(k6_partfun1(k1_xboole_0),D_8) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_5465])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1602,plain,(
    ! [A_169,A_170] :
      ( k7_tmap_1(A_169,A_170) = k6_partfun1(u1_struct_0(A_169))
      | ~ l1_pre_topc(A_169)
      | ~ v2_pre_topc(A_169)
      | v2_struct_0(A_169)
      | ~ r1_tarski(A_170,u1_struct_0(A_169)) ) ),
    inference(resolution,[status(thm)],[c_10,c_825])).

tff(c_1624,plain,(
    ! [A_171] :
      ( k7_tmap_1(A_171,u1_struct_0(A_171)) = k6_partfun1(u1_struct_0(A_171))
      | ~ l1_pre_topc(A_171)
      | ~ v2_pre_topc(A_171)
      | v2_struct_0(A_171) ) ),
    inference(resolution,[status(thm)],[c_6,c_1602])).

tff(c_535,plain,(
    ! [A_113,B_114] :
      ( v1_funct_1(k7_tmap_1(A_113,B_114))
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113)
      | ~ v2_pre_topc(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_606,plain,(
    ! [A_119,A_120] :
      ( v1_funct_1(k7_tmap_1(A_119,A_120))
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119)
      | v2_struct_0(A_119)
      | ~ r1_tarski(A_120,u1_struct_0(A_119)) ) ),
    inference(resolution,[status(thm)],[c_10,c_535])).

tff(c_627,plain,(
    ! [A_119] :
      ( v1_funct_1(k7_tmap_1(A_119,u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119)
      | v2_struct_0(A_119) ) ),
    inference(resolution,[status(thm)],[c_6,c_606])).

tff(c_1648,plain,(
    ! [A_171] :
      ( v1_funct_1(k6_partfun1(u1_struct_0(A_171)))
      | ~ l1_pre_topc(A_171)
      | ~ v2_pre_topc(A_171)
      | v2_struct_0(A_171)
      | ~ l1_pre_topc(A_171)
      | ~ v2_pre_topc(A_171)
      | v2_struct_0(A_171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1624,c_627])).

tff(c_4073,plain,
    ( v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3935,c_1648])).

tff(c_4292,plain,
    ( v1_funct_1(k6_partfun1(k1_xboole_0))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_74,c_72,c_4073])).

tff(c_4293,plain,(
    v1_funct_1(k6_partfun1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_4292])).

tff(c_50,plain,(
    ! [A_43,B_44] :
      ( v1_funct_2(k7_tmap_1(A_43,B_44),u1_struct_0(A_43),u1_struct_0(k6_tmap_1(A_43,B_44)))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43)
      | ~ v2_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_5325,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),k1_xboole_0)
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3914,c_50])).

tff(c_5548,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_3934,c_3935,c_3906,c_3935,c_5325])).

tff(c_5549,plain,(
    v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_5548])).

tff(c_4988,plain,(
    v5_pre_topc(k6_partfun1(k1_xboole_0),'#skF_2',k6_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3906,c_138])).

tff(c_48,plain,(
    ! [A_43,B_44] :
      ( m1_subset_1(k7_tmap_1(A_43,B_44),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_43),u1_struct_0(k6_tmap_1(A_43,B_44)))))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43)
      | ~ v2_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2928,plain,(
    ! [A_219,B_220,C_221,D_222] :
      ( k2_struct_0(A_219) != k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0(A_219),u1_struct_0(B_220),C_221,D_222),A_219)
      | ~ v3_pre_topc(D_222,B_220)
      | ~ m1_subset_1(D_222,k1_zfmisc_1(u1_struct_0(B_220)))
      | ~ v5_pre_topc(C_221,A_219,B_220)
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_219),u1_struct_0(B_220))))
      | ~ v1_funct_2(C_221,u1_struct_0(A_219),u1_struct_0(B_220))
      | ~ v1_funct_1(C_221)
      | ~ l1_pre_topc(B_220)
      | ~ l1_pre_topc(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_6518,plain,(
    ! [A_280,B_281,D_282] :
      ( k2_struct_0(A_280) != k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0(A_280),u1_struct_0(k6_tmap_1(A_280,B_281)),k7_tmap_1(A_280,B_281),D_282),A_280)
      | ~ v3_pre_topc(D_282,k6_tmap_1(A_280,B_281))
      | ~ m1_subset_1(D_282,k1_zfmisc_1(u1_struct_0(k6_tmap_1(A_280,B_281))))
      | ~ v5_pre_topc(k7_tmap_1(A_280,B_281),A_280,k6_tmap_1(A_280,B_281))
      | ~ v1_funct_2(k7_tmap_1(A_280,B_281),u1_struct_0(A_280),u1_struct_0(k6_tmap_1(A_280,B_281)))
      | ~ v1_funct_1(k7_tmap_1(A_280,B_281))
      | ~ l1_pre_topc(k6_tmap_1(A_280,B_281))
      | ~ m1_subset_1(B_281,k1_zfmisc_1(u1_struct_0(A_280)))
      | ~ l1_pre_topc(A_280)
      | ~ v2_pre_topc(A_280)
      | v2_struct_0(A_280) ) ),
    inference(resolution,[status(thm)],[c_48,c_2928])).

tff(c_6544,plain,(
    ! [D_282] :
      ( k2_struct_0('#skF_2') != k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')),k6_partfun1(k1_xboole_0),D_282),'#skF_2')
      | ~ v3_pre_topc(D_282,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_282,k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))))
      | ~ v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
      | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3906,c_6518])).

tff(c_6586,plain,(
    ! [D_282] :
      ( v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),D_282),'#skF_2')
      | ~ v3_pre_topc(D_282,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_282,k1_zfmisc_1(k1_xboole_0))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_3934,c_3935,c_294,c_4293,c_3906,c_5549,c_3914,c_3906,c_3935,c_4988,c_3906,c_3914,c_3914,c_3935,c_3864,c_6544])).

tff(c_6587,plain,(
    ! [D_282] :
      ( v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),D_282),'#skF_2')
      | ~ v3_pre_topc(D_282,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_282,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_6586])).

tff(c_9069,plain,(
    ! [D_339] :
      ( v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),D_339),'#skF_2')
      | ~ v3_pre_topc(D_339,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_339,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5466,c_6587])).

tff(c_9081,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3',k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4987,c_9069])).

tff(c_9087,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3934,c_1444,c_9081])).

tff(c_9089,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_248,c_9087])).

tff(c_9091,plain,(
    k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3229])).

tff(c_316,plain,(
    v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_187])).

tff(c_803,plain,(
    v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_720,c_316])).

tff(c_800,plain,(
    ! [D_80] : k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k7_tmap_1('#skF_2','#skF_3'),D_80) = k10_relat_1(k7_tmap_1('#skF_2','#skF_3'),D_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_720,c_579])).

tff(c_2877,plain,(
    ! [B_215,A_216,C_217,D_218] :
      ( k2_struct_0(B_215) = k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0(A_216),u1_struct_0(B_215),C_217,D_218),A_216)
      | ~ v3_pre_topc(D_218,B_215)
      | ~ m1_subset_1(D_218,k1_zfmisc_1(u1_struct_0(B_215)))
      | ~ v5_pre_topc(C_217,A_216,B_215)
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_216),u1_struct_0(B_215))))
      | ~ v1_funct_2(C_217,u1_struct_0(A_216),u1_struct_0(B_215))
      | ~ v1_funct_1(C_217)
      | ~ l1_pre_topc(B_215)
      | ~ l1_pre_topc(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_12172,plain,(
    ! [A_449,B_450,D_451] :
      ( k2_struct_0(k6_tmap_1(A_449,B_450)) = k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0(A_449),u1_struct_0(k6_tmap_1(A_449,B_450)),k7_tmap_1(A_449,B_450),D_451),A_449)
      | ~ v3_pre_topc(D_451,k6_tmap_1(A_449,B_450))
      | ~ m1_subset_1(D_451,k1_zfmisc_1(u1_struct_0(k6_tmap_1(A_449,B_450))))
      | ~ v5_pre_topc(k7_tmap_1(A_449,B_450),A_449,k6_tmap_1(A_449,B_450))
      | ~ v1_funct_2(k7_tmap_1(A_449,B_450),u1_struct_0(A_449),u1_struct_0(k6_tmap_1(A_449,B_450)))
      | ~ v1_funct_1(k7_tmap_1(A_449,B_450))
      | ~ l1_pre_topc(k6_tmap_1(A_449,B_450))
      | ~ m1_subset_1(B_450,k1_zfmisc_1(u1_struct_0(A_449)))
      | ~ l1_pre_topc(A_449)
      | ~ v2_pre_topc(A_449)
      | v2_struct_0(A_449) ) ),
    inference(resolution,[status(thm)],[c_48,c_2877])).

tff(c_12225,plain,(
    ! [D_451] :
      ( k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_2'),k7_tmap_1('#skF_2','#skF_3'),D_451),'#skF_2')
      | ~ v3_pre_topc(D_451,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_451,k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))))
      | ~ v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
      | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_719,c_12172])).

tff(c_12251,plain,(
    ! [D_451] :
      ( k2_struct_0('#skF_2') = k1_xboole_0
      | v3_pre_topc(k10_relat_1(k7_tmap_1('#skF_2','#skF_3'),D_451),'#skF_2')
      | ~ v3_pre_topc(D_451,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_451,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_110,c_109,c_294,c_115,c_803,c_109,c_719,c_138,c_719,c_800,c_109,c_720,c_12225])).

tff(c_12256,plain,(
    ! [D_452] :
      ( v3_pre_topc(k10_relat_1(k7_tmap_1('#skF_2','#skF_3'),D_452),'#skF_2')
      | ~ v3_pre_topc(D_452,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_452,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_9091,c_12251])).

tff(c_12262,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3',k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1326,c_12256])).

tff(c_12267,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_1444,c_12262])).

tff(c_12269,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_248,c_12267])).

tff(c_12270,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_12273,plain,(
    ~ m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12270,c_115,c_187,c_109,c_138,c_109,c_78])).

tff(c_12454,plain,(
    ~ m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0(k6_tmap_1('#skF_2','#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12416,c_12273])).

tff(c_12798,plain,(
    ~ m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12726,c_12454])).

tff(c_13453,plain,(
    ! [A_541,B_542] :
      ( m1_subset_1(k7_tmap_1(A_541,B_542),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_541),u1_struct_0(k6_tmap_1(A_541,B_542)))))
      | ~ m1_subset_1(B_542,k1_zfmisc_1(u1_struct_0(A_541)))
      | ~ l1_pre_topc(A_541)
      | ~ v2_pre_topc(A_541)
      | v2_struct_0(A_541) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_13478,plain,
    ( m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12725,c_13453])).

tff(c_13496,plain,
    ( m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_110,c_109,c_109,c_13478])).

tff(c_13498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_12798,c_13496])).

tff(c_13500,plain,(
    ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_13679,plain,(
    ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13663,c_13500])).

tff(c_14119,plain,(
    ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14029,c_13679])).

tff(c_14584,plain,(
    ! [A_624,B_625] :
      ( v1_funct_2(k7_tmap_1(A_624,B_625),u1_struct_0(A_624),u1_struct_0(k6_tmap_1(A_624,B_625)))
      | ~ m1_subset_1(B_625,k1_zfmisc_1(u1_struct_0(A_624)))
      | ~ l1_pre_topc(A_624)
      | ~ v2_pre_topc(A_624)
      | v2_struct_0(A_624) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_14599,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),k2_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14028,c_14584])).

tff(c_14614,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_110,c_109,c_109,c_14599])).

tff(c_14616,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_14119,c_14614])).

tff(c_14618,plain,(
    ~ v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2',k6_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_16177,plain,(
    ! [B_724,A_725,C_726] :
      ( k2_struct_0(B_724) = k1_xboole_0
      | v3_pre_topc('#skF_1'(A_725,B_724,C_726),B_724)
      | v5_pre_topc(C_726,A_725,B_724)
      | ~ m1_subset_1(C_726,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_725),u1_struct_0(B_724))))
      | ~ v1_funct_2(C_726,u1_struct_0(A_725),u1_struct_0(B_724))
      | ~ v1_funct_1(C_726)
      | ~ l1_pre_topc(B_724)
      | ~ l1_pre_topc(A_725) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_16198,plain,(
    ! [A_725,C_726] :
      ( k2_struct_0('#skF_2') = k1_xboole_0
      | v3_pre_topc('#skF_1'(A_725,'#skF_2',C_726),'#skF_2')
      | v5_pre_topc(C_726,A_725,'#skF_2')
      | ~ m1_subset_1(C_726,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_725),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_726,u1_struct_0(A_725),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_726)
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_725) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_16177])).

tff(c_16212,plain,(
    ! [A_725,C_726] :
      ( k2_struct_0('#skF_2') = k1_xboole_0
      | v3_pre_topc('#skF_1'(A_725,'#skF_2',C_726),'#skF_2')
      | v5_pre_topc(C_726,A_725,'#skF_2')
      | ~ m1_subset_1(C_726,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_725),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_726,u1_struct_0(A_725),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_726)
      | ~ l1_pre_topc(A_725) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_109,c_16198])).

tff(c_17417,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_16212])).

tff(c_15078,plain,(
    ! [A_677,B_678] :
      ( k7_tmap_1(A_677,B_678) = k6_partfun1(u1_struct_0(A_677))
      | ~ m1_subset_1(B_678,k1_zfmisc_1(u1_struct_0(A_677)))
      | ~ l1_pre_topc(A_677)
      | ~ v2_pre_topc(A_677)
      | v2_struct_0(A_677) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_15091,plain,(
    ! [B_678] :
      ( k7_tmap_1('#skF_2',B_678) = k6_partfun1(u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_678,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_15078])).

tff(c_15098,plain,(
    ! [B_678] :
      ( k7_tmap_1('#skF_2',B_678) = k6_partfun1(k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_678,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_109,c_15091])).

tff(c_15100,plain,(
    ! [B_679] :
      ( k7_tmap_1('#skF_2',B_679) = k6_partfun1(k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_679,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_15098])).

tff(c_15109,plain,(
    k6_partfun1(k2_struct_0('#skF_2')) = k7_tmap_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_110,c_15100])).

tff(c_17468,plain,(
    k7_tmap_1('#skF_2','#skF_3') = k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17417,c_15109])).

tff(c_17889,plain,(
    ~ v5_pre_topc(k6_partfun1(k1_xboole_0),'#skF_2',k6_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17468,c_14618])).

tff(c_17487,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17417,c_110])).

tff(c_17488,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_17417,c_109])).

tff(c_14876,plain,(
    ! [A_669,B_670] :
      ( l1_pre_topc(k6_tmap_1(A_669,B_670))
      | ~ m1_subset_1(B_670,k1_zfmisc_1(u1_struct_0(A_669)))
      | ~ l1_pre_topc(A_669)
      | ~ v2_pre_topc(A_669)
      | v2_struct_0(A_669) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_14883,plain,(
    ! [B_670] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_670))
      | ~ m1_subset_1(B_670,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_14876])).

tff(c_14886,plain,(
    ! [B_670] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_670))
      | ~ m1_subset_1(B_670,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_14883])).

tff(c_14888,plain,(
    ! [B_671] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_671))
      | ~ m1_subset_1(B_671,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_14886])).

tff(c_14897,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_110,c_14888])).

tff(c_15872,plain,(
    ! [A_716,A_717] :
      ( k7_tmap_1(A_716,A_717) = k6_partfun1(u1_struct_0(A_716))
      | ~ l1_pre_topc(A_716)
      | ~ v2_pre_topc(A_716)
      | v2_struct_0(A_716)
      | ~ r1_tarski(A_717,u1_struct_0(A_716)) ) ),
    inference(resolution,[status(thm)],[c_10,c_15078])).

tff(c_15924,plain,(
    ! [A_720] :
      ( k7_tmap_1(A_720,u1_struct_0(A_720)) = k6_partfun1(u1_struct_0(A_720))
      | ~ l1_pre_topc(A_720)
      | ~ v2_pre_topc(A_720)
      | v2_struct_0(A_720) ) ),
    inference(resolution,[status(thm)],[c_6,c_15872])).

tff(c_14771,plain,(
    ! [A_655,B_656] :
      ( v1_funct_1(k7_tmap_1(A_655,B_656))
      | ~ m1_subset_1(B_656,k1_zfmisc_1(u1_struct_0(A_655)))
      | ~ l1_pre_topc(A_655)
      | ~ v2_pre_topc(A_655)
      | v2_struct_0(A_655) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_14805,plain,(
    ! [A_659,A_660] :
      ( v1_funct_1(k7_tmap_1(A_659,A_660))
      | ~ l1_pre_topc(A_659)
      | ~ v2_pre_topc(A_659)
      | v2_struct_0(A_659)
      | ~ r1_tarski(A_660,u1_struct_0(A_659)) ) ),
    inference(resolution,[status(thm)],[c_10,c_14771])).

tff(c_14816,plain,(
    ! [A_659] :
      ( v1_funct_1(k7_tmap_1(A_659,u1_struct_0(A_659)))
      | ~ l1_pre_topc(A_659)
      | ~ v2_pre_topc(A_659)
      | v2_struct_0(A_659) ) ),
    inference(resolution,[status(thm)],[c_6,c_14805])).

tff(c_15937,plain,(
    ! [A_720] :
      ( v1_funct_1(k6_partfun1(u1_struct_0(A_720)))
      | ~ l1_pre_topc(A_720)
      | ~ v2_pre_topc(A_720)
      | v2_struct_0(A_720)
      | ~ l1_pre_topc(A_720)
      | ~ v2_pre_topc(A_720)
      | v2_struct_0(A_720) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15924,c_14816])).

tff(c_17551,plain,
    ( v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_17488,c_15937])).

tff(c_17688,plain,
    ( v1_funct_1(k6_partfun1(k1_xboole_0))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_74,c_72,c_17551])).

tff(c_17689,plain,(
    v1_funct_1(k6_partfun1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_17688])).

tff(c_15154,plain,(
    ! [A_682,B_683] :
      ( u1_struct_0(k6_tmap_1(A_682,B_683)) = u1_struct_0(A_682)
      | ~ m1_subset_1(B_683,k1_zfmisc_1(u1_struct_0(A_682)))
      | ~ l1_pre_topc(A_682)
      | ~ v2_pre_topc(A_682)
      | v2_struct_0(A_682) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_15167,plain,(
    ! [B_683] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_683)) = u1_struct_0('#skF_2')
      | ~ m1_subset_1(B_683,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_15154])).

tff(c_15174,plain,(
    ! [B_683] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_683)) = k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_683,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_109,c_15167])).

tff(c_15176,plain,(
    ! [B_684] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_684)) = k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_684,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_15174])).

tff(c_15185,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_110,c_15176])).

tff(c_17462,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_17417,c_15185])).

tff(c_18309,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),k1_xboole_0)
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_17462,c_50])).

tff(c_18452,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_17487,c_17488,c_17468,c_17488,c_18309])).

tff(c_18453,plain,(
    v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_18452])).

tff(c_18288,plain,
    ( m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),k1_xboole_0)))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_17462,c_48])).

tff(c_18436,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_17487,c_17488,c_17468,c_17488,c_18288])).

tff(c_18437,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_18436])).

tff(c_16752,plain,(
    ! [A_747,B_748,C_749] :
      ( k2_struct_0(A_747) != k1_xboole_0
      | m1_subset_1('#skF_1'(A_747,B_748,C_749),k1_zfmisc_1(u1_struct_0(B_748)))
      | v5_pre_topc(C_749,A_747,B_748)
      | ~ m1_subset_1(C_749,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_747),u1_struct_0(B_748))))
      | ~ v1_funct_2(C_749,u1_struct_0(A_747),u1_struct_0(B_748))
      | ~ v1_funct_1(C_749)
      | ~ l1_pre_topc(B_748)
      | ~ l1_pre_topc(A_747) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_20237,plain,(
    ! [A_833,B_834] :
      ( k2_struct_0(A_833) != k1_xboole_0
      | m1_subset_1('#skF_1'(A_833,k6_tmap_1(A_833,B_834),k7_tmap_1(A_833,B_834)),k1_zfmisc_1(u1_struct_0(k6_tmap_1(A_833,B_834))))
      | v5_pre_topc(k7_tmap_1(A_833,B_834),A_833,k6_tmap_1(A_833,B_834))
      | ~ v1_funct_2(k7_tmap_1(A_833,B_834),u1_struct_0(A_833),u1_struct_0(k6_tmap_1(A_833,B_834)))
      | ~ v1_funct_1(k7_tmap_1(A_833,B_834))
      | ~ l1_pre_topc(k6_tmap_1(A_833,B_834))
      | ~ m1_subset_1(B_834,k1_zfmisc_1(u1_struct_0(A_833)))
      | ~ l1_pre_topc(A_833)
      | ~ v2_pre_topc(A_833)
      | v2_struct_0(A_833) ) ),
    inference(resolution,[status(thm)],[c_48,c_16752])).

tff(c_20284,plain,
    ( k2_struct_0('#skF_2') != k1_xboole_0
    | m1_subset_1('#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3')),k1_zfmisc_1(k1_xboole_0))
    | v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_17462,c_20237])).

tff(c_20323,plain,
    ( m1_subset_1('#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_17487,c_17488,c_14897,c_17689,c_17468,c_18453,c_17462,c_17468,c_17488,c_17468,c_17468,c_17417,c_20284])).

tff(c_20324,plain,(
    m1_subset_1('#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_17889,c_20323])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20368,plain,(
    r1_tarski('#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k6_partfun1(k1_xboole_0)),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20324,c_8])).

tff(c_16523,plain,(
    ! [A_734,B_735,C_736] :
      ( k2_struct_0(A_734) != k1_xboole_0
      | v3_pre_topc('#skF_1'(A_734,B_735,C_736),B_735)
      | v5_pre_topc(C_736,A_734,B_735)
      | ~ m1_subset_1(C_736,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_734),u1_struct_0(B_735))))
      | ~ v1_funct_2(C_736,u1_struct_0(A_734),u1_struct_0(B_735))
      | ~ v1_funct_1(C_736)
      | ~ l1_pre_topc(B_735)
      | ~ l1_pre_topc(A_734) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_19810,plain,(
    ! [A_828,B_829] :
      ( k2_struct_0(A_828) != k1_xboole_0
      | v3_pre_topc('#skF_1'(A_828,k6_tmap_1(A_828,B_829),k7_tmap_1(A_828,B_829)),k6_tmap_1(A_828,B_829))
      | v5_pre_topc(k7_tmap_1(A_828,B_829),A_828,k6_tmap_1(A_828,B_829))
      | ~ v1_funct_2(k7_tmap_1(A_828,B_829),u1_struct_0(A_828),u1_struct_0(k6_tmap_1(A_828,B_829)))
      | ~ v1_funct_1(k7_tmap_1(A_828,B_829))
      | ~ l1_pre_topc(k6_tmap_1(A_828,B_829))
      | ~ m1_subset_1(B_829,k1_zfmisc_1(u1_struct_0(A_828)))
      | ~ l1_pre_topc(A_828)
      | ~ v2_pre_topc(A_828)
      | v2_struct_0(A_828) ) ),
    inference(resolution,[status(thm)],[c_48,c_16523])).

tff(c_19824,plain,
    ( k2_struct_0('#skF_2') != k1_xboole_0
    | v3_pre_topc('#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3')),k6_tmap_1('#skF_2','#skF_3'))
    | v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_17468,c_19810])).

tff(c_19855,plain,
    ( v3_pre_topc('#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k6_partfun1(k1_xboole_0)),k6_tmap_1('#skF_2','#skF_3'))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_17487,c_17488,c_14897,c_17689,c_17468,c_18453,c_17462,c_17488,c_17468,c_17468,c_17417,c_19824])).

tff(c_19856,plain,(
    v3_pre_topc('#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k6_partfun1(k1_xboole_0)),k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_17889,c_19855])).

tff(c_14617,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_14692,plain,(
    ! [B_638,A_639] :
      ( r2_hidden(B_638,u1_pre_topc(A_639))
      | ~ v3_pre_topc(B_638,A_639)
      | ~ m1_subset_1(B_638,k1_zfmisc_1(u1_struct_0(A_639)))
      | ~ l1_pre_topc(A_639) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14699,plain,(
    ! [B_638] :
      ( r2_hidden(B_638,u1_pre_topc('#skF_2'))
      | ~ v3_pre_topc(B_638,'#skF_2')
      | ~ m1_subset_1(B_638,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_14692])).

tff(c_14703,plain,(
    ! [B_640] :
      ( r2_hidden(B_640,u1_pre_topc('#skF_2'))
      | ~ v3_pre_topc(B_640,'#skF_2')
      | ~ m1_subset_1(B_640,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_14699])).

tff(c_14710,plain,
    ( r2_hidden('#skF_3',u1_pre_topc('#skF_2'))
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_110,c_14703])).

tff(c_14714,plain,(
    r2_hidden('#skF_3',u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14617,c_14710])).

tff(c_15511,plain,(
    ! [A_697,B_698] :
      ( k5_tmap_1(A_697,B_698) = u1_pre_topc(A_697)
      | ~ r2_hidden(B_698,u1_pre_topc(A_697))
      | ~ m1_subset_1(B_698,k1_zfmisc_1(u1_struct_0(A_697)))
      | ~ l1_pre_topc(A_697)
      | ~ v2_pre_topc(A_697)
      | v2_struct_0(A_697) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_15524,plain,(
    ! [B_698] :
      ( k5_tmap_1('#skF_2',B_698) = u1_pre_topc('#skF_2')
      | ~ r2_hidden(B_698,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_698,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_15511])).

tff(c_15531,plain,(
    ! [B_698] :
      ( k5_tmap_1('#skF_2',B_698) = u1_pre_topc('#skF_2')
      | ~ r2_hidden(B_698,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_698,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_15524])).

tff(c_15533,plain,(
    ! [B_699] :
      ( k5_tmap_1('#skF_2',B_699) = u1_pre_topc('#skF_2')
      | ~ r2_hidden(B_699,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_699,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_15531])).

tff(c_15540,plain,
    ( k5_tmap_1('#skF_2','#skF_3') = u1_pre_topc('#skF_2')
    | ~ r2_hidden('#skF_3',u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_110,c_15533])).

tff(c_15544,plain,(
    k5_tmap_1('#skF_2','#skF_3') = u1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14714,c_15540])).

tff(c_15357,plain,(
    ! [A_686,B_687] :
      ( u1_pre_topc(k6_tmap_1(A_686,B_687)) = k5_tmap_1(A_686,B_687)
      | ~ m1_subset_1(B_687,k1_zfmisc_1(u1_struct_0(A_686)))
      | ~ l1_pre_topc(A_686)
      | ~ v2_pre_topc(A_686)
      | v2_struct_0(A_686) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_15370,plain,(
    ! [B_687] :
      ( u1_pre_topc(k6_tmap_1('#skF_2',B_687)) = k5_tmap_1('#skF_2',B_687)
      | ~ m1_subset_1(B_687,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_15357])).

tff(c_15377,plain,(
    ! [B_687] :
      ( u1_pre_topc(k6_tmap_1('#skF_2',B_687)) = k5_tmap_1('#skF_2',B_687)
      | ~ m1_subset_1(B_687,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_15370])).

tff(c_15379,plain,(
    ! [B_688] :
      ( u1_pre_topc(k6_tmap_1('#skF_2',B_688)) = k5_tmap_1('#skF_2',B_688)
      | ~ m1_subset_1(B_688,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_15377])).

tff(c_15388,plain,(
    u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_110,c_15379])).

tff(c_15546,plain,(
    u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = u1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15544,c_15388])).

tff(c_14700,plain,(
    ! [A_3,A_639] :
      ( r2_hidden(A_3,u1_pre_topc(A_639))
      | ~ v3_pre_topc(A_3,A_639)
      | ~ l1_pre_topc(A_639)
      | ~ r1_tarski(A_3,u1_struct_0(A_639)) ) ),
    inference(resolution,[status(thm)],[c_10,c_14692])).

tff(c_15554,plain,(
    ! [A_3] :
      ( r2_hidden(A_3,u1_pre_topc('#skF_2'))
      | ~ v3_pre_topc(A_3,k6_tmap_1('#skF_2','#skF_3'))
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
      | ~ r1_tarski(A_3,u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15546,c_14700])).

tff(c_15561,plain,(
    ! [A_3] :
      ( r2_hidden(A_3,u1_pre_topc('#skF_2'))
      | ~ v3_pre_topc(A_3,k6_tmap_1('#skF_2','#skF_3'))
      | ~ r1_tarski(A_3,k2_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15185,c_14897,c_15554])).

tff(c_21166,plain,(
    ! [A_843] :
      ( r2_hidden(A_843,u1_pre_topc('#skF_2'))
      | ~ v3_pre_topc(A_843,k6_tmap_1('#skF_2','#skF_3'))
      | ~ r1_tarski(A_843,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17417,c_15561])).

tff(c_21173,plain,
    ( r2_hidden('#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k6_partfun1(k1_xboole_0)),u1_pre_topc('#skF_2'))
    | ~ r1_tarski('#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k6_partfun1(k1_xboole_0)),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_19856,c_21166])).

tff(c_21194,plain,(
    r2_hidden('#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k6_partfun1(k1_xboole_0)),u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20368,c_21173])).

tff(c_14666,plain,(
    ! [B_632,A_633] :
      ( v3_pre_topc(B_632,A_633)
      | ~ r2_hidden(B_632,u1_pre_topc(A_633))
      | ~ m1_subset_1(B_632,k1_zfmisc_1(u1_struct_0(A_633)))
      | ~ l1_pre_topc(A_633) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14673,plain,(
    ! [B_632] :
      ( v3_pre_topc(B_632,'#skF_2')
      | ~ r2_hidden(B_632,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_632,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_14666])).

tff(c_14676,plain,(
    ! [B_632] :
      ( v3_pre_topc(B_632,'#skF_2')
      | ~ r2_hidden(B_632,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_632,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_14673])).

tff(c_17483,plain,(
    ! [B_632] :
      ( v3_pre_topc(B_632,'#skF_2')
      | ~ r2_hidden(B_632,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_632,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17417,c_14676])).

tff(c_21213,plain,
    ( v3_pre_topc('#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k6_partfun1(k1_xboole_0)),'#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_21194,c_17483])).

tff(c_21228,plain,(
    v3_pre_topc('#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k6_partfun1(k1_xboole_0)),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20324,c_21213])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( k8_relset_1(A_9,A_9,k6_partfun1(A_9),B_10) = B_10
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20367,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),'#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k6_partfun1(k1_xboole_0))) = '#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_20324,c_14])).

tff(c_16073,plain,(
    ! [A_721,B_722] :
      ( m1_subset_1(k7_tmap_1(A_721,B_722),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_721),u1_struct_0(k6_tmap_1(A_721,B_722)))))
      | ~ m1_subset_1(B_722,k1_zfmisc_1(u1_struct_0(A_721)))
      | ~ l1_pre_topc(A_721)
      | ~ v2_pre_topc(A_721)
      | v2_struct_0(A_721) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_18508,plain,(
    ! [A_783,B_784,D_785] :
      ( k8_relset_1(u1_struct_0(A_783),u1_struct_0(k6_tmap_1(A_783,B_784)),k7_tmap_1(A_783,B_784),D_785) = k10_relat_1(k7_tmap_1(A_783,B_784),D_785)
      | ~ m1_subset_1(B_784,k1_zfmisc_1(u1_struct_0(A_783)))
      | ~ l1_pre_topc(A_783)
      | ~ v2_pre_topc(A_783)
      | v2_struct_0(A_783) ) ),
    inference(resolution,[status(thm)],[c_16073,c_12])).

tff(c_18537,plain,(
    ! [D_785] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')),k6_partfun1(k1_xboole_0),D_785) = k10_relat_1(k7_tmap_1('#skF_2','#skF_3'),D_785)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17468,c_18508])).

tff(c_18572,plain,(
    ! [D_785] :
      ( k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),D_785) = k10_relat_1(k6_partfun1(k1_xboole_0),D_785)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_17487,c_17488,c_17462,c_17468,c_17488,c_18537])).

tff(c_18573,plain,(
    ! [D_785] : k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),D_785) = k10_relat_1(k6_partfun1(k1_xboole_0),D_785) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_18572])).

tff(c_25152,plain,(
    k10_relat_1(k6_partfun1(k1_xboole_0),'#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k6_partfun1(k1_xboole_0))) = '#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k6_partfun1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20367,c_18573])).

tff(c_24,plain,(
    ! [A_16,B_28,C_34] :
      ( k2_struct_0(A_16) != k1_xboole_0
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(A_16),u1_struct_0(B_28),C_34,'#skF_1'(A_16,B_28,C_34)),A_16)
      | v5_pre_topc(C_34,A_16,B_28)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_16),u1_struct_0(B_28))))
      | ~ v1_funct_2(C_34,u1_struct_0(A_16),u1_struct_0(B_28))
      | ~ v1_funct_1(C_34)
      | ~ l1_pre_topc(B_28)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_30533,plain,(
    ! [A_1043,B_1044] :
      ( k2_struct_0(A_1043) != k1_xboole_0
      | ~ v3_pre_topc(k10_relat_1(k7_tmap_1(A_1043,B_1044),'#skF_1'(A_1043,k6_tmap_1(A_1043,B_1044),k7_tmap_1(A_1043,B_1044))),A_1043)
      | v5_pre_topc(k7_tmap_1(A_1043,B_1044),A_1043,k6_tmap_1(A_1043,B_1044))
      | ~ m1_subset_1(k7_tmap_1(A_1043,B_1044),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1043),u1_struct_0(k6_tmap_1(A_1043,B_1044)))))
      | ~ v1_funct_2(k7_tmap_1(A_1043,B_1044),u1_struct_0(A_1043),u1_struct_0(k6_tmap_1(A_1043,B_1044)))
      | ~ v1_funct_1(k7_tmap_1(A_1043,B_1044))
      | ~ l1_pre_topc(k6_tmap_1(A_1043,B_1044))
      | ~ l1_pre_topc(A_1043)
      | ~ m1_subset_1(B_1044,k1_zfmisc_1(u1_struct_0(A_1043)))
      | ~ l1_pre_topc(A_1043)
      | ~ v2_pre_topc(A_1043)
      | v2_struct_0(A_1043) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18508,c_24])).

tff(c_30573,plain,
    ( k2_struct_0('#skF_2') != k1_xboole_0
    | ~ v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),'#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'))),'#skF_2')
    | v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))))
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_17468,c_30533])).

tff(c_30624,plain,
    ( v5_pre_topc(k6_partfun1(k1_xboole_0),'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_17487,c_17488,c_72,c_14897,c_17689,c_17468,c_18453,c_17488,c_17468,c_17462,c_18437,c_17488,c_17468,c_17462,c_17468,c_21228,c_25152,c_17468,c_17417,c_30573])).

tff(c_30626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_17889,c_30624])).

tff(c_30628,plain,(
    k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_16212])).

tff(c_15687,plain,(
    ! [A_710,B_711] :
      ( v1_funct_2(k7_tmap_1(A_710,B_711),u1_struct_0(A_710),u1_struct_0(k6_tmap_1(A_710,B_711)))
      | ~ m1_subset_1(B_711,k1_zfmisc_1(u1_struct_0(A_710)))
      | ~ l1_pre_topc(A_710)
      | ~ v2_pre_topc(A_710)
      | v2_struct_0(A_710) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_15699,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),k2_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_15185,c_15687])).

tff(c_15714,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_110,c_109,c_109,c_15699])).

tff(c_15715,plain,(
    v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_15714])).

tff(c_16101,plain,
    ( m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_15185,c_16073])).

tff(c_16119,plain,
    ( m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_110,c_109,c_109,c_16101])).

tff(c_16120,plain,(
    m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_16119])).

tff(c_16136,plain,(
    r1_tarski(k7_tmap_1('#skF_2','#skF_3'),k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_16120,c_8])).

tff(c_14913,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_14897,c_104])).

tff(c_15186,plain,(
    k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15185,c_14913])).

tff(c_16625,plain,(
    ! [B_741,A_742,C_743] :
      ( k2_struct_0(B_741) = k1_xboole_0
      | m1_subset_1('#skF_1'(A_742,B_741,C_743),k1_zfmisc_1(u1_struct_0(B_741)))
      | v5_pre_topc(C_743,A_742,B_741)
      | ~ m1_subset_1(C_743,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_742),u1_struct_0(B_741))))
      | ~ v1_funct_2(C_743,u1_struct_0(A_742),u1_struct_0(B_741))
      | ~ v1_funct_1(C_743)
      | ~ l1_pre_topc(B_741)
      | ~ l1_pre_topc(A_742) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_31848,plain,(
    ! [B_1090,A_1091,A_1092] :
      ( k2_struct_0(B_1090) = k1_xboole_0
      | m1_subset_1('#skF_1'(A_1091,B_1090,A_1092),k1_zfmisc_1(u1_struct_0(B_1090)))
      | v5_pre_topc(A_1092,A_1091,B_1090)
      | ~ v1_funct_2(A_1092,u1_struct_0(A_1091),u1_struct_0(B_1090))
      | ~ v1_funct_1(A_1092)
      | ~ l1_pre_topc(B_1090)
      | ~ l1_pre_topc(A_1091)
      | ~ r1_tarski(A_1092,k2_zfmisc_1(u1_struct_0(A_1091),u1_struct_0(B_1090))) ) ),
    inference(resolution,[status(thm)],[c_10,c_16625])).

tff(c_31870,plain,(
    ! [B_1090,A_1092] :
      ( k2_struct_0(B_1090) = k1_xboole_0
      | m1_subset_1('#skF_1'('#skF_2',B_1090,A_1092),k1_zfmisc_1(u1_struct_0(B_1090)))
      | v5_pre_topc(A_1092,'#skF_2',B_1090)
      | ~ v1_funct_2(A_1092,u1_struct_0('#skF_2'),u1_struct_0(B_1090))
      | ~ v1_funct_1(A_1092)
      | ~ l1_pre_topc(B_1090)
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_1092,k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(B_1090))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_31848])).

tff(c_32410,plain,(
    ! [B_1109,A_1110] :
      ( k2_struct_0(B_1109) = k1_xboole_0
      | m1_subset_1('#skF_1'('#skF_2',B_1109,A_1110),k1_zfmisc_1(u1_struct_0(B_1109)))
      | v5_pre_topc(A_1110,'#skF_2',B_1109)
      | ~ v1_funct_2(A_1110,k2_struct_0('#skF_2'),u1_struct_0(B_1109))
      | ~ v1_funct_1(A_1110)
      | ~ l1_pre_topc(B_1109)
      | ~ r1_tarski(A_1110,k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(B_1109))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_109,c_31870])).

tff(c_32420,plain,(
    ! [A_1110] :
      ( k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k1_xboole_0
      | m1_subset_1('#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),A_1110),k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))))
      | v5_pre_topc(A_1110,'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
      | ~ v1_funct_2(A_1110,k2_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(A_1110)
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
      | ~ r1_tarski(A_1110,k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15185,c_32410])).

tff(c_32431,plain,(
    ! [A_1110] :
      ( k2_struct_0('#skF_2') = k1_xboole_0
      | m1_subset_1('#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),A_1110),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v5_pre_topc(A_1110,'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
      | ~ v1_funct_2(A_1110,k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(A_1110)
      | ~ r1_tarski(A_1110,k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14897,c_15185,c_15185,c_15186,c_32420])).

tff(c_32927,plain,(
    ! [A_1119] :
      ( m1_subset_1('#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),A_1119),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v5_pre_topc(A_1119,'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
      | ~ v1_funct_2(A_1119,k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(A_1119)
      | ~ r1_tarski(A_1119,k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30628,c_32431])).

tff(c_33001,plain,(
    ! [A_1121] :
      ( r1_tarski('#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),A_1121),k2_struct_0('#skF_2'))
      | v5_pre_topc(A_1121,'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
      | ~ v1_funct_2(A_1121,k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(A_1121)
      | ~ r1_tarski(A_1121,k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_32927,c_8])).

tff(c_16107,plain,(
    ! [B_722] :
      ( m1_subset_1(k7_tmap_1('#skF_2',B_722),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2',B_722)))))
      | ~ m1_subset_1(B_722,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_16073])).

tff(c_16125,plain,(
    ! [B_722] :
      ( m1_subset_1(k7_tmap_1('#skF_2',B_722),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2',B_722)))))
      | ~ m1_subset_1(B_722,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_109,c_16107])).

tff(c_16126,plain,(
    ! [B_722] :
      ( m1_subset_1(k7_tmap_1('#skF_2',B_722),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2',B_722)))))
      | ~ m1_subset_1(B_722,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_16125])).

tff(c_16196,plain,(
    ! [B_724,C_726] :
      ( k2_struct_0(B_724) = k1_xboole_0
      | v3_pre_topc('#skF_1'('#skF_2',B_724,C_726),B_724)
      | v5_pre_topc(C_726,'#skF_2',B_724)
      | ~ m1_subset_1(C_726,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(B_724))))
      | ~ v1_funct_2(C_726,u1_struct_0('#skF_2'),u1_struct_0(B_724))
      | ~ v1_funct_1(C_726)
      | ~ l1_pre_topc(B_724)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_16177])).

tff(c_30631,plain,(
    ! [B_1045,C_1046] :
      ( k2_struct_0(B_1045) = k1_xboole_0
      | v3_pre_topc('#skF_1'('#skF_2',B_1045,C_1046),B_1045)
      | v5_pre_topc(C_1046,'#skF_2',B_1045)
      | ~ m1_subset_1(C_1046,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(B_1045))))
      | ~ v1_funct_2(C_1046,k2_struct_0('#skF_2'),u1_struct_0(B_1045))
      | ~ v1_funct_1(C_1046)
      | ~ l1_pre_topc(B_1045) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_109,c_16196])).

tff(c_30828,plain,(
    ! [B_1056] :
      ( k2_struct_0(k6_tmap_1('#skF_2',B_1056)) = k1_xboole_0
      | v3_pre_topc('#skF_1'('#skF_2',k6_tmap_1('#skF_2',B_1056),k7_tmap_1('#skF_2',B_1056)),k6_tmap_1('#skF_2',B_1056))
      | v5_pre_topc(k7_tmap_1('#skF_2',B_1056),'#skF_2',k6_tmap_1('#skF_2',B_1056))
      | ~ v1_funct_2(k7_tmap_1('#skF_2',B_1056),k2_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2',B_1056)))
      | ~ v1_funct_1(k7_tmap_1('#skF_2',B_1056))
      | ~ l1_pre_topc(k6_tmap_1('#skF_2',B_1056))
      | ~ m1_subset_1(B_1056,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_16126,c_30631])).

tff(c_30843,plain,
    ( k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k1_xboole_0
    | v3_pre_topc('#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3')),k6_tmap_1('#skF_2','#skF_3'))
    | v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_15185,c_30828])).

tff(c_30860,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | v3_pre_topc('#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3')),k6_tmap_1('#skF_2','#skF_3'))
    | v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2',k6_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_14897,c_115,c_15715,c_15186,c_30843])).

tff(c_30861,plain,(
    v3_pre_topc('#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3')),k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_14618,c_30628,c_30860])).

tff(c_30868,plain,
    ( r2_hidden('#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3')),u1_pre_topc('#skF_2'))
    | ~ r1_tarski('#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3')),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_30861,c_15561])).

tff(c_30869,plain,(
    ~ r1_tarski('#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3')),k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_30868])).

tff(c_33004,plain,
    ( v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | ~ r1_tarski(k7_tmap_1('#skF_2','#skF_3'),k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_33001,c_30869])).

tff(c_33039,plain,(
    v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2',k6_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16136,c_115,c_15715,c_33004])).

tff(c_33041,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14618,c_33039])).

tff(c_33043,plain,(
    r1_tarski('#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3')),k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_30868])).

tff(c_33042,plain,(
    r2_hidden('#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3')),u1_pre_topc('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_30868])).

tff(c_14678,plain,(
    ! [B_634] :
      ( v3_pre_topc(B_634,'#skF_2')
      | ~ r2_hidden(B_634,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_634,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_14673])).

tff(c_14686,plain,(
    ! [A_3] :
      ( v3_pre_topc(A_3,'#skF_2')
      | ~ r2_hidden(A_3,u1_pre_topc('#skF_2'))
      | ~ r1_tarski(A_3,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_10,c_14678])).

tff(c_33064,plain,
    ( v3_pre_topc('#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3')),'#skF_2')
    | ~ r1_tarski('#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3')),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_33042,c_14686])).

tff(c_37456,plain,(
    v3_pre_topc('#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33043,c_33064])).

tff(c_16134,plain,(
    ! [D_8] : k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k7_tmap_1('#skF_2','#skF_3'),D_8) = k10_relat_1(k7_tmap_1('#skF_2','#skF_3'),D_8) ),
    inference(resolution,[status(thm)],[c_16120,c_12])).

tff(c_14621,plain,(
    ! [A_627,B_628] :
      ( k8_relset_1(A_627,A_627,k6_partfun1(A_627),B_628) = B_628
      | ~ m1_subset_1(B_628,k1_zfmisc_1(A_627)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14626,plain,(
    ! [B_4,A_3] :
      ( k8_relset_1(B_4,B_4,k6_partfun1(B_4),A_3) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_14621])).

tff(c_15115,plain,(
    ! [A_3] :
      ( k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k7_tmap_1('#skF_2','#skF_3'),A_3) = A_3
      | ~ r1_tarski(A_3,k2_struct_0('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15109,c_14626])).

tff(c_16145,plain,(
    ! [A_3] :
      ( k10_relat_1(k7_tmap_1('#skF_2','#skF_3'),A_3) = A_3
      | ~ r1_tarski(A_3,k2_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16134,c_15115])).

tff(c_33097,plain,(
    k10_relat_1(k7_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'))) = '#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_33043,c_16145])).

tff(c_33112,plain,(
    ! [A_1122,B_1123,D_1124] :
      ( k8_relset_1(u1_struct_0(A_1122),u1_struct_0(k6_tmap_1(A_1122,B_1123)),k7_tmap_1(A_1122,B_1123),D_1124) = k10_relat_1(k7_tmap_1(A_1122,B_1123),D_1124)
      | ~ m1_subset_1(B_1123,k1_zfmisc_1(u1_struct_0(A_1122)))
      | ~ l1_pre_topc(A_1122)
      | ~ v2_pre_topc(A_1122)
      | v2_struct_0(A_1122) ) ),
    inference(resolution,[status(thm)],[c_16073,c_12])).

tff(c_26,plain,(
    ! [B_28,A_16,C_34] :
      ( k2_struct_0(B_28) = k1_xboole_0
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(A_16),u1_struct_0(B_28),C_34,'#skF_1'(A_16,B_28,C_34)),A_16)
      | v5_pre_topc(C_34,A_16,B_28)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_16),u1_struct_0(B_28))))
      | ~ v1_funct_2(C_34,u1_struct_0(A_16),u1_struct_0(B_28))
      | ~ v1_funct_1(C_34)
      | ~ l1_pre_topc(B_28)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_76837,plain,(
    ! [A_1925,B_1926] :
      ( k2_struct_0(k6_tmap_1(A_1925,B_1926)) = k1_xboole_0
      | ~ v3_pre_topc(k10_relat_1(k7_tmap_1(A_1925,B_1926),'#skF_1'(A_1925,k6_tmap_1(A_1925,B_1926),k7_tmap_1(A_1925,B_1926))),A_1925)
      | v5_pre_topc(k7_tmap_1(A_1925,B_1926),A_1925,k6_tmap_1(A_1925,B_1926))
      | ~ m1_subset_1(k7_tmap_1(A_1925,B_1926),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1925),u1_struct_0(k6_tmap_1(A_1925,B_1926)))))
      | ~ v1_funct_2(k7_tmap_1(A_1925,B_1926),u1_struct_0(A_1925),u1_struct_0(k6_tmap_1(A_1925,B_1926)))
      | ~ v1_funct_1(k7_tmap_1(A_1925,B_1926))
      | ~ l1_pre_topc(k6_tmap_1(A_1925,B_1926))
      | ~ l1_pre_topc(A_1925)
      | ~ m1_subset_1(B_1926,k1_zfmisc_1(u1_struct_0(A_1925)))
      | ~ l1_pre_topc(A_1925)
      | ~ v2_pre_topc(A_1925)
      | v2_struct_0(A_1925) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33112,c_26])).

tff(c_76876,plain,
    ( k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k1_xboole_0
    | ~ v3_pre_topc('#skF_1'('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3')),'#skF_2')
    | v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))))
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_33097,c_76837])).

tff(c_76931,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_110,c_109,c_72,c_14897,c_115,c_15715,c_109,c_15185,c_16120,c_109,c_15185,c_37456,c_15186,c_76876])).

tff(c_76933,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_14618,c_30628,c_76931])).

tff(c_76935,plain,(
    ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_77215,plain,(
    ! [A_1977,B_1978] :
      ( v1_funct_1(k7_tmap_1(A_1977,B_1978))
      | ~ m1_subset_1(B_1978,k1_zfmisc_1(u1_struct_0(A_1977)))
      | ~ l1_pre_topc(A_1977)
      | ~ v2_pre_topc(A_1977)
      | v2_struct_0(A_1977) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_77222,plain,(
    ! [B_1978] :
      ( v1_funct_1(k7_tmap_1('#skF_2',B_1978))
      | ~ m1_subset_1(B_1978,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_77215])).

tff(c_77225,plain,(
    ! [B_1978] :
      ( v1_funct_1(k7_tmap_1('#skF_2',B_1978))
      | ~ m1_subset_1(B_1978,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_77222])).

tff(c_77227,plain,(
    ! [B_1979] :
      ( v1_funct_1(k7_tmap_1('#skF_2',B_1979))
      | ~ m1_subset_1(B_1979,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_77225])).

tff(c_77234,plain,(
    v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_110,c_77227])).

tff(c_77239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76935,c_77234])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:15:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 29.98/19.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.20/19.38  
% 30.20/19.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.20/19.39  %$ v5_pre_topc > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k7_tmap_1 > k6_tmap_1 > k5_tmap_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > u1_pre_topc > k6_partfun1 > k3_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 30.20/19.39  
% 30.20/19.39  %Foreground sorts:
% 30.20/19.39  
% 30.20/19.39  
% 30.20/19.39  %Background operators:
% 30.20/19.39  
% 30.20/19.39  
% 30.20/19.39  %Foreground operators:
% 30.20/19.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 30.20/19.39  tff(k7_tmap_1, type, k7_tmap_1: ($i * $i) > $i).
% 30.20/19.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 30.20/19.39  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 30.20/19.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 30.20/19.39  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 30.20/19.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 30.20/19.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 30.20/19.39  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 30.20/19.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 30.20/19.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 30.20/19.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 30.20/19.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 30.20/19.39  tff('#skF_2', type, '#skF_2': $i).
% 30.20/19.39  tff('#skF_3', type, '#skF_3': $i).
% 30.20/19.39  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 30.20/19.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 30.20/19.39  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 30.20/19.39  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 30.20/19.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 30.20/19.39  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 30.20/19.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 30.20/19.39  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 30.20/19.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 30.20/19.39  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 30.20/19.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 30.20/19.39  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 30.20/19.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 30.20/19.39  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 30.20/19.39  tff(k3_struct_0, type, k3_struct_0: $i > $i).
% 30.20/19.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 30.20/19.39  
% 30.20/19.43  tff(f_206, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (((v1_funct_1(k7_tmap_1(A, B)) & v1_funct_2(k7_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))) & v5_pre_topc(k7_tmap_1(A, B), A, k6_tmap_1(A, B))) & m1_subset_1(k7_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_tmap_1)).
% 30.20/19.43  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 30.20/19.43  tff(f_47, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 30.20/19.43  tff(f_168, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 30.20/19.43  tff(f_112, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 30.20/19.43  tff(f_185, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k6_tmap_1(A, B)))) => ((C = B) => v3_pre_topc(C, k6_tmap_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_tmap_1)).
% 30.20/19.43  tff(f_39, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 30.20/19.43  tff(f_97, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k7_tmap_1(A, B) = k6_partfun1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_tmap_1)).
% 30.20/19.43  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_2)).
% 30.20/19.43  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 30.20/19.43  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_struct_0(B) = k1_xboole_0) => (k2_struct_0(A) = k1_xboole_0)) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (v3_pre_topc(D, B) => v3_pre_topc(k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), A)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_2)).
% 30.20/19.43  tff(f_127, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_funct_1(k7_tmap_1(A, B)) & v1_funct_2(k7_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))) & m1_subset_1(k7_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 30.20/19.43  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 30.20/19.43  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 30.20/19.43  tff(f_154, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tmap_1)).
% 30.20/19.43  tff(c_76, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 30.20/19.43  tff(c_72, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 30.20/19.43  tff(c_22, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 30.20/19.43  tff(c_100, plain, (![A_62]: (u1_struct_0(A_62)=k2_struct_0(A_62) | ~l1_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_47])).
% 30.20/19.43  tff(c_105, plain, (![A_63]: (u1_struct_0(A_63)=k2_struct_0(A_63) | ~l1_pre_topc(A_63))), inference(resolution, [status(thm)], [c_22, c_100])).
% 30.20/19.43  tff(c_109, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_72, c_105])).
% 30.20/19.43  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_206])).
% 30.20/19.43  tff(c_110, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_70])).
% 30.20/19.43  tff(c_74, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 30.20/19.43  tff(c_13997, plain, (![A_594, B_595]: (u1_struct_0(k6_tmap_1(A_594, B_595))=u1_struct_0(A_594) | ~m1_subset_1(B_595, k1_zfmisc_1(u1_struct_0(A_594))) | ~l1_pre_topc(A_594) | ~v2_pre_topc(A_594) | v2_struct_0(A_594))), inference(cnfTransformation, [status(thm)], [f_168])).
% 30.20/19.43  tff(c_14010, plain, (![B_595]: (u1_struct_0(k6_tmap_1('#skF_2', B_595))=u1_struct_0('#skF_2') | ~m1_subset_1(B_595, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_13997])).
% 30.20/19.43  tff(c_14017, plain, (![B_595]: (u1_struct_0(k6_tmap_1('#skF_2', B_595))=k2_struct_0('#skF_2') | ~m1_subset_1(B_595, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_109, c_14010])).
% 30.20/19.43  tff(c_14019, plain, (![B_596]: (u1_struct_0(k6_tmap_1('#skF_2', B_596))=k2_struct_0('#skF_2') | ~m1_subset_1(B_596, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_14017])).
% 30.20/19.43  tff(c_14028, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_110, c_14019])).
% 30.20/19.43  tff(c_13627, plain, (![A_569, B_570]: (l1_pre_topc(k6_tmap_1(A_569, B_570)) | ~m1_subset_1(B_570, k1_zfmisc_1(u1_struct_0(A_569))) | ~l1_pre_topc(A_569) | ~v2_pre_topc(A_569) | v2_struct_0(A_569))), inference(cnfTransformation, [status(thm)], [f_112])).
% 30.20/19.43  tff(c_13634, plain, (![B_570]: (l1_pre_topc(k6_tmap_1('#skF_2', B_570)) | ~m1_subset_1(B_570, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_13627])).
% 30.20/19.43  tff(c_13637, plain, (![B_570]: (l1_pre_topc(k6_tmap_1('#skF_2', B_570)) | ~m1_subset_1(B_570, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_13634])).
% 30.20/19.43  tff(c_13650, plain, (![B_572]: (l1_pre_topc(k6_tmap_1('#skF_2', B_572)) | ~m1_subset_1(B_572, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_13637])).
% 30.20/19.43  tff(c_13659, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_110, c_13650])).
% 30.20/19.43  tff(c_104, plain, (![A_15]: (u1_struct_0(A_15)=k2_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(resolution, [status(thm)], [c_22, c_100])).
% 30.20/19.43  tff(c_13663, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_13659, c_104])).
% 30.20/19.43  tff(c_14029, plain, (k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14028, c_13663])).
% 30.20/19.43  tff(c_12694, plain, (![A_498, B_499]: (u1_struct_0(k6_tmap_1(A_498, B_499))=u1_struct_0(A_498) | ~m1_subset_1(B_499, k1_zfmisc_1(u1_struct_0(A_498))) | ~l1_pre_topc(A_498) | ~v2_pre_topc(A_498) | v2_struct_0(A_498))), inference(cnfTransformation, [status(thm)], [f_168])).
% 30.20/19.43  tff(c_12707, plain, (![B_499]: (u1_struct_0(k6_tmap_1('#skF_2', B_499))=u1_struct_0('#skF_2') | ~m1_subset_1(B_499, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_12694])).
% 30.20/19.43  tff(c_12714, plain, (![B_499]: (u1_struct_0(k6_tmap_1('#skF_2', B_499))=k2_struct_0('#skF_2') | ~m1_subset_1(B_499, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_109, c_12707])).
% 30.20/19.43  tff(c_12716, plain, (![B_500]: (u1_struct_0(k6_tmap_1('#skF_2', B_500))=k2_struct_0('#skF_2') | ~m1_subset_1(B_500, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_12714])).
% 30.20/19.43  tff(c_12725, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_110, c_12716])).
% 30.20/19.43  tff(c_12379, plain, (![A_476, B_477]: (l1_pre_topc(k6_tmap_1(A_476, B_477)) | ~m1_subset_1(B_477, k1_zfmisc_1(u1_struct_0(A_476))) | ~l1_pre_topc(A_476) | ~v2_pre_topc(A_476) | v2_struct_0(A_476))), inference(cnfTransformation, [status(thm)], [f_112])).
% 30.20/19.43  tff(c_12386, plain, (![B_477]: (l1_pre_topc(k6_tmap_1('#skF_2', B_477)) | ~m1_subset_1(B_477, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_12379])).
% 30.20/19.43  tff(c_12389, plain, (![B_477]: (l1_pre_topc(k6_tmap_1('#skF_2', B_477)) | ~m1_subset_1(B_477, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_12386])).
% 30.20/19.43  tff(c_12403, plain, (![B_480]: (l1_pre_topc(k6_tmap_1('#skF_2', B_480)) | ~m1_subset_1(B_480, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_12389])).
% 30.20/19.43  tff(c_12412, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_110, c_12403])).
% 30.20/19.43  tff(c_12416, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_12412, c_104])).
% 30.20/19.43  tff(c_12726, plain, (k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12725, c_12416])).
% 30.20/19.43  tff(c_96, plain, (v3_pre_topc('#skF_3', '#skF_2') | v1_funct_1(k7_tmap_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_206])).
% 30.20/19.43  tff(c_115, plain, (v1_funct_1(k7_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_96])).
% 30.20/19.43  tff(c_92, plain, (v3_pre_topc('#skF_3', '#skF_2') | v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_206])).
% 30.20/19.43  tff(c_186, plain, (v3_pre_topc('#skF_3', '#skF_2') | v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_92])).
% 30.20/19.43  tff(c_187, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_186])).
% 30.20/19.43  tff(c_88, plain, (v3_pre_topc('#skF_3', '#skF_2') | v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', k6_tmap_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_206])).
% 30.20/19.43  tff(c_138, plain, (v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', k6_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_88])).
% 30.20/19.43  tff(c_84, plain, (v3_pre_topc('#skF_3', '#skF_2') | m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))))), inference(cnfTransformation, [status(thm)], [f_206])).
% 30.20/19.43  tff(c_188, plain, (v3_pre_topc('#skF_3', '#skF_2') | m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_84])).
% 30.20/19.43  tff(c_189, plain, (m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))))), inference(splitLeft, [status(thm)], [c_188])).
% 30.20/19.43  tff(c_78, plain, (~m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))))) | ~v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k7_tmap_1('#skF_2', '#skF_3')) | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 30.20/19.43  tff(c_248, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_115, c_187, c_109, c_138, c_189, c_109, c_78])).
% 30.20/19.43  tff(c_677, plain, (![A_125, B_126]: (u1_struct_0(k6_tmap_1(A_125, B_126))=u1_struct_0(A_125) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125) | ~v2_pre_topc(A_125) | v2_struct_0(A_125))), inference(cnfTransformation, [status(thm)], [f_168])).
% 30.20/19.43  tff(c_690, plain, (![B_126]: (u1_struct_0(k6_tmap_1('#skF_2', B_126))=u1_struct_0('#skF_2') | ~m1_subset_1(B_126, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_677])).
% 30.20/19.43  tff(c_697, plain, (![B_126]: (u1_struct_0(k6_tmap_1('#skF_2', B_126))=k2_struct_0('#skF_2') | ~m1_subset_1(B_126, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_109, c_690])).
% 30.20/19.43  tff(c_710, plain, (![B_128]: (u1_struct_0(k6_tmap_1('#skF_2', B_128))=k2_struct_0('#skF_2') | ~m1_subset_1(B_128, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_697])).
% 30.20/19.43  tff(c_719, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_110, c_710])).
% 30.20/19.43  tff(c_1428, plain, (![C_163, A_164]: (v3_pre_topc(C_163, k6_tmap_1(A_164, C_163)) | ~m1_subset_1(C_163, k1_zfmisc_1(u1_struct_0(k6_tmap_1(A_164, C_163)))) | ~m1_subset_1(C_163, k1_zfmisc_1(u1_struct_0(A_164))) | ~l1_pre_topc(A_164) | ~v2_pre_topc(A_164) | v2_struct_0(A_164))), inference(cnfTransformation, [status(thm)], [f_185])).
% 30.20/19.43  tff(c_1434, plain, (v3_pre_topc('#skF_3', k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_719, c_1428])).
% 30.20/19.43  tff(c_1443, plain, (v3_pre_topc('#skF_3', k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_110, c_109, c_110, c_1434])).
% 30.20/19.43  tff(c_1444, plain, (v3_pre_topc('#skF_3', k6_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_76, c_1443])).
% 30.20/19.43  tff(c_273, plain, (![A_97, B_98]: (l1_pre_topc(k6_tmap_1(A_97, B_98)) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97) | ~v2_pre_topc(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_112])).
% 30.20/19.43  tff(c_280, plain, (![B_98]: (l1_pre_topc(k6_tmap_1('#skF_2', B_98)) | ~m1_subset_1(B_98, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_273])).
% 30.20/19.43  tff(c_283, plain, (![B_98]: (l1_pre_topc(k6_tmap_1('#skF_2', B_98)) | ~m1_subset_1(B_98, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_280])).
% 30.20/19.43  tff(c_285, plain, (![B_99]: (l1_pre_topc(k6_tmap_1('#skF_2', B_99)) | ~m1_subset_1(B_99, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_283])).
% 30.20/19.43  tff(c_294, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_110, c_285])).
% 30.20/19.43  tff(c_298, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_294, c_104])).
% 30.20/19.43  tff(c_720, plain, (k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_719, c_298])).
% 30.20/19.43  tff(c_200, plain, (![A_77, B_78, C_79, D_80]: (k8_relset_1(A_77, B_78, C_79, D_80)=k10_relat_1(C_79, D_80) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 30.20/19.43  tff(c_206, plain, (![D_80]: (k8_relset_1(k2_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')), k7_tmap_1('#skF_2', '#skF_3'), D_80)=k10_relat_1(k7_tmap_1('#skF_2', '#skF_3'), D_80))), inference(resolution, [status(thm)], [c_189, c_200])).
% 30.20/19.43  tff(c_579, plain, (![D_80]: (k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0(k6_tmap_1('#skF_2', '#skF_3')), k7_tmap_1('#skF_2', '#skF_3'), D_80)=k10_relat_1(k7_tmap_1('#skF_2', '#skF_3'), D_80))), inference(demodulation, [status(thm), theory('equality')], [c_298, c_206])).
% 30.20/19.43  tff(c_1320, plain, (![D_158]: (k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k7_tmap_1('#skF_2', '#skF_3'), D_158)=k10_relat_1(k7_tmap_1('#skF_2', '#skF_3'), D_158))), inference(demodulation, [status(thm), theory('equality')], [c_720, c_579])).
% 30.20/19.43  tff(c_825, plain, (![A_130, B_131]: (k7_tmap_1(A_130, B_131)=k6_partfun1(u1_struct_0(A_130)) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130) | ~v2_pre_topc(A_130) | v2_struct_0(A_130))), inference(cnfTransformation, [status(thm)], [f_97])).
% 30.20/19.43  tff(c_838, plain, (![B_131]: (k7_tmap_1('#skF_2', B_131)=k6_partfun1(u1_struct_0('#skF_2')) | ~m1_subset_1(B_131, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_825])).
% 30.20/19.43  tff(c_845, plain, (![B_131]: (k7_tmap_1('#skF_2', B_131)=k6_partfun1(k2_struct_0('#skF_2')) | ~m1_subset_1(B_131, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_109, c_838])).
% 30.20/19.43  tff(c_947, plain, (![B_132]: (k7_tmap_1('#skF_2', B_132)=k6_partfun1(k2_struct_0('#skF_2')) | ~m1_subset_1(B_132, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_845])).
% 30.20/19.43  tff(c_956, plain, (k6_partfun1(k2_struct_0('#skF_2'))=k7_tmap_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_110, c_947])).
% 30.20/19.43  tff(c_140, plain, (![A_72, B_73]: (k8_relset_1(A_72, A_72, k6_partfun1(A_72), B_73)=B_73 | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 30.20/19.43  tff(c_146, plain, (k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k6_partfun1(k2_struct_0('#skF_2')), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_110, c_140])).
% 30.20/19.43  tff(c_958, plain, (k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k7_tmap_1('#skF_2', '#skF_3'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_956, c_146])).
% 30.20/19.43  tff(c_1326, plain, (k10_relat_1(k7_tmap_1('#skF_2', '#skF_3'), '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1320, c_958])).
% 30.20/19.43  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 30.20/19.43  tff(c_1545, plain, (![B_165, A_166, C_167]: (k2_struct_0(B_165)=k1_xboole_0 | v3_pre_topc('#skF_1'(A_166, B_165, C_167), B_165) | v5_pre_topc(C_167, A_166, B_165) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_166), u1_struct_0(B_165)))) | ~v1_funct_2(C_167, u1_struct_0(A_166), u1_struct_0(B_165)) | ~v1_funct_1(C_167) | ~l1_pre_topc(B_165) | ~l1_pre_topc(A_166))), inference(cnfTransformation, [status(thm)], [f_85])).
% 30.20/19.43  tff(c_3191, plain, (![B_231, A_232, A_233]: (k2_struct_0(B_231)=k1_xboole_0 | v3_pre_topc('#skF_1'(A_232, B_231, A_233), B_231) | v5_pre_topc(A_233, A_232, B_231) | ~v1_funct_2(A_233, u1_struct_0(A_232), u1_struct_0(B_231)) | ~v1_funct_1(A_233) | ~l1_pre_topc(B_231) | ~l1_pre_topc(A_232) | ~r1_tarski(A_233, k2_zfmisc_1(u1_struct_0(A_232), u1_struct_0(B_231))))), inference(resolution, [status(thm)], [c_10, c_1545])).
% 30.20/19.43  tff(c_3213, plain, (![A_232, A_233]: (k2_struct_0('#skF_2')=k1_xboole_0 | v3_pre_topc('#skF_1'(A_232, '#skF_2', A_233), '#skF_2') | v5_pre_topc(A_233, A_232, '#skF_2') | ~v1_funct_2(A_233, u1_struct_0(A_232), u1_struct_0('#skF_2')) | ~v1_funct_1(A_233) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_232) | ~r1_tarski(A_233, k2_zfmisc_1(u1_struct_0(A_232), k2_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_109, c_3191])).
% 30.20/19.43  tff(c_3229, plain, (![A_232, A_233]: (k2_struct_0('#skF_2')=k1_xboole_0 | v3_pre_topc('#skF_1'(A_232, '#skF_2', A_233), '#skF_2') | v5_pre_topc(A_233, A_232, '#skF_2') | ~v1_funct_2(A_233, u1_struct_0(A_232), k2_struct_0('#skF_2')) | ~v1_funct_1(A_233) | ~l1_pre_topc(A_232) | ~r1_tarski(A_233, k2_zfmisc_1(u1_struct_0(A_232), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_109, c_3213])).
% 30.20/19.43  tff(c_3864, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3229])).
% 30.20/19.43  tff(c_3934, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_3864, c_110])).
% 30.20/19.43  tff(c_3906, plain, (k7_tmap_1('#skF_2', '#skF_3')=k6_partfun1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3864, c_956])).
% 30.20/19.43  tff(c_4987, plain, (k10_relat_1(k6_partfun1(k1_xboole_0), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3906, c_1326])).
% 30.20/19.43  tff(c_3935, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3864, c_109])).
% 30.20/19.43  tff(c_3914, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3864, c_719])).
% 30.20/19.43  tff(c_1335, plain, (![A_159, B_160]: (m1_subset_1(k7_tmap_1(A_159, B_160), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_159), u1_struct_0(k6_tmap_1(A_159, B_160))))) | ~m1_subset_1(B_160, k1_zfmisc_1(u1_struct_0(A_159))) | ~l1_pre_topc(A_159) | ~v2_pre_topc(A_159) | v2_struct_0(A_159))), inference(cnfTransformation, [status(thm)], [f_127])).
% 30.20/19.43  tff(c_12, plain, (![A_5, B_6, C_7, D_8]: (k8_relset_1(A_5, B_6, C_7, D_8)=k10_relat_1(C_7, D_8) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 30.20/19.43  tff(c_1361, plain, (![A_159, B_160, D_8]: (k8_relset_1(u1_struct_0(A_159), u1_struct_0(k6_tmap_1(A_159, B_160)), k7_tmap_1(A_159, B_160), D_8)=k10_relat_1(k7_tmap_1(A_159, B_160), D_8) | ~m1_subset_1(B_160, k1_zfmisc_1(u1_struct_0(A_159))) | ~l1_pre_topc(A_159) | ~v2_pre_topc(A_159) | v2_struct_0(A_159))), inference(resolution, [status(thm)], [c_1335, c_12])).
% 30.20/19.43  tff(c_5220, plain, (![D_8]: (k8_relset_1(u1_struct_0('#skF_2'), k1_xboole_0, k7_tmap_1('#skF_2', '#skF_3'), D_8)=k10_relat_1(k7_tmap_1('#skF_2', '#skF_3'), D_8) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3914, c_1361])).
% 30.20/19.43  tff(c_5465, plain, (![D_8]: (k8_relset_1(k1_xboole_0, k1_xboole_0, k6_partfun1(k1_xboole_0), D_8)=k10_relat_1(k6_partfun1(k1_xboole_0), D_8) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_3934, c_3935, c_3906, c_3906, c_3935, c_5220])).
% 30.20/19.43  tff(c_5466, plain, (![D_8]: (k8_relset_1(k1_xboole_0, k1_xboole_0, k6_partfun1(k1_xboole_0), D_8)=k10_relat_1(k6_partfun1(k1_xboole_0), D_8))), inference(negUnitSimplification, [status(thm)], [c_76, c_5465])).
% 30.20/19.43  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 30.20/19.43  tff(c_1602, plain, (![A_169, A_170]: (k7_tmap_1(A_169, A_170)=k6_partfun1(u1_struct_0(A_169)) | ~l1_pre_topc(A_169) | ~v2_pre_topc(A_169) | v2_struct_0(A_169) | ~r1_tarski(A_170, u1_struct_0(A_169)))), inference(resolution, [status(thm)], [c_10, c_825])).
% 30.20/19.43  tff(c_1624, plain, (![A_171]: (k7_tmap_1(A_171, u1_struct_0(A_171))=k6_partfun1(u1_struct_0(A_171)) | ~l1_pre_topc(A_171) | ~v2_pre_topc(A_171) | v2_struct_0(A_171))), inference(resolution, [status(thm)], [c_6, c_1602])).
% 30.20/19.43  tff(c_535, plain, (![A_113, B_114]: (v1_funct_1(k7_tmap_1(A_113, B_114)) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113) | ~v2_pre_topc(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_127])).
% 30.20/19.43  tff(c_606, plain, (![A_119, A_120]: (v1_funct_1(k7_tmap_1(A_119, A_120)) | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119) | v2_struct_0(A_119) | ~r1_tarski(A_120, u1_struct_0(A_119)))), inference(resolution, [status(thm)], [c_10, c_535])).
% 30.20/19.43  tff(c_627, plain, (![A_119]: (v1_funct_1(k7_tmap_1(A_119, u1_struct_0(A_119))) | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119) | v2_struct_0(A_119))), inference(resolution, [status(thm)], [c_6, c_606])).
% 30.20/19.43  tff(c_1648, plain, (![A_171]: (v1_funct_1(k6_partfun1(u1_struct_0(A_171))) | ~l1_pre_topc(A_171) | ~v2_pre_topc(A_171) | v2_struct_0(A_171) | ~l1_pre_topc(A_171) | ~v2_pre_topc(A_171) | v2_struct_0(A_171))), inference(superposition, [status(thm), theory('equality')], [c_1624, c_627])).
% 30.20/19.43  tff(c_4073, plain, (v1_funct_1(k6_partfun1(k1_xboole_0)) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3935, c_1648])).
% 30.20/19.43  tff(c_4292, plain, (v1_funct_1(k6_partfun1(k1_xboole_0)) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_74, c_72, c_4073])).
% 30.20/19.43  tff(c_4293, plain, (v1_funct_1(k6_partfun1(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_76, c_4292])).
% 30.20/19.43  tff(c_50, plain, (![A_43, B_44]: (v1_funct_2(k7_tmap_1(A_43, B_44), u1_struct_0(A_43), u1_struct_0(k6_tmap_1(A_43, B_44))) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43) | ~v2_pre_topc(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_127])).
% 30.20/19.43  tff(c_5325, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), k1_xboole_0) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3914, c_50])).
% 30.20/19.43  tff(c_5548, plain, (v1_funct_2(k6_partfun1(k1_xboole_0), k1_xboole_0, k1_xboole_0) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_3934, c_3935, c_3906, c_3935, c_5325])).
% 30.20/19.43  tff(c_5549, plain, (v1_funct_2(k6_partfun1(k1_xboole_0), k1_xboole_0, k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_76, c_5548])).
% 30.20/19.43  tff(c_4988, plain, (v5_pre_topc(k6_partfun1(k1_xboole_0), '#skF_2', k6_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3906, c_138])).
% 30.20/19.43  tff(c_48, plain, (![A_43, B_44]: (m1_subset_1(k7_tmap_1(A_43, B_44), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_43), u1_struct_0(k6_tmap_1(A_43, B_44))))) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43) | ~v2_pre_topc(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_127])).
% 30.20/19.43  tff(c_2928, plain, (![A_219, B_220, C_221, D_222]: (k2_struct_0(A_219)!=k1_xboole_0 | v3_pre_topc(k8_relset_1(u1_struct_0(A_219), u1_struct_0(B_220), C_221, D_222), A_219) | ~v3_pre_topc(D_222, B_220) | ~m1_subset_1(D_222, k1_zfmisc_1(u1_struct_0(B_220))) | ~v5_pre_topc(C_221, A_219, B_220) | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_219), u1_struct_0(B_220)))) | ~v1_funct_2(C_221, u1_struct_0(A_219), u1_struct_0(B_220)) | ~v1_funct_1(C_221) | ~l1_pre_topc(B_220) | ~l1_pre_topc(A_219))), inference(cnfTransformation, [status(thm)], [f_85])).
% 30.20/19.43  tff(c_6518, plain, (![A_280, B_281, D_282]: (k2_struct_0(A_280)!=k1_xboole_0 | v3_pre_topc(k8_relset_1(u1_struct_0(A_280), u1_struct_0(k6_tmap_1(A_280, B_281)), k7_tmap_1(A_280, B_281), D_282), A_280) | ~v3_pre_topc(D_282, k6_tmap_1(A_280, B_281)) | ~m1_subset_1(D_282, k1_zfmisc_1(u1_struct_0(k6_tmap_1(A_280, B_281)))) | ~v5_pre_topc(k7_tmap_1(A_280, B_281), A_280, k6_tmap_1(A_280, B_281)) | ~v1_funct_2(k7_tmap_1(A_280, B_281), u1_struct_0(A_280), u1_struct_0(k6_tmap_1(A_280, B_281))) | ~v1_funct_1(k7_tmap_1(A_280, B_281)) | ~l1_pre_topc(k6_tmap_1(A_280, B_281)) | ~m1_subset_1(B_281, k1_zfmisc_1(u1_struct_0(A_280))) | ~l1_pre_topc(A_280) | ~v2_pre_topc(A_280) | v2_struct_0(A_280))), inference(resolution, [status(thm)], [c_48, c_2928])).
% 30.20/19.43  tff(c_6544, plain, (![D_282]: (k2_struct_0('#skF_2')!=k1_xboole_0 | v3_pre_topc(k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')), k6_partfun1(k1_xboole_0), D_282), '#skF_2') | ~v3_pre_topc(D_282, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_282, k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))) | ~v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k7_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3906, c_6518])).
% 30.20/19.43  tff(c_6586, plain, (![D_282]: (v3_pre_topc(k8_relset_1(k1_xboole_0, k1_xboole_0, k6_partfun1(k1_xboole_0), D_282), '#skF_2') | ~v3_pre_topc(D_282, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_282, k1_zfmisc_1(k1_xboole_0)) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_3934, c_3935, c_294, c_4293, c_3906, c_5549, c_3914, c_3906, c_3935, c_4988, c_3906, c_3914, c_3914, c_3935, c_3864, c_6544])).
% 30.20/19.43  tff(c_6587, plain, (![D_282]: (v3_pre_topc(k8_relset_1(k1_xboole_0, k1_xboole_0, k6_partfun1(k1_xboole_0), D_282), '#skF_2') | ~v3_pre_topc(D_282, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_282, k1_zfmisc_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_76, c_6586])).
% 30.20/19.43  tff(c_9069, plain, (![D_339]: (v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0), D_339), '#skF_2') | ~v3_pre_topc(D_339, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_339, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_5466, c_6587])).
% 30.20/19.43  tff(c_9081, plain, (v3_pre_topc('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4987, c_9069])).
% 30.20/19.43  tff(c_9087, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3934, c_1444, c_9081])).
% 30.20/19.43  tff(c_9089, plain, $false, inference(negUnitSimplification, [status(thm)], [c_248, c_9087])).
% 30.20/19.43  tff(c_9091, plain, (k2_struct_0('#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_3229])).
% 30.20/19.43  tff(c_316, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0(k6_tmap_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_298, c_187])).
% 30.20/19.43  tff(c_803, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_720, c_316])).
% 30.20/19.43  tff(c_800, plain, (![D_80]: (k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k7_tmap_1('#skF_2', '#skF_3'), D_80)=k10_relat_1(k7_tmap_1('#skF_2', '#skF_3'), D_80))), inference(demodulation, [status(thm), theory('equality')], [c_720, c_579])).
% 30.20/19.43  tff(c_2877, plain, (![B_215, A_216, C_217, D_218]: (k2_struct_0(B_215)=k1_xboole_0 | v3_pre_topc(k8_relset_1(u1_struct_0(A_216), u1_struct_0(B_215), C_217, D_218), A_216) | ~v3_pre_topc(D_218, B_215) | ~m1_subset_1(D_218, k1_zfmisc_1(u1_struct_0(B_215))) | ~v5_pre_topc(C_217, A_216, B_215) | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_216), u1_struct_0(B_215)))) | ~v1_funct_2(C_217, u1_struct_0(A_216), u1_struct_0(B_215)) | ~v1_funct_1(C_217) | ~l1_pre_topc(B_215) | ~l1_pre_topc(A_216))), inference(cnfTransformation, [status(thm)], [f_85])).
% 30.20/19.43  tff(c_12172, plain, (![A_449, B_450, D_451]: (k2_struct_0(k6_tmap_1(A_449, B_450))=k1_xboole_0 | v3_pre_topc(k8_relset_1(u1_struct_0(A_449), u1_struct_0(k6_tmap_1(A_449, B_450)), k7_tmap_1(A_449, B_450), D_451), A_449) | ~v3_pre_topc(D_451, k6_tmap_1(A_449, B_450)) | ~m1_subset_1(D_451, k1_zfmisc_1(u1_struct_0(k6_tmap_1(A_449, B_450)))) | ~v5_pre_topc(k7_tmap_1(A_449, B_450), A_449, k6_tmap_1(A_449, B_450)) | ~v1_funct_2(k7_tmap_1(A_449, B_450), u1_struct_0(A_449), u1_struct_0(k6_tmap_1(A_449, B_450))) | ~v1_funct_1(k7_tmap_1(A_449, B_450)) | ~l1_pre_topc(k6_tmap_1(A_449, B_450)) | ~m1_subset_1(B_450, k1_zfmisc_1(u1_struct_0(A_449))) | ~l1_pre_topc(A_449) | ~v2_pre_topc(A_449) | v2_struct_0(A_449))), inference(resolution, [status(thm)], [c_48, c_2877])).
% 30.20/19.43  tff(c_12225, plain, (![D_451]: (k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k1_xboole_0 | v3_pre_topc(k8_relset_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_2'), k7_tmap_1('#skF_2', '#skF_3'), D_451), '#skF_2') | ~v3_pre_topc(D_451, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_451, k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))) | ~v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k7_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_719, c_12172])).
% 30.20/19.43  tff(c_12251, plain, (![D_451]: (k2_struct_0('#skF_2')=k1_xboole_0 | v3_pre_topc(k10_relat_1(k7_tmap_1('#skF_2', '#skF_3'), D_451), '#skF_2') | ~v3_pre_topc(D_451, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_451, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_110, c_109, c_294, c_115, c_803, c_109, c_719, c_138, c_719, c_800, c_109, c_720, c_12225])).
% 30.20/19.43  tff(c_12256, plain, (![D_452]: (v3_pre_topc(k10_relat_1(k7_tmap_1('#skF_2', '#skF_3'), D_452), '#skF_2') | ~v3_pre_topc(D_452, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_452, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_9091, c_12251])).
% 30.20/19.43  tff(c_12262, plain, (v3_pre_topc('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1326, c_12256])).
% 30.20/19.43  tff(c_12267, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_1444, c_12262])).
% 30.20/19.43  tff(c_12269, plain, $false, inference(negUnitSimplification, [status(thm)], [c_248, c_12267])).
% 30.20/19.43  tff(c_12270, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_188])).
% 30.20/19.43  tff(c_12273, plain, (~m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_12270, c_115, c_187, c_109, c_138, c_109, c_78])).
% 30.20/19.43  tff(c_12454, plain, (~m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0(k6_tmap_1('#skF_2', '#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_12416, c_12273])).
% 30.20/19.43  tff(c_12798, plain, (~m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_12726, c_12454])).
% 30.20/19.43  tff(c_13453, plain, (![A_541, B_542]: (m1_subset_1(k7_tmap_1(A_541, B_542), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_541), u1_struct_0(k6_tmap_1(A_541, B_542))))) | ~m1_subset_1(B_542, k1_zfmisc_1(u1_struct_0(A_541))) | ~l1_pre_topc(A_541) | ~v2_pre_topc(A_541) | v2_struct_0(A_541))), inference(cnfTransformation, [status(thm)], [f_127])).
% 30.20/19.43  tff(c_13478, plain, (m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12725, c_13453])).
% 30.20/19.43  tff(c_13496, plain, (m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_110, c_109, c_109, c_13478])).
% 30.20/19.43  tff(c_13498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_12798, c_13496])).
% 30.20/19.43  tff(c_13500, plain, (~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_186])).
% 30.20/19.43  tff(c_13679, plain, (~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0(k6_tmap_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_13663, c_13500])).
% 30.20/19.43  tff(c_14119, plain, (~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14029, c_13679])).
% 30.20/19.43  tff(c_14584, plain, (![A_624, B_625]: (v1_funct_2(k7_tmap_1(A_624, B_625), u1_struct_0(A_624), u1_struct_0(k6_tmap_1(A_624, B_625))) | ~m1_subset_1(B_625, k1_zfmisc_1(u1_struct_0(A_624))) | ~l1_pre_topc(A_624) | ~v2_pre_topc(A_624) | v2_struct_0(A_624))), inference(cnfTransformation, [status(thm)], [f_127])).
% 30.20/19.43  tff(c_14599, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14028, c_14584])).
% 30.20/19.43  tff(c_14614, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_110, c_109, c_109, c_14599])).
% 30.20/19.43  tff(c_14616, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_14119, c_14614])).
% 30.20/19.43  tff(c_14618, plain, (~v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', k6_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_88])).
% 30.20/19.43  tff(c_16177, plain, (![B_724, A_725, C_726]: (k2_struct_0(B_724)=k1_xboole_0 | v3_pre_topc('#skF_1'(A_725, B_724, C_726), B_724) | v5_pre_topc(C_726, A_725, B_724) | ~m1_subset_1(C_726, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_725), u1_struct_0(B_724)))) | ~v1_funct_2(C_726, u1_struct_0(A_725), u1_struct_0(B_724)) | ~v1_funct_1(C_726) | ~l1_pre_topc(B_724) | ~l1_pre_topc(A_725))), inference(cnfTransformation, [status(thm)], [f_85])).
% 30.20/19.43  tff(c_16198, plain, (![A_725, C_726]: (k2_struct_0('#skF_2')=k1_xboole_0 | v3_pre_topc('#skF_1'(A_725, '#skF_2', C_726), '#skF_2') | v5_pre_topc(C_726, A_725, '#skF_2') | ~m1_subset_1(C_726, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_725), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_726, u1_struct_0(A_725), u1_struct_0('#skF_2')) | ~v1_funct_1(C_726) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_725))), inference(superposition, [status(thm), theory('equality')], [c_109, c_16177])).
% 30.20/19.43  tff(c_16212, plain, (![A_725, C_726]: (k2_struct_0('#skF_2')=k1_xboole_0 | v3_pre_topc('#skF_1'(A_725, '#skF_2', C_726), '#skF_2') | v5_pre_topc(C_726, A_725, '#skF_2') | ~m1_subset_1(C_726, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_725), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_726, u1_struct_0(A_725), k2_struct_0('#skF_2')) | ~v1_funct_1(C_726) | ~l1_pre_topc(A_725))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_109, c_16198])).
% 30.20/19.43  tff(c_17417, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_16212])).
% 30.20/19.43  tff(c_15078, plain, (![A_677, B_678]: (k7_tmap_1(A_677, B_678)=k6_partfun1(u1_struct_0(A_677)) | ~m1_subset_1(B_678, k1_zfmisc_1(u1_struct_0(A_677))) | ~l1_pre_topc(A_677) | ~v2_pre_topc(A_677) | v2_struct_0(A_677))), inference(cnfTransformation, [status(thm)], [f_97])).
% 30.20/19.43  tff(c_15091, plain, (![B_678]: (k7_tmap_1('#skF_2', B_678)=k6_partfun1(u1_struct_0('#skF_2')) | ~m1_subset_1(B_678, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_15078])).
% 30.20/19.43  tff(c_15098, plain, (![B_678]: (k7_tmap_1('#skF_2', B_678)=k6_partfun1(k2_struct_0('#skF_2')) | ~m1_subset_1(B_678, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_109, c_15091])).
% 30.20/19.43  tff(c_15100, plain, (![B_679]: (k7_tmap_1('#skF_2', B_679)=k6_partfun1(k2_struct_0('#skF_2')) | ~m1_subset_1(B_679, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_15098])).
% 30.20/19.43  tff(c_15109, plain, (k6_partfun1(k2_struct_0('#skF_2'))=k7_tmap_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_110, c_15100])).
% 30.20/19.43  tff(c_17468, plain, (k7_tmap_1('#skF_2', '#skF_3')=k6_partfun1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_17417, c_15109])).
% 30.20/19.43  tff(c_17889, plain, (~v5_pre_topc(k6_partfun1(k1_xboole_0), '#skF_2', k6_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_17468, c_14618])).
% 30.20/19.43  tff(c_17487, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_17417, c_110])).
% 30.20/19.43  tff(c_17488, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_17417, c_109])).
% 30.20/19.43  tff(c_14876, plain, (![A_669, B_670]: (l1_pre_topc(k6_tmap_1(A_669, B_670)) | ~m1_subset_1(B_670, k1_zfmisc_1(u1_struct_0(A_669))) | ~l1_pre_topc(A_669) | ~v2_pre_topc(A_669) | v2_struct_0(A_669))), inference(cnfTransformation, [status(thm)], [f_112])).
% 30.20/19.43  tff(c_14883, plain, (![B_670]: (l1_pre_topc(k6_tmap_1('#skF_2', B_670)) | ~m1_subset_1(B_670, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_14876])).
% 30.20/19.43  tff(c_14886, plain, (![B_670]: (l1_pre_topc(k6_tmap_1('#skF_2', B_670)) | ~m1_subset_1(B_670, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_14883])).
% 30.20/19.43  tff(c_14888, plain, (![B_671]: (l1_pre_topc(k6_tmap_1('#skF_2', B_671)) | ~m1_subset_1(B_671, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_14886])).
% 30.20/19.43  tff(c_14897, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_110, c_14888])).
% 30.20/19.43  tff(c_15872, plain, (![A_716, A_717]: (k7_tmap_1(A_716, A_717)=k6_partfun1(u1_struct_0(A_716)) | ~l1_pre_topc(A_716) | ~v2_pre_topc(A_716) | v2_struct_0(A_716) | ~r1_tarski(A_717, u1_struct_0(A_716)))), inference(resolution, [status(thm)], [c_10, c_15078])).
% 30.20/19.43  tff(c_15924, plain, (![A_720]: (k7_tmap_1(A_720, u1_struct_0(A_720))=k6_partfun1(u1_struct_0(A_720)) | ~l1_pre_topc(A_720) | ~v2_pre_topc(A_720) | v2_struct_0(A_720))), inference(resolution, [status(thm)], [c_6, c_15872])).
% 30.20/19.43  tff(c_14771, plain, (![A_655, B_656]: (v1_funct_1(k7_tmap_1(A_655, B_656)) | ~m1_subset_1(B_656, k1_zfmisc_1(u1_struct_0(A_655))) | ~l1_pre_topc(A_655) | ~v2_pre_topc(A_655) | v2_struct_0(A_655))), inference(cnfTransformation, [status(thm)], [f_127])).
% 30.20/19.43  tff(c_14805, plain, (![A_659, A_660]: (v1_funct_1(k7_tmap_1(A_659, A_660)) | ~l1_pre_topc(A_659) | ~v2_pre_topc(A_659) | v2_struct_0(A_659) | ~r1_tarski(A_660, u1_struct_0(A_659)))), inference(resolution, [status(thm)], [c_10, c_14771])).
% 30.20/19.43  tff(c_14816, plain, (![A_659]: (v1_funct_1(k7_tmap_1(A_659, u1_struct_0(A_659))) | ~l1_pre_topc(A_659) | ~v2_pre_topc(A_659) | v2_struct_0(A_659))), inference(resolution, [status(thm)], [c_6, c_14805])).
% 30.20/19.43  tff(c_15937, plain, (![A_720]: (v1_funct_1(k6_partfun1(u1_struct_0(A_720))) | ~l1_pre_topc(A_720) | ~v2_pre_topc(A_720) | v2_struct_0(A_720) | ~l1_pre_topc(A_720) | ~v2_pre_topc(A_720) | v2_struct_0(A_720))), inference(superposition, [status(thm), theory('equality')], [c_15924, c_14816])).
% 30.20/19.43  tff(c_17551, plain, (v1_funct_1(k6_partfun1(k1_xboole_0)) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_17488, c_15937])).
% 30.20/19.43  tff(c_17688, plain, (v1_funct_1(k6_partfun1(k1_xboole_0)) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_74, c_72, c_17551])).
% 30.20/19.43  tff(c_17689, plain, (v1_funct_1(k6_partfun1(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_76, c_17688])).
% 30.20/19.43  tff(c_15154, plain, (![A_682, B_683]: (u1_struct_0(k6_tmap_1(A_682, B_683))=u1_struct_0(A_682) | ~m1_subset_1(B_683, k1_zfmisc_1(u1_struct_0(A_682))) | ~l1_pre_topc(A_682) | ~v2_pre_topc(A_682) | v2_struct_0(A_682))), inference(cnfTransformation, [status(thm)], [f_168])).
% 30.20/19.43  tff(c_15167, plain, (![B_683]: (u1_struct_0(k6_tmap_1('#skF_2', B_683))=u1_struct_0('#skF_2') | ~m1_subset_1(B_683, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_15154])).
% 30.20/19.43  tff(c_15174, plain, (![B_683]: (u1_struct_0(k6_tmap_1('#skF_2', B_683))=k2_struct_0('#skF_2') | ~m1_subset_1(B_683, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_109, c_15167])).
% 30.20/19.43  tff(c_15176, plain, (![B_684]: (u1_struct_0(k6_tmap_1('#skF_2', B_684))=k2_struct_0('#skF_2') | ~m1_subset_1(B_684, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_15174])).
% 30.20/19.43  tff(c_15185, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_110, c_15176])).
% 30.20/19.43  tff(c_17462, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_17417, c_15185])).
% 30.20/19.43  tff(c_18309, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), k1_xboole_0) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_17462, c_50])).
% 30.20/19.43  tff(c_18452, plain, (v1_funct_2(k6_partfun1(k1_xboole_0), k1_xboole_0, k1_xboole_0) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_17487, c_17488, c_17468, c_17488, c_18309])).
% 30.20/19.43  tff(c_18453, plain, (v1_funct_2(k6_partfun1(k1_xboole_0), k1_xboole_0, k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_76, c_18452])).
% 30.20/19.43  tff(c_18288, plain, (m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), k1_xboole_0))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_17462, c_48])).
% 30.20/19.43  tff(c_18436, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_17487, c_17488, c_17468, c_17488, c_18288])).
% 30.20/19.43  tff(c_18437, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_76, c_18436])).
% 30.20/19.43  tff(c_16752, plain, (![A_747, B_748, C_749]: (k2_struct_0(A_747)!=k1_xboole_0 | m1_subset_1('#skF_1'(A_747, B_748, C_749), k1_zfmisc_1(u1_struct_0(B_748))) | v5_pre_topc(C_749, A_747, B_748) | ~m1_subset_1(C_749, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_747), u1_struct_0(B_748)))) | ~v1_funct_2(C_749, u1_struct_0(A_747), u1_struct_0(B_748)) | ~v1_funct_1(C_749) | ~l1_pre_topc(B_748) | ~l1_pre_topc(A_747))), inference(cnfTransformation, [status(thm)], [f_85])).
% 30.20/19.43  tff(c_20237, plain, (![A_833, B_834]: (k2_struct_0(A_833)!=k1_xboole_0 | m1_subset_1('#skF_1'(A_833, k6_tmap_1(A_833, B_834), k7_tmap_1(A_833, B_834)), k1_zfmisc_1(u1_struct_0(k6_tmap_1(A_833, B_834)))) | v5_pre_topc(k7_tmap_1(A_833, B_834), A_833, k6_tmap_1(A_833, B_834)) | ~v1_funct_2(k7_tmap_1(A_833, B_834), u1_struct_0(A_833), u1_struct_0(k6_tmap_1(A_833, B_834))) | ~v1_funct_1(k7_tmap_1(A_833, B_834)) | ~l1_pre_topc(k6_tmap_1(A_833, B_834)) | ~m1_subset_1(B_834, k1_zfmisc_1(u1_struct_0(A_833))) | ~l1_pre_topc(A_833) | ~v2_pre_topc(A_833) | v2_struct_0(A_833))), inference(resolution, [status(thm)], [c_48, c_16752])).
% 30.20/19.43  tff(c_20284, plain, (k2_struct_0('#skF_2')!=k1_xboole_0 | m1_subset_1('#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3')), k1_zfmisc_1(k1_xboole_0)) | v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k7_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_17462, c_20237])).
% 30.20/19.43  tff(c_20323, plain, (m1_subset_1('#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k6_partfun1(k1_xboole_0)), k1_zfmisc_1(k1_xboole_0)) | v5_pre_topc(k6_partfun1(k1_xboole_0), '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_17487, c_17488, c_14897, c_17689, c_17468, c_18453, c_17462, c_17468, c_17488, c_17468, c_17468, c_17417, c_20284])).
% 30.20/19.43  tff(c_20324, plain, (m1_subset_1('#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k6_partfun1(k1_xboole_0)), k1_zfmisc_1(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_76, c_17889, c_20323])).
% 30.20/19.43  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 30.20/19.43  tff(c_20368, plain, (r1_tarski('#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k6_partfun1(k1_xboole_0)), k1_xboole_0)), inference(resolution, [status(thm)], [c_20324, c_8])).
% 30.20/19.43  tff(c_16523, plain, (![A_734, B_735, C_736]: (k2_struct_0(A_734)!=k1_xboole_0 | v3_pre_topc('#skF_1'(A_734, B_735, C_736), B_735) | v5_pre_topc(C_736, A_734, B_735) | ~m1_subset_1(C_736, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_734), u1_struct_0(B_735)))) | ~v1_funct_2(C_736, u1_struct_0(A_734), u1_struct_0(B_735)) | ~v1_funct_1(C_736) | ~l1_pre_topc(B_735) | ~l1_pre_topc(A_734))), inference(cnfTransformation, [status(thm)], [f_85])).
% 30.20/19.43  tff(c_19810, plain, (![A_828, B_829]: (k2_struct_0(A_828)!=k1_xboole_0 | v3_pre_topc('#skF_1'(A_828, k6_tmap_1(A_828, B_829), k7_tmap_1(A_828, B_829)), k6_tmap_1(A_828, B_829)) | v5_pre_topc(k7_tmap_1(A_828, B_829), A_828, k6_tmap_1(A_828, B_829)) | ~v1_funct_2(k7_tmap_1(A_828, B_829), u1_struct_0(A_828), u1_struct_0(k6_tmap_1(A_828, B_829))) | ~v1_funct_1(k7_tmap_1(A_828, B_829)) | ~l1_pre_topc(k6_tmap_1(A_828, B_829)) | ~m1_subset_1(B_829, k1_zfmisc_1(u1_struct_0(A_828))) | ~l1_pre_topc(A_828) | ~v2_pre_topc(A_828) | v2_struct_0(A_828))), inference(resolution, [status(thm)], [c_48, c_16523])).
% 30.20/19.43  tff(c_19824, plain, (k2_struct_0('#skF_2')!=k1_xboole_0 | v3_pre_topc('#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3')), k6_tmap_1('#skF_2', '#skF_3')) | v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k6_partfun1(k1_xboole_0), u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k7_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_17468, c_19810])).
% 30.20/19.43  tff(c_19855, plain, (v3_pre_topc('#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k6_partfun1(k1_xboole_0)), k6_tmap_1('#skF_2', '#skF_3')) | v5_pre_topc(k6_partfun1(k1_xboole_0), '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_17487, c_17488, c_14897, c_17689, c_17468, c_18453, c_17462, c_17488, c_17468, c_17468, c_17417, c_19824])).
% 30.20/19.43  tff(c_19856, plain, (v3_pre_topc('#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k6_partfun1(k1_xboole_0)), k6_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_76, c_17889, c_19855])).
% 30.20/19.43  tff(c_14617, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_88])).
% 30.20/19.43  tff(c_14692, plain, (![B_638, A_639]: (r2_hidden(B_638, u1_pre_topc(A_639)) | ~v3_pre_topc(B_638, A_639) | ~m1_subset_1(B_638, k1_zfmisc_1(u1_struct_0(A_639))) | ~l1_pre_topc(A_639))), inference(cnfTransformation, [status(thm)], [f_56])).
% 30.20/19.43  tff(c_14699, plain, (![B_638]: (r2_hidden(B_638, u1_pre_topc('#skF_2')) | ~v3_pre_topc(B_638, '#skF_2') | ~m1_subset_1(B_638, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_14692])).
% 30.20/19.43  tff(c_14703, plain, (![B_640]: (r2_hidden(B_640, u1_pre_topc('#skF_2')) | ~v3_pre_topc(B_640, '#skF_2') | ~m1_subset_1(B_640, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_14699])).
% 30.20/19.43  tff(c_14710, plain, (r2_hidden('#skF_3', u1_pre_topc('#skF_2')) | ~v3_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_110, c_14703])).
% 30.20/19.43  tff(c_14714, plain, (r2_hidden('#skF_3', u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14617, c_14710])).
% 30.20/19.43  tff(c_15511, plain, (![A_697, B_698]: (k5_tmap_1(A_697, B_698)=u1_pre_topc(A_697) | ~r2_hidden(B_698, u1_pre_topc(A_697)) | ~m1_subset_1(B_698, k1_zfmisc_1(u1_struct_0(A_697))) | ~l1_pre_topc(A_697) | ~v2_pre_topc(A_697) | v2_struct_0(A_697))), inference(cnfTransformation, [status(thm)], [f_154])).
% 30.20/19.43  tff(c_15524, plain, (![B_698]: (k5_tmap_1('#skF_2', B_698)=u1_pre_topc('#skF_2') | ~r2_hidden(B_698, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_698, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_15511])).
% 30.20/19.43  tff(c_15531, plain, (![B_698]: (k5_tmap_1('#skF_2', B_698)=u1_pre_topc('#skF_2') | ~r2_hidden(B_698, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_698, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_15524])).
% 30.20/19.43  tff(c_15533, plain, (![B_699]: (k5_tmap_1('#skF_2', B_699)=u1_pre_topc('#skF_2') | ~r2_hidden(B_699, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_699, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_15531])).
% 30.20/19.43  tff(c_15540, plain, (k5_tmap_1('#skF_2', '#skF_3')=u1_pre_topc('#skF_2') | ~r2_hidden('#skF_3', u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_110, c_15533])).
% 30.20/19.43  tff(c_15544, plain, (k5_tmap_1('#skF_2', '#skF_3')=u1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14714, c_15540])).
% 30.20/19.43  tff(c_15357, plain, (![A_686, B_687]: (u1_pre_topc(k6_tmap_1(A_686, B_687))=k5_tmap_1(A_686, B_687) | ~m1_subset_1(B_687, k1_zfmisc_1(u1_struct_0(A_686))) | ~l1_pre_topc(A_686) | ~v2_pre_topc(A_686) | v2_struct_0(A_686))), inference(cnfTransformation, [status(thm)], [f_168])).
% 30.20/19.43  tff(c_15370, plain, (![B_687]: (u1_pre_topc(k6_tmap_1('#skF_2', B_687))=k5_tmap_1('#skF_2', B_687) | ~m1_subset_1(B_687, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_15357])).
% 30.20/19.43  tff(c_15377, plain, (![B_687]: (u1_pre_topc(k6_tmap_1('#skF_2', B_687))=k5_tmap_1('#skF_2', B_687) | ~m1_subset_1(B_687, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_15370])).
% 30.20/19.43  tff(c_15379, plain, (![B_688]: (u1_pre_topc(k6_tmap_1('#skF_2', B_688))=k5_tmap_1('#skF_2', B_688) | ~m1_subset_1(B_688, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_15377])).
% 30.20/19.43  tff(c_15388, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=k5_tmap_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_110, c_15379])).
% 30.20/19.43  tff(c_15546, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=u1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_15544, c_15388])).
% 30.20/19.43  tff(c_14700, plain, (![A_3, A_639]: (r2_hidden(A_3, u1_pre_topc(A_639)) | ~v3_pre_topc(A_3, A_639) | ~l1_pre_topc(A_639) | ~r1_tarski(A_3, u1_struct_0(A_639)))), inference(resolution, [status(thm)], [c_10, c_14692])).
% 30.20/19.43  tff(c_15554, plain, (![A_3]: (r2_hidden(A_3, u1_pre_topc('#skF_2')) | ~v3_pre_topc(A_3, k6_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | ~r1_tarski(A_3, u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_15546, c_14700])).
% 30.20/19.43  tff(c_15561, plain, (![A_3]: (r2_hidden(A_3, u1_pre_topc('#skF_2')) | ~v3_pre_topc(A_3, k6_tmap_1('#skF_2', '#skF_3')) | ~r1_tarski(A_3, k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_15185, c_14897, c_15554])).
% 30.20/19.43  tff(c_21166, plain, (![A_843]: (r2_hidden(A_843, u1_pre_topc('#skF_2')) | ~v3_pre_topc(A_843, k6_tmap_1('#skF_2', '#skF_3')) | ~r1_tarski(A_843, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_17417, c_15561])).
% 30.20/19.43  tff(c_21173, plain, (r2_hidden('#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k6_partfun1(k1_xboole_0)), u1_pre_topc('#skF_2')) | ~r1_tarski('#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k6_partfun1(k1_xboole_0)), k1_xboole_0)), inference(resolution, [status(thm)], [c_19856, c_21166])).
% 30.20/19.43  tff(c_21194, plain, (r2_hidden('#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k6_partfun1(k1_xboole_0)), u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20368, c_21173])).
% 30.20/19.43  tff(c_14666, plain, (![B_632, A_633]: (v3_pre_topc(B_632, A_633) | ~r2_hidden(B_632, u1_pre_topc(A_633)) | ~m1_subset_1(B_632, k1_zfmisc_1(u1_struct_0(A_633))) | ~l1_pre_topc(A_633))), inference(cnfTransformation, [status(thm)], [f_56])).
% 30.20/19.43  tff(c_14673, plain, (![B_632]: (v3_pre_topc(B_632, '#skF_2') | ~r2_hidden(B_632, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_632, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_14666])).
% 30.20/19.43  tff(c_14676, plain, (![B_632]: (v3_pre_topc(B_632, '#skF_2') | ~r2_hidden(B_632, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_632, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_14673])).
% 30.20/19.43  tff(c_17483, plain, (![B_632]: (v3_pre_topc(B_632, '#skF_2') | ~r2_hidden(B_632, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_632, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_17417, c_14676])).
% 30.20/19.43  tff(c_21213, plain, (v3_pre_topc('#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k6_partfun1(k1_xboole_0)), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k6_partfun1(k1_xboole_0)), k1_zfmisc_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_21194, c_17483])).
% 30.20/19.43  tff(c_21228, plain, (v3_pre_topc('#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k6_partfun1(k1_xboole_0)), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20324, c_21213])).
% 30.20/19.43  tff(c_14, plain, (![A_9, B_10]: (k8_relset_1(A_9, A_9, k6_partfun1(A_9), B_10)=B_10 | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 30.20/19.43  tff(c_20367, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, k6_partfun1(k1_xboole_0), '#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k6_partfun1(k1_xboole_0)))='#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_20324, c_14])).
% 30.20/19.43  tff(c_16073, plain, (![A_721, B_722]: (m1_subset_1(k7_tmap_1(A_721, B_722), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_721), u1_struct_0(k6_tmap_1(A_721, B_722))))) | ~m1_subset_1(B_722, k1_zfmisc_1(u1_struct_0(A_721))) | ~l1_pre_topc(A_721) | ~v2_pre_topc(A_721) | v2_struct_0(A_721))), inference(cnfTransformation, [status(thm)], [f_127])).
% 30.20/19.43  tff(c_18508, plain, (![A_783, B_784, D_785]: (k8_relset_1(u1_struct_0(A_783), u1_struct_0(k6_tmap_1(A_783, B_784)), k7_tmap_1(A_783, B_784), D_785)=k10_relat_1(k7_tmap_1(A_783, B_784), D_785) | ~m1_subset_1(B_784, k1_zfmisc_1(u1_struct_0(A_783))) | ~l1_pre_topc(A_783) | ~v2_pre_topc(A_783) | v2_struct_0(A_783))), inference(resolution, [status(thm)], [c_16073, c_12])).
% 30.20/19.43  tff(c_18537, plain, (![D_785]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')), k6_partfun1(k1_xboole_0), D_785)=k10_relat_1(k7_tmap_1('#skF_2', '#skF_3'), D_785) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_17468, c_18508])).
% 30.20/19.43  tff(c_18572, plain, (![D_785]: (k8_relset_1(k1_xboole_0, k1_xboole_0, k6_partfun1(k1_xboole_0), D_785)=k10_relat_1(k6_partfun1(k1_xboole_0), D_785) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_17487, c_17488, c_17462, c_17468, c_17488, c_18537])).
% 30.20/19.43  tff(c_18573, plain, (![D_785]: (k8_relset_1(k1_xboole_0, k1_xboole_0, k6_partfun1(k1_xboole_0), D_785)=k10_relat_1(k6_partfun1(k1_xboole_0), D_785))), inference(negUnitSimplification, [status(thm)], [c_76, c_18572])).
% 30.20/19.43  tff(c_25152, plain, (k10_relat_1(k6_partfun1(k1_xboole_0), '#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k6_partfun1(k1_xboole_0)))='#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k6_partfun1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20367, c_18573])).
% 30.20/19.43  tff(c_24, plain, (![A_16, B_28, C_34]: (k2_struct_0(A_16)!=k1_xboole_0 | ~v3_pre_topc(k8_relset_1(u1_struct_0(A_16), u1_struct_0(B_28), C_34, '#skF_1'(A_16, B_28, C_34)), A_16) | v5_pre_topc(C_34, A_16, B_28) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_16), u1_struct_0(B_28)))) | ~v1_funct_2(C_34, u1_struct_0(A_16), u1_struct_0(B_28)) | ~v1_funct_1(C_34) | ~l1_pre_topc(B_28) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_85])).
% 30.20/19.43  tff(c_30533, plain, (![A_1043, B_1044]: (k2_struct_0(A_1043)!=k1_xboole_0 | ~v3_pre_topc(k10_relat_1(k7_tmap_1(A_1043, B_1044), '#skF_1'(A_1043, k6_tmap_1(A_1043, B_1044), k7_tmap_1(A_1043, B_1044))), A_1043) | v5_pre_topc(k7_tmap_1(A_1043, B_1044), A_1043, k6_tmap_1(A_1043, B_1044)) | ~m1_subset_1(k7_tmap_1(A_1043, B_1044), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1043), u1_struct_0(k6_tmap_1(A_1043, B_1044))))) | ~v1_funct_2(k7_tmap_1(A_1043, B_1044), u1_struct_0(A_1043), u1_struct_0(k6_tmap_1(A_1043, B_1044))) | ~v1_funct_1(k7_tmap_1(A_1043, B_1044)) | ~l1_pre_topc(k6_tmap_1(A_1043, B_1044)) | ~l1_pre_topc(A_1043) | ~m1_subset_1(B_1044, k1_zfmisc_1(u1_struct_0(A_1043))) | ~l1_pre_topc(A_1043) | ~v2_pre_topc(A_1043) | v2_struct_0(A_1043))), inference(superposition, [status(thm), theory('equality')], [c_18508, c_24])).
% 30.20/19.43  tff(c_30573, plain, (k2_struct_0('#skF_2')!=k1_xboole_0 | ~v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0), '#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'))), '#skF_2') | v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))))) | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k7_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_17468, c_30533])).
% 30.20/19.43  tff(c_30624, plain, (v5_pre_topc(k6_partfun1(k1_xboole_0), '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_17487, c_17488, c_72, c_14897, c_17689, c_17468, c_18453, c_17488, c_17468, c_17462, c_18437, c_17488, c_17468, c_17462, c_17468, c_21228, c_25152, c_17468, c_17417, c_30573])).
% 30.20/19.43  tff(c_30626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_17889, c_30624])).
% 30.20/19.43  tff(c_30628, plain, (k2_struct_0('#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_16212])).
% 30.20/19.43  tff(c_15687, plain, (![A_710, B_711]: (v1_funct_2(k7_tmap_1(A_710, B_711), u1_struct_0(A_710), u1_struct_0(k6_tmap_1(A_710, B_711))) | ~m1_subset_1(B_711, k1_zfmisc_1(u1_struct_0(A_710))) | ~l1_pre_topc(A_710) | ~v2_pre_topc(A_710) | v2_struct_0(A_710))), inference(cnfTransformation, [status(thm)], [f_127])).
% 30.20/19.43  tff(c_15699, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_15185, c_15687])).
% 30.20/19.43  tff(c_15714, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_110, c_109, c_109, c_15699])).
% 30.20/19.43  tff(c_15715, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_76, c_15714])).
% 30.20/19.43  tff(c_16101, plain, (m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_15185, c_16073])).
% 30.20/19.43  tff(c_16119, plain, (m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_110, c_109, c_109, c_16101])).
% 30.20/19.43  tff(c_16120, plain, (m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_16119])).
% 30.20/19.43  tff(c_16136, plain, (r1_tarski(k7_tmap_1('#skF_2', '#skF_3'), k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_16120, c_8])).
% 30.20/19.43  tff(c_14913, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_14897, c_104])).
% 30.20/19.43  tff(c_15186, plain, (k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_15185, c_14913])).
% 30.20/19.43  tff(c_16625, plain, (![B_741, A_742, C_743]: (k2_struct_0(B_741)=k1_xboole_0 | m1_subset_1('#skF_1'(A_742, B_741, C_743), k1_zfmisc_1(u1_struct_0(B_741))) | v5_pre_topc(C_743, A_742, B_741) | ~m1_subset_1(C_743, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_742), u1_struct_0(B_741)))) | ~v1_funct_2(C_743, u1_struct_0(A_742), u1_struct_0(B_741)) | ~v1_funct_1(C_743) | ~l1_pre_topc(B_741) | ~l1_pre_topc(A_742))), inference(cnfTransformation, [status(thm)], [f_85])).
% 30.20/19.43  tff(c_31848, plain, (![B_1090, A_1091, A_1092]: (k2_struct_0(B_1090)=k1_xboole_0 | m1_subset_1('#skF_1'(A_1091, B_1090, A_1092), k1_zfmisc_1(u1_struct_0(B_1090))) | v5_pre_topc(A_1092, A_1091, B_1090) | ~v1_funct_2(A_1092, u1_struct_0(A_1091), u1_struct_0(B_1090)) | ~v1_funct_1(A_1092) | ~l1_pre_topc(B_1090) | ~l1_pre_topc(A_1091) | ~r1_tarski(A_1092, k2_zfmisc_1(u1_struct_0(A_1091), u1_struct_0(B_1090))))), inference(resolution, [status(thm)], [c_10, c_16625])).
% 30.20/19.43  tff(c_31870, plain, (![B_1090, A_1092]: (k2_struct_0(B_1090)=k1_xboole_0 | m1_subset_1('#skF_1'('#skF_2', B_1090, A_1092), k1_zfmisc_1(u1_struct_0(B_1090))) | v5_pre_topc(A_1092, '#skF_2', B_1090) | ~v1_funct_2(A_1092, u1_struct_0('#skF_2'), u1_struct_0(B_1090)) | ~v1_funct_1(A_1092) | ~l1_pre_topc(B_1090) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_1092, k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(B_1090))))), inference(superposition, [status(thm), theory('equality')], [c_109, c_31848])).
% 30.20/19.43  tff(c_32410, plain, (![B_1109, A_1110]: (k2_struct_0(B_1109)=k1_xboole_0 | m1_subset_1('#skF_1'('#skF_2', B_1109, A_1110), k1_zfmisc_1(u1_struct_0(B_1109))) | v5_pre_topc(A_1110, '#skF_2', B_1109) | ~v1_funct_2(A_1110, k2_struct_0('#skF_2'), u1_struct_0(B_1109)) | ~v1_funct_1(A_1110) | ~l1_pre_topc(B_1109) | ~r1_tarski(A_1110, k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(B_1109))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_109, c_31870])).
% 30.20/19.43  tff(c_32420, plain, (![A_1110]: (k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k1_xboole_0 | m1_subset_1('#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), A_1110), k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))) | v5_pre_topc(A_1110, '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(A_1110, k2_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(A_1110) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | ~r1_tarski(A_1110, k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_15185, c_32410])).
% 30.20/19.43  tff(c_32431, plain, (![A_1110]: (k2_struct_0('#skF_2')=k1_xboole_0 | m1_subset_1('#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), A_1110), k1_zfmisc_1(k2_struct_0('#skF_2'))) | v5_pre_topc(A_1110, '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(A_1110, k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(A_1110) | ~r1_tarski(A_1110, k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_14897, c_15185, c_15185, c_15186, c_32420])).
% 30.20/19.43  tff(c_32927, plain, (![A_1119]: (m1_subset_1('#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), A_1119), k1_zfmisc_1(k2_struct_0('#skF_2'))) | v5_pre_topc(A_1119, '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(A_1119, k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(A_1119) | ~r1_tarski(A_1119, k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_30628, c_32431])).
% 30.20/19.43  tff(c_33001, plain, (![A_1121]: (r1_tarski('#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), A_1121), k2_struct_0('#skF_2')) | v5_pre_topc(A_1121, '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(A_1121, k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(A_1121) | ~r1_tarski(A_1121, k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_32927, c_8])).
% 30.20/19.43  tff(c_16107, plain, (![B_722]: (m1_subset_1(k7_tmap_1('#skF_2', B_722), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', B_722))))) | ~m1_subset_1(B_722, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_16073])).
% 30.20/19.43  tff(c_16125, plain, (![B_722]: (m1_subset_1(k7_tmap_1('#skF_2', B_722), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', B_722))))) | ~m1_subset_1(B_722, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_109, c_16107])).
% 30.20/19.43  tff(c_16126, plain, (![B_722]: (m1_subset_1(k7_tmap_1('#skF_2', B_722), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', B_722))))) | ~m1_subset_1(B_722, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_16125])).
% 30.20/19.43  tff(c_16196, plain, (![B_724, C_726]: (k2_struct_0(B_724)=k1_xboole_0 | v3_pre_topc('#skF_1'('#skF_2', B_724, C_726), B_724) | v5_pre_topc(C_726, '#skF_2', B_724) | ~m1_subset_1(C_726, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(B_724)))) | ~v1_funct_2(C_726, u1_struct_0('#skF_2'), u1_struct_0(B_724)) | ~v1_funct_1(C_726) | ~l1_pre_topc(B_724) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_16177])).
% 30.20/19.43  tff(c_30631, plain, (![B_1045, C_1046]: (k2_struct_0(B_1045)=k1_xboole_0 | v3_pre_topc('#skF_1'('#skF_2', B_1045, C_1046), B_1045) | v5_pre_topc(C_1046, '#skF_2', B_1045) | ~m1_subset_1(C_1046, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(B_1045)))) | ~v1_funct_2(C_1046, k2_struct_0('#skF_2'), u1_struct_0(B_1045)) | ~v1_funct_1(C_1046) | ~l1_pre_topc(B_1045))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_109, c_16196])).
% 30.20/19.43  tff(c_30828, plain, (![B_1056]: (k2_struct_0(k6_tmap_1('#skF_2', B_1056))=k1_xboole_0 | v3_pre_topc('#skF_1'('#skF_2', k6_tmap_1('#skF_2', B_1056), k7_tmap_1('#skF_2', B_1056)), k6_tmap_1('#skF_2', B_1056)) | v5_pre_topc(k7_tmap_1('#skF_2', B_1056), '#skF_2', k6_tmap_1('#skF_2', B_1056)) | ~v1_funct_2(k7_tmap_1('#skF_2', B_1056), k2_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', B_1056))) | ~v1_funct_1(k7_tmap_1('#skF_2', B_1056)) | ~l1_pre_topc(k6_tmap_1('#skF_2', B_1056)) | ~m1_subset_1(B_1056, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_16126, c_30631])).
% 30.20/19.43  tff(c_30843, plain, (k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k1_xboole_0 | v3_pre_topc('#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3')), k6_tmap_1('#skF_2', '#skF_3')) | v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(k7_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_15185, c_30828])).
% 30.20/19.43  tff(c_30860, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | v3_pre_topc('#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3')), k6_tmap_1('#skF_2', '#skF_3')) | v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', k6_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_14897, c_115, c_15715, c_15186, c_30843])).
% 30.20/19.43  tff(c_30861, plain, (v3_pre_topc('#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3')), k6_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_14618, c_30628, c_30860])).
% 30.20/19.43  tff(c_30868, plain, (r2_hidden('#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3')), u1_pre_topc('#skF_2')) | ~r1_tarski('#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3')), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30861, c_15561])).
% 30.20/19.43  tff(c_30869, plain, (~r1_tarski('#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3')), k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_30868])).
% 30.20/19.43  tff(c_33004, plain, (v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(k7_tmap_1('#skF_2', '#skF_3')) | ~r1_tarski(k7_tmap_1('#skF_2', '#skF_3'), k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_33001, c_30869])).
% 30.20/19.43  tff(c_33039, plain, (v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', k6_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_16136, c_115, c_15715, c_33004])).
% 30.20/19.43  tff(c_33041, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14618, c_33039])).
% 30.20/19.43  tff(c_33043, plain, (r1_tarski('#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3')), k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_30868])).
% 30.20/19.43  tff(c_33042, plain, (r2_hidden('#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3')), u1_pre_topc('#skF_2'))), inference(splitRight, [status(thm)], [c_30868])).
% 30.20/19.43  tff(c_14678, plain, (![B_634]: (v3_pre_topc(B_634, '#skF_2') | ~r2_hidden(B_634, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_634, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_14673])).
% 30.20/19.43  tff(c_14686, plain, (![A_3]: (v3_pre_topc(A_3, '#skF_2') | ~r2_hidden(A_3, u1_pre_topc('#skF_2')) | ~r1_tarski(A_3, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_10, c_14678])).
% 30.20/19.43  tff(c_33064, plain, (v3_pre_topc('#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3')), '#skF_2') | ~r1_tarski('#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3')), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_33042, c_14686])).
% 30.20/19.43  tff(c_37456, plain, (v3_pre_topc('#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_33043, c_33064])).
% 30.20/19.43  tff(c_16134, plain, (![D_8]: (k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k7_tmap_1('#skF_2', '#skF_3'), D_8)=k10_relat_1(k7_tmap_1('#skF_2', '#skF_3'), D_8))), inference(resolution, [status(thm)], [c_16120, c_12])).
% 30.20/19.43  tff(c_14621, plain, (![A_627, B_628]: (k8_relset_1(A_627, A_627, k6_partfun1(A_627), B_628)=B_628 | ~m1_subset_1(B_628, k1_zfmisc_1(A_627)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 30.20/19.43  tff(c_14626, plain, (![B_4, A_3]: (k8_relset_1(B_4, B_4, k6_partfun1(B_4), A_3)=A_3 | ~r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_10, c_14621])).
% 30.20/19.43  tff(c_15115, plain, (![A_3]: (k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k7_tmap_1('#skF_2', '#skF_3'), A_3)=A_3 | ~r1_tarski(A_3, k2_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_15109, c_14626])).
% 30.20/19.43  tff(c_16145, plain, (![A_3]: (k10_relat_1(k7_tmap_1('#skF_2', '#skF_3'), A_3)=A_3 | ~r1_tarski(A_3, k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_16134, c_15115])).
% 30.20/19.43  tff(c_33097, plain, (k10_relat_1(k7_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3')))='#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_33043, c_16145])).
% 30.20/19.43  tff(c_33112, plain, (![A_1122, B_1123, D_1124]: (k8_relset_1(u1_struct_0(A_1122), u1_struct_0(k6_tmap_1(A_1122, B_1123)), k7_tmap_1(A_1122, B_1123), D_1124)=k10_relat_1(k7_tmap_1(A_1122, B_1123), D_1124) | ~m1_subset_1(B_1123, k1_zfmisc_1(u1_struct_0(A_1122))) | ~l1_pre_topc(A_1122) | ~v2_pre_topc(A_1122) | v2_struct_0(A_1122))), inference(resolution, [status(thm)], [c_16073, c_12])).
% 30.20/19.43  tff(c_26, plain, (![B_28, A_16, C_34]: (k2_struct_0(B_28)=k1_xboole_0 | ~v3_pre_topc(k8_relset_1(u1_struct_0(A_16), u1_struct_0(B_28), C_34, '#skF_1'(A_16, B_28, C_34)), A_16) | v5_pre_topc(C_34, A_16, B_28) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_16), u1_struct_0(B_28)))) | ~v1_funct_2(C_34, u1_struct_0(A_16), u1_struct_0(B_28)) | ~v1_funct_1(C_34) | ~l1_pre_topc(B_28) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_85])).
% 30.20/19.43  tff(c_76837, plain, (![A_1925, B_1926]: (k2_struct_0(k6_tmap_1(A_1925, B_1926))=k1_xboole_0 | ~v3_pre_topc(k10_relat_1(k7_tmap_1(A_1925, B_1926), '#skF_1'(A_1925, k6_tmap_1(A_1925, B_1926), k7_tmap_1(A_1925, B_1926))), A_1925) | v5_pre_topc(k7_tmap_1(A_1925, B_1926), A_1925, k6_tmap_1(A_1925, B_1926)) | ~m1_subset_1(k7_tmap_1(A_1925, B_1926), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1925), u1_struct_0(k6_tmap_1(A_1925, B_1926))))) | ~v1_funct_2(k7_tmap_1(A_1925, B_1926), u1_struct_0(A_1925), u1_struct_0(k6_tmap_1(A_1925, B_1926))) | ~v1_funct_1(k7_tmap_1(A_1925, B_1926)) | ~l1_pre_topc(k6_tmap_1(A_1925, B_1926)) | ~l1_pre_topc(A_1925) | ~m1_subset_1(B_1926, k1_zfmisc_1(u1_struct_0(A_1925))) | ~l1_pre_topc(A_1925) | ~v2_pre_topc(A_1925) | v2_struct_0(A_1925))), inference(superposition, [status(thm), theory('equality')], [c_33112, c_26])).
% 30.20/19.43  tff(c_76876, plain, (k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k1_xboole_0 | ~v3_pre_topc('#skF_1'('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3')), '#skF_2') | v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))))) | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k7_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_33097, c_76837])).
% 30.20/19.43  tff(c_76931, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_110, c_109, c_72, c_14897, c_115, c_15715, c_109, c_15185, c_16120, c_109, c_15185, c_37456, c_15186, c_76876])).
% 30.20/19.43  tff(c_76933, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_14618, c_30628, c_76931])).
% 30.20/19.43  tff(c_76935, plain, (~v1_funct_1(k7_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_96])).
% 30.20/19.43  tff(c_77215, plain, (![A_1977, B_1978]: (v1_funct_1(k7_tmap_1(A_1977, B_1978)) | ~m1_subset_1(B_1978, k1_zfmisc_1(u1_struct_0(A_1977))) | ~l1_pre_topc(A_1977) | ~v2_pre_topc(A_1977) | v2_struct_0(A_1977))), inference(cnfTransformation, [status(thm)], [f_127])).
% 30.20/19.43  tff(c_77222, plain, (![B_1978]: (v1_funct_1(k7_tmap_1('#skF_2', B_1978)) | ~m1_subset_1(B_1978, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_77215])).
% 30.20/19.43  tff(c_77225, plain, (![B_1978]: (v1_funct_1(k7_tmap_1('#skF_2', B_1978)) | ~m1_subset_1(B_1978, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_77222])).
% 30.20/19.43  tff(c_77227, plain, (![B_1979]: (v1_funct_1(k7_tmap_1('#skF_2', B_1979)) | ~m1_subset_1(B_1979, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_77225])).
% 30.20/19.43  tff(c_77234, plain, (v1_funct_1(k7_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_110, c_77227])).
% 30.20/19.43  tff(c_77239, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76935, c_77234])).
% 30.20/19.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.20/19.43  
% 30.20/19.43  Inference rules
% 30.20/19.43  ----------------------
% 30.20/19.43  #Ref     : 0
% 30.20/19.43  #Sup     : 17690
% 30.20/19.43  #Fact    : 0
% 30.20/19.43  #Define  : 0
% 30.20/19.43  #Split   : 77
% 30.20/19.43  #Chain   : 0
% 30.20/19.43  #Close   : 0
% 30.20/19.43  
% 30.20/19.43  Ordering : KBO
% 30.20/19.43  
% 30.20/19.43  Simplification rules
% 30.20/19.43  ----------------------
% 30.20/19.43  #Subsume      : 1952
% 30.20/19.43  #Demod        : 61128
% 30.20/19.43  #Tautology    : 5619
% 30.20/19.43  #SimpNegUnit  : 2692
% 30.20/19.43  #BackRed      : 208
% 30.20/19.43  
% 30.20/19.43  #Partial instantiations: 0
% 30.20/19.43  #Strategies tried      : 1
% 30.20/19.43  
% 30.20/19.43  Timing (in seconds)
% 30.20/19.43  ----------------------
% 30.20/19.43  Preprocessing        : 0.39
% 30.20/19.43  Parsing              : 0.21
% 30.20/19.43  CNF conversion       : 0.03
% 30.20/19.43  Main loop            : 18.18
% 30.20/19.43  Inferencing          : 3.39
% 30.20/19.43  Reduction            : 8.79
% 30.20/19.43  Demodulation         : 7.41
% 30.20/19.43  BG Simplification    : 0.44
% 30.20/19.43  Subsumption          : 4.83
% 30.20/19.43  Abstraction          : 0.74
% 30.20/19.43  MUC search           : 0.00
% 30.20/19.43  Cooper               : 0.00
% 30.20/19.43  Total                : 18.69
% 30.20/19.43  Index Insertion      : 0.00
% 30.20/19.43  Index Deletion       : 0.00
% 30.20/19.43  Index Matching       : 0.00
% 30.20/19.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
