%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1795+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:24 EST 2020

% Result     : Theorem 19.10s
% Output     : CNFRefutation 19.29s
% Verified   : 
% Statistics : Number of formulae       :  220 (2337 expanded)
%              Number of leaves         :   46 ( 844 expanded)
%              Depth                    :   22
%              Number of atoms          :  604 (9718 expanded)
%              Number of equality atoms :   27 ( 644 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > r1_xboole_0 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k9_subset_1 > k7_tmap_1 > k6_tmap_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k7_tmap_1,type,(
    k7_tmap_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_218,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ( r1_xboole_0(u1_struct_0(C),B)
                 => ( v1_funct_1(k2_tmap_1(A,k6_tmap_1(A,B),k7_tmap_1(A,B),C))
                    & v1_funct_2(k2_tmap_1(A,k6_tmap_1(A,B),k7_tmap_1(A,B),C),u1_struct_0(C),u1_struct_0(k6_tmap_1(A,B)))
                    & v5_pre_topc(k2_tmap_1(A,k6_tmap_1(A,B),k7_tmap_1(A,B),C),C,k6_tmap_1(A,B))
                    & m1_subset_1(k2_tmap_1(A,k6_tmap_1(A,B),k7_tmap_1(A,B),C),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(k6_tmap_1(A,B))))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_tmap_1)).

tff(f_131,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( ~ v2_struct_0(k6_tmap_1(A,B))
        & v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tmap_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_funct_1(k7_tmap_1(A,B))
        & v1_funct_2(k7_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B)))
        & m1_subset_1(k7_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_162,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_137,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_51,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k7_tmap_1(A,B) = k6_partfun1(u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_tmap_1)).

tff(f_70,axiom,(
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

tff(f_33,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_191,axiom,(
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
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ( v5_pre_topc(C,B,A)
              <=> ! [D] :
                    ( m1_subset_1(D,u1_struct_0(B))
                   => r1_tmap_1(B,A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tmap_1)).

tff(f_160,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( r1_xboole_0(u1_struct_0(C),B)
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(C))
                   => r1_tmap_1(C,k6_tmap_1(A,B),k2_tmap_1(A,k6_tmap_1(A,B),k7_tmap_1(A,B),C),D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_tmap_1)).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_68,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_66,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_34033,plain,(
    ! [A_738,B_739] :
      ( ~ v2_struct_0(k6_tmap_1(A_738,B_739))
      | ~ m1_subset_1(B_739,k1_zfmisc_1(u1_struct_0(A_738)))
      | ~ l1_pre_topc(A_738)
      | ~ v2_pre_topc(A_738)
      | v2_struct_0(A_738) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_34058,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_34033])).

tff(c_34086,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_34058])).

tff(c_34087,plain,(
    ~ v2_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_34086])).

tff(c_26,plain,(
    ! [A_18,B_19] :
      ( v1_funct_2(k7_tmap_1(A_18,B_19),u1_struct_0(A_18),u1_struct_0(k6_tmap_1(A_18,B_19)))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_60,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_174,plain,(
    ! [B_81,A_82] :
      ( l1_pre_topc(B_81)
      | ~ m1_pre_topc(B_81,A_82)
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_177,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_174])).

tff(c_180,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_177])).

tff(c_32,plain,(
    ! [A_23] :
      ( l1_struct_0(A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_33593,plain,(
    ! [A_712,B_713] :
      ( l1_pre_topc(k6_tmap_1(A_712,B_713))
      | ~ m1_subset_1(B_713,k1_zfmisc_1(u1_struct_0(A_712)))
      | ~ l1_pre_topc(A_712)
      | ~ v2_pre_topc(A_712)
      | v2_struct_0(A_712) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_33618,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_33593])).

tff(c_33646,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_33618])).

tff(c_33647,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_33646])).

tff(c_92,plain,(
    ! [B_78,A_79] : k3_xboole_0(B_78,A_79) = k3_xboole_0(A_79,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_48,plain,(
    ! [A_48] : k3_xboole_0(A_48,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_108,plain,(
    ! [A_79] : k3_xboole_0(k1_xboole_0,A_79) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_48])).

tff(c_21286,plain,(
    ! [A_472,B_473,C_474] :
      ( k9_subset_1(A_472,B_473,C_474) = k3_xboole_0(B_473,C_474)
      | ~ m1_subset_1(C_474,k1_zfmisc_1(A_472)) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_21293,plain,(
    ! [B_475] : k9_subset_1(u1_struct_0('#skF_2'),B_475,'#skF_3') = k3_xboole_0(B_475,'#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_21286])).

tff(c_30,plain,(
    ! [A_20,B_21,C_22] :
      ( m1_subset_1(k9_subset_1(A_20,B_21,C_22),k1_zfmisc_1(A_20))
      | ~ m1_subset_1(C_22,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_21299,plain,(
    ! [B_475] :
      ( m1_subset_1(k3_xboole_0(B_475,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21293,c_30])).

tff(c_21307,plain,(
    ! [B_476] : m1_subset_1(k3_xboole_0(B_476,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_21299])).

tff(c_21312,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_21307])).

tff(c_34161,plain,(
    ! [A_746,B_747] :
      ( v1_funct_1(k7_tmap_1(A_746,B_747))
      | ~ m1_subset_1(B_747,k1_zfmisc_1(u1_struct_0(A_746)))
      | ~ l1_pre_topc(A_746)
      | ~ v2_pre_topc(A_746)
      | v2_struct_0(A_746) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_34186,plain,
    ( v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_34161])).

tff(c_34214,plain,
    ( v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_34186])).

tff(c_34215,plain,(
    v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_34214])).

tff(c_34322,plain,(
    ! [A_756,B_757] :
      ( k7_tmap_1(A_756,B_757) = k6_partfun1(u1_struct_0(A_756))
      | ~ m1_subset_1(B_757,k1_zfmisc_1(u1_struct_0(A_756)))
      | ~ l1_pre_topc(A_756)
      | ~ v2_pre_topc(A_756)
      | v2_struct_0(A_756) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_34347,plain,
    ( k6_partfun1(u1_struct_0('#skF_2')) = k7_tmap_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_34322])).

tff(c_34375,plain,
    ( k6_partfun1(u1_struct_0('#skF_2')) = k7_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_34347])).

tff(c_34376,plain,(
    k6_partfun1(u1_struct_0('#skF_2')) = k7_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_34375])).

tff(c_34337,plain,
    ( k6_partfun1(u1_struct_0('#skF_2')) = k7_tmap_1('#skF_2',k1_xboole_0)
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_21312,c_34322])).

tff(c_34366,plain,
    ( k6_partfun1(u1_struct_0('#skF_2')) = k7_tmap_1('#skF_2',k1_xboole_0)
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_34337])).

tff(c_34367,plain,(
    k6_partfun1(u1_struct_0('#skF_2')) = k7_tmap_1('#skF_2',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_34366])).

tff(c_34381,plain,(
    k7_tmap_1('#skF_2',k1_xboole_0) = k7_tmap_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34376,c_34367])).

tff(c_34528,plain,(
    ! [A_764,B_765] :
      ( v1_funct_2(k7_tmap_1(A_764,B_765),u1_struct_0(A_764),u1_struct_0(k6_tmap_1(A_764,B_765)))
      | ~ m1_subset_1(B_765,k1_zfmisc_1(u1_struct_0(A_764)))
      | ~ l1_pre_topc(A_764)
      | ~ v2_pre_topc(A_764)
      | v2_struct_0(A_764) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_34537,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2',k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_34381,c_34528])).

tff(c_34545,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2',k1_xboole_0)))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_21312,c_34537])).

tff(c_34546,plain,(
    v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2',k1_xboole_0))) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_34545])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k7_tmap_1(A_18,B_19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_18),u1_struct_0(k6_tmap_1(A_18,B_19)))))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_34752,plain,(
    ! [A_780,B_781,C_782,D_783] :
      ( v1_funct_1(k2_tmap_1(A_780,B_781,C_782,D_783))
      | ~ l1_struct_0(D_783)
      | ~ m1_subset_1(C_782,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_780),u1_struct_0(B_781))))
      | ~ v1_funct_2(C_782,u1_struct_0(A_780),u1_struct_0(B_781))
      | ~ v1_funct_1(C_782)
      | ~ l1_struct_0(B_781)
      | ~ l1_struct_0(A_780) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_46939,plain,(
    ! [A_934,B_935,D_936] :
      ( v1_funct_1(k2_tmap_1(A_934,k6_tmap_1(A_934,B_935),k7_tmap_1(A_934,B_935),D_936))
      | ~ l1_struct_0(D_936)
      | ~ v1_funct_2(k7_tmap_1(A_934,B_935),u1_struct_0(A_934),u1_struct_0(k6_tmap_1(A_934,B_935)))
      | ~ v1_funct_1(k7_tmap_1(A_934,B_935))
      | ~ l1_struct_0(k6_tmap_1(A_934,B_935))
      | ~ l1_struct_0(A_934)
      | ~ m1_subset_1(B_935,k1_zfmisc_1(u1_struct_0(A_934)))
      | ~ l1_pre_topc(A_934)
      | ~ v2_pre_topc(A_934)
      | v2_struct_0(A_934) ) ),
    inference(resolution,[status(thm)],[c_24,c_34752])).

tff(c_46963,plain,(
    ! [D_936] :
      ( v1_funct_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2',k1_xboole_0),k7_tmap_1('#skF_2',k1_xboole_0),D_936))
      | ~ l1_struct_0(D_936)
      | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2',k1_xboole_0)))
      | ~ v1_funct_1(k7_tmap_1('#skF_2',k1_xboole_0))
      | ~ l1_struct_0(k6_tmap_1('#skF_2',k1_xboole_0))
      | ~ l1_struct_0('#skF_2')
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34381,c_46939])).

tff(c_46996,plain,(
    ! [D_936] :
      ( v1_funct_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2',k1_xboole_0),k7_tmap_1('#skF_2','#skF_3'),D_936))
      | ~ l1_struct_0(D_936)
      | ~ l1_struct_0(k6_tmap_1('#skF_2',k1_xboole_0))
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_21312,c_34215,c_34381,c_34546,c_34381,c_46963])).

tff(c_46997,plain,(
    ! [D_936] :
      ( v1_funct_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2',k1_xboole_0),k7_tmap_1('#skF_2','#skF_3'),D_936))
      | ~ l1_struct_0(D_936)
      | ~ l1_struct_0(k6_tmap_1('#skF_2',k1_xboole_0))
      | ~ l1_struct_0('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_46996])).

tff(c_46999,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_46997])).

tff(c_47002,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_46999])).

tff(c_47006,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_47002])).

tff(c_47008,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_46997])).

tff(c_35156,plain,(
    ! [A_794,B_795,C_796,D_797] :
      ( v1_funct_2(k2_tmap_1(A_794,B_795,C_796,D_797),u1_struct_0(D_797),u1_struct_0(B_795))
      | ~ l1_struct_0(D_797)
      | ~ m1_subset_1(C_796,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_794),u1_struct_0(B_795))))
      | ~ v1_funct_2(C_796,u1_struct_0(A_794),u1_struct_0(B_795))
      | ~ v1_funct_1(C_796)
      | ~ l1_struct_0(B_795)
      | ~ l1_struct_0(A_794) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_47496,plain,(
    ! [A_953,B_954,D_955] :
      ( v1_funct_2(k2_tmap_1(A_953,k6_tmap_1(A_953,B_954),k7_tmap_1(A_953,B_954),D_955),u1_struct_0(D_955),u1_struct_0(k6_tmap_1(A_953,B_954)))
      | ~ l1_struct_0(D_955)
      | ~ v1_funct_2(k7_tmap_1(A_953,B_954),u1_struct_0(A_953),u1_struct_0(k6_tmap_1(A_953,B_954)))
      | ~ v1_funct_1(k7_tmap_1(A_953,B_954))
      | ~ l1_struct_0(k6_tmap_1(A_953,B_954))
      | ~ l1_struct_0(A_953)
      | ~ m1_subset_1(B_954,k1_zfmisc_1(u1_struct_0(A_953)))
      | ~ l1_pre_topc(A_953)
      | ~ v2_pre_topc(A_953)
      | v2_struct_0(A_953) ) ),
    inference(resolution,[status(thm)],[c_24,c_35156])).

tff(c_21747,plain,(
    ! [A_504,B_505] :
      ( l1_pre_topc(k6_tmap_1(A_504,B_505))
      | ~ m1_subset_1(B_505,k1_zfmisc_1(u1_struct_0(A_504)))
      | ~ l1_pre_topc(A_504)
      | ~ v2_pre_topc(A_504)
      | v2_struct_0(A_504) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_21766,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_21747])).

tff(c_21786,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_21766])).

tff(c_21787,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_21786])).

tff(c_21897,plain,(
    ! [A_514,B_515] :
      ( v1_funct_1(k7_tmap_1(A_514,B_515))
      | ~ m1_subset_1(B_515,k1_zfmisc_1(u1_struct_0(A_514)))
      | ~ l1_pre_topc(A_514)
      | ~ v2_pre_topc(A_514)
      | v2_struct_0(A_514) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_21916,plain,
    ( v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_21897])).

tff(c_21936,plain,
    ( v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_21916])).

tff(c_21937,plain,(
    v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_21936])).

tff(c_23075,plain,(
    ! [A_578,B_579,C_580,D_581] :
      ( m1_subset_1(k2_tmap_1(A_578,B_579,C_580,D_581),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_581),u1_struct_0(B_579))))
      | ~ l1_struct_0(D_581)
      | ~ m1_subset_1(C_580,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_578),u1_struct_0(B_579))))
      | ~ v1_funct_2(C_580,u1_struct_0(A_578),u1_struct_0(B_579))
      | ~ v1_funct_1(C_580)
      | ~ l1_struct_0(B_579)
      | ~ l1_struct_0(A_578) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_418,plain,(
    ! [A_104,B_105] :
      ( l1_pre_topc(k6_tmap_1(A_104,B_105))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104)
      | ~ v2_pre_topc(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_437,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_418])).

tff(c_457,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_437])).

tff(c_458,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_457])).

tff(c_190,plain,(
    ! [A_85,B_86,C_87] :
      ( k9_subset_1(A_85,B_86,C_87) = k3_xboole_0(B_86,C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_193,plain,(
    ! [B_86] : k9_subset_1(u1_struct_0('#skF_2'),B_86,'#skF_3') = k3_xboole_0(B_86,'#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_190])).

tff(c_203,plain,(
    ! [A_89,B_90,C_91] :
      ( m1_subset_1(k9_subset_1(A_89,B_90,C_91),k1_zfmisc_1(A_89))
      | ~ m1_subset_1(C_91,k1_zfmisc_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_208,plain,(
    ! [B_86] :
      ( m1_subset_1(k3_xboole_0(B_86,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_203])).

tff(c_220,plain,(
    ! [B_95] : m1_subset_1(k3_xboole_0(B_95,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_208])).

tff(c_227,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_220])).

tff(c_930,plain,(
    ! [A_138,B_139] :
      ( v1_funct_1(k7_tmap_1(A_138,B_139))
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_949,plain,
    ( v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_930])).

tff(c_969,plain,
    ( v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_949])).

tff(c_970,plain,(
    v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_969])).

tff(c_1053,plain,(
    ! [A_146,B_147] :
      ( k7_tmap_1(A_146,B_147) = k6_partfun1(u1_struct_0(A_146))
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_pre_topc(A_146)
      | ~ v2_pre_topc(A_146)
      | v2_struct_0(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1072,plain,
    ( k6_partfun1(u1_struct_0('#skF_2')) = k7_tmap_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_1053])).

tff(c_1092,plain,
    ( k6_partfun1(u1_struct_0('#skF_2')) = k7_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1072])).

tff(c_1093,plain,(
    k6_partfun1(u1_struct_0('#skF_2')) = k7_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1092])).

tff(c_1062,plain,
    ( k6_partfun1(u1_struct_0('#skF_2')) = k7_tmap_1('#skF_2',k1_xboole_0)
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_227,c_1053])).

tff(c_1083,plain,
    ( k6_partfun1(u1_struct_0('#skF_2')) = k7_tmap_1('#skF_2',k1_xboole_0)
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1062])).

tff(c_1084,plain,(
    k6_partfun1(u1_struct_0('#skF_2')) = k7_tmap_1('#skF_2',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1083])).

tff(c_1098,plain,(
    k7_tmap_1('#skF_2',k1_xboole_0) = k7_tmap_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1093,c_1084])).

tff(c_1221,plain,(
    ! [A_154,B_155] :
      ( v1_funct_2(k7_tmap_1(A_154,B_155),u1_struct_0(A_154),u1_struct_0(k6_tmap_1(A_154,B_155)))
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_pre_topc(A_154)
      | ~ v2_pre_topc(A_154)
      | v2_struct_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1230,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2',k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1098,c_1221])).

tff(c_1238,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2',k1_xboole_0)))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_227,c_1230])).

tff(c_1239,plain,(
    v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2',k1_xboole_0))) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1238])).

tff(c_1543,plain,(
    ! [A_174,B_175,C_176,D_177] :
      ( v1_funct_1(k2_tmap_1(A_174,B_175,C_176,D_177))
      | ~ l1_struct_0(D_177)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_174),u1_struct_0(B_175))))
      | ~ v1_funct_2(C_176,u1_struct_0(A_174),u1_struct_0(B_175))
      | ~ v1_funct_1(C_176)
      | ~ l1_struct_0(B_175)
      | ~ l1_struct_0(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12556,plain,(
    ! [A_323,B_324,D_325] :
      ( v1_funct_1(k2_tmap_1(A_323,k6_tmap_1(A_323,B_324),k7_tmap_1(A_323,B_324),D_325))
      | ~ l1_struct_0(D_325)
      | ~ v1_funct_2(k7_tmap_1(A_323,B_324),u1_struct_0(A_323),u1_struct_0(k6_tmap_1(A_323,B_324)))
      | ~ v1_funct_1(k7_tmap_1(A_323,B_324))
      | ~ l1_struct_0(k6_tmap_1(A_323,B_324))
      | ~ l1_struct_0(A_323)
      | ~ m1_subset_1(B_324,k1_zfmisc_1(u1_struct_0(A_323)))
      | ~ l1_pre_topc(A_323)
      | ~ v2_pre_topc(A_323)
      | v2_struct_0(A_323) ) ),
    inference(resolution,[status(thm)],[c_24,c_1543])).

tff(c_12580,plain,(
    ! [D_325] :
      ( v1_funct_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2',k1_xboole_0),k7_tmap_1('#skF_2',k1_xboole_0),D_325))
      | ~ l1_struct_0(D_325)
      | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2',k1_xboole_0)))
      | ~ v1_funct_1(k7_tmap_1('#skF_2',k1_xboole_0))
      | ~ l1_struct_0(k6_tmap_1('#skF_2',k1_xboole_0))
      | ~ l1_struct_0('#skF_2')
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1098,c_12556])).

tff(c_12613,plain,(
    ! [D_325] :
      ( v1_funct_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2',k1_xboole_0),k7_tmap_1('#skF_2','#skF_3'),D_325))
      | ~ l1_struct_0(D_325)
      | ~ l1_struct_0(k6_tmap_1('#skF_2',k1_xboole_0))
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_227,c_970,c_1098,c_1239,c_1098,c_12580])).

tff(c_12614,plain,(
    ! [D_325] :
      ( v1_funct_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2',k1_xboole_0),k7_tmap_1('#skF_2','#skF_3'),D_325))
      | ~ l1_struct_0(D_325)
      | ~ l1_struct_0(k6_tmap_1('#skF_2',k1_xboole_0))
      | ~ l1_struct_0('#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_12613])).

tff(c_12615,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_12614])).

tff(c_12618,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_12615])).

tff(c_12622,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_12618])).

tff(c_12624,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_12614])).

tff(c_21189,plain,(
    ! [A_466,B_467,D_468] :
      ( v1_funct_1(k2_tmap_1(A_466,k6_tmap_1(A_466,B_467),k7_tmap_1(A_466,B_467),D_468))
      | ~ l1_struct_0(D_468)
      | ~ v1_funct_1(k7_tmap_1(A_466,B_467))
      | ~ l1_struct_0(k6_tmap_1(A_466,B_467))
      | ~ l1_struct_0(A_466)
      | ~ m1_subset_1(B_467,k1_zfmisc_1(u1_struct_0(A_466)))
      | ~ l1_pre_topc(A_466)
      | ~ v2_pre_topc(A_466)
      | v2_struct_0(A_466) ) ),
    inference(resolution,[status(thm)],[c_26,c_12556])).

tff(c_56,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k6_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_189,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_21192,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_21189,c_189])).

tff(c_21231,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_12624,c_970,c_21192])).

tff(c_21232,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_21231])).

tff(c_21266,plain,(
    ~ l1_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_21232])).

tff(c_21269,plain,(
    ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_21266])).

tff(c_21273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_21269])).

tff(c_21274,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_21232])).

tff(c_21278,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_21274])).

tff(c_21282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_21278])).

tff(c_21283,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | ~ v5_pre_topc(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_21373,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitLeft,[status(thm)],[c_21283])).

tff(c_23082,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))))
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_23075,c_21373])).

tff(c_23091,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))))
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | ~ l1_struct_0(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21937,c_23082])).

tff(c_33079,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_23091])).

tff(c_33082,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_33079])).

tff(c_33086,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_33082])).

tff(c_33087,plain,
    ( ~ l1_struct_0(k6_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | ~ m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))))
    | ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_23091])).

tff(c_33142,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_33087])).

tff(c_33145,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_33142])).

tff(c_33149,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_33145])).

tff(c_33150,plain,
    ( ~ m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))))
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | ~ l1_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_33087])).

tff(c_33211,plain,(
    ~ l1_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_33150])).

tff(c_33214,plain,(
    ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_33211])).

tff(c_33218,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21787,c_33214])).

tff(c_33219,plain,
    ( ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | ~ m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitRight,[status(thm)],[c_33150])).

tff(c_33366,plain,(
    ~ m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitLeft,[status(thm)],[c_33219])).

tff(c_33369,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_33366])).

tff(c_33372,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_33369])).

tff(c_33374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_33372])).

tff(c_33375,plain,(
    ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_33219])).

tff(c_33379,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_33375])).

tff(c_33382,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_33379])).

tff(c_33384,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_33382])).

tff(c_33385,plain,
    ( ~ v5_pre_topc(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k6_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_21283])).

tff(c_34836,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_33385])).

tff(c_47499,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_47496,c_34836])).

tff(c_47535,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | ~ l1_struct_0(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_47008,c_34215,c_47499])).

tff(c_47536,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | ~ l1_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_47535])).

tff(c_47570,plain,(
    ~ l1_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_47536])).

tff(c_47573,plain,(
    ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_47570])).

tff(c_47577,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33647,c_47573])).

tff(c_47578,plain,
    ( ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_47536])).

tff(c_47580,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_47578])).

tff(c_47583,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_47580])).

tff(c_47587,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_47583])).

tff(c_47588,plain,(
    ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_47578])).

tff(c_47596,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_47588])).

tff(c_47599,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_47596])).

tff(c_47601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_47599])).

tff(c_47602,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k6_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_33385])).

tff(c_58,plain,(
    r1_xboole_0(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_33757,plain,(
    ! [A_722,B_723] :
      ( v2_pre_topc(k6_tmap_1(A_722,B_723))
      | ~ m1_subset_1(B_723,k1_zfmisc_1(u1_struct_0(A_722)))
      | ~ l1_pre_topc(A_722)
      | ~ v2_pre_topc(A_722)
      | v2_struct_0(A_722) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_33782,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_33757])).

tff(c_33810,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_33782])).

tff(c_33811,plain,(
    v2_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_33810])).

tff(c_182,plain,(
    ! [B_83,A_84] :
      ( v2_pre_topc(B_83)
      | ~ m1_pre_topc(B_83,A_84)
      | ~ l1_pre_topc(A_84)
      | ~ v2_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_185,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_182])).

tff(c_188,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_185])).

tff(c_21284,plain,(
    v1_funct_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_47603,plain,(
    v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_33385])).

tff(c_33386,plain,(
    m1_subset_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitRight,[status(thm)],[c_21283])).

tff(c_50601,plain,(
    ! [A_1000,B_1001,C_1002] :
      ( m1_subset_1('#skF_1'(A_1000,B_1001,C_1002),u1_struct_0(B_1001))
      | v5_pre_topc(C_1002,B_1001,A_1000)
      | ~ m1_subset_1(C_1002,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_1001),u1_struct_0(A_1000))))
      | ~ v1_funct_2(C_1002,u1_struct_0(B_1001),u1_struct_0(A_1000))
      | ~ v1_funct_1(C_1002)
      | ~ l1_pre_topc(B_1001)
      | ~ v2_pre_topc(B_1001)
      | v2_struct_0(B_1001)
      | ~ l1_pre_topc(A_1000)
      | ~ v2_pre_topc(A_1000)
      | v2_struct_0(A_1000) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_50611,plain,
    ( m1_subset_1('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),'#skF_4',k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4')),u1_struct_0('#skF_4'))
    | v5_pre_topc(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k6_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_33386,c_50601])).

tff(c_50627,plain,
    ( m1_subset_1('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),'#skF_4',k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4')),u1_struct_0('#skF_4'))
    | v5_pre_topc(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_4')
    | v2_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33811,c_33647,c_188,c_180,c_21284,c_47603,c_50611])).

tff(c_50628,plain,(
    m1_subset_1('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),'#skF_4',k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4')),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_34087,c_62,c_47602,c_50627])).

tff(c_46,plain,(
    ! [C_45,A_33,B_41,D_47] :
      ( r1_tmap_1(C_45,k6_tmap_1(A_33,B_41),k2_tmap_1(A_33,k6_tmap_1(A_33,B_41),k7_tmap_1(A_33,B_41),C_45),D_47)
      | ~ m1_subset_1(D_47,u1_struct_0(C_45))
      | ~ r1_xboole_0(u1_struct_0(C_45),B_41)
      | ~ m1_pre_topc(C_45,A_33)
      | v2_struct_0(C_45)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_50880,plain,(
    ! [B_1008,A_1009,C_1010] :
      ( ~ r1_tmap_1(B_1008,A_1009,C_1010,'#skF_1'(A_1009,B_1008,C_1010))
      | v5_pre_topc(C_1010,B_1008,A_1009)
      | ~ m1_subset_1(C_1010,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_1008),u1_struct_0(A_1009))))
      | ~ v1_funct_2(C_1010,u1_struct_0(B_1008),u1_struct_0(A_1009))
      | ~ v1_funct_1(C_1010)
      | ~ l1_pre_topc(B_1008)
      | ~ v2_pre_topc(B_1008)
      | v2_struct_0(B_1008)
      | ~ l1_pre_topc(A_1009)
      | ~ v2_pre_topc(A_1009)
      | v2_struct_0(A_1009) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_69690,plain,(
    ! [A_1277,B_1278,C_1279] :
      ( v5_pre_topc(k2_tmap_1(A_1277,k6_tmap_1(A_1277,B_1278),k7_tmap_1(A_1277,B_1278),C_1279),C_1279,k6_tmap_1(A_1277,B_1278))
      | ~ m1_subset_1(k2_tmap_1(A_1277,k6_tmap_1(A_1277,B_1278),k7_tmap_1(A_1277,B_1278),C_1279),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1279),u1_struct_0(k6_tmap_1(A_1277,B_1278)))))
      | ~ v1_funct_2(k2_tmap_1(A_1277,k6_tmap_1(A_1277,B_1278),k7_tmap_1(A_1277,B_1278),C_1279),u1_struct_0(C_1279),u1_struct_0(k6_tmap_1(A_1277,B_1278)))
      | ~ v1_funct_1(k2_tmap_1(A_1277,k6_tmap_1(A_1277,B_1278),k7_tmap_1(A_1277,B_1278),C_1279))
      | ~ l1_pre_topc(C_1279)
      | ~ v2_pre_topc(C_1279)
      | ~ l1_pre_topc(k6_tmap_1(A_1277,B_1278))
      | ~ v2_pre_topc(k6_tmap_1(A_1277,B_1278))
      | v2_struct_0(k6_tmap_1(A_1277,B_1278))
      | ~ m1_subset_1('#skF_1'(k6_tmap_1(A_1277,B_1278),C_1279,k2_tmap_1(A_1277,k6_tmap_1(A_1277,B_1278),k7_tmap_1(A_1277,B_1278),C_1279)),u1_struct_0(C_1279))
      | ~ r1_xboole_0(u1_struct_0(C_1279),B_1278)
      | ~ m1_pre_topc(C_1279,A_1277)
      | v2_struct_0(C_1279)
      | ~ m1_subset_1(B_1278,k1_zfmisc_1(u1_struct_0(A_1277)))
      | ~ l1_pre_topc(A_1277)
      | ~ v2_pre_topc(A_1277)
      | v2_struct_0(A_1277) ) ),
    inference(resolution,[status(thm)],[c_46,c_50880])).

tff(c_69709,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k6_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),'#skF_4',k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4')),u1_struct_0('#skF_4'))
    | ~ r1_xboole_0(u1_struct_0('#skF_4'),'#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_33386,c_69690])).

tff(c_69740,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_60,c_58,c_50628,c_33811,c_33647,c_188,c_180,c_21284,c_47603,c_69709])).

tff(c_69742,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_62,c_34087,c_47602,c_69740])).

%------------------------------------------------------------------------------
