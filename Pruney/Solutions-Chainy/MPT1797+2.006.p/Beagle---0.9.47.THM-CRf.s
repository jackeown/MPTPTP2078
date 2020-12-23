%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:56 EST 2020

% Result     : Theorem 14.90s
% Output     : CNFRefutation 15.43s
% Verified   : 
% Statistics : Number of formulae       :  366 (27167 expanded)
%              Number of leaves         :   42 (9468 expanded)
%              Depth                    :   29
%              Number of atoms          : 1226 (92258 expanded)
%              Number of equality atoms :  133 (13217 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v3_pre_topc > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k7_tmap_1 > k6_tmap_1 > k5_tmap_1 > k2_zfmisc_1 > k10_relat_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k6_partfun1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_221,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_tmap_1)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_169,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_140,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_186,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_tmap_1)).

tff(f_29,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_125,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k7_tmap_1(A,B) = k6_partfun1(u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_tmap_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_113,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_2)).

tff(f_155,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_funct_1(k7_tmap_1(A,B))
        & v1_funct_2(k7_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B)))
        & m1_subset_1(k7_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

tff(f_200,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))),u1_struct_0(B))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))),u1_struct_0(B)))) )
                 => ( C = D
                   => ( v5_pre_topc(C,A,B)
                    <=> v5_pre_topc(D,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_60,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_8,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_86,plain,(
    ! [A_75] :
      ( u1_struct_0(A_75) = k2_struct_0(A_75)
      | ~ l1_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_91,plain,(
    ! [A_76] :
      ( u1_struct_0(A_76) = k2_struct_0(A_76)
      | ~ l1_pre_topc(A_76) ) ),
    inference(resolution,[status(thm)],[c_8,c_86])).

tff(c_95,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_91])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_96,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_58])).

tff(c_62,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_5183,plain,(
    ! [A_513,B_514] :
      ( u1_struct_0(k6_tmap_1(A_513,B_514)) = u1_struct_0(A_513)
      | ~ m1_subset_1(B_514,k1_zfmisc_1(u1_struct_0(A_513)))
      | ~ l1_pre_topc(A_513)
      | ~ v2_pre_topc(A_513)
      | v2_struct_0(A_513) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_5189,plain,(
    ! [B_514] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_514)) = u1_struct_0('#skF_2')
      | ~ m1_subset_1(B_514,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_5183])).

tff(c_5193,plain,(
    ! [B_514] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_514)) = k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_514,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_95,c_5189])).

tff(c_5195,plain,(
    ! [B_515] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_515)) = k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_515,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_5193])).

tff(c_5199,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_96,c_5195])).

tff(c_5139,plain,(
    ! [A_510,B_511] :
      ( l1_pre_topc(k6_tmap_1(A_510,B_511))
      | ~ m1_subset_1(B_511,k1_zfmisc_1(u1_struct_0(A_510)))
      | ~ l1_pre_topc(A_510)
      | ~ v2_pre_topc(A_510)
      | v2_struct_0(A_510) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_5142,plain,(
    ! [B_511] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_511))
      | ~ m1_subset_1(B_511,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_5139])).

tff(c_5144,plain,(
    ! [B_511] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_511))
      | ~ m1_subset_1(B_511,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_5142])).

tff(c_5146,plain,(
    ! [B_512] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_512))
      | ~ m1_subset_1(B_512,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_5144])).

tff(c_5150,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_96,c_5146])).

tff(c_90,plain,(
    ! [A_8] :
      ( u1_struct_0(A_8) = k2_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(resolution,[status(thm)],[c_8,c_86])).

tff(c_5154,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_5150,c_90])).

tff(c_5200,plain,(
    k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5199,c_5154])).

tff(c_4867,plain,(
    ! [A_472,B_473] :
      ( u1_struct_0(k6_tmap_1(A_472,B_473)) = u1_struct_0(A_472)
      | ~ m1_subset_1(B_473,k1_zfmisc_1(u1_struct_0(A_472)))
      | ~ l1_pre_topc(A_472)
      | ~ v2_pre_topc(A_472)
      | v2_struct_0(A_472) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_4873,plain,(
    ! [B_473] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_473)) = u1_struct_0('#skF_2')
      | ~ m1_subset_1(B_473,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_4867])).

tff(c_4877,plain,(
    ! [B_473] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_473)) = k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_473,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_95,c_4873])).

tff(c_4884,plain,(
    ! [B_475] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_475)) = k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_475,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_4877])).

tff(c_4888,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_96,c_4884])).

tff(c_4816,plain,(
    ! [A_467,B_468] :
      ( l1_pre_topc(k6_tmap_1(A_467,B_468))
      | ~ m1_subset_1(B_468,k1_zfmisc_1(u1_struct_0(A_467)))
      | ~ l1_pre_topc(A_467)
      | ~ v2_pre_topc(A_467)
      | v2_struct_0(A_467) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_4819,plain,(
    ! [B_468] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_468))
      | ~ m1_subset_1(B_468,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_4816])).

tff(c_4821,plain,(
    ! [B_468] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_468))
      | ~ m1_subset_1(B_468,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_4819])).

tff(c_4823,plain,(
    ! [B_469] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_469))
      | ~ m1_subset_1(B_469,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_4821])).

tff(c_4827,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_96,c_4823])).

tff(c_4833,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4827,c_90])).

tff(c_4889,plain,(
    k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4888,c_4833])).

tff(c_84,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_101,plain,(
    v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_80,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_111,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_80])).

tff(c_112,plain,(
    v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_76,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2',k6_tmap_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_110,plain,(
    v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2',k6_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_72,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))))) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_121,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_72])).

tff(c_122,plain,(
    m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_66,plain,
    ( ~ m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))))
    | ~ v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_167,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_112,c_95,c_110,c_122,c_95,c_66])).

tff(c_253,plain,(
    ! [A_100,B_101] :
      ( u1_struct_0(k6_tmap_1(A_100,B_101)) = u1_struct_0(A_100)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_259,plain,(
    ! [B_101] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_101)) = u1_struct_0('#skF_2')
      | ~ m1_subset_1(B_101,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_253])).

tff(c_263,plain,(
    ! [B_101] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_101)) = k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_101,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_95,c_259])).

tff(c_265,plain,(
    ! [B_102] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_102)) = k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_102,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_263])).

tff(c_269,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_96,c_265])).

tff(c_489,plain,(
    ! [C_121,A_122] :
      ( v3_pre_topc(C_121,k6_tmap_1(A_122,C_121))
      | ~ m1_subset_1(C_121,k1_zfmisc_1(u1_struct_0(k6_tmap_1(A_122,C_121))))
      | ~ m1_subset_1(C_121,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_492,plain,
    ( v3_pre_topc('#skF_3',k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_489])).

tff(c_494,plain,
    ( v3_pre_topc('#skF_3',k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_96,c_95,c_96,c_492])).

tff(c_495,plain,(
    v3_pre_topc('#skF_3',k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_494])).

tff(c_159,plain,(
    ! [A_92,B_93] :
      ( l1_pre_topc(k6_tmap_1(A_92,B_93))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92)
      | ~ v2_pre_topc(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_162,plain,(
    ! [B_93] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_93))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_159])).

tff(c_164,plain,(
    ! [B_93] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_93))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_162])).

tff(c_168,plain,(
    ! [B_94] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_94))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_164])).

tff(c_172,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_96,c_168])).

tff(c_176,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_172,c_90])).

tff(c_270,plain,(
    k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_176])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( k8_relset_1(A_1,B_2,C_3,D_4) = k10_relat_1(C_3,D_4)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_132,plain,(
    ! [D_4] : k8_relset_1(k2_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')),k7_tmap_1('#skF_2','#skF_3'),D_4) = k10_relat_1(k7_tmap_1('#skF_2','#skF_3'),D_4) ),
    inference(resolution,[status(thm)],[c_122,c_2])).

tff(c_242,plain,(
    ! [D_4] : k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0(k6_tmap_1('#skF_2','#skF_3')),k7_tmap_1('#skF_2','#skF_3'),D_4) = k10_relat_1(k7_tmap_1('#skF_2','#skF_3'),D_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_132])).

tff(c_339,plain,(
    ! [D_106] : k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k7_tmap_1('#skF_2','#skF_3'),D_106) = k10_relat_1(k7_tmap_1('#skF_2','#skF_3'),D_106) ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_242])).

tff(c_209,plain,(
    ! [A_95,B_96] :
      ( k7_tmap_1(A_95,B_96) = k6_partfun1(u1_struct_0(A_95))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_215,plain,(
    ! [B_96] :
      ( k7_tmap_1('#skF_2',B_96) = k6_partfun1(u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_209])).

tff(c_219,plain,(
    ! [B_96] :
      ( k7_tmap_1('#skF_2',B_96) = k6_partfun1(k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_95,c_215])).

tff(c_221,plain,(
    ! [B_97] :
      ( k7_tmap_1('#skF_2',B_97) = k6_partfun1(k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_219])).

tff(c_225,plain,(
    k6_partfun1(k2_struct_0('#skF_2')) = k7_tmap_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_221])).

tff(c_102,plain,(
    ! [A_77,B_78] :
      ( k8_relset_1(A_77,A_77,k6_partfun1(A_77),B_78) = B_78
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_105,plain,(
    k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k6_partfun1(k2_struct_0('#skF_2')),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_96,c_102])).

tff(c_227,plain,(
    k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k7_tmap_1('#skF_2','#skF_3'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_105])).

tff(c_345,plain,(
    k10_relat_1(k7_tmap_1('#skF_2','#skF_3'),'#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_227])).

tff(c_178,plain,(
    v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_112])).

tff(c_319,plain,(
    v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_178])).

tff(c_317,plain,(
    ! [D_4] : k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k7_tmap_1('#skF_2','#skF_3'),D_4) = k10_relat_1(k7_tmap_1('#skF_2','#skF_3'),D_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_242])).

tff(c_177,plain,(
    m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0(k6_tmap_1('#skF_2','#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_122])).

tff(c_318,plain,(
    m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_177])).

tff(c_524,plain,(
    ! [A_126,B_127,C_128] :
      ( k2_struct_0(A_126) != k1_xboole_0
      | v3_pre_topc('#skF_1'(A_126,B_127,C_128),B_127)
      | v5_pre_topc(C_128,A_126,B_127)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_126),u1_struct_0(B_127))))
      | ~ v1_funct_2(C_128,u1_struct_0(A_126),u1_struct_0(B_127))
      | ~ v1_funct_1(C_128)
      | ~ l1_pre_topc(B_127)
      | ~ l1_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_532,plain,(
    ! [B_127,C_128] :
      ( k2_struct_0('#skF_2') != k1_xboole_0
      | v3_pre_topc('#skF_1'('#skF_2',B_127,C_128),B_127)
      | v5_pre_topc(C_128,'#skF_2',B_127)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(B_127))))
      | ~ v1_funct_2(C_128,u1_struct_0('#skF_2'),u1_struct_0(B_127))
      | ~ v1_funct_1(C_128)
      | ~ l1_pre_topc(B_127)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_524])).

tff(c_541,plain,(
    ! [B_127,C_128] :
      ( k2_struct_0('#skF_2') != k1_xboole_0
      | v3_pre_topc('#skF_1'('#skF_2',B_127,C_128),B_127)
      | v5_pre_topc(C_128,'#skF_2',B_127)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(B_127))))
      | ~ v1_funct_2(C_128,k2_struct_0('#skF_2'),u1_struct_0(B_127))
      | ~ v1_funct_1(C_128)
      | ~ l1_pre_topc(B_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_95,c_532])).

tff(c_545,plain,(
    k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_541])).

tff(c_1233,plain,(
    ! [B_214,A_215,C_216,D_217] :
      ( k2_struct_0(B_214) = k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0(A_215),u1_struct_0(B_214),C_216,D_217),A_215)
      | ~ v3_pre_topc(D_217,B_214)
      | ~ m1_subset_1(D_217,k1_zfmisc_1(u1_struct_0(B_214)))
      | ~ v5_pre_topc(C_216,A_215,B_214)
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_215),u1_struct_0(B_214))))
      | ~ v1_funct_2(C_216,u1_struct_0(A_215),u1_struct_0(B_214))
      | ~ v1_funct_1(C_216)
      | ~ l1_pre_topc(B_214)
      | ~ l1_pre_topc(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1241,plain,(
    ! [B_214,C_216,D_217] :
      ( k2_struct_0(B_214) = k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_214),C_216,D_217),'#skF_2')
      | ~ v3_pre_topc(D_217,B_214)
      | ~ m1_subset_1(D_217,k1_zfmisc_1(u1_struct_0(B_214)))
      | ~ v5_pre_topc(C_216,'#skF_2',B_214)
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(B_214))))
      | ~ v1_funct_2(C_216,u1_struct_0('#skF_2'),u1_struct_0(B_214))
      | ~ v1_funct_1(C_216)
      | ~ l1_pre_topc(B_214)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_1233])).

tff(c_1751,plain,(
    ! [B_271,C_272,D_273] :
      ( k2_struct_0(B_271) = k1_xboole_0
      | v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'),u1_struct_0(B_271),C_272,D_273),'#skF_2')
      | ~ v3_pre_topc(D_273,B_271)
      | ~ m1_subset_1(D_273,k1_zfmisc_1(u1_struct_0(B_271)))
      | ~ v5_pre_topc(C_272,'#skF_2',B_271)
      | ~ m1_subset_1(C_272,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(B_271))))
      | ~ v1_funct_2(C_272,k2_struct_0('#skF_2'),u1_struct_0(B_271))
      | ~ v1_funct_1(C_272)
      | ~ l1_pre_topc(B_271) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_95,c_95,c_1241])).

tff(c_1755,plain,(
    ! [C_272,D_273] :
      ( k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k1_xboole_0
      | v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')),C_272,D_273),'#skF_2')
      | ~ v3_pre_topc(D_273,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_273,k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))))
      | ~ v5_pre_topc(C_272,'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_272,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_272,k2_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_272)
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_1751])).

tff(c_1760,plain,(
    ! [C_272,D_273] :
      ( k2_struct_0('#skF_2') = k1_xboole_0
      | v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),C_272,D_273),'#skF_2')
      | ~ v3_pre_topc(D_273,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_273,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v5_pre_topc(C_272,'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_272,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_272,k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_272) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_269,c_269,c_269,c_270,c_1755])).

tff(c_1772,plain,(
    ! [C_275,D_276] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),C_275,D_276),'#skF_2')
      | ~ v3_pre_topc(D_276,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_276,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v5_pre_topc(C_275,'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_275,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_275,k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_275) ) ),
    inference(negUnitSimplification,[status(thm)],[c_545,c_1760])).

tff(c_1774,plain,(
    ! [D_276] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k7_tmap_1('#skF_2','#skF_3'),D_276),'#skF_2')
      | ~ v3_pre_topc(D_276,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_276,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
      | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_318,c_1772])).

tff(c_1778,plain,(
    ! [D_277] :
      ( v3_pre_topc(k10_relat_1(k7_tmap_1('#skF_2','#skF_3'),D_277),'#skF_2')
      | ~ v3_pre_topc(D_277,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_277,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_319,c_110,c_317,c_1774])).

tff(c_1784,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3',k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_1778])).

tff(c_1786,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_495,c_1784])).

tff(c_1788,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_1786])).

tff(c_1790,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_541])).

tff(c_1812,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1790,c_96])).

tff(c_1807,plain,(
    k7_tmap_1('#skF_2','#skF_3') = k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1790,c_225])).

tff(c_2013,plain,(
    k10_relat_1(k6_partfun1(k1_xboole_0),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1807,c_345])).

tff(c_2015,plain,(
    v1_funct_1(k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1807,c_101])).

tff(c_1813,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1790,c_95])).

tff(c_1803,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1790,c_269])).

tff(c_44,plain,(
    ! [A_58,B_59] :
      ( v1_funct_2(k7_tmap_1(A_58,B_59),u1_struct_0(A_58),u1_struct_0(k6_tmap_1(A_58,B_59)))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_2025,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1807,c_44])).

tff(c_2035,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1812,c_1813,c_1803,c_1813,c_2025])).

tff(c_2036,plain,(
    v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2035])).

tff(c_2014,plain,(
    v5_pre_topc(k6_partfun1(k1_xboole_0),'#skF_2',k6_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1807,c_110])).

tff(c_439,plain,(
    ! [A_116,B_117] :
      ( m1_subset_1(k7_tmap_1(A_116,B_117),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_116),u1_struct_0(k6_tmap_1(A_116,B_117)))))
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116)
      | v2_struct_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_453,plain,(
    ! [A_116,B_117,D_4] :
      ( k8_relset_1(u1_struct_0(A_116),u1_struct_0(k6_tmap_1(A_116,B_117)),k7_tmap_1(A_116,B_117),D_4) = k10_relat_1(k7_tmap_1(A_116,B_117),D_4)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116)
      | v2_struct_0(A_116) ) ),
    inference(resolution,[status(thm)],[c_439,c_2])).

tff(c_2019,plain,(
    ! [D_4] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')),k6_partfun1(k1_xboole_0),D_4) = k10_relat_1(k7_tmap_1('#skF_2','#skF_3'),D_4)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1807,c_453])).

tff(c_2029,plain,(
    ! [D_4] :
      ( k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),D_4) = k10_relat_1(k6_partfun1(k1_xboole_0),D_4)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1812,c_1813,c_1807,c_1803,c_1813,c_2019])).

tff(c_2030,plain,(
    ! [D_4] : k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),D_4) = k10_relat_1(k6_partfun1(k1_xboole_0),D_4) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2029])).

tff(c_42,plain,(
    ! [A_58,B_59] :
      ( m1_subset_1(k7_tmap_1(A_58,B_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_58),u1_struct_0(k6_tmap_1(A_58,B_59)))))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_2022,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1807,c_42])).

tff(c_2032,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1812,c_1813,c_1803,c_1813,c_2022])).

tff(c_2033,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2032])).

tff(c_2497,plain,(
    ! [A_324,B_325,C_326,D_327] :
      ( k2_struct_0(A_324) != k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0(A_324),u1_struct_0(B_325),C_326,D_327),A_324)
      | ~ v3_pre_topc(D_327,B_325)
      | ~ m1_subset_1(D_327,k1_zfmisc_1(u1_struct_0(B_325)))
      | ~ v5_pre_topc(C_326,A_324,B_325)
      | ~ m1_subset_1(C_326,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_324),u1_struct_0(B_325))))
      | ~ v1_funct_2(C_326,u1_struct_0(A_324),u1_struct_0(B_325))
      | ~ v1_funct_1(C_326)
      | ~ l1_pre_topc(B_325)
      | ~ l1_pre_topc(A_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2503,plain,(
    ! [B_325,C_326,D_327] :
      ( k2_struct_0('#skF_2') != k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_325),C_326,D_327),'#skF_2')
      | ~ v3_pre_topc(D_327,B_325)
      | ~ m1_subset_1(D_327,k1_zfmisc_1(u1_struct_0(B_325)))
      | ~ v5_pre_topc(C_326,'#skF_2',B_325)
      | ~ m1_subset_1(C_326,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(B_325))))
      | ~ v1_funct_2(C_326,u1_struct_0('#skF_2'),u1_struct_0(B_325))
      | ~ v1_funct_1(C_326)
      | ~ l1_pre_topc(B_325)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1813,c_2497])).

tff(c_4645,plain,(
    ! [B_451,C_452,D_453] :
      ( v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(B_451),C_452,D_453),'#skF_2')
      | ~ v3_pre_topc(D_453,B_451)
      | ~ m1_subset_1(D_453,k1_zfmisc_1(u1_struct_0(B_451)))
      | ~ v5_pre_topc(C_452,'#skF_2',B_451)
      | ~ m1_subset_1(C_452,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(B_451))))
      | ~ v1_funct_2(C_452,k1_xboole_0,u1_struct_0(B_451))
      | ~ v1_funct_1(C_452)
      | ~ l1_pre_topc(B_451) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1813,c_1813,c_1790,c_2503])).

tff(c_4655,plain,(
    ! [C_452,D_453] :
      ( v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1('#skF_2','#skF_3')),C_452,D_453),'#skF_2')
      | ~ v3_pre_topc(D_453,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_453,k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))))
      | ~ v5_pre_topc(C_452,'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_452,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ v1_funct_2(C_452,k1_xboole_0,u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_452)
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1803,c_4645])).

tff(c_4762,plain,(
    ! [C_459,D_460] :
      ( v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,C_459,D_460),'#skF_2')
      | ~ v3_pre_topc(D_460,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_460,k1_zfmisc_1(k1_xboole_0))
      | ~ v5_pre_topc(C_459,'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_459,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ v1_funct_2(C_459,k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_1(C_459) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_1803,c_1803,c_1803,c_4655])).

tff(c_4768,plain,(
    ! [D_460] :
      ( v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),D_460),'#skF_2')
      | ~ v3_pre_topc(D_460,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_460,k1_zfmisc_1(k1_xboole_0))
      | ~ v5_pre_topc(k6_partfun1(k1_xboole_0),'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
      | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_1(k6_partfun1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_2033,c_4762])).

tff(c_4779,plain,(
    ! [D_462] :
      ( v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),D_462),'#skF_2')
      | ~ v3_pre_topc(D_462,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_462,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2015,c_2036,c_2014,c_2030,c_4768])).

tff(c_4791,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3',k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2013,c_4779])).

tff(c_4793,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1812,c_495,c_4791])).

tff(c_4795,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_4793])).

tff(c_4797,plain,(
    ~ m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_4834,plain,(
    ~ m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0(k6_tmap_1('#skF_2','#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4833,c_4797])).

tff(c_4919,plain,(
    ~ m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4889,c_4834])).

tff(c_5076,plain,(
    ! [A_495,B_496] :
      ( m1_subset_1(k7_tmap_1(A_495,B_496),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_495),u1_struct_0(k6_tmap_1(A_495,B_496)))))
      | ~ m1_subset_1(B_496,k1_zfmisc_1(u1_struct_0(A_495)))
      | ~ l1_pre_topc(A_495)
      | ~ v2_pre_topc(A_495)
      | v2_struct_0(A_495) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_5086,plain,
    ( m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4888,c_5076])).

tff(c_5095,plain,
    ( m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_96,c_95,c_95,c_5086])).

tff(c_5097,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_4919,c_5095])).

tff(c_5098,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_5181,plain,
    ( ~ m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0(k6_tmap_1('#skF_2','#skF_3')))))
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5098,c_101,c_5154,c_95,c_110,c_5154,c_95,c_66])).

tff(c_5182,plain,(
    ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_5181])).

tff(c_5242,plain,(
    ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5200,c_5182])).

tff(c_5298,plain,(
    ! [A_523,B_524] :
      ( v1_funct_2(k7_tmap_1(A_523,B_524),u1_struct_0(A_523),u1_struct_0(k6_tmap_1(A_523,B_524)))
      | ~ m1_subset_1(B_524,k1_zfmisc_1(u1_struct_0(A_523)))
      | ~ l1_pre_topc(A_523)
      | ~ v2_pre_topc(A_523)
      | v2_struct_0(A_523) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_5304,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),k2_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5199,c_5298])).

tff(c_5311,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_96,c_95,c_95,c_5304])).

tff(c_5313,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_5242,c_5311])).

tff(c_5315,plain,(
    v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_5181])).

tff(c_5099,plain,(
    ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_5155,plain,(
    ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5154,c_5099])).

tff(c_5317,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5315,c_5155])).

tff(c_5319,plain,(
    ~ v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2',k6_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_5435,plain,(
    ! [A_545,B_546] :
      ( u1_struct_0(k6_tmap_1(A_545,B_546)) = u1_struct_0(A_545)
      | ~ m1_subset_1(B_546,k1_zfmisc_1(u1_struct_0(A_545)))
      | ~ l1_pre_topc(A_545)
      | ~ v2_pre_topc(A_545)
      | v2_struct_0(A_545) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_5441,plain,(
    ! [B_546] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_546)) = u1_struct_0('#skF_2')
      | ~ m1_subset_1(B_546,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_5435])).

tff(c_5445,plain,(
    ! [B_546] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_546)) = k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_546,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_95,c_5441])).

tff(c_5447,plain,(
    ! [B_547] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_547)) = k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_547,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_5445])).

tff(c_5451,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_96,c_5447])).

tff(c_5518,plain,(
    ! [A_551,B_552] :
      ( v1_funct_2(k7_tmap_1(A_551,B_552),u1_struct_0(A_551),u1_struct_0(k6_tmap_1(A_551,B_552)))
      | ~ m1_subset_1(B_552,k1_zfmisc_1(u1_struct_0(A_551)))
      | ~ l1_pre_topc(A_551)
      | ~ v2_pre_topc(A_551)
      | v2_struct_0(A_551) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_5524,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),k2_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5451,c_5518])).

tff(c_5531,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_96,c_95,c_95,c_5524])).

tff(c_5532,plain,(
    v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_5531])).

tff(c_5617,plain,(
    ! [A_564,B_565] :
      ( m1_subset_1(k7_tmap_1(A_564,B_565),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_564),u1_struct_0(k6_tmap_1(A_564,B_565)))))
      | ~ m1_subset_1(B_565,k1_zfmisc_1(u1_struct_0(A_564)))
      | ~ l1_pre_topc(A_564)
      | ~ v2_pre_topc(A_564)
      | v2_struct_0(A_564) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_5627,plain,
    ( m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5451,c_5617])).

tff(c_5636,plain,
    ( m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_96,c_95,c_95,c_5627])).

tff(c_5637,plain,(
    m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_5636])).

tff(c_5365,plain,(
    ! [A_535,B_536] :
      ( v2_pre_topc(k6_tmap_1(A_535,B_536))
      | ~ m1_subset_1(B_536,k1_zfmisc_1(u1_struct_0(A_535)))
      | ~ l1_pre_topc(A_535)
      | ~ v2_pre_topc(A_535)
      | v2_struct_0(A_535) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_5371,plain,(
    ! [B_536] :
      ( v2_pre_topc(k6_tmap_1('#skF_2',B_536))
      | ~ m1_subset_1(B_536,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_5365])).

tff(c_5375,plain,(
    ! [B_536] :
      ( v2_pre_topc(k6_tmap_1('#skF_2',B_536))
      | ~ m1_subset_1(B_536,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_5371])).

tff(c_5377,plain,(
    ! [B_537] :
      ( v2_pre_topc(k6_tmap_1('#skF_2',B_537))
      | ~ m1_subset_1(B_537,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_5375])).

tff(c_5381,plain,(
    v2_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_96,c_5377])).

tff(c_5334,plain,(
    ! [A_532,B_533] :
      ( l1_pre_topc(k6_tmap_1(A_532,B_533))
      | ~ m1_subset_1(B_533,k1_zfmisc_1(u1_struct_0(A_532)))
      | ~ l1_pre_topc(A_532)
      | ~ v2_pre_topc(A_532)
      | v2_struct_0(A_532) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_5337,plain,(
    ! [B_533] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_533))
      | ~ m1_subset_1(B_533,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_5334])).

tff(c_5339,plain,(
    ! [B_533] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_533))
      | ~ m1_subset_1(B_533,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_5337])).

tff(c_5341,plain,(
    ! [B_534] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_534))
      | ~ m1_subset_1(B_534,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_5339])).

tff(c_5345,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_96,c_5341])).

tff(c_5318,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_5573,plain,(
    ! [A_557,B_558] :
      ( k6_tmap_1(A_557,B_558) = g1_pre_topc(u1_struct_0(A_557),u1_pre_topc(A_557))
      | ~ v3_pre_topc(B_558,A_557)
      | ~ m1_subset_1(B_558,k1_zfmisc_1(u1_struct_0(A_557)))
      | ~ l1_pre_topc(A_557)
      | ~ v2_pre_topc(A_557)
      | v2_struct_0(A_557) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_5577,plain,(
    ! [B_558] :
      ( k6_tmap_1('#skF_2',B_558) = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ v3_pre_topc(B_558,'#skF_2')
      | ~ m1_subset_1(B_558,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_5573])).

tff(c_5581,plain,(
    ! [B_558] :
      ( k6_tmap_1('#skF_2',B_558) = g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ v3_pre_topc(B_558,'#skF_2')
      | ~ m1_subset_1(B_558,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_95,c_5577])).

tff(c_5583,plain,(
    ! [B_559] :
      ( k6_tmap_1('#skF_2',B_559) = g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ v3_pre_topc(B_559,'#skF_2')
      | ~ m1_subset_1(B_559,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_5581])).

tff(c_5586,plain,
    ( g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k6_tmap_1('#skF_2','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_96,c_5583])).

tff(c_5589,plain,(
    g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k6_tmap_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5318,c_5586])).

tff(c_7043,plain,(
    ! [D_658,A_659,B_660] :
      ( v5_pre_topc(D_658,A_659,B_660)
      | ~ v5_pre_topc(D_658,g1_pre_topc(u1_struct_0(A_659),u1_pre_topc(A_659)),B_660)
      | ~ m1_subset_1(D_658,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_659),u1_pre_topc(A_659))),u1_struct_0(B_660))))
      | ~ v1_funct_2(D_658,u1_struct_0(g1_pre_topc(u1_struct_0(A_659),u1_pre_topc(A_659))),u1_struct_0(B_660))
      | ~ m1_subset_1(D_658,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_659),u1_struct_0(B_660))))
      | ~ v1_funct_2(D_658,u1_struct_0(A_659),u1_struct_0(B_660))
      | ~ v1_funct_1(D_658)
      | ~ l1_pre_topc(B_660)
      | ~ v2_pre_topc(B_660)
      | ~ l1_pre_topc(A_659)
      | ~ v2_pre_topc(A_659) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_7068,plain,(
    ! [D_658,B_660] :
      ( v5_pre_topc(D_658,'#skF_2',B_660)
      | ~ v5_pre_topc(D_658,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),B_660)
      | ~ m1_subset_1(D_658,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0(B_660))))
      | ~ v1_funct_2(D_658,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0(B_660))
      | ~ m1_subset_1(D_658,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_660))))
      | ~ v1_funct_2(D_658,u1_struct_0('#skF_2'),u1_struct_0(B_660))
      | ~ v1_funct_1(D_658)
      | ~ l1_pre_topc(B_660)
      | ~ v2_pre_topc(B_660)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_7043])).

tff(c_7089,plain,(
    ! [D_661,B_662] :
      ( v5_pre_topc(D_661,'#skF_2',B_662)
      | ~ v5_pre_topc(D_661,k6_tmap_1('#skF_2','#skF_3'),B_662)
      | ~ m1_subset_1(D_661,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(B_662))))
      | ~ v1_funct_2(D_661,k2_struct_0('#skF_2'),u1_struct_0(B_662))
      | ~ v1_funct_1(D_661)
      | ~ l1_pre_topc(B_662)
      | ~ v2_pre_topc(B_662) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_95,c_95,c_5451,c_5589,c_95,c_5451,c_5589,c_5589,c_95,c_7068])).

tff(c_7098,plain,(
    ! [D_661] :
      ( v5_pre_topc(D_661,'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
      | ~ v5_pre_topc(D_661,k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_661,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_661,k2_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(D_661)
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
      | ~ v2_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5451,c_7089])).

tff(c_7116,plain,(
    ! [D_664] :
      ( v5_pre_topc(D_664,'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
      | ~ v5_pre_topc(D_664,k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_664,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_664,k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(D_664) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5381,c_5345,c_5451,c_7098])).

tff(c_7119,plain,
    ( v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
    | ~ v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_5637,c_7116])).

tff(c_7122,plain,
    ( v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
    | ~ v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_5532,c_7119])).

tff(c_7123,plain,(
    ~ v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_5319,c_7122])).

tff(c_5723,plain,(
    ! [A_573,B_574,C_575] :
      ( k2_struct_0(A_573) != k1_xboole_0
      | v3_pre_topc('#skF_1'(A_573,B_574,C_575),B_574)
      | v5_pre_topc(C_575,A_573,B_574)
      | ~ m1_subset_1(C_575,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_573),u1_struct_0(B_574))))
      | ~ v1_funct_2(C_575,u1_struct_0(A_573),u1_struct_0(B_574))
      | ~ v1_funct_1(C_575)
      | ~ l1_pre_topc(B_574)
      | ~ l1_pre_topc(A_573) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_5731,plain,(
    ! [B_574,C_575] :
      ( k2_struct_0('#skF_2') != k1_xboole_0
      | v3_pre_topc('#skF_1'('#skF_2',B_574,C_575),B_574)
      | v5_pre_topc(C_575,'#skF_2',B_574)
      | ~ m1_subset_1(C_575,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(B_574))))
      | ~ v1_funct_2(C_575,u1_struct_0('#skF_2'),u1_struct_0(B_574))
      | ~ v1_funct_1(C_575)
      | ~ l1_pre_topc(B_574)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_5723])).

tff(c_5740,plain,(
    ! [B_574,C_575] :
      ( k2_struct_0('#skF_2') != k1_xboole_0
      | v3_pre_topc('#skF_1'('#skF_2',B_574,C_575),B_574)
      | v5_pre_topc(C_575,'#skF_2',B_574)
      | ~ m1_subset_1(C_575,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(B_574))))
      | ~ v1_funct_2(C_575,k2_struct_0('#skF_2'),u1_struct_0(B_574))
      | ~ v1_funct_1(C_575)
      | ~ l1_pre_topc(B_574) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_95,c_5731])).

tff(c_5759,plain,(
    k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_5740])).

tff(c_5349,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_5345,c_90])).

tff(c_5452,plain,(
    k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5451,c_5349])).

tff(c_5795,plain,(
    ! [B_582,A_583,C_584] :
      ( k2_struct_0(B_582) = k1_xboole_0
      | v3_pre_topc('#skF_1'(A_583,B_582,C_584),B_582)
      | v5_pre_topc(C_584,A_583,B_582)
      | ~ m1_subset_1(C_584,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_583),u1_struct_0(B_582))))
      | ~ v1_funct_2(C_584,u1_struct_0(A_583),u1_struct_0(B_582))
      | ~ v1_funct_1(C_584)
      | ~ l1_pre_topc(B_582)
      | ~ l1_pre_topc(A_583) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_5801,plain,(
    ! [A_583,C_584] :
      ( k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k1_xboole_0
      | v3_pre_topc('#skF_1'(A_583,k6_tmap_1('#skF_2','#skF_3'),C_584),k6_tmap_1('#skF_2','#skF_3'))
      | v5_pre_topc(C_584,A_583,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_584,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_583),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_584,u1_struct_0(A_583),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_584)
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_583) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5451,c_5795])).

tff(c_5810,plain,(
    ! [A_583,C_584] :
      ( k2_struct_0('#skF_2') = k1_xboole_0
      | v3_pre_topc('#skF_1'(A_583,k6_tmap_1('#skF_2','#skF_3'),C_584),k6_tmap_1('#skF_2','#skF_3'))
      | v5_pre_topc(C_584,A_583,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_584,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_583),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_584,u1_struct_0(A_583),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_584)
      | ~ l1_pre_topc(A_583) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5345,c_5451,c_5452,c_5801])).

tff(c_5976,plain,(
    ! [A_606,C_607] :
      ( v3_pre_topc('#skF_1'(A_606,k6_tmap_1('#skF_2','#skF_3'),C_607),k6_tmap_1('#skF_2','#skF_3'))
      | v5_pre_topc(C_607,A_606,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_607,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_606),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_607,u1_struct_0(A_606),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_607)
      | ~ l1_pre_topc(A_606) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5759,c_5810])).

tff(c_5979,plain,(
    ! [C_607] :
      ( v3_pre_topc('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),C_607),k6_tmap_1('#skF_2','#skF_3'))
      | v5_pre_topc(C_607,k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_607,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_607,u1_struct_0(k6_tmap_1('#skF_2','#skF_3')),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_607)
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5451,c_5976])).

tff(c_5984,plain,(
    ! [C_607] :
      ( v3_pre_topc('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),C_607),k6_tmap_1('#skF_2','#skF_3'))
      | v5_pre_topc(C_607,k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_607,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_607,k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_607) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5345,c_5451,c_5979])).

tff(c_5645,plain,(
    ! [D_4] : k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k7_tmap_1('#skF_2','#skF_3'),D_4) = k10_relat_1(k7_tmap_1('#skF_2','#skF_3'),D_4) ),
    inference(resolution,[status(thm)],[c_5637,c_2])).

tff(c_5400,plain,(
    ! [A_541,B_542] :
      ( k7_tmap_1(A_541,B_542) = k6_partfun1(u1_struct_0(A_541))
      | ~ m1_subset_1(B_542,k1_zfmisc_1(u1_struct_0(A_541)))
      | ~ l1_pre_topc(A_541)
      | ~ v2_pre_topc(A_541)
      | v2_struct_0(A_541) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_5406,plain,(
    ! [B_542] :
      ( k7_tmap_1('#skF_2',B_542) = k6_partfun1(u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_542,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_5400])).

tff(c_5410,plain,(
    ! [B_542] :
      ( k7_tmap_1('#skF_2',B_542) = k6_partfun1(k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_542,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_95,c_5406])).

tff(c_5412,plain,(
    ! [B_543] :
      ( k7_tmap_1('#skF_2',B_543) = k6_partfun1(k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_543,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_5410])).

tff(c_5416,plain,(
    k6_partfun1(k2_struct_0('#skF_2')) = k7_tmap_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_5412])).

tff(c_5987,plain,(
    ! [B_608,A_609,C_610] :
      ( k2_struct_0(B_608) = k1_xboole_0
      | m1_subset_1('#skF_1'(A_609,B_608,C_610),k1_zfmisc_1(u1_struct_0(B_608)))
      | v5_pre_topc(C_610,A_609,B_608)
      | ~ m1_subset_1(C_610,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_609),u1_struct_0(B_608))))
      | ~ v1_funct_2(C_610,u1_struct_0(A_609),u1_struct_0(B_608))
      | ~ v1_funct_1(C_610)
      | ~ l1_pre_topc(B_608)
      | ~ l1_pre_topc(A_609) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_5993,plain,(
    ! [A_609,C_610] :
      ( k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k1_xboole_0
      | m1_subset_1('#skF_1'(A_609,k6_tmap_1('#skF_2','#skF_3'),C_610),k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))))
      | v5_pre_topc(C_610,A_609,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_610,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_609),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_610,u1_struct_0(A_609),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_610)
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_609) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5451,c_5987])).

tff(c_6002,plain,(
    ! [A_609,C_610] :
      ( k2_struct_0('#skF_2') = k1_xboole_0
      | m1_subset_1('#skF_1'(A_609,k6_tmap_1('#skF_2','#skF_3'),C_610),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v5_pre_topc(C_610,A_609,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_610,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_609),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_610,u1_struct_0(A_609),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_610)
      | ~ l1_pre_topc(A_609) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5345,c_5451,c_5451,c_5452,c_5993])).

tff(c_6003,plain,(
    ! [A_609,C_610] :
      ( m1_subset_1('#skF_1'(A_609,k6_tmap_1('#skF_2','#skF_3'),C_610),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v5_pre_topc(C_610,A_609,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_610,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_609),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_610,u1_struct_0(A_609),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_610)
      | ~ l1_pre_topc(A_609) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5759,c_6002])).

tff(c_6986,plain,(
    ! [A_654,C_655] :
      ( m1_subset_1('#skF_1'(A_654,k6_tmap_1('#skF_2','#skF_3'),C_655),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v5_pre_topc(C_655,A_654,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_655,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_654),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_655,u1_struct_0(A_654),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_655)
      | ~ l1_pre_topc(A_654) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5759,c_6002])).

tff(c_5340,plain,(
    ! [B_533] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_533))
      | ~ m1_subset_1(B_533,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_5339])).

tff(c_7126,plain,(
    ! [A_665,C_666] :
      ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_1'(A_665,k6_tmap_1('#skF_2','#skF_3'),C_666)))
      | v5_pre_topc(C_666,A_665,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_666,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_665),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_666,u1_struct_0(A_665),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_666)
      | ~ l1_pre_topc(A_665) ) ),
    inference(resolution,[status(thm)],[c_6986,c_5340])).

tff(c_7132,plain,(
    ! [C_666] :
      ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),C_666)))
      | v5_pre_topc(C_666,k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_666,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_666,u1_struct_0(k6_tmap_1('#skF_2','#skF_3')),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_666)
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5451,c_7126])).

tff(c_7397,plain,(
    ! [C_682] :
      ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),C_682)))
      | v5_pre_topc(C_682,k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_682,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_682,k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_682) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5345,c_5451,c_7132])).

tff(c_7400,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'))))
    | v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_5637,c_7397])).

tff(c_7403,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'))))
    | v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_5532,c_7400])).

tff(c_7404,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2','#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3')))) ),
    inference(negUnitSimplification,[status(thm)],[c_7123,c_7403])).

tff(c_7408,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3')))) = k2_struct_0(k6_tmap_1('#skF_2','#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3')))) ),
    inference(resolution,[status(thm)],[c_7404,c_90])).

tff(c_7581,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'))),u1_struct_0('#skF_2'),k2_struct_0(k6_tmap_1('#skF_2','#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3')))))
    | ~ m1_subset_1('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7408,c_44])).

tff(c_7726,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'))),k2_struct_0('#skF_2'),k2_struct_0(k6_tmap_1('#skF_2','#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3')))))
    | ~ m1_subset_1('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3')),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_95,c_95,c_7581])).

tff(c_7727,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'))),k2_struct_0('#skF_2'),k2_struct_0(k6_tmap_1('#skF_2','#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3')))))
    | ~ m1_subset_1('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3')),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_7726])).

tff(c_7743,plain,(
    ~ m1_subset_1('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3')),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_7727])).

tff(c_7746,plain,
    ( v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2','#skF_3')),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')),k2_struct_0('#skF_2'))
    | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6003,c_7743])).

tff(c_7749,plain,(
    v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5345,c_101,c_5532,c_5451,c_5637,c_5451,c_7746])).

tff(c_7751,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7123,c_7749])).

tff(c_7753,plain,(
    m1_subset_1('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3')),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_7727])).

tff(c_4,plain,(
    ! [A_5,B_6] :
      ( k8_relset_1(A_5,A_5,k6_partfun1(A_5),B_6) = B_6
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_7782,plain,(
    k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k6_partfun1(k2_struct_0('#skF_2')),'#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'))) = '#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_7753,c_4])).

tff(c_7795,plain,(
    k10_relat_1(k7_tmap_1('#skF_2','#skF_3'),'#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'))) = '#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5645,c_5416,c_7782])).

tff(c_6407,plain,(
    ! [B_629,A_630,C_631] :
      ( k2_struct_0(B_629) = k1_xboole_0
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(A_630),u1_struct_0(B_629),C_631,'#skF_1'(A_630,B_629,C_631)),A_630)
      | v5_pre_topc(C_631,A_630,B_629)
      | ~ m1_subset_1(C_631,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_630),u1_struct_0(B_629))))
      | ~ v1_funct_2(C_631,u1_struct_0(A_630),u1_struct_0(B_629))
      | ~ v1_funct_1(C_631)
      | ~ l1_pre_topc(B_629)
      | ~ l1_pre_topc(A_630) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_6423,plain,(
    ! [A_630,C_631] :
      ( k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k1_xboole_0
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(A_630),k2_struct_0('#skF_2'),C_631,'#skF_1'(A_630,k6_tmap_1('#skF_2','#skF_3'),C_631)),A_630)
      | v5_pre_topc(C_631,A_630,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_631,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_630),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))))
      | ~ v1_funct_2(C_631,u1_struct_0(A_630),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_631)
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_630) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5451,c_6407])).

tff(c_6437,plain,(
    ! [A_630,C_631] :
      ( k2_struct_0('#skF_2') = k1_xboole_0
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(A_630),k2_struct_0('#skF_2'),C_631,'#skF_1'(A_630,k6_tmap_1('#skF_2','#skF_3'),C_631)),A_630)
      | v5_pre_topc(C_631,A_630,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_631,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_630),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_631,u1_struct_0(A_630),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_631)
      | ~ l1_pre_topc(A_630) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5345,c_5451,c_5451,c_5452,c_6423])).

tff(c_11547,plain,(
    ! [A_774,C_775] :
      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(A_774),k2_struct_0('#skF_2'),C_775,'#skF_1'(A_774,k6_tmap_1('#skF_2','#skF_3'),C_775)),A_774)
      | v5_pre_topc(C_775,A_774,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_775,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_774),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_775,u1_struct_0(A_774),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_775)
      | ~ l1_pre_topc(A_774) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5759,c_6437])).

tff(c_11562,plain,(
    ! [C_775] :
      ( ~ v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),C_775,'#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),C_775)),k6_tmap_1('#skF_2','#skF_3'))
      | v5_pre_topc(C_775,k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_775,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2','#skF_3')),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_775,u1_struct_0(k6_tmap_1('#skF_2','#skF_3')),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_775)
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5451,c_11547])).

tff(c_12790,plain,(
    ! [C_829] :
      ( ~ v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),C_829,'#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),C_829)),k6_tmap_1('#skF_2','#skF_3'))
      | v5_pre_topc(C_829,k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_829,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_829,k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_829) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5345,c_5451,c_5451,c_11562])).

tff(c_12798,plain,
    ( ~ v3_pre_topc(k10_relat_1(k7_tmap_1('#skF_2','#skF_3'),'#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'))),k6_tmap_1('#skF_2','#skF_3'))
    | v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5645,c_12790])).

tff(c_12801,plain,
    ( ~ v3_pre_topc('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3')),k6_tmap_1('#skF_2','#skF_3'))
    | v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_5532,c_5637,c_7795,c_12798])).

tff(c_12802,plain,(
    ~ v3_pre_topc('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3')),k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_7123,c_12801])).

tff(c_12830,plain,
    ( v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_5984,c_12802])).

tff(c_12833,plain,(
    v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_5532,c_5637,c_12830])).

tff(c_12835,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7123,c_12833])).

tff(c_12837,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_5740])).

tff(c_12854,plain,(
    k7_tmap_1('#skF_2','#skF_3') = k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12837,c_5416])).

tff(c_12963,plain,(
    ~ v5_pre_topc(k6_partfun1(k1_xboole_0),'#skF_2',k6_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12854,c_5319])).

tff(c_12964,plain,(
    v1_funct_1(k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12854,c_101])).

tff(c_12859,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12837,c_96])).

tff(c_12860,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12837,c_95])).

tff(c_12850,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12837,c_5451])).

tff(c_13020,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),k1_xboole_0)
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12850,c_44])).

tff(c_13070,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_12859,c_12860,c_12854,c_12860,c_13020])).

tff(c_13071,plain,(
    v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_13070])).

tff(c_13007,plain,
    ( m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),k1_xboole_0)))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12850,c_42])).

tff(c_13058,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_12859,c_12860,c_12854,c_12860,c_13007])).

tff(c_13059,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_13058])).

tff(c_12849,plain,(
    k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12837,c_5452])).

tff(c_22,plain,(
    ! [A_31,B_43,C_49] :
      ( k2_struct_0(A_31) != k1_xboole_0
      | v3_pre_topc('#skF_1'(A_31,B_43,C_49),B_43)
      | v5_pre_topc(C_49,A_31,B_43)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_31),u1_struct_0(B_43))))
      | ~ v1_funct_2(C_49,u1_struct_0(A_31),u1_struct_0(B_43))
      | ~ v1_funct_1(C_49)
      | ~ l1_pre_topc(B_43)
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_12995,plain,(
    ! [A_31,C_49] :
      ( k2_struct_0(A_31) != k1_xboole_0
      | v3_pre_topc('#skF_1'(A_31,k6_tmap_1('#skF_2','#skF_3'),C_49),k6_tmap_1('#skF_2','#skF_3'))
      | v5_pre_topc(C_49,A_31,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_31),k1_xboole_0)))
      | ~ v1_funct_2(C_49,u1_struct_0(A_31),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_49)
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12850,c_22])).

tff(c_13049,plain,(
    ! [A_31,C_49] :
      ( k2_struct_0(A_31) != k1_xboole_0
      | v3_pre_topc('#skF_1'(A_31,k6_tmap_1('#skF_2','#skF_3'),C_49),k6_tmap_1('#skF_2','#skF_3'))
      | v5_pre_topc(C_49,A_31,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_31),k1_xboole_0)))
      | ~ v1_funct_2(C_49,u1_struct_0(A_31),k1_xboole_0)
      | ~ v1_funct_1(C_49)
      | ~ l1_pre_topc(A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5345,c_12850,c_12995])).

tff(c_13175,plain,(
    ! [A_843,B_844,C_845] :
      ( k2_struct_0(A_843) != k1_xboole_0
      | m1_subset_1('#skF_1'(A_843,B_844,C_845),k1_zfmisc_1(u1_struct_0(B_844)))
      | v5_pre_topc(C_845,A_843,B_844)
      | ~ m1_subset_1(C_845,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_843),u1_struct_0(B_844))))
      | ~ v1_funct_2(C_845,u1_struct_0(A_843),u1_struct_0(B_844))
      | ~ v1_funct_1(C_845)
      | ~ l1_pre_topc(B_844)
      | ~ l1_pre_topc(A_843) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_13179,plain,(
    ! [A_843,C_845] :
      ( k2_struct_0(A_843) != k1_xboole_0
      | m1_subset_1('#skF_1'(A_843,k6_tmap_1('#skF_2','#skF_3'),C_845),k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))))
      | v5_pre_topc(C_845,A_843,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_845,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_843),k1_xboole_0)))
      | ~ v1_funct_2(C_845,u1_struct_0(A_843),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_845)
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_843) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12850,c_13175])).

tff(c_13189,plain,(
    ! [A_843,C_845] :
      ( k2_struct_0(A_843) != k1_xboole_0
      | m1_subset_1('#skF_1'(A_843,k6_tmap_1('#skF_2','#skF_3'),C_845),k1_zfmisc_1(k1_xboole_0))
      | v5_pre_topc(C_845,A_843,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_845,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_843),k1_xboole_0)))
      | ~ v1_funct_2(C_845,u1_struct_0(A_843),k1_xboole_0)
      | ~ v1_funct_1(C_845)
      | ~ l1_pre_topc(A_843) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5345,c_12850,c_12850,c_13179])).

tff(c_12871,plain,(
    ! [B_43,C_49] :
      ( k2_struct_0('#skF_2') != k1_xboole_0
      | v3_pre_topc('#skF_1'('#skF_2',B_43,C_49),B_43)
      | v5_pre_topc(C_49,'#skF_2',B_43)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(B_43))))
      | ~ v1_funct_2(C_49,u1_struct_0('#skF_2'),u1_struct_0(B_43))
      | ~ v1_funct_1(C_49)
      | ~ l1_pre_topc(B_43)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12860,c_22])).

tff(c_13342,plain,(
    ! [B_861,C_862] :
      ( v3_pre_topc('#skF_1'('#skF_2',B_861,C_862),B_861)
      | v5_pre_topc(C_862,'#skF_2',B_861)
      | ~ m1_subset_1(C_862,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(B_861))))
      | ~ v1_funct_2(C_862,k1_xboole_0,u1_struct_0(B_861))
      | ~ v1_funct_1(C_862)
      | ~ l1_pre_topc(B_861) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_12860,c_12837,c_12871])).

tff(c_13348,plain,(
    ! [C_862] :
      ( v3_pre_topc('#skF_1'('#skF_2','#skF_2',C_862),'#skF_2')
      | v5_pre_topc(C_862,'#skF_2','#skF_2')
      | ~ m1_subset_1(C_862,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ v1_funct_2(C_862,k1_xboole_0,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_862)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12860,c_13342])).

tff(c_13354,plain,(
    ! [C_863] :
      ( v3_pre_topc('#skF_1'('#skF_2','#skF_2',C_863),'#skF_2')
      | v5_pre_topc(C_863,'#skF_2','#skF_2')
      | ~ m1_subset_1(C_863,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ v1_funct_2(C_863,k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_1(C_863) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_12860,c_13348])).

tff(c_13357,plain,
    ( v3_pre_topc('#skF_1'('#skF_2','#skF_2',k6_partfun1(k1_xboole_0)),'#skF_2')
    | v5_pre_topc(k6_partfun1(k1_xboole_0),'#skF_2','#skF_2')
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_13059,c_13354])).

tff(c_13360,plain,
    ( v3_pre_topc('#skF_1'('#skF_2','#skF_2',k6_partfun1(k1_xboole_0)),'#skF_2')
    | v5_pre_topc(k6_partfun1(k1_xboole_0),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12964,c_13071,c_13357])).

tff(c_13361,plain,(
    v5_pre_topc(k6_partfun1(k1_xboole_0),'#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_13360])).

tff(c_12845,plain,(
    g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2')) = k6_tmap_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12837,c_5589])).

tff(c_13779,plain,(
    ! [D_893,A_894,B_895] :
      ( v5_pre_topc(D_893,g1_pre_topc(u1_struct_0(A_894),u1_pre_topc(A_894)),B_895)
      | ~ v5_pre_topc(D_893,A_894,B_895)
      | ~ m1_subset_1(D_893,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_894),u1_pre_topc(A_894))),u1_struct_0(B_895))))
      | ~ v1_funct_2(D_893,u1_struct_0(g1_pre_topc(u1_struct_0(A_894),u1_pre_topc(A_894))),u1_struct_0(B_895))
      | ~ m1_subset_1(D_893,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_894),u1_struct_0(B_895))))
      | ~ v1_funct_2(D_893,u1_struct_0(A_894),u1_struct_0(B_895))
      | ~ v1_funct_1(D_893)
      | ~ l1_pre_topc(B_895)
      | ~ v2_pre_topc(B_895)
      | ~ l1_pre_topc(A_894)
      | ~ v2_pre_topc(A_894) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_13788,plain,(
    ! [D_893,B_895] :
      ( v5_pre_topc(D_893,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),B_895)
      | ~ v5_pre_topc(D_893,'#skF_2',B_895)
      | ~ m1_subset_1(D_893,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))),u1_struct_0(B_895))))
      | ~ v1_funct_2(D_893,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0(B_895))
      | ~ m1_subset_1(D_893,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_895))))
      | ~ v1_funct_2(D_893,u1_struct_0('#skF_2'),u1_struct_0(B_895))
      | ~ v1_funct_1(D_893)
      | ~ l1_pre_topc(B_895)
      | ~ v2_pre_topc(B_895)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12860,c_13779])).

tff(c_14235,plain,(
    ! [D_903,B_904] :
      ( v5_pre_topc(D_903,k6_tmap_1('#skF_2','#skF_3'),B_904)
      | ~ v5_pre_topc(D_903,'#skF_2',B_904)
      | ~ m1_subset_1(D_903,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(B_904))))
      | ~ v1_funct_2(D_903,k1_xboole_0,u1_struct_0(B_904))
      | ~ v1_funct_1(D_903)
      | ~ l1_pre_topc(B_904)
      | ~ v2_pre_topc(B_904) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_12860,c_12860,c_12850,c_12845,c_12860,c_12850,c_12845,c_12845,c_12860,c_13788])).

tff(c_14247,plain,(
    ! [D_903] :
      ( v5_pre_topc(D_903,k6_tmap_1('#skF_2','#skF_3'),'#skF_2')
      | ~ v5_pre_topc(D_903,'#skF_2','#skF_2')
      | ~ m1_subset_1(D_903,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ v1_funct_2(D_903,k1_xboole_0,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_903)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12860,c_14235])).

tff(c_14323,plain,(
    ! [D_907] :
      ( v5_pre_topc(D_907,k6_tmap_1('#skF_2','#skF_3'),'#skF_2')
      | ~ v5_pre_topc(D_907,'#skF_2','#skF_2')
      | ~ m1_subset_1(D_907,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ v1_funct_2(D_907,k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_1(D_907) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_12860,c_14247])).

tff(c_14326,plain,
    ( v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1('#skF_2','#skF_3'),'#skF_2')
    | ~ v5_pre_topc(k6_partfun1(k1_xboole_0),'#skF_2','#skF_2')
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_13059,c_14323])).

tff(c_14329,plain,(
    v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12964,c_13071,c_13361,c_14326])).

tff(c_5631,plain,(
    ! [A_564,B_565,D_4] :
      ( k8_relset_1(u1_struct_0(A_564),u1_struct_0(k6_tmap_1(A_564,B_565)),k7_tmap_1(A_564,B_565),D_4) = k10_relat_1(k7_tmap_1(A_564,B_565),D_4)
      | ~ m1_subset_1(B_565,k1_zfmisc_1(u1_struct_0(A_564)))
      | ~ l1_pre_topc(A_564)
      | ~ v2_pre_topc(A_564)
      | v2_struct_0(A_564) ) ),
    inference(resolution,[status(thm)],[c_5617,c_2])).

tff(c_13001,plain,(
    ! [D_4] :
      ( k8_relset_1(u1_struct_0('#skF_2'),k1_xboole_0,k7_tmap_1('#skF_2','#skF_3'),D_4) = k10_relat_1(k7_tmap_1('#skF_2','#skF_3'),D_4)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12850,c_5631])).

tff(c_13053,plain,(
    ! [D_4] :
      ( k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),D_4) = k10_relat_1(k6_partfun1(k1_xboole_0),D_4)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_12859,c_12860,c_12854,c_12854,c_12860,c_13001])).

tff(c_13054,plain,(
    ! [D_4] : k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),D_4) = k10_relat_1(k6_partfun1(k1_xboole_0),D_4) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_13053])).

tff(c_13455,plain,(
    ! [A_871,B_872,C_873,D_874] :
      ( k2_struct_0(A_871) != k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0(A_871),u1_struct_0(B_872),C_873,D_874),A_871)
      | ~ v3_pre_topc(D_874,B_872)
      | ~ m1_subset_1(D_874,k1_zfmisc_1(u1_struct_0(B_872)))
      | ~ v5_pre_topc(C_873,A_871,B_872)
      | ~ m1_subset_1(C_873,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_871),u1_struct_0(B_872))))
      | ~ v1_funct_2(C_873,u1_struct_0(A_871),u1_struct_0(B_872))
      | ~ v1_funct_1(C_873)
      | ~ l1_pre_topc(B_872)
      | ~ l1_pre_topc(A_871) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_13463,plain,(
    ! [A_871,C_873,D_874] :
      ( k2_struct_0(A_871) != k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0(A_871),u1_struct_0('#skF_2'),C_873,D_874),A_871)
      | ~ v3_pre_topc(D_874,'#skF_2')
      | ~ m1_subset_1(D_874,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v5_pre_topc(C_873,A_871,'#skF_2')
      | ~ m1_subset_1(C_873,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_871),k1_xboole_0)))
      | ~ v1_funct_2(C_873,u1_struct_0(A_871),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_873)
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_871) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12860,c_13455])).

tff(c_20642,plain,(
    ! [A_1114,C_1115,D_1116] :
      ( k2_struct_0(A_1114) != k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0(A_1114),k1_xboole_0,C_1115,D_1116),A_1114)
      | ~ v3_pre_topc(D_1116,'#skF_2')
      | ~ m1_subset_1(D_1116,k1_zfmisc_1(k1_xboole_0))
      | ~ v5_pre_topc(C_1115,A_1114,'#skF_2')
      | ~ m1_subset_1(C_1115,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1114),k1_xboole_0)))
      | ~ v1_funct_2(C_1115,u1_struct_0(A_1114),k1_xboole_0)
      | ~ v1_funct_1(C_1115)
      | ~ l1_pre_topc(A_1114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_12860,c_12860,c_12860,c_13463])).

tff(c_20658,plain,(
    ! [C_1115,D_1116] :
      ( k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) != k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0(k6_tmap_1('#skF_2','#skF_3')),k1_xboole_0,C_1115,D_1116),k6_tmap_1('#skF_2','#skF_3'))
      | ~ v3_pre_topc(D_1116,'#skF_2')
      | ~ m1_subset_1(D_1116,k1_zfmisc_1(k1_xboole_0))
      | ~ v5_pre_topc(C_1115,k6_tmap_1('#skF_2','#skF_3'),'#skF_2')
      | ~ m1_subset_1(C_1115,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ v1_funct_2(C_1115,u1_struct_0(k6_tmap_1('#skF_2','#skF_3')),k1_xboole_0)
      | ~ v1_funct_1(C_1115)
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12850,c_20642])).

tff(c_20669,plain,(
    ! [C_1117,D_1118] :
      ( v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,C_1117,D_1118),k6_tmap_1('#skF_2','#skF_3'))
      | ~ v3_pre_topc(D_1118,'#skF_2')
      | ~ m1_subset_1(D_1118,k1_zfmisc_1(k1_xboole_0))
      | ~ v5_pre_topc(C_1117,k6_tmap_1('#skF_2','#skF_3'),'#skF_2')
      | ~ m1_subset_1(C_1117,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ v1_funct_2(C_1117,k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_1(C_1117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5345,c_12850,c_12850,c_12849,c_20658])).

tff(c_20686,plain,(
    ! [D_4] :
      ( v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),D_4),k6_tmap_1('#skF_2','#skF_3'))
      | ~ v3_pre_topc(D_4,'#skF_2')
      | ~ m1_subset_1(D_4,k1_zfmisc_1(k1_xboole_0))
      | ~ v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1('#skF_2','#skF_3'),'#skF_2')
      | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_1(k6_partfun1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13054,c_20669])).

tff(c_20700,plain,(
    ! [D_1119] :
      ( v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),D_1119),k6_tmap_1('#skF_2','#skF_3'))
      | ~ v3_pre_topc(D_1119,'#skF_2')
      | ~ m1_subset_1(D_1119,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12964,c_13071,c_13059,c_14329,c_20686])).

tff(c_13362,plain,(
    ! [A_864,B_865,C_866] :
      ( k2_struct_0(A_864) != k1_xboole_0
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(A_864),u1_struct_0(B_865),C_866,'#skF_1'(A_864,B_865,C_866)),A_864)
      | v5_pre_topc(C_866,A_864,B_865)
      | ~ m1_subset_1(C_866,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_864),u1_struct_0(B_865))))
      | ~ v1_funct_2(C_866,u1_struct_0(A_864),u1_struct_0(B_865))
      | ~ v1_funct_1(C_866)
      | ~ l1_pre_topc(B_865)
      | ~ l1_pre_topc(A_864) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_13365,plain,(
    ! [B_865,C_866] :
      ( k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) != k1_xboole_0
      | ~ v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(B_865),C_866,'#skF_1'(k6_tmap_1('#skF_2','#skF_3'),B_865,C_866)),k6_tmap_1('#skF_2','#skF_3'))
      | v5_pre_topc(C_866,k6_tmap_1('#skF_2','#skF_3'),B_865)
      | ~ m1_subset_1(C_866,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2','#skF_3')),u1_struct_0(B_865))))
      | ~ v1_funct_2(C_866,u1_struct_0(k6_tmap_1('#skF_2','#skF_3')),u1_struct_0(B_865))
      | ~ v1_funct_1(C_866)
      | ~ l1_pre_topc(B_865)
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12850,c_13362])).

tff(c_20435,plain,(
    ! [B_1097,C_1098] :
      ( ~ v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(B_1097),C_1098,'#skF_1'(k6_tmap_1('#skF_2','#skF_3'),B_1097,C_1098)),k6_tmap_1('#skF_2','#skF_3'))
      | v5_pre_topc(C_1098,k6_tmap_1('#skF_2','#skF_3'),B_1097)
      | ~ m1_subset_1(C_1098,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(B_1097))))
      | ~ v1_funct_2(C_1098,k1_xboole_0,u1_struct_0(B_1097))
      | ~ v1_funct_1(C_1098)
      | ~ l1_pre_topc(B_1097) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5345,c_12850,c_12850,c_12849,c_13365])).

tff(c_20463,plain,(
    ! [C_1098] :
      ( ~ v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,C_1098,'#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),C_1098)),k6_tmap_1('#skF_2','#skF_3'))
      | v5_pre_topc(C_1098,k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_1098,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))))
      | ~ v1_funct_2(C_1098,k1_xboole_0,u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_1098)
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12850,c_20435])).

tff(c_20475,plain,(
    ! [C_1099] :
      ( ~ v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,C_1099,'#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),C_1099)),k6_tmap_1('#skF_2','#skF_3'))
      | v5_pre_topc(C_1099,k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_1099,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ v1_funct_2(C_1099,k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_1(C_1099) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5345,c_12850,c_12850,c_20463])).

tff(c_20479,plain,
    ( ~ v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),'#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k6_partfun1(k1_xboole_0))),k6_tmap_1('#skF_2','#skF_3'))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_13054,c_20475])).

tff(c_20481,plain,
    ( ~ v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),'#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k6_partfun1(k1_xboole_0))),k6_tmap_1('#skF_2','#skF_3'))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12964,c_13071,c_13059,c_20479])).

tff(c_20482,plain,(
    ~ v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),'#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k6_partfun1(k1_xboole_0))),k6_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_20481])).

tff(c_20722,plain,
    ( ~ v3_pre_topc('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k6_partfun1(k1_xboole_0)),'#skF_2')
    | ~ m1_subset_1('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_20700,c_20482])).

tff(c_20755,plain,(
    ~ m1_subset_1('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_20722])).

tff(c_20758,plain,
    ( k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) != k1_xboole_0
    | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2','#skF_3')),k1_xboole_0)))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')),k1_xboole_0)
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_13189,c_20755])).

tff(c_20764,plain,(
    v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5345,c_12964,c_13071,c_12850,c_13059,c_12850,c_12849,c_20758])).

tff(c_14061,plain,(
    ! [D_896,A_897,B_898] :
      ( v5_pre_topc(D_896,A_897,B_898)
      | ~ v5_pre_topc(D_896,g1_pre_topc(u1_struct_0(A_897),u1_pre_topc(A_897)),B_898)
      | ~ m1_subset_1(D_896,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_897),u1_pre_topc(A_897))),u1_struct_0(B_898))))
      | ~ v1_funct_2(D_896,u1_struct_0(g1_pre_topc(u1_struct_0(A_897),u1_pre_topc(A_897))),u1_struct_0(B_898))
      | ~ m1_subset_1(D_896,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_897),u1_struct_0(B_898))))
      | ~ v1_funct_2(D_896,u1_struct_0(A_897),u1_struct_0(B_898))
      | ~ v1_funct_1(D_896)
      | ~ l1_pre_topc(B_898)
      | ~ v2_pre_topc(B_898)
      | ~ l1_pre_topc(A_897)
      | ~ v2_pre_topc(A_897) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14079,plain,(
    ! [D_896,B_898] :
      ( v5_pre_topc(D_896,'#skF_2',B_898)
      | ~ v5_pre_topc(D_896,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),B_898)
      | ~ m1_subset_1(D_896,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))),u1_struct_0(B_898))))
      | ~ v1_funct_2(D_896,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0(B_898))
      | ~ m1_subset_1(D_896,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_898))))
      | ~ v1_funct_2(D_896,u1_struct_0('#skF_2'),u1_struct_0(B_898))
      | ~ v1_funct_1(D_896)
      | ~ l1_pre_topc(B_898)
      | ~ v2_pre_topc(B_898)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12860,c_14061])).

tff(c_14377,plain,(
    ! [D_910,B_911] :
      ( v5_pre_topc(D_910,'#skF_2',B_911)
      | ~ v5_pre_topc(D_910,k6_tmap_1('#skF_2','#skF_3'),B_911)
      | ~ m1_subset_1(D_910,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(B_911))))
      | ~ v1_funct_2(D_910,k1_xboole_0,u1_struct_0(B_911))
      | ~ v1_funct_1(D_910)
      | ~ l1_pre_topc(B_911)
      | ~ v2_pre_topc(B_911) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_12860,c_12860,c_12850,c_12845,c_12860,c_12850,c_12845,c_12845,c_12860,c_14079])).

tff(c_14386,plain,(
    ! [D_910] :
      ( v5_pre_topc(D_910,'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
      | ~ v5_pre_topc(D_910,k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_910,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ v1_funct_2(D_910,k1_xboole_0,u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(D_910)
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
      | ~ v2_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12850,c_14377])).

tff(c_14394,plain,(
    ! [D_910] :
      ( v5_pre_topc(D_910,'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
      | ~ v5_pre_topc(D_910,k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_910,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ v1_funct_2(D_910,k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_1(D_910) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5381,c_5345,c_12850,c_14386])).

tff(c_20770,plain,
    ( v5_pre_topc(k6_partfun1(k1_xboole_0),'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_20764,c_14394])).

tff(c_20773,plain,(
    v5_pre_topc(k6_partfun1(k1_xboole_0),'#skF_2',k6_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12964,c_13071,c_13059,c_20770])).

tff(c_20775,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12963,c_20773])).

tff(c_20777,plain,(
    m1_subset_1('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_20722])).

tff(c_20818,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),'#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k6_partfun1(k1_xboole_0))) = '#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_20777,c_4])).

tff(c_21589,plain,(
    k10_relat_1(k6_partfun1(k1_xboole_0),'#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k6_partfun1(k1_xboole_0))) = '#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k6_partfun1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20818,c_13054])).

tff(c_21600,plain,(
    ~ v3_pre_topc('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'),k6_partfun1(k1_xboole_0)),k6_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21589,c_20482])).

tff(c_21619,plain,
    ( k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) != k1_xboole_0
    | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2','#skF_3')),k1_xboole_0)))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')),k1_xboole_0)
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_13049,c_21600])).

tff(c_21625,plain,(
    v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5345,c_12964,c_13071,c_12850,c_13059,c_12850,c_12849,c_21619])).

tff(c_21631,plain,
    ( v5_pre_topc(k6_partfun1(k1_xboole_0),'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_21625,c_14394])).

tff(c_21634,plain,(
    v5_pre_topc(k6_partfun1(k1_xboole_0),'#skF_2',k6_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12964,c_13071,c_13059,c_21631])).

tff(c_21636,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12963,c_21634])).

tff(c_21637,plain,(
    v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_20481])).

tff(c_21641,plain,
    ( v5_pre_topc(k6_partfun1(k1_xboole_0),'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_21637,c_14394])).

tff(c_21644,plain,(
    v5_pre_topc(k6_partfun1(k1_xboole_0),'#skF_2',k6_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12964,c_13071,c_13059,c_21641])).

tff(c_21646,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12963,c_21644])).

tff(c_21648,plain,(
    ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_21661,plain,(
    ! [A_1132,B_1133] :
      ( v1_funct_1(k7_tmap_1(A_1132,B_1133))
      | ~ m1_subset_1(B_1133,k1_zfmisc_1(u1_struct_0(A_1132)))
      | ~ l1_pre_topc(A_1132)
      | ~ v2_pre_topc(A_1132)
      | v2_struct_0(A_1132) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_21664,plain,(
    ! [B_1133] :
      ( v1_funct_1(k7_tmap_1('#skF_2',B_1133))
      | ~ m1_subset_1(B_1133,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_21661])).

tff(c_21666,plain,(
    ! [B_1133] :
      ( v1_funct_1(k7_tmap_1('#skF_2',B_1133))
      | ~ m1_subset_1(B_1133,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_21664])).

tff(c_21668,plain,(
    ! [B_1134] :
      ( v1_funct_1(k7_tmap_1('#skF_2',B_1134))
      | ~ m1_subset_1(B_1134,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_21666])).

tff(c_21671,plain,(
    v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_96,c_21668])).

tff(c_21675,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21648,c_21671])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:53:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.90/7.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.05/7.27  
% 15.05/7.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.05/7.27  %$ v5_pre_topc > v1_funct_2 > v3_pre_topc > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k7_tmap_1 > k6_tmap_1 > k5_tmap_1 > k2_zfmisc_1 > k10_relat_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k6_partfun1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 15.05/7.27  
% 15.05/7.27  %Foreground sorts:
% 15.05/7.27  
% 15.05/7.27  
% 15.05/7.27  %Background operators:
% 15.05/7.27  
% 15.05/7.27  
% 15.05/7.27  %Foreground operators:
% 15.05/7.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 15.05/7.27  tff(k7_tmap_1, type, k7_tmap_1: ($i * $i) > $i).
% 15.05/7.27  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 15.05/7.27  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 15.05/7.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 15.05/7.27  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 15.05/7.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.05/7.27  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 15.05/7.27  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 15.05/7.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.05/7.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 15.05/7.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 15.05/7.27  tff('#skF_2', type, '#skF_2': $i).
% 15.05/7.27  tff('#skF_3', type, '#skF_3': $i).
% 15.05/7.27  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 15.05/7.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.05/7.27  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 15.05/7.27  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 15.05/7.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.05/7.27  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 15.05/7.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 15.05/7.27  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 15.05/7.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.05/7.27  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 15.05/7.27  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 15.05/7.27  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 15.05/7.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 15.05/7.27  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 15.05/7.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.05/7.27  
% 15.43/7.32  tff(f_221, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (((v1_funct_1(k7_tmap_1(A, B)) & v1_funct_2(k7_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))) & v5_pre_topc(k7_tmap_1(A, B), A, k6_tmap_1(A, B))) & m1_subset_1(k7_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_tmap_1)).
% 15.43/7.32  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 15.43/7.32  tff(f_37, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 15.43/7.32  tff(f_169, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 15.43/7.32  tff(f_140, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 15.43/7.32  tff(f_186, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k6_tmap_1(A, B)))) => ((C = B) => v3_pre_topc(C, k6_tmap_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_tmap_1)).
% 15.43/7.32  tff(f_29, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 15.43/7.32  tff(f_125, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k7_tmap_1(A, B) = k6_partfun1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_tmap_1)).
% 15.43/7.32  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 15.43/7.32  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_struct_0(B) = k1_xboole_0) => (k2_struct_0(A) = k1_xboole_0)) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (v3_pre_topc(D, B) => v3_pre_topc(k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), A)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_2)).
% 15.43/7.32  tff(f_155, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_funct_1(k7_tmap_1(A, B)) & v1_funct_2(k7_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))) & m1_subset_1(k7_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 15.43/7.32  tff(f_200, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_tmap_1)).
% 15.43/7.32  tff(f_70, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(B))))) => ((C = D) => (v5_pre_topc(C, A, B) <=> v5_pre_topc(D, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)), B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_pre_topc)).
% 15.43/7.32  tff(c_64, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_221])).
% 15.43/7.32  tff(c_60, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_221])).
% 15.43/7.32  tff(c_8, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.43/7.32  tff(c_86, plain, (![A_75]: (u1_struct_0(A_75)=k2_struct_0(A_75) | ~l1_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.43/7.32  tff(c_91, plain, (![A_76]: (u1_struct_0(A_76)=k2_struct_0(A_76) | ~l1_pre_topc(A_76))), inference(resolution, [status(thm)], [c_8, c_86])).
% 15.43/7.32  tff(c_95, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_91])).
% 15.43/7.32  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_221])).
% 15.43/7.32  tff(c_96, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_58])).
% 15.43/7.32  tff(c_62, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_221])).
% 15.43/7.32  tff(c_5183, plain, (![A_513, B_514]: (u1_struct_0(k6_tmap_1(A_513, B_514))=u1_struct_0(A_513) | ~m1_subset_1(B_514, k1_zfmisc_1(u1_struct_0(A_513))) | ~l1_pre_topc(A_513) | ~v2_pre_topc(A_513) | v2_struct_0(A_513))), inference(cnfTransformation, [status(thm)], [f_169])).
% 15.43/7.32  tff(c_5189, plain, (![B_514]: (u1_struct_0(k6_tmap_1('#skF_2', B_514))=u1_struct_0('#skF_2') | ~m1_subset_1(B_514, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_95, c_5183])).
% 15.43/7.32  tff(c_5193, plain, (![B_514]: (u1_struct_0(k6_tmap_1('#skF_2', B_514))=k2_struct_0('#skF_2') | ~m1_subset_1(B_514, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_95, c_5189])).
% 15.43/7.32  tff(c_5195, plain, (![B_515]: (u1_struct_0(k6_tmap_1('#skF_2', B_515))=k2_struct_0('#skF_2') | ~m1_subset_1(B_515, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_5193])).
% 15.43/7.32  tff(c_5199, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_96, c_5195])).
% 15.43/7.32  tff(c_5139, plain, (![A_510, B_511]: (l1_pre_topc(k6_tmap_1(A_510, B_511)) | ~m1_subset_1(B_511, k1_zfmisc_1(u1_struct_0(A_510))) | ~l1_pre_topc(A_510) | ~v2_pre_topc(A_510) | v2_struct_0(A_510))), inference(cnfTransformation, [status(thm)], [f_140])).
% 15.43/7.32  tff(c_5142, plain, (![B_511]: (l1_pre_topc(k6_tmap_1('#skF_2', B_511)) | ~m1_subset_1(B_511, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_95, c_5139])).
% 15.43/7.32  tff(c_5144, plain, (![B_511]: (l1_pre_topc(k6_tmap_1('#skF_2', B_511)) | ~m1_subset_1(B_511, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_5142])).
% 15.43/7.32  tff(c_5146, plain, (![B_512]: (l1_pre_topc(k6_tmap_1('#skF_2', B_512)) | ~m1_subset_1(B_512, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_5144])).
% 15.43/7.32  tff(c_5150, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_96, c_5146])).
% 15.43/7.32  tff(c_90, plain, (![A_8]: (u1_struct_0(A_8)=k2_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(resolution, [status(thm)], [c_8, c_86])).
% 15.43/7.32  tff(c_5154, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_5150, c_90])).
% 15.43/7.32  tff(c_5200, plain, (k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5199, c_5154])).
% 15.43/7.32  tff(c_4867, plain, (![A_472, B_473]: (u1_struct_0(k6_tmap_1(A_472, B_473))=u1_struct_0(A_472) | ~m1_subset_1(B_473, k1_zfmisc_1(u1_struct_0(A_472))) | ~l1_pre_topc(A_472) | ~v2_pre_topc(A_472) | v2_struct_0(A_472))), inference(cnfTransformation, [status(thm)], [f_169])).
% 15.43/7.32  tff(c_4873, plain, (![B_473]: (u1_struct_0(k6_tmap_1('#skF_2', B_473))=u1_struct_0('#skF_2') | ~m1_subset_1(B_473, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_95, c_4867])).
% 15.43/7.32  tff(c_4877, plain, (![B_473]: (u1_struct_0(k6_tmap_1('#skF_2', B_473))=k2_struct_0('#skF_2') | ~m1_subset_1(B_473, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_95, c_4873])).
% 15.43/7.32  tff(c_4884, plain, (![B_475]: (u1_struct_0(k6_tmap_1('#skF_2', B_475))=k2_struct_0('#skF_2') | ~m1_subset_1(B_475, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_4877])).
% 15.43/7.32  tff(c_4888, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_96, c_4884])).
% 15.43/7.32  tff(c_4816, plain, (![A_467, B_468]: (l1_pre_topc(k6_tmap_1(A_467, B_468)) | ~m1_subset_1(B_468, k1_zfmisc_1(u1_struct_0(A_467))) | ~l1_pre_topc(A_467) | ~v2_pre_topc(A_467) | v2_struct_0(A_467))), inference(cnfTransformation, [status(thm)], [f_140])).
% 15.43/7.32  tff(c_4819, plain, (![B_468]: (l1_pre_topc(k6_tmap_1('#skF_2', B_468)) | ~m1_subset_1(B_468, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_95, c_4816])).
% 15.43/7.32  tff(c_4821, plain, (![B_468]: (l1_pre_topc(k6_tmap_1('#skF_2', B_468)) | ~m1_subset_1(B_468, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_4819])).
% 15.43/7.32  tff(c_4823, plain, (![B_469]: (l1_pre_topc(k6_tmap_1('#skF_2', B_469)) | ~m1_subset_1(B_469, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_4821])).
% 15.43/7.32  tff(c_4827, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_96, c_4823])).
% 15.43/7.32  tff(c_4833, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4827, c_90])).
% 15.43/7.32  tff(c_4889, plain, (k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4888, c_4833])).
% 15.43/7.32  tff(c_84, plain, (v3_pre_topc('#skF_3', '#skF_2') | v1_funct_1(k7_tmap_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_221])).
% 15.43/7.32  tff(c_101, plain, (v1_funct_1(k7_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_84])).
% 15.43/7.32  tff(c_80, plain, (v3_pre_topc('#skF_3', '#skF_2') | v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_221])).
% 15.43/7.32  tff(c_111, plain, (v3_pre_topc('#skF_3', '#skF_2') | v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_80])).
% 15.43/7.32  tff(c_112, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_111])).
% 15.43/7.32  tff(c_76, plain, (v3_pre_topc('#skF_3', '#skF_2') | v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', k6_tmap_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_221])).
% 15.43/7.32  tff(c_110, plain, (v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', k6_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_76])).
% 15.43/7.32  tff(c_72, plain, (v3_pre_topc('#skF_3', '#skF_2') | m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))))), inference(cnfTransformation, [status(thm)], [f_221])).
% 15.43/7.32  tff(c_121, plain, (v3_pre_topc('#skF_3', '#skF_2') | m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_72])).
% 15.43/7.32  tff(c_122, plain, (m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))))), inference(splitLeft, [status(thm)], [c_121])).
% 15.43/7.32  tff(c_66, plain, (~m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))))) | ~v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k7_tmap_1('#skF_2', '#skF_3')) | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_221])).
% 15.43/7.32  tff(c_167, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_112, c_95, c_110, c_122, c_95, c_66])).
% 15.43/7.32  tff(c_253, plain, (![A_100, B_101]: (u1_struct_0(k6_tmap_1(A_100, B_101))=u1_struct_0(A_100) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100) | ~v2_pre_topc(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_169])).
% 15.43/7.32  tff(c_259, plain, (![B_101]: (u1_struct_0(k6_tmap_1('#skF_2', B_101))=u1_struct_0('#skF_2') | ~m1_subset_1(B_101, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_95, c_253])).
% 15.43/7.32  tff(c_263, plain, (![B_101]: (u1_struct_0(k6_tmap_1('#skF_2', B_101))=k2_struct_0('#skF_2') | ~m1_subset_1(B_101, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_95, c_259])).
% 15.43/7.32  tff(c_265, plain, (![B_102]: (u1_struct_0(k6_tmap_1('#skF_2', B_102))=k2_struct_0('#skF_2') | ~m1_subset_1(B_102, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_263])).
% 15.43/7.32  tff(c_269, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_96, c_265])).
% 15.43/7.32  tff(c_489, plain, (![C_121, A_122]: (v3_pre_topc(C_121, k6_tmap_1(A_122, C_121)) | ~m1_subset_1(C_121, k1_zfmisc_1(u1_struct_0(k6_tmap_1(A_122, C_121)))) | ~m1_subset_1(C_121, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_pre_topc(A_122) | ~v2_pre_topc(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_186])).
% 15.43/7.32  tff(c_492, plain, (v3_pre_topc('#skF_3', k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_269, c_489])).
% 15.43/7.32  tff(c_494, plain, (v3_pre_topc('#skF_3', k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_96, c_95, c_96, c_492])).
% 15.43/7.32  tff(c_495, plain, (v3_pre_topc('#skF_3', k6_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_64, c_494])).
% 15.43/7.32  tff(c_159, plain, (![A_92, B_93]: (l1_pre_topc(k6_tmap_1(A_92, B_93)) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92) | ~v2_pre_topc(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_140])).
% 15.43/7.32  tff(c_162, plain, (![B_93]: (l1_pre_topc(k6_tmap_1('#skF_2', B_93)) | ~m1_subset_1(B_93, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_95, c_159])).
% 15.43/7.32  tff(c_164, plain, (![B_93]: (l1_pre_topc(k6_tmap_1('#skF_2', B_93)) | ~m1_subset_1(B_93, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_162])).
% 15.43/7.32  tff(c_168, plain, (![B_94]: (l1_pre_topc(k6_tmap_1('#skF_2', B_94)) | ~m1_subset_1(B_94, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_164])).
% 15.43/7.32  tff(c_172, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_96, c_168])).
% 15.43/7.32  tff(c_176, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_172, c_90])).
% 15.43/7.32  tff(c_270, plain, (k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_269, c_176])).
% 15.43/7.32  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (k8_relset_1(A_1, B_2, C_3, D_4)=k10_relat_1(C_3, D_4) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 15.43/7.32  tff(c_132, plain, (![D_4]: (k8_relset_1(k2_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')), k7_tmap_1('#skF_2', '#skF_3'), D_4)=k10_relat_1(k7_tmap_1('#skF_2', '#skF_3'), D_4))), inference(resolution, [status(thm)], [c_122, c_2])).
% 15.43/7.32  tff(c_242, plain, (![D_4]: (k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0(k6_tmap_1('#skF_2', '#skF_3')), k7_tmap_1('#skF_2', '#skF_3'), D_4)=k10_relat_1(k7_tmap_1('#skF_2', '#skF_3'), D_4))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_132])).
% 15.43/7.32  tff(c_339, plain, (![D_106]: (k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k7_tmap_1('#skF_2', '#skF_3'), D_106)=k10_relat_1(k7_tmap_1('#skF_2', '#skF_3'), D_106))), inference(demodulation, [status(thm), theory('equality')], [c_270, c_242])).
% 15.43/7.32  tff(c_209, plain, (![A_95, B_96]: (k7_tmap_1(A_95, B_96)=k6_partfun1(u1_struct_0(A_95)) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_125])).
% 15.43/7.32  tff(c_215, plain, (![B_96]: (k7_tmap_1('#skF_2', B_96)=k6_partfun1(u1_struct_0('#skF_2')) | ~m1_subset_1(B_96, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_95, c_209])).
% 15.43/7.32  tff(c_219, plain, (![B_96]: (k7_tmap_1('#skF_2', B_96)=k6_partfun1(k2_struct_0('#skF_2')) | ~m1_subset_1(B_96, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_95, c_215])).
% 15.43/7.32  tff(c_221, plain, (![B_97]: (k7_tmap_1('#skF_2', B_97)=k6_partfun1(k2_struct_0('#skF_2')) | ~m1_subset_1(B_97, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_219])).
% 15.43/7.32  tff(c_225, plain, (k6_partfun1(k2_struct_0('#skF_2'))=k7_tmap_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_96, c_221])).
% 15.43/7.32  tff(c_102, plain, (![A_77, B_78]: (k8_relset_1(A_77, A_77, k6_partfun1(A_77), B_78)=B_78 | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 15.43/7.32  tff(c_105, plain, (k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k6_partfun1(k2_struct_0('#skF_2')), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_96, c_102])).
% 15.43/7.32  tff(c_227, plain, (k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k7_tmap_1('#skF_2', '#skF_3'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_225, c_105])).
% 15.43/7.32  tff(c_345, plain, (k10_relat_1(k7_tmap_1('#skF_2', '#skF_3'), '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_339, c_227])).
% 15.43/7.32  tff(c_178, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0(k6_tmap_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_112])).
% 15.43/7.32  tff(c_319, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_270, c_178])).
% 15.43/7.32  tff(c_317, plain, (![D_4]: (k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k7_tmap_1('#skF_2', '#skF_3'), D_4)=k10_relat_1(k7_tmap_1('#skF_2', '#skF_3'), D_4))), inference(demodulation, [status(thm), theory('equality')], [c_270, c_242])).
% 15.43/7.32  tff(c_177, plain, (m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0(k6_tmap_1('#skF_2', '#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_122])).
% 15.43/7.32  tff(c_318, plain, (m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_270, c_177])).
% 15.43/7.32  tff(c_524, plain, (![A_126, B_127, C_128]: (k2_struct_0(A_126)!=k1_xboole_0 | v3_pre_topc('#skF_1'(A_126, B_127, C_128), B_127) | v5_pre_topc(C_128, A_126, B_127) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_126), u1_struct_0(B_127)))) | ~v1_funct_2(C_128, u1_struct_0(A_126), u1_struct_0(B_127)) | ~v1_funct_1(C_128) | ~l1_pre_topc(B_127) | ~l1_pre_topc(A_126))), inference(cnfTransformation, [status(thm)], [f_113])).
% 15.43/7.32  tff(c_532, plain, (![B_127, C_128]: (k2_struct_0('#skF_2')!=k1_xboole_0 | v3_pre_topc('#skF_1'('#skF_2', B_127, C_128), B_127) | v5_pre_topc(C_128, '#skF_2', B_127) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(B_127)))) | ~v1_funct_2(C_128, u1_struct_0('#skF_2'), u1_struct_0(B_127)) | ~v1_funct_1(C_128) | ~l1_pre_topc(B_127) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_95, c_524])).
% 15.43/7.32  tff(c_541, plain, (![B_127, C_128]: (k2_struct_0('#skF_2')!=k1_xboole_0 | v3_pre_topc('#skF_1'('#skF_2', B_127, C_128), B_127) | v5_pre_topc(C_128, '#skF_2', B_127) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(B_127)))) | ~v1_funct_2(C_128, k2_struct_0('#skF_2'), u1_struct_0(B_127)) | ~v1_funct_1(C_128) | ~l1_pre_topc(B_127))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_95, c_532])).
% 15.43/7.32  tff(c_545, plain, (k2_struct_0('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_541])).
% 15.43/7.32  tff(c_1233, plain, (![B_214, A_215, C_216, D_217]: (k2_struct_0(B_214)=k1_xboole_0 | v3_pre_topc(k8_relset_1(u1_struct_0(A_215), u1_struct_0(B_214), C_216, D_217), A_215) | ~v3_pre_topc(D_217, B_214) | ~m1_subset_1(D_217, k1_zfmisc_1(u1_struct_0(B_214))) | ~v5_pre_topc(C_216, A_215, B_214) | ~m1_subset_1(C_216, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_215), u1_struct_0(B_214)))) | ~v1_funct_2(C_216, u1_struct_0(A_215), u1_struct_0(B_214)) | ~v1_funct_1(C_216) | ~l1_pre_topc(B_214) | ~l1_pre_topc(A_215))), inference(cnfTransformation, [status(thm)], [f_113])).
% 15.43/7.32  tff(c_1241, plain, (![B_214, C_216, D_217]: (k2_struct_0(B_214)=k1_xboole_0 | v3_pre_topc(k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_214), C_216, D_217), '#skF_2') | ~v3_pre_topc(D_217, B_214) | ~m1_subset_1(D_217, k1_zfmisc_1(u1_struct_0(B_214))) | ~v5_pre_topc(C_216, '#skF_2', B_214) | ~m1_subset_1(C_216, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(B_214)))) | ~v1_funct_2(C_216, u1_struct_0('#skF_2'), u1_struct_0(B_214)) | ~v1_funct_1(C_216) | ~l1_pre_topc(B_214) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_95, c_1233])).
% 15.43/7.32  tff(c_1751, plain, (![B_271, C_272, D_273]: (k2_struct_0(B_271)=k1_xboole_0 | v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'), u1_struct_0(B_271), C_272, D_273), '#skF_2') | ~v3_pre_topc(D_273, B_271) | ~m1_subset_1(D_273, k1_zfmisc_1(u1_struct_0(B_271))) | ~v5_pre_topc(C_272, '#skF_2', B_271) | ~m1_subset_1(C_272, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(B_271)))) | ~v1_funct_2(C_272, k2_struct_0('#skF_2'), u1_struct_0(B_271)) | ~v1_funct_1(C_272) | ~l1_pre_topc(B_271))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_95, c_95, c_1241])).
% 15.43/7.32  tff(c_1755, plain, (![C_272, D_273]: (k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k1_xboole_0 | v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')), C_272, D_273), '#skF_2') | ~v3_pre_topc(D_273, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_273, k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))) | ~v5_pre_topc(C_272, '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(C_272, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_272, k2_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(C_272) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_269, c_1751])).
% 15.43/7.32  tff(c_1760, plain, (![C_272, D_273]: (k2_struct_0('#skF_2')=k1_xboole_0 | v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), C_272, D_273), '#skF_2') | ~v3_pre_topc(D_273, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_273, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v5_pre_topc(C_272, '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(C_272, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_272, k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_272))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_269, c_269, c_269, c_270, c_1755])).
% 15.43/7.32  tff(c_1772, plain, (![C_275, D_276]: (v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), C_275, D_276), '#skF_2') | ~v3_pre_topc(D_276, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_276, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v5_pre_topc(C_275, '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(C_275, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_275, k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_275))), inference(negUnitSimplification, [status(thm)], [c_545, c_1760])).
% 15.43/7.32  tff(c_1774, plain, (![D_276]: (v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k7_tmap_1('#skF_2', '#skF_3'), D_276), '#skF_2') | ~v3_pre_topc(D_276, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_276, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(k7_tmap_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_318, c_1772])).
% 15.43/7.32  tff(c_1778, plain, (![D_277]: (v3_pre_topc(k10_relat_1(k7_tmap_1('#skF_2', '#skF_3'), D_277), '#skF_2') | ~v3_pre_topc(D_277, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_277, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_319, c_110, c_317, c_1774])).
% 15.43/7.32  tff(c_1784, plain, (v3_pre_topc('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_345, c_1778])).
% 15.43/7.32  tff(c_1786, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_495, c_1784])).
% 15.43/7.32  tff(c_1788, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_1786])).
% 15.43/7.32  tff(c_1790, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_541])).
% 15.43/7.32  tff(c_1812, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1790, c_96])).
% 15.43/7.32  tff(c_1807, plain, (k7_tmap_1('#skF_2', '#skF_3')=k6_partfun1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1790, c_225])).
% 15.43/7.32  tff(c_2013, plain, (k10_relat_1(k6_partfun1(k1_xboole_0), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1807, c_345])).
% 15.43/7.32  tff(c_2015, plain, (v1_funct_1(k6_partfun1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1807, c_101])).
% 15.43/7.32  tff(c_1813, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1790, c_95])).
% 15.43/7.32  tff(c_1803, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1790, c_269])).
% 15.43/7.32  tff(c_44, plain, (![A_58, B_59]: (v1_funct_2(k7_tmap_1(A_58, B_59), u1_struct_0(A_58), u1_struct_0(k6_tmap_1(A_58, B_59))) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_155])).
% 15.43/7.32  tff(c_2025, plain, (v1_funct_2(k6_partfun1(k1_xboole_0), u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1807, c_44])).
% 15.43/7.32  tff(c_2035, plain, (v1_funct_2(k6_partfun1(k1_xboole_0), k1_xboole_0, k1_xboole_0) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1812, c_1813, c_1803, c_1813, c_2025])).
% 15.43/7.32  tff(c_2036, plain, (v1_funct_2(k6_partfun1(k1_xboole_0), k1_xboole_0, k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_64, c_2035])).
% 15.43/7.32  tff(c_2014, plain, (v5_pre_topc(k6_partfun1(k1_xboole_0), '#skF_2', k6_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1807, c_110])).
% 15.43/7.32  tff(c_439, plain, (![A_116, B_117]: (m1_subset_1(k7_tmap_1(A_116, B_117), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_116), u1_struct_0(k6_tmap_1(A_116, B_117))))) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116) | v2_struct_0(A_116))), inference(cnfTransformation, [status(thm)], [f_155])).
% 15.43/7.32  tff(c_453, plain, (![A_116, B_117, D_4]: (k8_relset_1(u1_struct_0(A_116), u1_struct_0(k6_tmap_1(A_116, B_117)), k7_tmap_1(A_116, B_117), D_4)=k10_relat_1(k7_tmap_1(A_116, B_117), D_4) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116) | v2_struct_0(A_116))), inference(resolution, [status(thm)], [c_439, c_2])).
% 15.43/7.32  tff(c_2019, plain, (![D_4]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')), k6_partfun1(k1_xboole_0), D_4)=k10_relat_1(k7_tmap_1('#skF_2', '#skF_3'), D_4) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1807, c_453])).
% 15.43/7.32  tff(c_2029, plain, (![D_4]: (k8_relset_1(k1_xboole_0, k1_xboole_0, k6_partfun1(k1_xboole_0), D_4)=k10_relat_1(k6_partfun1(k1_xboole_0), D_4) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1812, c_1813, c_1807, c_1803, c_1813, c_2019])).
% 15.43/7.32  tff(c_2030, plain, (![D_4]: (k8_relset_1(k1_xboole_0, k1_xboole_0, k6_partfun1(k1_xboole_0), D_4)=k10_relat_1(k6_partfun1(k1_xboole_0), D_4))), inference(negUnitSimplification, [status(thm)], [c_64, c_2029])).
% 15.43/7.32  tff(c_42, plain, (![A_58, B_59]: (m1_subset_1(k7_tmap_1(A_58, B_59), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_58), u1_struct_0(k6_tmap_1(A_58, B_59))))) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_155])).
% 15.43/7.32  tff(c_2022, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1807, c_42])).
% 15.43/7.32  tff(c_2032, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1812, c_1813, c_1803, c_1813, c_2022])).
% 15.43/7.32  tff(c_2033, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_64, c_2032])).
% 15.43/7.32  tff(c_2497, plain, (![A_324, B_325, C_326, D_327]: (k2_struct_0(A_324)!=k1_xboole_0 | v3_pre_topc(k8_relset_1(u1_struct_0(A_324), u1_struct_0(B_325), C_326, D_327), A_324) | ~v3_pre_topc(D_327, B_325) | ~m1_subset_1(D_327, k1_zfmisc_1(u1_struct_0(B_325))) | ~v5_pre_topc(C_326, A_324, B_325) | ~m1_subset_1(C_326, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_324), u1_struct_0(B_325)))) | ~v1_funct_2(C_326, u1_struct_0(A_324), u1_struct_0(B_325)) | ~v1_funct_1(C_326) | ~l1_pre_topc(B_325) | ~l1_pre_topc(A_324))), inference(cnfTransformation, [status(thm)], [f_113])).
% 15.43/7.32  tff(c_2503, plain, (![B_325, C_326, D_327]: (k2_struct_0('#skF_2')!=k1_xboole_0 | v3_pre_topc(k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_325), C_326, D_327), '#skF_2') | ~v3_pre_topc(D_327, B_325) | ~m1_subset_1(D_327, k1_zfmisc_1(u1_struct_0(B_325))) | ~v5_pre_topc(C_326, '#skF_2', B_325) | ~m1_subset_1(C_326, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, u1_struct_0(B_325)))) | ~v1_funct_2(C_326, u1_struct_0('#skF_2'), u1_struct_0(B_325)) | ~v1_funct_1(C_326) | ~l1_pre_topc(B_325) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1813, c_2497])).
% 15.43/7.32  tff(c_4645, plain, (![B_451, C_452, D_453]: (v3_pre_topc(k8_relset_1(k1_xboole_0, u1_struct_0(B_451), C_452, D_453), '#skF_2') | ~v3_pre_topc(D_453, B_451) | ~m1_subset_1(D_453, k1_zfmisc_1(u1_struct_0(B_451))) | ~v5_pre_topc(C_452, '#skF_2', B_451) | ~m1_subset_1(C_452, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, u1_struct_0(B_451)))) | ~v1_funct_2(C_452, k1_xboole_0, u1_struct_0(B_451)) | ~v1_funct_1(C_452) | ~l1_pre_topc(B_451))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1813, c_1813, c_1790, c_2503])).
% 15.43/7.32  tff(c_4655, plain, (![C_452, D_453]: (v3_pre_topc(k8_relset_1(k1_xboole_0, u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')), C_452, D_453), '#skF_2') | ~v3_pre_topc(D_453, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_453, k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))) | ~v5_pre_topc(C_452, '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(C_452, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~v1_funct_2(C_452, k1_xboole_0, u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(C_452) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1803, c_4645])).
% 15.43/7.32  tff(c_4762, plain, (![C_459, D_460]: (v3_pre_topc(k8_relset_1(k1_xboole_0, k1_xboole_0, C_459, D_460), '#skF_2') | ~v3_pre_topc(D_460, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_460, k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(C_459, '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(C_459, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~v1_funct_2(C_459, k1_xboole_0, k1_xboole_0) | ~v1_funct_1(C_459))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_1803, c_1803, c_1803, c_4655])).
% 15.43/7.32  tff(c_4768, plain, (![D_460]: (v3_pre_topc(k8_relset_1(k1_xboole_0, k1_xboole_0, k6_partfun1(k1_xboole_0), D_460), '#skF_2') | ~v3_pre_topc(D_460, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_460, k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(k6_partfun1(k1_xboole_0), '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k6_partfun1(k1_xboole_0), k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k6_partfun1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_2033, c_4762])).
% 15.43/7.32  tff(c_4779, plain, (![D_462]: (v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0), D_462), '#skF_2') | ~v3_pre_topc(D_462, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_462, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2015, c_2036, c_2014, c_2030, c_4768])).
% 15.43/7.32  tff(c_4791, plain, (v3_pre_topc('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2013, c_4779])).
% 15.43/7.32  tff(c_4793, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1812, c_495, c_4791])).
% 15.43/7.32  tff(c_4795, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_4793])).
% 15.43/7.32  tff(c_4797, plain, (~m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))))), inference(splitRight, [status(thm)], [c_121])).
% 15.43/7.32  tff(c_4834, plain, (~m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0(k6_tmap_1('#skF_2', '#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_4833, c_4797])).
% 15.43/7.32  tff(c_4919, plain, (~m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_4889, c_4834])).
% 15.43/7.32  tff(c_5076, plain, (![A_495, B_496]: (m1_subset_1(k7_tmap_1(A_495, B_496), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_495), u1_struct_0(k6_tmap_1(A_495, B_496))))) | ~m1_subset_1(B_496, k1_zfmisc_1(u1_struct_0(A_495))) | ~l1_pre_topc(A_495) | ~v2_pre_topc(A_495) | v2_struct_0(A_495))), inference(cnfTransformation, [status(thm)], [f_155])).
% 15.43/7.32  tff(c_5086, plain, (m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4888, c_5076])).
% 15.43/7.32  tff(c_5095, plain, (m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_96, c_95, c_95, c_5086])).
% 15.43/7.32  tff(c_5097, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_4919, c_5095])).
% 15.43/7.32  tff(c_5098, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_111])).
% 15.43/7.32  tff(c_5181, plain, (~m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))))) | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0(k6_tmap_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_5098, c_101, c_5154, c_95, c_110, c_5154, c_95, c_66])).
% 15.43/7.32  tff(c_5182, plain, (~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0(k6_tmap_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_5181])).
% 15.43/7.32  tff(c_5242, plain, (~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5200, c_5182])).
% 15.43/7.32  tff(c_5298, plain, (![A_523, B_524]: (v1_funct_2(k7_tmap_1(A_523, B_524), u1_struct_0(A_523), u1_struct_0(k6_tmap_1(A_523, B_524))) | ~m1_subset_1(B_524, k1_zfmisc_1(u1_struct_0(A_523))) | ~l1_pre_topc(A_523) | ~v2_pre_topc(A_523) | v2_struct_0(A_523))), inference(cnfTransformation, [status(thm)], [f_155])).
% 15.43/7.32  tff(c_5304, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5199, c_5298])).
% 15.43/7.32  tff(c_5311, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_96, c_95, c_95, c_5304])).
% 15.43/7.32  tff(c_5313, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_5242, c_5311])).
% 15.43/7.32  tff(c_5315, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0(k6_tmap_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_5181])).
% 15.43/7.32  tff(c_5099, plain, (~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_111])).
% 15.43/7.32  tff(c_5155, plain, (~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0(k6_tmap_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_5154, c_5099])).
% 15.43/7.32  tff(c_5317, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5315, c_5155])).
% 15.43/7.32  tff(c_5319, plain, (~v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', k6_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_76])).
% 15.43/7.32  tff(c_5435, plain, (![A_545, B_546]: (u1_struct_0(k6_tmap_1(A_545, B_546))=u1_struct_0(A_545) | ~m1_subset_1(B_546, k1_zfmisc_1(u1_struct_0(A_545))) | ~l1_pre_topc(A_545) | ~v2_pre_topc(A_545) | v2_struct_0(A_545))), inference(cnfTransformation, [status(thm)], [f_169])).
% 15.43/7.32  tff(c_5441, plain, (![B_546]: (u1_struct_0(k6_tmap_1('#skF_2', B_546))=u1_struct_0('#skF_2') | ~m1_subset_1(B_546, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_95, c_5435])).
% 15.43/7.32  tff(c_5445, plain, (![B_546]: (u1_struct_0(k6_tmap_1('#skF_2', B_546))=k2_struct_0('#skF_2') | ~m1_subset_1(B_546, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_95, c_5441])).
% 15.43/7.32  tff(c_5447, plain, (![B_547]: (u1_struct_0(k6_tmap_1('#skF_2', B_547))=k2_struct_0('#skF_2') | ~m1_subset_1(B_547, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_5445])).
% 15.43/7.32  tff(c_5451, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_96, c_5447])).
% 15.43/7.32  tff(c_5518, plain, (![A_551, B_552]: (v1_funct_2(k7_tmap_1(A_551, B_552), u1_struct_0(A_551), u1_struct_0(k6_tmap_1(A_551, B_552))) | ~m1_subset_1(B_552, k1_zfmisc_1(u1_struct_0(A_551))) | ~l1_pre_topc(A_551) | ~v2_pre_topc(A_551) | v2_struct_0(A_551))), inference(cnfTransformation, [status(thm)], [f_155])).
% 15.43/7.32  tff(c_5524, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5451, c_5518])).
% 15.43/7.32  tff(c_5531, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_96, c_95, c_95, c_5524])).
% 15.43/7.32  tff(c_5532, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_64, c_5531])).
% 15.43/7.32  tff(c_5617, plain, (![A_564, B_565]: (m1_subset_1(k7_tmap_1(A_564, B_565), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_564), u1_struct_0(k6_tmap_1(A_564, B_565))))) | ~m1_subset_1(B_565, k1_zfmisc_1(u1_struct_0(A_564))) | ~l1_pre_topc(A_564) | ~v2_pre_topc(A_564) | v2_struct_0(A_564))), inference(cnfTransformation, [status(thm)], [f_155])).
% 15.43/7.32  tff(c_5627, plain, (m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5451, c_5617])).
% 15.43/7.32  tff(c_5636, plain, (m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_96, c_95, c_95, c_5627])).
% 15.43/7.32  tff(c_5637, plain, (m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_5636])).
% 15.43/7.32  tff(c_5365, plain, (![A_535, B_536]: (v2_pre_topc(k6_tmap_1(A_535, B_536)) | ~m1_subset_1(B_536, k1_zfmisc_1(u1_struct_0(A_535))) | ~l1_pre_topc(A_535) | ~v2_pre_topc(A_535) | v2_struct_0(A_535))), inference(cnfTransformation, [status(thm)], [f_140])).
% 15.43/7.32  tff(c_5371, plain, (![B_536]: (v2_pre_topc(k6_tmap_1('#skF_2', B_536)) | ~m1_subset_1(B_536, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_95, c_5365])).
% 15.43/7.32  tff(c_5375, plain, (![B_536]: (v2_pre_topc(k6_tmap_1('#skF_2', B_536)) | ~m1_subset_1(B_536, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_5371])).
% 15.43/7.32  tff(c_5377, plain, (![B_537]: (v2_pre_topc(k6_tmap_1('#skF_2', B_537)) | ~m1_subset_1(B_537, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_5375])).
% 15.43/7.32  tff(c_5381, plain, (v2_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_96, c_5377])).
% 15.43/7.32  tff(c_5334, plain, (![A_532, B_533]: (l1_pre_topc(k6_tmap_1(A_532, B_533)) | ~m1_subset_1(B_533, k1_zfmisc_1(u1_struct_0(A_532))) | ~l1_pre_topc(A_532) | ~v2_pre_topc(A_532) | v2_struct_0(A_532))), inference(cnfTransformation, [status(thm)], [f_140])).
% 15.43/7.32  tff(c_5337, plain, (![B_533]: (l1_pre_topc(k6_tmap_1('#skF_2', B_533)) | ~m1_subset_1(B_533, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_95, c_5334])).
% 15.43/7.32  tff(c_5339, plain, (![B_533]: (l1_pre_topc(k6_tmap_1('#skF_2', B_533)) | ~m1_subset_1(B_533, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_5337])).
% 15.43/7.32  tff(c_5341, plain, (![B_534]: (l1_pre_topc(k6_tmap_1('#skF_2', B_534)) | ~m1_subset_1(B_534, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_5339])).
% 15.43/7.32  tff(c_5345, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_96, c_5341])).
% 15.43/7.32  tff(c_5318, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_76])).
% 15.43/7.32  tff(c_5573, plain, (![A_557, B_558]: (k6_tmap_1(A_557, B_558)=g1_pre_topc(u1_struct_0(A_557), u1_pre_topc(A_557)) | ~v3_pre_topc(B_558, A_557) | ~m1_subset_1(B_558, k1_zfmisc_1(u1_struct_0(A_557))) | ~l1_pre_topc(A_557) | ~v2_pre_topc(A_557) | v2_struct_0(A_557))), inference(cnfTransformation, [status(thm)], [f_200])).
% 15.43/7.32  tff(c_5577, plain, (![B_558]: (k6_tmap_1('#skF_2', B_558)=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v3_pre_topc(B_558, '#skF_2') | ~m1_subset_1(B_558, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_95, c_5573])).
% 15.43/7.32  tff(c_5581, plain, (![B_558]: (k6_tmap_1('#skF_2', B_558)=g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v3_pre_topc(B_558, '#skF_2') | ~m1_subset_1(B_558, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_95, c_5577])).
% 15.43/7.32  tff(c_5583, plain, (![B_559]: (k6_tmap_1('#skF_2', B_559)=g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v3_pre_topc(B_559, '#skF_2') | ~m1_subset_1(B_559, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_5581])).
% 15.43/7.32  tff(c_5586, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k6_tmap_1('#skF_2', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_96, c_5583])).
% 15.43/7.32  tff(c_5589, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k6_tmap_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5318, c_5586])).
% 15.43/7.32  tff(c_7043, plain, (![D_658, A_659, B_660]: (v5_pre_topc(D_658, A_659, B_660) | ~v5_pre_topc(D_658, g1_pre_topc(u1_struct_0(A_659), u1_pre_topc(A_659)), B_660) | ~m1_subset_1(D_658, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_659), u1_pre_topc(A_659))), u1_struct_0(B_660)))) | ~v1_funct_2(D_658, u1_struct_0(g1_pre_topc(u1_struct_0(A_659), u1_pre_topc(A_659))), u1_struct_0(B_660)) | ~m1_subset_1(D_658, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_659), u1_struct_0(B_660)))) | ~v1_funct_2(D_658, u1_struct_0(A_659), u1_struct_0(B_660)) | ~v1_funct_1(D_658) | ~l1_pre_topc(B_660) | ~v2_pre_topc(B_660) | ~l1_pre_topc(A_659) | ~v2_pre_topc(A_659))), inference(cnfTransformation, [status(thm)], [f_70])).
% 15.43/7.32  tff(c_7068, plain, (![D_658, B_660]: (v5_pre_topc(D_658, '#skF_2', B_660) | ~v5_pre_topc(D_658, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), B_660) | ~m1_subset_1(D_658, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0(B_660)))) | ~v1_funct_2(D_658, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0(B_660)) | ~m1_subset_1(D_658, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_660)))) | ~v1_funct_2(D_658, u1_struct_0('#skF_2'), u1_struct_0(B_660)) | ~v1_funct_1(D_658) | ~l1_pre_topc(B_660) | ~v2_pre_topc(B_660) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_95, c_7043])).
% 15.43/7.32  tff(c_7089, plain, (![D_661, B_662]: (v5_pre_topc(D_661, '#skF_2', B_662) | ~v5_pre_topc(D_661, k6_tmap_1('#skF_2', '#skF_3'), B_662) | ~m1_subset_1(D_661, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(B_662)))) | ~v1_funct_2(D_661, k2_struct_0('#skF_2'), u1_struct_0(B_662)) | ~v1_funct_1(D_661) | ~l1_pre_topc(B_662) | ~v2_pre_topc(B_662))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_95, c_95, c_5451, c_5589, c_95, c_5451, c_5589, c_5589, c_95, c_7068])).
% 15.43/7.32  tff(c_7098, plain, (![D_661]: (v5_pre_topc(D_661, '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~v5_pre_topc(D_661, k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_661, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~v1_funct_2(D_661, k2_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(D_661) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | ~v2_pre_topc(k6_tmap_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5451, c_7089])).
% 15.43/7.32  tff(c_7116, plain, (![D_664]: (v5_pre_topc(D_664, '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~v5_pre_topc(D_664, k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_664, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~v1_funct_2(D_664, k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(D_664))), inference(demodulation, [status(thm), theory('equality')], [c_5381, c_5345, c_5451, c_7098])).
% 15.43/7.32  tff(c_7119, plain, (v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(k7_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_5637, c_7116])).
% 15.43/7.32  tff(c_7122, plain, (v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_5532, c_7119])).
% 15.43/7.32  tff(c_7123, plain, (~v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_5319, c_7122])).
% 15.43/7.32  tff(c_5723, plain, (![A_573, B_574, C_575]: (k2_struct_0(A_573)!=k1_xboole_0 | v3_pre_topc('#skF_1'(A_573, B_574, C_575), B_574) | v5_pre_topc(C_575, A_573, B_574) | ~m1_subset_1(C_575, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_573), u1_struct_0(B_574)))) | ~v1_funct_2(C_575, u1_struct_0(A_573), u1_struct_0(B_574)) | ~v1_funct_1(C_575) | ~l1_pre_topc(B_574) | ~l1_pre_topc(A_573))), inference(cnfTransformation, [status(thm)], [f_113])).
% 15.43/7.32  tff(c_5731, plain, (![B_574, C_575]: (k2_struct_0('#skF_2')!=k1_xboole_0 | v3_pre_topc('#skF_1'('#skF_2', B_574, C_575), B_574) | v5_pre_topc(C_575, '#skF_2', B_574) | ~m1_subset_1(C_575, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(B_574)))) | ~v1_funct_2(C_575, u1_struct_0('#skF_2'), u1_struct_0(B_574)) | ~v1_funct_1(C_575) | ~l1_pre_topc(B_574) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_95, c_5723])).
% 15.43/7.32  tff(c_5740, plain, (![B_574, C_575]: (k2_struct_0('#skF_2')!=k1_xboole_0 | v3_pre_topc('#skF_1'('#skF_2', B_574, C_575), B_574) | v5_pre_topc(C_575, '#skF_2', B_574) | ~m1_subset_1(C_575, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(B_574)))) | ~v1_funct_2(C_575, k2_struct_0('#skF_2'), u1_struct_0(B_574)) | ~v1_funct_1(C_575) | ~l1_pre_topc(B_574))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_95, c_5731])).
% 15.43/7.32  tff(c_5759, plain, (k2_struct_0('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_5740])).
% 15.43/7.32  tff(c_5349, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_5345, c_90])).
% 15.43/7.32  tff(c_5452, plain, (k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5451, c_5349])).
% 15.43/7.32  tff(c_5795, plain, (![B_582, A_583, C_584]: (k2_struct_0(B_582)=k1_xboole_0 | v3_pre_topc('#skF_1'(A_583, B_582, C_584), B_582) | v5_pre_topc(C_584, A_583, B_582) | ~m1_subset_1(C_584, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_583), u1_struct_0(B_582)))) | ~v1_funct_2(C_584, u1_struct_0(A_583), u1_struct_0(B_582)) | ~v1_funct_1(C_584) | ~l1_pre_topc(B_582) | ~l1_pre_topc(A_583))), inference(cnfTransformation, [status(thm)], [f_113])).
% 15.43/7.32  tff(c_5801, plain, (![A_583, C_584]: (k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k1_xboole_0 | v3_pre_topc('#skF_1'(A_583, k6_tmap_1('#skF_2', '#skF_3'), C_584), k6_tmap_1('#skF_2', '#skF_3')) | v5_pre_topc(C_584, A_583, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(C_584, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_583), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_584, u1_struct_0(A_583), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(C_584) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc(A_583))), inference(superposition, [status(thm), theory('equality')], [c_5451, c_5795])).
% 15.43/7.32  tff(c_5810, plain, (![A_583, C_584]: (k2_struct_0('#skF_2')=k1_xboole_0 | v3_pre_topc('#skF_1'(A_583, k6_tmap_1('#skF_2', '#skF_3'), C_584), k6_tmap_1('#skF_2', '#skF_3')) | v5_pre_topc(C_584, A_583, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(C_584, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_583), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_584, u1_struct_0(A_583), k2_struct_0('#skF_2')) | ~v1_funct_1(C_584) | ~l1_pre_topc(A_583))), inference(demodulation, [status(thm), theory('equality')], [c_5345, c_5451, c_5452, c_5801])).
% 15.43/7.32  tff(c_5976, plain, (![A_606, C_607]: (v3_pre_topc('#skF_1'(A_606, k6_tmap_1('#skF_2', '#skF_3'), C_607), k6_tmap_1('#skF_2', '#skF_3')) | v5_pre_topc(C_607, A_606, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(C_607, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_606), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_607, u1_struct_0(A_606), k2_struct_0('#skF_2')) | ~v1_funct_1(C_607) | ~l1_pre_topc(A_606))), inference(negUnitSimplification, [status(thm)], [c_5759, c_5810])).
% 15.43/7.32  tff(c_5979, plain, (![C_607]: (v3_pre_topc('#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), C_607), k6_tmap_1('#skF_2', '#skF_3')) | v5_pre_topc(C_607, k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(C_607, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_607, u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')), k2_struct_0('#skF_2')) | ~v1_funct_1(C_607) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5451, c_5976])).
% 15.43/7.32  tff(c_5984, plain, (![C_607]: (v3_pre_topc('#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), C_607), k6_tmap_1('#skF_2', '#skF_3')) | v5_pre_topc(C_607, k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(C_607, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_607, k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_607))), inference(demodulation, [status(thm), theory('equality')], [c_5345, c_5451, c_5979])).
% 15.43/7.32  tff(c_5645, plain, (![D_4]: (k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k7_tmap_1('#skF_2', '#skF_3'), D_4)=k10_relat_1(k7_tmap_1('#skF_2', '#skF_3'), D_4))), inference(resolution, [status(thm)], [c_5637, c_2])).
% 15.43/7.32  tff(c_5400, plain, (![A_541, B_542]: (k7_tmap_1(A_541, B_542)=k6_partfun1(u1_struct_0(A_541)) | ~m1_subset_1(B_542, k1_zfmisc_1(u1_struct_0(A_541))) | ~l1_pre_topc(A_541) | ~v2_pre_topc(A_541) | v2_struct_0(A_541))), inference(cnfTransformation, [status(thm)], [f_125])).
% 15.43/7.32  tff(c_5406, plain, (![B_542]: (k7_tmap_1('#skF_2', B_542)=k6_partfun1(u1_struct_0('#skF_2')) | ~m1_subset_1(B_542, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_95, c_5400])).
% 15.43/7.32  tff(c_5410, plain, (![B_542]: (k7_tmap_1('#skF_2', B_542)=k6_partfun1(k2_struct_0('#skF_2')) | ~m1_subset_1(B_542, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_95, c_5406])).
% 15.43/7.32  tff(c_5412, plain, (![B_543]: (k7_tmap_1('#skF_2', B_543)=k6_partfun1(k2_struct_0('#skF_2')) | ~m1_subset_1(B_543, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_5410])).
% 15.43/7.32  tff(c_5416, plain, (k6_partfun1(k2_struct_0('#skF_2'))=k7_tmap_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_96, c_5412])).
% 15.43/7.32  tff(c_5987, plain, (![B_608, A_609, C_610]: (k2_struct_0(B_608)=k1_xboole_0 | m1_subset_1('#skF_1'(A_609, B_608, C_610), k1_zfmisc_1(u1_struct_0(B_608))) | v5_pre_topc(C_610, A_609, B_608) | ~m1_subset_1(C_610, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_609), u1_struct_0(B_608)))) | ~v1_funct_2(C_610, u1_struct_0(A_609), u1_struct_0(B_608)) | ~v1_funct_1(C_610) | ~l1_pre_topc(B_608) | ~l1_pre_topc(A_609))), inference(cnfTransformation, [status(thm)], [f_113])).
% 15.43/7.32  tff(c_5993, plain, (![A_609, C_610]: (k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k1_xboole_0 | m1_subset_1('#skF_1'(A_609, k6_tmap_1('#skF_2', '#skF_3'), C_610), k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))) | v5_pre_topc(C_610, A_609, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(C_610, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_609), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_610, u1_struct_0(A_609), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(C_610) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc(A_609))), inference(superposition, [status(thm), theory('equality')], [c_5451, c_5987])).
% 15.43/7.32  tff(c_6002, plain, (![A_609, C_610]: (k2_struct_0('#skF_2')=k1_xboole_0 | m1_subset_1('#skF_1'(A_609, k6_tmap_1('#skF_2', '#skF_3'), C_610), k1_zfmisc_1(k2_struct_0('#skF_2'))) | v5_pre_topc(C_610, A_609, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(C_610, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_609), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_610, u1_struct_0(A_609), k2_struct_0('#skF_2')) | ~v1_funct_1(C_610) | ~l1_pre_topc(A_609))), inference(demodulation, [status(thm), theory('equality')], [c_5345, c_5451, c_5451, c_5452, c_5993])).
% 15.43/7.32  tff(c_6003, plain, (![A_609, C_610]: (m1_subset_1('#skF_1'(A_609, k6_tmap_1('#skF_2', '#skF_3'), C_610), k1_zfmisc_1(k2_struct_0('#skF_2'))) | v5_pre_topc(C_610, A_609, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(C_610, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_609), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_610, u1_struct_0(A_609), k2_struct_0('#skF_2')) | ~v1_funct_1(C_610) | ~l1_pre_topc(A_609))), inference(negUnitSimplification, [status(thm)], [c_5759, c_6002])).
% 15.43/7.32  tff(c_6986, plain, (![A_654, C_655]: (m1_subset_1('#skF_1'(A_654, k6_tmap_1('#skF_2', '#skF_3'), C_655), k1_zfmisc_1(k2_struct_0('#skF_2'))) | v5_pre_topc(C_655, A_654, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(C_655, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_654), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_655, u1_struct_0(A_654), k2_struct_0('#skF_2')) | ~v1_funct_1(C_655) | ~l1_pre_topc(A_654))), inference(negUnitSimplification, [status(thm)], [c_5759, c_6002])).
% 15.43/7.32  tff(c_5340, plain, (![B_533]: (l1_pre_topc(k6_tmap_1('#skF_2', B_533)) | ~m1_subset_1(B_533, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_5339])).
% 15.43/7.32  tff(c_7126, plain, (![A_665, C_666]: (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_1'(A_665, k6_tmap_1('#skF_2', '#skF_3'), C_666))) | v5_pre_topc(C_666, A_665, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(C_666, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_665), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_666, u1_struct_0(A_665), k2_struct_0('#skF_2')) | ~v1_funct_1(C_666) | ~l1_pre_topc(A_665))), inference(resolution, [status(thm)], [c_6986, c_5340])).
% 15.43/7.32  tff(c_7132, plain, (![C_666]: (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), C_666))) | v5_pre_topc(C_666, k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(C_666, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_666, u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')), k2_struct_0('#skF_2')) | ~v1_funct_1(C_666) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5451, c_7126])).
% 15.43/7.32  tff(c_7397, plain, (![C_682]: (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), C_682))) | v5_pre_topc(C_682, k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(C_682, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_682, k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_682))), inference(demodulation, [status(thm), theory('equality')], [c_5345, c_5451, c_7132])).
% 15.43/7.32  tff(c_7400, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3')))) | v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(k7_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_5637, c_7397])).
% 15.43/7.32  tff(c_7403, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3')))) | v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_5532, c_7400])).
% 15.43/7.32  tff(c_7404, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_7123, c_7403])).
% 15.43/7.32  tff(c_7408, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'))))=k2_struct_0(k6_tmap_1('#skF_2', '#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_7404, c_90])).
% 15.43/7.32  tff(c_7581, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'))), u1_struct_0('#skF_2'), k2_struct_0(k6_tmap_1('#skF_2', '#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'))))) | ~m1_subset_1('#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7408, c_44])).
% 15.43/7.32  tff(c_7726, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'))), k2_struct_0('#skF_2'), k2_struct_0(k6_tmap_1('#skF_2', '#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'))))) | ~m1_subset_1('#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3')), k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_95, c_95, c_7581])).
% 15.43/7.32  tff(c_7727, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'))), k2_struct_0('#skF_2'), k2_struct_0(k6_tmap_1('#skF_2', '#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'))))) | ~m1_subset_1('#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3')), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_64, c_7726])).
% 15.43/7.32  tff(c_7743, plain, (~m1_subset_1('#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3')), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_7727])).
% 15.43/7.32  tff(c_7746, plain, (v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')), k2_struct_0('#skF_2')))) | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')), k2_struct_0('#skF_2')) | ~v1_funct_1(k7_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_6003, c_7743])).
% 15.43/7.32  tff(c_7749, plain, (v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5345, c_101, c_5532, c_5451, c_5637, c_5451, c_7746])).
% 15.43/7.32  tff(c_7751, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7123, c_7749])).
% 15.43/7.32  tff(c_7753, plain, (m1_subset_1('#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3')), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_7727])).
% 15.43/7.32  tff(c_4, plain, (![A_5, B_6]: (k8_relset_1(A_5, A_5, k6_partfun1(A_5), B_6)=B_6 | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 15.43/7.32  tff(c_7782, plain, (k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k6_partfun1(k2_struct_0('#skF_2')), '#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3')))='#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_7753, c_4])).
% 15.43/7.32  tff(c_7795, plain, (k10_relat_1(k7_tmap_1('#skF_2', '#skF_3'), '#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3')))='#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5645, c_5416, c_7782])).
% 15.43/7.32  tff(c_6407, plain, (![B_629, A_630, C_631]: (k2_struct_0(B_629)=k1_xboole_0 | ~v3_pre_topc(k8_relset_1(u1_struct_0(A_630), u1_struct_0(B_629), C_631, '#skF_1'(A_630, B_629, C_631)), A_630) | v5_pre_topc(C_631, A_630, B_629) | ~m1_subset_1(C_631, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_630), u1_struct_0(B_629)))) | ~v1_funct_2(C_631, u1_struct_0(A_630), u1_struct_0(B_629)) | ~v1_funct_1(C_631) | ~l1_pre_topc(B_629) | ~l1_pre_topc(A_630))), inference(cnfTransformation, [status(thm)], [f_113])).
% 15.43/7.32  tff(c_6423, plain, (![A_630, C_631]: (k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k1_xboole_0 | ~v3_pre_topc(k8_relset_1(u1_struct_0(A_630), k2_struct_0('#skF_2'), C_631, '#skF_1'(A_630, k6_tmap_1('#skF_2', '#skF_3'), C_631)), A_630) | v5_pre_topc(C_631, A_630, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(C_631, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_630), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))))) | ~v1_funct_2(C_631, u1_struct_0(A_630), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(C_631) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc(A_630))), inference(superposition, [status(thm), theory('equality')], [c_5451, c_6407])).
% 15.43/7.32  tff(c_6437, plain, (![A_630, C_631]: (k2_struct_0('#skF_2')=k1_xboole_0 | ~v3_pre_topc(k8_relset_1(u1_struct_0(A_630), k2_struct_0('#skF_2'), C_631, '#skF_1'(A_630, k6_tmap_1('#skF_2', '#skF_3'), C_631)), A_630) | v5_pre_topc(C_631, A_630, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(C_631, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_630), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_631, u1_struct_0(A_630), k2_struct_0('#skF_2')) | ~v1_funct_1(C_631) | ~l1_pre_topc(A_630))), inference(demodulation, [status(thm), theory('equality')], [c_5345, c_5451, c_5451, c_5452, c_6423])).
% 15.43/7.32  tff(c_11547, plain, (![A_774, C_775]: (~v3_pre_topc(k8_relset_1(u1_struct_0(A_774), k2_struct_0('#skF_2'), C_775, '#skF_1'(A_774, k6_tmap_1('#skF_2', '#skF_3'), C_775)), A_774) | v5_pre_topc(C_775, A_774, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(C_775, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_774), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_775, u1_struct_0(A_774), k2_struct_0('#skF_2')) | ~v1_funct_1(C_775) | ~l1_pre_topc(A_774))), inference(negUnitSimplification, [status(thm)], [c_5759, c_6437])).
% 15.43/7.32  tff(c_11562, plain, (![C_775]: (~v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), C_775, '#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), C_775)), k6_tmap_1('#skF_2', '#skF_3')) | v5_pre_topc(C_775, k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(C_775, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_775, u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')), k2_struct_0('#skF_2')) | ~v1_funct_1(C_775) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5451, c_11547])).
% 15.43/7.32  tff(c_12790, plain, (![C_829]: (~v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), C_829, '#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), C_829)), k6_tmap_1('#skF_2', '#skF_3')) | v5_pre_topc(C_829, k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(C_829, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_829, k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_829))), inference(demodulation, [status(thm), theory('equality')], [c_5345, c_5451, c_5451, c_11562])).
% 15.43/7.32  tff(c_12798, plain, (~v3_pre_topc(k10_relat_1(k7_tmap_1('#skF_2', '#skF_3'), '#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'))), k6_tmap_1('#skF_2', '#skF_3')) | v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(k7_tmap_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5645, c_12790])).
% 15.43/7.32  tff(c_12801, plain, (~v3_pre_topc('#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3')), k6_tmap_1('#skF_2', '#skF_3')) | v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_5532, c_5637, c_7795, c_12798])).
% 15.43/7.32  tff(c_12802, plain, (~v3_pre_topc('#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3')), k6_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_7123, c_12801])).
% 15.43/7.32  tff(c_12830, plain, (v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(k7_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_5984, c_12802])).
% 15.43/7.32  tff(c_12833, plain, (v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_5532, c_5637, c_12830])).
% 15.43/7.32  tff(c_12835, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7123, c_12833])).
% 15.43/7.32  tff(c_12837, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_5740])).
% 15.43/7.32  tff(c_12854, plain, (k7_tmap_1('#skF_2', '#skF_3')=k6_partfun1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12837, c_5416])).
% 15.43/7.32  tff(c_12963, plain, (~v5_pre_topc(k6_partfun1(k1_xboole_0), '#skF_2', k6_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12854, c_5319])).
% 15.43/7.32  tff(c_12964, plain, (v1_funct_1(k6_partfun1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12854, c_101])).
% 15.43/7.32  tff(c_12859, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12837, c_96])).
% 15.43/7.32  tff(c_12860, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12837, c_95])).
% 15.43/7.32  tff(c_12850, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12837, c_5451])).
% 15.43/7.32  tff(c_13020, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), k1_xboole_0) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12850, c_44])).
% 15.43/7.32  tff(c_13070, plain, (v1_funct_2(k6_partfun1(k1_xboole_0), k1_xboole_0, k1_xboole_0) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_12859, c_12860, c_12854, c_12860, c_13020])).
% 15.43/7.32  tff(c_13071, plain, (v1_funct_2(k6_partfun1(k1_xboole_0), k1_xboole_0, k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_64, c_13070])).
% 15.43/7.32  tff(c_13007, plain, (m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), k1_xboole_0))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12850, c_42])).
% 15.43/7.32  tff(c_13058, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_12859, c_12860, c_12854, c_12860, c_13007])).
% 15.43/7.32  tff(c_13059, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_64, c_13058])).
% 15.43/7.32  tff(c_12849, plain, (k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12837, c_5452])).
% 15.43/7.32  tff(c_22, plain, (![A_31, B_43, C_49]: (k2_struct_0(A_31)!=k1_xboole_0 | v3_pre_topc('#skF_1'(A_31, B_43, C_49), B_43) | v5_pre_topc(C_49, A_31, B_43) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_31), u1_struct_0(B_43)))) | ~v1_funct_2(C_49, u1_struct_0(A_31), u1_struct_0(B_43)) | ~v1_funct_1(C_49) | ~l1_pre_topc(B_43) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_113])).
% 15.43/7.32  tff(c_12995, plain, (![A_31, C_49]: (k2_struct_0(A_31)!=k1_xboole_0 | v3_pre_topc('#skF_1'(A_31, k6_tmap_1('#skF_2', '#skF_3'), C_49), k6_tmap_1('#skF_2', '#skF_3')) | v5_pre_topc(C_49, A_31, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_31), k1_xboole_0))) | ~v1_funct_2(C_49, u1_struct_0(A_31), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(C_49) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc(A_31))), inference(superposition, [status(thm), theory('equality')], [c_12850, c_22])).
% 15.43/7.32  tff(c_13049, plain, (![A_31, C_49]: (k2_struct_0(A_31)!=k1_xboole_0 | v3_pre_topc('#skF_1'(A_31, k6_tmap_1('#skF_2', '#skF_3'), C_49), k6_tmap_1('#skF_2', '#skF_3')) | v5_pre_topc(C_49, A_31, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_31), k1_xboole_0))) | ~v1_funct_2(C_49, u1_struct_0(A_31), k1_xboole_0) | ~v1_funct_1(C_49) | ~l1_pre_topc(A_31))), inference(demodulation, [status(thm), theory('equality')], [c_5345, c_12850, c_12995])).
% 15.43/7.32  tff(c_13175, plain, (![A_843, B_844, C_845]: (k2_struct_0(A_843)!=k1_xboole_0 | m1_subset_1('#skF_1'(A_843, B_844, C_845), k1_zfmisc_1(u1_struct_0(B_844))) | v5_pre_topc(C_845, A_843, B_844) | ~m1_subset_1(C_845, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_843), u1_struct_0(B_844)))) | ~v1_funct_2(C_845, u1_struct_0(A_843), u1_struct_0(B_844)) | ~v1_funct_1(C_845) | ~l1_pre_topc(B_844) | ~l1_pre_topc(A_843))), inference(cnfTransformation, [status(thm)], [f_113])).
% 15.43/7.32  tff(c_13179, plain, (![A_843, C_845]: (k2_struct_0(A_843)!=k1_xboole_0 | m1_subset_1('#skF_1'(A_843, k6_tmap_1('#skF_2', '#skF_3'), C_845), k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))) | v5_pre_topc(C_845, A_843, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(C_845, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_843), k1_xboole_0))) | ~v1_funct_2(C_845, u1_struct_0(A_843), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(C_845) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc(A_843))), inference(superposition, [status(thm), theory('equality')], [c_12850, c_13175])).
% 15.43/7.32  tff(c_13189, plain, (![A_843, C_845]: (k2_struct_0(A_843)!=k1_xboole_0 | m1_subset_1('#skF_1'(A_843, k6_tmap_1('#skF_2', '#skF_3'), C_845), k1_zfmisc_1(k1_xboole_0)) | v5_pre_topc(C_845, A_843, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(C_845, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_843), k1_xboole_0))) | ~v1_funct_2(C_845, u1_struct_0(A_843), k1_xboole_0) | ~v1_funct_1(C_845) | ~l1_pre_topc(A_843))), inference(demodulation, [status(thm), theory('equality')], [c_5345, c_12850, c_12850, c_13179])).
% 15.43/7.32  tff(c_12871, plain, (![B_43, C_49]: (k2_struct_0('#skF_2')!=k1_xboole_0 | v3_pre_topc('#skF_1'('#skF_2', B_43, C_49), B_43) | v5_pre_topc(C_49, '#skF_2', B_43) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, u1_struct_0(B_43)))) | ~v1_funct_2(C_49, u1_struct_0('#skF_2'), u1_struct_0(B_43)) | ~v1_funct_1(C_49) | ~l1_pre_topc(B_43) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_12860, c_22])).
% 15.43/7.32  tff(c_13342, plain, (![B_861, C_862]: (v3_pre_topc('#skF_1'('#skF_2', B_861, C_862), B_861) | v5_pre_topc(C_862, '#skF_2', B_861) | ~m1_subset_1(C_862, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, u1_struct_0(B_861)))) | ~v1_funct_2(C_862, k1_xboole_0, u1_struct_0(B_861)) | ~v1_funct_1(C_862) | ~l1_pre_topc(B_861))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_12860, c_12837, c_12871])).
% 15.43/7.32  tff(c_13348, plain, (![C_862]: (v3_pre_topc('#skF_1'('#skF_2', '#skF_2', C_862), '#skF_2') | v5_pre_topc(C_862, '#skF_2', '#skF_2') | ~m1_subset_1(C_862, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~v1_funct_2(C_862, k1_xboole_0, u1_struct_0('#skF_2')) | ~v1_funct_1(C_862) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_12860, c_13342])).
% 15.43/7.32  tff(c_13354, plain, (![C_863]: (v3_pre_topc('#skF_1'('#skF_2', '#skF_2', C_863), '#skF_2') | v5_pre_topc(C_863, '#skF_2', '#skF_2') | ~m1_subset_1(C_863, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~v1_funct_2(C_863, k1_xboole_0, k1_xboole_0) | ~v1_funct_1(C_863))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_12860, c_13348])).
% 15.43/7.32  tff(c_13357, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_2', k6_partfun1(k1_xboole_0)), '#skF_2') | v5_pre_topc(k6_partfun1(k1_xboole_0), '#skF_2', '#skF_2') | ~v1_funct_2(k6_partfun1(k1_xboole_0), k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_13059, c_13354])).
% 15.43/7.32  tff(c_13360, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_2', k6_partfun1(k1_xboole_0)), '#skF_2') | v5_pre_topc(k6_partfun1(k1_xboole_0), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12964, c_13071, c_13357])).
% 15.43/7.32  tff(c_13361, plain, (v5_pre_topc(k6_partfun1(k1_xboole_0), '#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_13360])).
% 15.43/7.32  tff(c_12845, plain, (g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2'))=k6_tmap_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12837, c_5589])).
% 15.43/7.32  tff(c_13779, plain, (![D_893, A_894, B_895]: (v5_pre_topc(D_893, g1_pre_topc(u1_struct_0(A_894), u1_pre_topc(A_894)), B_895) | ~v5_pre_topc(D_893, A_894, B_895) | ~m1_subset_1(D_893, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_894), u1_pre_topc(A_894))), u1_struct_0(B_895)))) | ~v1_funct_2(D_893, u1_struct_0(g1_pre_topc(u1_struct_0(A_894), u1_pre_topc(A_894))), u1_struct_0(B_895)) | ~m1_subset_1(D_893, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_894), u1_struct_0(B_895)))) | ~v1_funct_2(D_893, u1_struct_0(A_894), u1_struct_0(B_895)) | ~v1_funct_1(D_893) | ~l1_pre_topc(B_895) | ~v2_pre_topc(B_895) | ~l1_pre_topc(A_894) | ~v2_pre_topc(A_894))), inference(cnfTransformation, [status(thm)], [f_70])).
% 15.43/7.32  tff(c_13788, plain, (![D_893, B_895]: (v5_pre_topc(D_893, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), B_895) | ~v5_pre_topc(D_893, '#skF_2', B_895) | ~m1_subset_1(D_893, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2'))), u1_struct_0(B_895)))) | ~v1_funct_2(D_893, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0(B_895)) | ~m1_subset_1(D_893, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_895)))) | ~v1_funct_2(D_893, u1_struct_0('#skF_2'), u1_struct_0(B_895)) | ~v1_funct_1(D_893) | ~l1_pre_topc(B_895) | ~v2_pre_topc(B_895) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_12860, c_13779])).
% 15.43/7.32  tff(c_14235, plain, (![D_903, B_904]: (v5_pre_topc(D_903, k6_tmap_1('#skF_2', '#skF_3'), B_904) | ~v5_pre_topc(D_903, '#skF_2', B_904) | ~m1_subset_1(D_903, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, u1_struct_0(B_904)))) | ~v1_funct_2(D_903, k1_xboole_0, u1_struct_0(B_904)) | ~v1_funct_1(D_903) | ~l1_pre_topc(B_904) | ~v2_pre_topc(B_904))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_12860, c_12860, c_12850, c_12845, c_12860, c_12850, c_12845, c_12845, c_12860, c_13788])).
% 15.43/7.32  tff(c_14247, plain, (![D_903]: (v5_pre_topc(D_903, k6_tmap_1('#skF_2', '#skF_3'), '#skF_2') | ~v5_pre_topc(D_903, '#skF_2', '#skF_2') | ~m1_subset_1(D_903, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~v1_funct_2(D_903, k1_xboole_0, u1_struct_0('#skF_2')) | ~v1_funct_1(D_903) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_12860, c_14235])).
% 15.43/7.32  tff(c_14323, plain, (![D_907]: (v5_pre_topc(D_907, k6_tmap_1('#skF_2', '#skF_3'), '#skF_2') | ~v5_pre_topc(D_907, '#skF_2', '#skF_2') | ~m1_subset_1(D_907, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~v1_funct_2(D_907, k1_xboole_0, k1_xboole_0) | ~v1_funct_1(D_907))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_12860, c_14247])).
% 15.43/7.32  tff(c_14326, plain, (v5_pre_topc(k6_partfun1(k1_xboole_0), k6_tmap_1('#skF_2', '#skF_3'), '#skF_2') | ~v5_pre_topc(k6_partfun1(k1_xboole_0), '#skF_2', '#skF_2') | ~v1_funct_2(k6_partfun1(k1_xboole_0), k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_13059, c_14323])).
% 15.43/7.32  tff(c_14329, plain, (v5_pre_topc(k6_partfun1(k1_xboole_0), k6_tmap_1('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12964, c_13071, c_13361, c_14326])).
% 15.43/7.32  tff(c_5631, plain, (![A_564, B_565, D_4]: (k8_relset_1(u1_struct_0(A_564), u1_struct_0(k6_tmap_1(A_564, B_565)), k7_tmap_1(A_564, B_565), D_4)=k10_relat_1(k7_tmap_1(A_564, B_565), D_4) | ~m1_subset_1(B_565, k1_zfmisc_1(u1_struct_0(A_564))) | ~l1_pre_topc(A_564) | ~v2_pre_topc(A_564) | v2_struct_0(A_564))), inference(resolution, [status(thm)], [c_5617, c_2])).
% 15.43/7.32  tff(c_13001, plain, (![D_4]: (k8_relset_1(u1_struct_0('#skF_2'), k1_xboole_0, k7_tmap_1('#skF_2', '#skF_3'), D_4)=k10_relat_1(k7_tmap_1('#skF_2', '#skF_3'), D_4) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_12850, c_5631])).
% 15.43/7.32  tff(c_13053, plain, (![D_4]: (k8_relset_1(k1_xboole_0, k1_xboole_0, k6_partfun1(k1_xboole_0), D_4)=k10_relat_1(k6_partfun1(k1_xboole_0), D_4) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_12859, c_12860, c_12854, c_12854, c_12860, c_13001])).
% 15.43/7.32  tff(c_13054, plain, (![D_4]: (k8_relset_1(k1_xboole_0, k1_xboole_0, k6_partfun1(k1_xboole_0), D_4)=k10_relat_1(k6_partfun1(k1_xboole_0), D_4))), inference(negUnitSimplification, [status(thm)], [c_64, c_13053])).
% 15.43/7.32  tff(c_13455, plain, (![A_871, B_872, C_873, D_874]: (k2_struct_0(A_871)!=k1_xboole_0 | v3_pre_topc(k8_relset_1(u1_struct_0(A_871), u1_struct_0(B_872), C_873, D_874), A_871) | ~v3_pre_topc(D_874, B_872) | ~m1_subset_1(D_874, k1_zfmisc_1(u1_struct_0(B_872))) | ~v5_pre_topc(C_873, A_871, B_872) | ~m1_subset_1(C_873, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_871), u1_struct_0(B_872)))) | ~v1_funct_2(C_873, u1_struct_0(A_871), u1_struct_0(B_872)) | ~v1_funct_1(C_873) | ~l1_pre_topc(B_872) | ~l1_pre_topc(A_871))), inference(cnfTransformation, [status(thm)], [f_113])).
% 15.43/7.32  tff(c_13463, plain, (![A_871, C_873, D_874]: (k2_struct_0(A_871)!=k1_xboole_0 | v3_pre_topc(k8_relset_1(u1_struct_0(A_871), u1_struct_0('#skF_2'), C_873, D_874), A_871) | ~v3_pre_topc(D_874, '#skF_2') | ~m1_subset_1(D_874, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v5_pre_topc(C_873, A_871, '#skF_2') | ~m1_subset_1(C_873, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_871), k1_xboole_0))) | ~v1_funct_2(C_873, u1_struct_0(A_871), u1_struct_0('#skF_2')) | ~v1_funct_1(C_873) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_871))), inference(superposition, [status(thm), theory('equality')], [c_12860, c_13455])).
% 15.43/7.32  tff(c_20642, plain, (![A_1114, C_1115, D_1116]: (k2_struct_0(A_1114)!=k1_xboole_0 | v3_pre_topc(k8_relset_1(u1_struct_0(A_1114), k1_xboole_0, C_1115, D_1116), A_1114) | ~v3_pre_topc(D_1116, '#skF_2') | ~m1_subset_1(D_1116, k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(C_1115, A_1114, '#skF_2') | ~m1_subset_1(C_1115, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1114), k1_xboole_0))) | ~v1_funct_2(C_1115, u1_struct_0(A_1114), k1_xboole_0) | ~v1_funct_1(C_1115) | ~l1_pre_topc(A_1114))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_12860, c_12860, c_12860, c_13463])).
% 15.43/7.32  tff(c_20658, plain, (![C_1115, D_1116]: (k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))!=k1_xboole_0 | v3_pre_topc(k8_relset_1(u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')), k1_xboole_0, C_1115, D_1116), k6_tmap_1('#skF_2', '#skF_3')) | ~v3_pre_topc(D_1116, '#skF_2') | ~m1_subset_1(D_1116, k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(C_1115, k6_tmap_1('#skF_2', '#skF_3'), '#skF_2') | ~m1_subset_1(C_1115, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~v1_funct_2(C_1115, u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')), k1_xboole_0) | ~v1_funct_1(C_1115) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_12850, c_20642])).
% 15.43/7.32  tff(c_20669, plain, (![C_1117, D_1118]: (v3_pre_topc(k8_relset_1(k1_xboole_0, k1_xboole_0, C_1117, D_1118), k6_tmap_1('#skF_2', '#skF_3')) | ~v3_pre_topc(D_1118, '#skF_2') | ~m1_subset_1(D_1118, k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(C_1117, k6_tmap_1('#skF_2', '#skF_3'), '#skF_2') | ~m1_subset_1(C_1117, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~v1_funct_2(C_1117, k1_xboole_0, k1_xboole_0) | ~v1_funct_1(C_1117))), inference(demodulation, [status(thm), theory('equality')], [c_5345, c_12850, c_12850, c_12849, c_20658])).
% 15.43/7.32  tff(c_20686, plain, (![D_4]: (v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0), D_4), k6_tmap_1('#skF_2', '#skF_3')) | ~v3_pre_topc(D_4, '#skF_2') | ~m1_subset_1(D_4, k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(k6_partfun1(k1_xboole_0), k6_tmap_1('#skF_2', '#skF_3'), '#skF_2') | ~m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~v1_funct_2(k6_partfun1(k1_xboole_0), k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k6_partfun1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_13054, c_20669])).
% 15.43/7.32  tff(c_20700, plain, (![D_1119]: (v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0), D_1119), k6_tmap_1('#skF_2', '#skF_3')) | ~v3_pre_topc(D_1119, '#skF_2') | ~m1_subset_1(D_1119, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12964, c_13071, c_13059, c_14329, c_20686])).
% 15.43/7.32  tff(c_13362, plain, (![A_864, B_865, C_866]: (k2_struct_0(A_864)!=k1_xboole_0 | ~v3_pre_topc(k8_relset_1(u1_struct_0(A_864), u1_struct_0(B_865), C_866, '#skF_1'(A_864, B_865, C_866)), A_864) | v5_pre_topc(C_866, A_864, B_865) | ~m1_subset_1(C_866, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_864), u1_struct_0(B_865)))) | ~v1_funct_2(C_866, u1_struct_0(A_864), u1_struct_0(B_865)) | ~v1_funct_1(C_866) | ~l1_pre_topc(B_865) | ~l1_pre_topc(A_864))), inference(cnfTransformation, [status(thm)], [f_113])).
% 15.43/7.32  tff(c_13365, plain, (![B_865, C_866]: (k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))!=k1_xboole_0 | ~v3_pre_topc(k8_relset_1(k1_xboole_0, u1_struct_0(B_865), C_866, '#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), B_865, C_866)), k6_tmap_1('#skF_2', '#skF_3')) | v5_pre_topc(C_866, k6_tmap_1('#skF_2', '#skF_3'), B_865) | ~m1_subset_1(C_866, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')), u1_struct_0(B_865)))) | ~v1_funct_2(C_866, u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')), u1_struct_0(B_865)) | ~v1_funct_1(C_866) | ~l1_pre_topc(B_865) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_12850, c_13362])).
% 15.43/7.32  tff(c_20435, plain, (![B_1097, C_1098]: (~v3_pre_topc(k8_relset_1(k1_xboole_0, u1_struct_0(B_1097), C_1098, '#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), B_1097, C_1098)), k6_tmap_1('#skF_2', '#skF_3')) | v5_pre_topc(C_1098, k6_tmap_1('#skF_2', '#skF_3'), B_1097) | ~m1_subset_1(C_1098, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, u1_struct_0(B_1097)))) | ~v1_funct_2(C_1098, k1_xboole_0, u1_struct_0(B_1097)) | ~v1_funct_1(C_1098) | ~l1_pre_topc(B_1097))), inference(demodulation, [status(thm), theory('equality')], [c_5345, c_12850, c_12850, c_12849, c_13365])).
% 15.43/7.32  tff(c_20463, plain, (![C_1098]: (~v3_pre_topc(k8_relset_1(k1_xboole_0, k1_xboole_0, C_1098, '#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), C_1098)), k6_tmap_1('#skF_2', '#skF_3')) | v5_pre_topc(C_1098, k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(C_1098, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))))) | ~v1_funct_2(C_1098, k1_xboole_0, u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(C_1098) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_12850, c_20435])).
% 15.43/7.32  tff(c_20475, plain, (![C_1099]: (~v3_pre_topc(k8_relset_1(k1_xboole_0, k1_xboole_0, C_1099, '#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), C_1099)), k6_tmap_1('#skF_2', '#skF_3')) | v5_pre_topc(C_1099, k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(C_1099, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~v1_funct_2(C_1099, k1_xboole_0, k1_xboole_0) | ~v1_funct_1(C_1099))), inference(demodulation, [status(thm), theory('equality')], [c_5345, c_12850, c_12850, c_20463])).
% 15.43/7.32  tff(c_20479, plain, (~v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0), '#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k6_partfun1(k1_xboole_0))), k6_tmap_1('#skF_2', '#skF_3')) | v5_pre_topc(k6_partfun1(k1_xboole_0), k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~v1_funct_2(k6_partfun1(k1_xboole_0), k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k6_partfun1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_13054, c_20475])).
% 15.43/7.32  tff(c_20481, plain, (~v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0), '#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k6_partfun1(k1_xboole_0))), k6_tmap_1('#skF_2', '#skF_3')) | v5_pre_topc(k6_partfun1(k1_xboole_0), k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12964, c_13071, c_13059, c_20479])).
% 15.43/7.32  tff(c_20482, plain, (~v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0), '#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k6_partfun1(k1_xboole_0))), k6_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_20481])).
% 15.43/7.32  tff(c_20722, plain, (~v3_pre_topc('#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k6_partfun1(k1_xboole_0)), '#skF_2') | ~m1_subset_1('#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k6_partfun1(k1_xboole_0)), k1_zfmisc_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_20700, c_20482])).
% 15.43/7.32  tff(c_20755, plain, (~m1_subset_1('#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k6_partfun1(k1_xboole_0)), k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_20722])).
% 15.43/7.32  tff(c_20758, plain, (k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))!=k1_xboole_0 | v5_pre_topc(k6_partfun1(k1_xboole_0), k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')), k1_xboole_0))) | ~v1_funct_2(k6_partfun1(k1_xboole_0), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')), k1_xboole_0) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_13189, c_20755])).
% 15.43/7.32  tff(c_20764, plain, (v5_pre_topc(k6_partfun1(k1_xboole_0), k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5345, c_12964, c_13071, c_12850, c_13059, c_12850, c_12849, c_20758])).
% 15.43/7.32  tff(c_14061, plain, (![D_896, A_897, B_898]: (v5_pre_topc(D_896, A_897, B_898) | ~v5_pre_topc(D_896, g1_pre_topc(u1_struct_0(A_897), u1_pre_topc(A_897)), B_898) | ~m1_subset_1(D_896, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_897), u1_pre_topc(A_897))), u1_struct_0(B_898)))) | ~v1_funct_2(D_896, u1_struct_0(g1_pre_topc(u1_struct_0(A_897), u1_pre_topc(A_897))), u1_struct_0(B_898)) | ~m1_subset_1(D_896, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_897), u1_struct_0(B_898)))) | ~v1_funct_2(D_896, u1_struct_0(A_897), u1_struct_0(B_898)) | ~v1_funct_1(D_896) | ~l1_pre_topc(B_898) | ~v2_pre_topc(B_898) | ~l1_pre_topc(A_897) | ~v2_pre_topc(A_897))), inference(cnfTransformation, [status(thm)], [f_70])).
% 15.43/7.32  tff(c_14079, plain, (![D_896, B_898]: (v5_pre_topc(D_896, '#skF_2', B_898) | ~v5_pre_topc(D_896, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), B_898) | ~m1_subset_1(D_896, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2'))), u1_struct_0(B_898)))) | ~v1_funct_2(D_896, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0(B_898)) | ~m1_subset_1(D_896, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_898)))) | ~v1_funct_2(D_896, u1_struct_0('#skF_2'), u1_struct_0(B_898)) | ~v1_funct_1(D_896) | ~l1_pre_topc(B_898) | ~v2_pre_topc(B_898) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_12860, c_14061])).
% 15.43/7.32  tff(c_14377, plain, (![D_910, B_911]: (v5_pre_topc(D_910, '#skF_2', B_911) | ~v5_pre_topc(D_910, k6_tmap_1('#skF_2', '#skF_3'), B_911) | ~m1_subset_1(D_910, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, u1_struct_0(B_911)))) | ~v1_funct_2(D_910, k1_xboole_0, u1_struct_0(B_911)) | ~v1_funct_1(D_910) | ~l1_pre_topc(B_911) | ~v2_pre_topc(B_911))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_12860, c_12860, c_12850, c_12845, c_12860, c_12850, c_12845, c_12845, c_12860, c_14079])).
% 15.43/7.32  tff(c_14386, plain, (![D_910]: (v5_pre_topc(D_910, '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~v5_pre_topc(D_910, k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_910, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~v1_funct_2(D_910, k1_xboole_0, u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(D_910) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | ~v2_pre_topc(k6_tmap_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_12850, c_14377])).
% 15.43/7.32  tff(c_14394, plain, (![D_910]: (v5_pre_topc(D_910, '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~v5_pre_topc(D_910, k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_910, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~v1_funct_2(D_910, k1_xboole_0, k1_xboole_0) | ~v1_funct_1(D_910))), inference(demodulation, [status(thm), theory('equality')], [c_5381, c_5345, c_12850, c_14386])).
% 15.43/7.32  tff(c_20770, plain, (v5_pre_topc(k6_partfun1(k1_xboole_0), '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~v1_funct_2(k6_partfun1(k1_xboole_0), k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_20764, c_14394])).
% 15.43/7.32  tff(c_20773, plain, (v5_pre_topc(k6_partfun1(k1_xboole_0), '#skF_2', k6_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12964, c_13071, c_13059, c_20770])).
% 15.43/7.32  tff(c_20775, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12963, c_20773])).
% 15.43/7.32  tff(c_20777, plain, (m1_subset_1('#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k6_partfun1(k1_xboole_0)), k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_20722])).
% 15.43/7.32  tff(c_20818, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, k6_partfun1(k1_xboole_0), '#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k6_partfun1(k1_xboole_0)))='#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_20777, c_4])).
% 15.43/7.32  tff(c_21589, plain, (k10_relat_1(k6_partfun1(k1_xboole_0), '#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k6_partfun1(k1_xboole_0)))='#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k6_partfun1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20818, c_13054])).
% 15.43/7.32  tff(c_21600, plain, (~v3_pre_topc('#skF_1'(k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'), k6_partfun1(k1_xboole_0)), k6_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_21589, c_20482])).
% 15.43/7.32  tff(c_21619, plain, (k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))!=k1_xboole_0 | v5_pre_topc(k6_partfun1(k1_xboole_0), k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')), k1_xboole_0))) | ~v1_funct_2(k6_partfun1(k1_xboole_0), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')), k1_xboole_0) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_13049, c_21600])).
% 15.43/7.32  tff(c_21625, plain, (v5_pre_topc(k6_partfun1(k1_xboole_0), k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5345, c_12964, c_13071, c_12850, c_13059, c_12850, c_12849, c_21619])).
% 15.43/7.32  tff(c_21631, plain, (v5_pre_topc(k6_partfun1(k1_xboole_0), '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~v1_funct_2(k6_partfun1(k1_xboole_0), k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_21625, c_14394])).
% 15.43/7.32  tff(c_21634, plain, (v5_pre_topc(k6_partfun1(k1_xboole_0), '#skF_2', k6_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12964, c_13071, c_13059, c_21631])).
% 15.43/7.32  tff(c_21636, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12963, c_21634])).
% 15.43/7.32  tff(c_21637, plain, (v5_pre_topc(k6_partfun1(k1_xboole_0), k6_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_20481])).
% 15.43/7.32  tff(c_21641, plain, (v5_pre_topc(k6_partfun1(k1_xboole_0), '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~v1_funct_2(k6_partfun1(k1_xboole_0), k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_21637, c_14394])).
% 15.43/7.32  tff(c_21644, plain, (v5_pre_topc(k6_partfun1(k1_xboole_0), '#skF_2', k6_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12964, c_13071, c_13059, c_21641])).
% 15.43/7.32  tff(c_21646, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12963, c_21644])).
% 15.43/7.32  tff(c_21648, plain, (~v1_funct_1(k7_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_84])).
% 15.43/7.32  tff(c_21661, plain, (![A_1132, B_1133]: (v1_funct_1(k7_tmap_1(A_1132, B_1133)) | ~m1_subset_1(B_1133, k1_zfmisc_1(u1_struct_0(A_1132))) | ~l1_pre_topc(A_1132) | ~v2_pre_topc(A_1132) | v2_struct_0(A_1132))), inference(cnfTransformation, [status(thm)], [f_155])).
% 15.43/7.32  tff(c_21664, plain, (![B_1133]: (v1_funct_1(k7_tmap_1('#skF_2', B_1133)) | ~m1_subset_1(B_1133, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_95, c_21661])).
% 15.43/7.32  tff(c_21666, plain, (![B_1133]: (v1_funct_1(k7_tmap_1('#skF_2', B_1133)) | ~m1_subset_1(B_1133, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_21664])).
% 15.43/7.32  tff(c_21668, plain, (![B_1134]: (v1_funct_1(k7_tmap_1('#skF_2', B_1134)) | ~m1_subset_1(B_1134, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_21666])).
% 15.43/7.32  tff(c_21671, plain, (v1_funct_1(k7_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_96, c_21668])).
% 15.43/7.32  tff(c_21675, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21648, c_21671])).
% 15.43/7.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.43/7.32  
% 15.43/7.32  Inference rules
% 15.43/7.32  ----------------------
% 15.43/7.32  #Ref     : 0
% 15.43/7.32  #Sup     : 4788
% 15.43/7.32  #Fact    : 0
% 15.43/7.32  #Define  : 0
% 15.43/7.32  #Split   : 49
% 15.43/7.32  #Chain   : 0
% 15.43/7.32  #Close   : 0
% 15.43/7.32  
% 15.43/7.32  Ordering : KBO
% 15.43/7.32  
% 15.43/7.32  Simplification rules
% 15.43/7.32  ----------------------
% 15.43/7.32  #Subsume      : 541
% 15.43/7.32  #Demod        : 20581
% 15.43/7.32  #Tautology    : 1246
% 15.43/7.32  #SimpNegUnit  : 1025
% 15.43/7.32  #BackRed      : 89
% 15.43/7.32  
% 15.43/7.32  #Partial instantiations: 0
% 15.43/7.32  #Strategies tried      : 1
% 15.43/7.32  
% 15.43/7.32  Timing (in seconds)
% 15.43/7.32  ----------------------
% 15.43/7.32  Preprocessing        : 0.42
% 15.43/7.32  Parsing              : 0.22
% 15.43/7.32  CNF conversion       : 0.03
% 15.43/7.32  Main loop            : 6.03
% 15.43/7.32  Inferencing          : 1.34
% 15.43/7.32  Reduction            : 2.90
% 15.43/7.32  Demodulation         : 2.36
% 15.43/7.32  BG Simplification    : 0.17
% 15.43/7.32  Subsumption          : 1.37
% 15.43/7.32  Abstraction          : 0.29
% 15.43/7.32  MUC search           : 0.00
% 15.43/7.32  Cooper               : 0.00
% 15.43/7.32  Total                : 6.59
% 15.43/7.32  Index Insertion      : 0.00
% 15.43/7.32  Index Deletion       : 0.00
% 15.43/7.32  Index Matching       : 0.00
% 15.43/7.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
