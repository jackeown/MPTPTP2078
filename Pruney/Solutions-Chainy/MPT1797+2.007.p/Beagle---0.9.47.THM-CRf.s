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
% DateTime   : Thu Dec  3 10:27:56 EST 2020

% Result     : Theorem 10.74s
% Output     : CNFRefutation 11.21s
% Verified   : 
% Statistics : Number of formulae       :  319 (17729 expanded)
%              Number of leaves         :   40 (6176 expanded)
%              Depth                    :   23
%              Number of atoms          : 1017 (59754 expanded)
%              Number of equality atoms :  117 (8751 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v3_pre_topc > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k7_tmap_1 > k6_tmap_1 > k5_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k6_partfun1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(f_199,negated_conjecture,(
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

tff(f_37,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_147,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_118,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_164,axiom,(
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

tff(f_103,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k7_tmap_1(A,B) = k6_partfun1(u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_tmap_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_91,axiom,(
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

tff(f_133,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_funct_1(k7_tmap_1(A,B))
        & v1_funct_2(k7_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B)))
        & m1_subset_1(k7_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

tff(f_178,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).

tff(f_66,axiom,(
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
                    & v1_funct_2(D,u1_struct_0(A),u1_struct_0(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))))) )
                 => ( C = D
                   => ( v5_pre_topc(C,A,B)
                    <=> v5_pre_topc(D,A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_pre_topc)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_6,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_80,plain,(
    ! [A_64] :
      ( u1_struct_0(A_64) = k2_struct_0(A_64)
      | ~ l1_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_85,plain,(
    ! [A_65] :
      ( u1_struct_0(A_65) = k2_struct_0(A_65)
      | ~ l1_pre_topc(A_65) ) ),
    inference(resolution,[status(thm)],[c_6,c_80])).

tff(c_89,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_85])).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_90,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_52])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_4596,plain,(
    ! [A_460,B_461] :
      ( u1_struct_0(k6_tmap_1(A_460,B_461)) = u1_struct_0(A_460)
      | ~ m1_subset_1(B_461,k1_zfmisc_1(u1_struct_0(A_460)))
      | ~ l1_pre_topc(A_460)
      | ~ v2_pre_topc(A_460)
      | v2_struct_0(A_460) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_4602,plain,(
    ! [B_461] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_461)) = u1_struct_0('#skF_2')
      | ~ m1_subset_1(B_461,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_4596])).

tff(c_4606,plain,(
    ! [B_461] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_461)) = k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_461,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_89,c_4602])).

tff(c_4608,plain,(
    ! [B_462] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_462)) = k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_462,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4606])).

tff(c_4612,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_90,c_4608])).

tff(c_4473,plain,(
    ! [A_444,B_445] :
      ( l1_pre_topc(k6_tmap_1(A_444,B_445))
      | ~ m1_subset_1(B_445,k1_zfmisc_1(u1_struct_0(A_444)))
      | ~ l1_pre_topc(A_444)
      | ~ v2_pre_topc(A_444)
      | v2_struct_0(A_444) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_4476,plain,(
    ! [B_445] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_445))
      | ~ m1_subset_1(B_445,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_4473])).

tff(c_4478,plain,(
    ! [B_445] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_445))
      | ~ m1_subset_1(B_445,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4476])).

tff(c_4480,plain,(
    ! [B_446] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_446))
      | ~ m1_subset_1(B_446,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4478])).

tff(c_4484,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_90,c_4480])).

tff(c_84,plain,(
    ! [A_4] :
      ( u1_struct_0(A_4) = k2_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_80])).

tff(c_4495,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4484,c_84])).

tff(c_4613,plain,(
    k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4612,c_4495])).

tff(c_4275,plain,(
    ! [A_423,B_424] :
      ( u1_struct_0(k6_tmap_1(A_423,B_424)) = u1_struct_0(A_423)
      | ~ m1_subset_1(B_424,k1_zfmisc_1(u1_struct_0(A_423)))
      | ~ l1_pre_topc(A_423)
      | ~ v2_pre_topc(A_423)
      | v2_struct_0(A_423) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_4281,plain,(
    ! [B_424] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_424)) = u1_struct_0('#skF_2')
      | ~ m1_subset_1(B_424,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_4275])).

tff(c_4285,plain,(
    ! [B_424] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_424)) = k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_424,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_89,c_4281])).

tff(c_4287,plain,(
    ! [B_425] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_425)) = k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_425,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4285])).

tff(c_4291,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_90,c_4287])).

tff(c_4183,plain,(
    ! [A_414,B_415] :
      ( l1_pre_topc(k6_tmap_1(A_414,B_415))
      | ~ m1_subset_1(B_415,k1_zfmisc_1(u1_struct_0(A_414)))
      | ~ l1_pre_topc(A_414)
      | ~ v2_pre_topc(A_414)
      | v2_struct_0(A_414) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_4186,plain,(
    ! [B_415] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_415))
      | ~ m1_subset_1(B_415,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_4183])).

tff(c_4188,plain,(
    ! [B_415] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_415))
      | ~ m1_subset_1(B_415,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4186])).

tff(c_4190,plain,(
    ! [B_416] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_416))
      | ~ m1_subset_1(B_416,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4188])).

tff(c_4194,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_90,c_4190])).

tff(c_4198,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4194,c_84])).

tff(c_4292,plain,(
    k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4291,c_4198])).

tff(c_4068,plain,(
    ! [A_404,B_405] :
      ( u1_struct_0(k6_tmap_1(A_404,B_405)) = u1_struct_0(A_404)
      | ~ m1_subset_1(B_405,k1_zfmisc_1(u1_struct_0(A_404)))
      | ~ l1_pre_topc(A_404)
      | ~ v2_pre_topc(A_404)
      | v2_struct_0(A_404) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_4074,plain,(
    ! [B_405] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_405)) = u1_struct_0('#skF_2')
      | ~ m1_subset_1(B_405,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_4068])).

tff(c_4078,plain,(
    ! [B_405] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_405)) = k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_405,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_89,c_4074])).

tff(c_4090,plain,(
    ! [B_406] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_406)) = k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_406,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4078])).

tff(c_4094,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_90,c_4090])).

tff(c_137,plain,(
    ! [A_74,B_75] :
      ( l1_pre_topc(k6_tmap_1(A_74,B_75))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_140,plain,(
    ! [B_75] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_75))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_137])).

tff(c_142,plain,(
    ! [B_75] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_75))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_140])).

tff(c_151,plain,(
    ! [B_78] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_78))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_142])).

tff(c_155,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_90,c_151])).

tff(c_159,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_155,c_84])).

tff(c_4095,plain,(
    k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4094,c_159])).

tff(c_66,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))))) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_120,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_66])).

tff(c_121,plain,(
    m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_160,plain,(
    m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0(k6_tmap_1('#skF_2','#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_121])).

tff(c_4130,plain,(
    m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4095,c_160])).

tff(c_74,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_105,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_74])).

tff(c_106,plain,(
    v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_105])).

tff(c_161,plain,(
    v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_106])).

tff(c_4131,plain,(
    v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4095,c_161])).

tff(c_78,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_95,plain,(
    v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_70,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2',k6_tmap_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_104,plain,(
    v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2',k6_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_60,plain,
    ( ~ m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))))
    | ~ v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_187,plain,
    ( ~ m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0(k6_tmap_1('#skF_2','#skF_3')))))
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_159,c_89,c_104,c_159,c_89,c_60])).

tff(c_188,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_230,plain,(
    ! [A_84,B_85] :
      ( u1_struct_0(k6_tmap_1(A_84,B_85)) = u1_struct_0(A_84)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84)
      | ~ v2_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_236,plain,(
    ! [B_85] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_85)) = u1_struct_0('#skF_2')
      | ~ m1_subset_1(B_85,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_230])).

tff(c_240,plain,(
    ! [B_85] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_85)) = k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_85,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_89,c_236])).

tff(c_242,plain,(
    ! [B_86] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_86)) = k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_86,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_240])).

tff(c_246,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_90,c_242])).

tff(c_396,plain,(
    ! [C_99,A_100] :
      ( v3_pre_topc(C_99,k6_tmap_1(A_100,C_99))
      | ~ m1_subset_1(C_99,k1_zfmisc_1(u1_struct_0(k6_tmap_1(A_100,C_99))))
      | ~ m1_subset_1(C_99,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_399,plain,
    ( v3_pre_topc('#skF_3',k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_396])).

tff(c_401,plain,
    ( v3_pre_topc('#skF_3',k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_90,c_89,c_90,c_399])).

tff(c_402,plain,(
    v3_pre_topc('#skF_3',k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_401])).

tff(c_197,plain,(
    ! [A_80,B_81] :
      ( k7_tmap_1(A_80,B_81) = k6_partfun1(u1_struct_0(A_80))
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_203,plain,(
    ! [B_81] :
      ( k7_tmap_1('#skF_2',B_81) = k6_partfun1(u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_81,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_197])).

tff(c_207,plain,(
    ! [B_81] :
      ( k7_tmap_1('#skF_2',B_81) = k6_partfun1(k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_81,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_89,c_203])).

tff(c_209,plain,(
    ! [B_82] :
      ( k7_tmap_1('#skF_2',B_82) = k6_partfun1(k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_207])).

tff(c_213,plain,(
    k6_partfun1(k2_struct_0('#skF_2')) = k7_tmap_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_209])).

tff(c_96,plain,(
    ! [A_66,B_67] :
      ( k8_relset_1(A_66,A_66,k6_partfun1(A_66),B_67) = B_67
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_99,plain,(
    k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k6_partfun1(k2_struct_0('#skF_2')),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_90,c_96])).

tff(c_215,plain,(
    k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k7_tmap_1('#skF_2','#skF_3'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_99])).

tff(c_247,plain,(
    k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_159])).

tff(c_283,plain,(
    v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_161])).

tff(c_282,plain,(
    m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_160])).

tff(c_424,plain,(
    ! [A_103,B_104,C_105] :
      ( k2_struct_0(A_103) != k1_xboole_0
      | v3_pre_topc('#skF_1'(A_103,B_104,C_105),B_104)
      | v5_pre_topc(C_105,A_103,B_104)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_103),u1_struct_0(B_104))))
      | ~ v1_funct_2(C_105,u1_struct_0(A_103),u1_struct_0(B_104))
      | ~ v1_funct_1(C_105)
      | ~ l1_pre_topc(B_104)
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_432,plain,(
    ! [B_104,C_105] :
      ( k2_struct_0('#skF_2') != k1_xboole_0
      | v3_pre_topc('#skF_1'('#skF_2',B_104,C_105),B_104)
      | v5_pre_topc(C_105,'#skF_2',B_104)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(B_104))))
      | ~ v1_funct_2(C_105,u1_struct_0('#skF_2'),u1_struct_0(B_104))
      | ~ v1_funct_1(C_105)
      | ~ l1_pre_topc(B_104)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_424])).

tff(c_441,plain,(
    ! [B_104,C_105] :
      ( k2_struct_0('#skF_2') != k1_xboole_0
      | v3_pre_topc('#skF_1'('#skF_2',B_104,C_105),B_104)
      | v5_pre_topc(C_105,'#skF_2',B_104)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(B_104))))
      | ~ v1_funct_2(C_105,k2_struct_0('#skF_2'),u1_struct_0(B_104))
      | ~ v1_funct_1(C_105)
      | ~ l1_pre_topc(B_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_89,c_432])).

tff(c_454,plain,(
    k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_441])).

tff(c_988,plain,(
    ! [B_172,A_173,C_174,D_175] :
      ( k2_struct_0(B_172) = k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0(A_173),u1_struct_0(B_172),C_174,D_175),A_173)
      | ~ v3_pre_topc(D_175,B_172)
      | ~ m1_subset_1(D_175,k1_zfmisc_1(u1_struct_0(B_172)))
      | ~ v5_pre_topc(C_174,A_173,B_172)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_173),u1_struct_0(B_172))))
      | ~ v1_funct_2(C_174,u1_struct_0(A_173),u1_struct_0(B_172))
      | ~ v1_funct_1(C_174)
      | ~ l1_pre_topc(B_172)
      | ~ l1_pre_topc(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_996,plain,(
    ! [B_172,C_174,D_175] :
      ( k2_struct_0(B_172) = k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_172),C_174,D_175),'#skF_2')
      | ~ v3_pre_topc(D_175,B_172)
      | ~ m1_subset_1(D_175,k1_zfmisc_1(u1_struct_0(B_172)))
      | ~ v5_pre_topc(C_174,'#skF_2',B_172)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(B_172))))
      | ~ v1_funct_2(C_174,u1_struct_0('#skF_2'),u1_struct_0(B_172))
      | ~ v1_funct_1(C_174)
      | ~ l1_pre_topc(B_172)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_988])).

tff(c_1446,plain,(
    ! [B_227,C_228,D_229] :
      ( k2_struct_0(B_227) = k1_xboole_0
      | v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'),u1_struct_0(B_227),C_228,D_229),'#skF_2')
      | ~ v3_pre_topc(D_229,B_227)
      | ~ m1_subset_1(D_229,k1_zfmisc_1(u1_struct_0(B_227)))
      | ~ v5_pre_topc(C_228,'#skF_2',B_227)
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(B_227))))
      | ~ v1_funct_2(C_228,k2_struct_0('#skF_2'),u1_struct_0(B_227))
      | ~ v1_funct_1(C_228)
      | ~ l1_pre_topc(B_227) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_89,c_89,c_996])).

tff(c_1450,plain,(
    ! [C_228,D_229] :
      ( k2_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k1_xboole_0
      | v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')),C_228,D_229),'#skF_2')
      | ~ v3_pre_topc(D_229,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_229,k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))))
      | ~ v5_pre_topc(C_228,'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_228,k2_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_228)
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_1446])).

tff(c_1455,plain,(
    ! [C_228,D_229] :
      ( k2_struct_0('#skF_2') = k1_xboole_0
      | v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),C_228,D_229),'#skF_2')
      | ~ v3_pre_topc(D_229,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_229,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v5_pre_topc(C_228,'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_228,k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_228) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_246,c_246,c_246,c_247,c_1450])).

tff(c_1478,plain,(
    ! [C_232,D_233] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),C_232,D_233),'#skF_2')
      | ~ v3_pre_topc(D_233,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_233,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v5_pre_topc(C_232,'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_232,k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_232) ) ),
    inference(negUnitSimplification,[status(thm)],[c_454,c_1455])).

tff(c_1480,plain,(
    ! [D_233] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k7_tmap_1('#skF_2','#skF_3'),D_233),'#skF_2')
      | ~ v3_pre_topc(D_233,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_233,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
      | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_282,c_1478])).

tff(c_1484,plain,(
    ! [D_234] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k7_tmap_1('#skF_2','#skF_3'),D_234),'#skF_2')
      | ~ v3_pre_topc(D_234,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_234,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_283,c_104,c_1480])).

tff(c_1495,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3',k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_1484])).

tff(c_1503,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_402,c_1495])).

tff(c_1505,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_1503])).

tff(c_1507,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_441])).

tff(c_1527,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1507,c_90])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k8_relset_1(A_1,A_1,k6_partfun1(A_1),B_2) = B_2
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1611,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1527,c_2])).

tff(c_1528,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1507,c_89])).

tff(c_1522,plain,(
    k7_tmap_1('#skF_2','#skF_3') = k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1507,c_213])).

tff(c_1613,plain,(
    v1_funct_1(k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1522,c_95])).

tff(c_1518,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1507,c_246])).

tff(c_38,plain,(
    ! [A_47,B_48] :
      ( v1_funct_2(k7_tmap_1(A_47,B_48),u1_struct_0(A_47),u1_struct_0(k6_tmap_1(A_47,B_48)))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1653,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),k1_xboole_0)
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1518,c_38])).

tff(c_1696,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1527,c_1528,c_1522,c_1528,c_1653])).

tff(c_1697,plain,(
    v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1696])).

tff(c_1612,plain,(
    v5_pre_topc(k6_partfun1(k1_xboole_0),'#skF_2',k6_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1522,c_104])).

tff(c_36,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(k7_tmap_1(A_47,B_48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_47),u1_struct_0(k6_tmap_1(A_47,B_48)))))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2162,plain,(
    ! [A_283,B_284,C_285,D_286] :
      ( k2_struct_0(A_283) != k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0(A_283),u1_struct_0(B_284),C_285,D_286),A_283)
      | ~ v3_pre_topc(D_286,B_284)
      | ~ m1_subset_1(D_286,k1_zfmisc_1(u1_struct_0(B_284)))
      | ~ v5_pre_topc(C_285,A_283,B_284)
      | ~ m1_subset_1(C_285,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_283),u1_struct_0(B_284))))
      | ~ v1_funct_2(C_285,u1_struct_0(A_283),u1_struct_0(B_284))
      | ~ v1_funct_1(C_285)
      | ~ l1_pre_topc(B_284)
      | ~ l1_pre_topc(A_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3919,plain,(
    ! [A_395,B_396,D_397] :
      ( k2_struct_0(A_395) != k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0(A_395),u1_struct_0(k6_tmap_1(A_395,B_396)),k7_tmap_1(A_395,B_396),D_397),A_395)
      | ~ v3_pre_topc(D_397,k6_tmap_1(A_395,B_396))
      | ~ m1_subset_1(D_397,k1_zfmisc_1(u1_struct_0(k6_tmap_1(A_395,B_396))))
      | ~ v5_pre_topc(k7_tmap_1(A_395,B_396),A_395,k6_tmap_1(A_395,B_396))
      | ~ v1_funct_2(k7_tmap_1(A_395,B_396),u1_struct_0(A_395),u1_struct_0(k6_tmap_1(A_395,B_396)))
      | ~ v1_funct_1(k7_tmap_1(A_395,B_396))
      | ~ l1_pre_topc(k6_tmap_1(A_395,B_396))
      | ~ m1_subset_1(B_396,k1_zfmisc_1(u1_struct_0(A_395)))
      | ~ l1_pre_topc(A_395)
      | ~ v2_pre_topc(A_395)
      | v2_struct_0(A_395) ) ),
    inference(resolution,[status(thm)],[c_36,c_2162])).

tff(c_3954,plain,(
    ! [D_397] :
      ( k2_struct_0('#skF_2') != k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0('#skF_2'),k1_xboole_0,k7_tmap_1('#skF_2','#skF_3'),D_397),'#skF_2')
      | ~ v3_pre_topc(D_397,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_397,k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))))
      | ~ v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
      | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1518,c_3919])).

tff(c_3978,plain,(
    ! [D_397] :
      ( v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),D_397),'#skF_2')
      | ~ v3_pre_topc(D_397,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_397,k1_zfmisc_1(k1_xboole_0))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1527,c_1528,c_155,c_1613,c_1522,c_1697,c_1518,c_1522,c_1528,c_1612,c_1522,c_1518,c_1522,c_1528,c_1507,c_3954])).

tff(c_4013,plain,(
    ! [D_399] :
      ( v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),D_399),'#skF_2')
      | ~ v3_pre_topc(D_399,k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_399,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3978])).

tff(c_4030,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3',k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1611,c_4013])).

tff(c_4038,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1527,c_402,c_4030])).

tff(c_4040,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_4038])).

tff(c_4041,plain,
    ( ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | ~ m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0(k6_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_4168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4130,c_4095,c_4131,c_4095,c_4041])).

tff(c_4170,plain,(
    ~ m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_4199,plain,(
    ~ m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0(k6_tmap_1('#skF_2','#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4198,c_4170])).

tff(c_4327,plain,(
    ~ m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4292,c_4199])).

tff(c_4447,plain,(
    ! [A_442,B_443] :
      ( m1_subset_1(k7_tmap_1(A_442,B_443),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_442),u1_struct_0(k6_tmap_1(A_442,B_443)))))
      | ~ m1_subset_1(B_443,k1_zfmisc_1(u1_struct_0(A_442)))
      | ~ l1_pre_topc(A_442)
      | ~ v2_pre_topc(A_442)
      | v2_struct_0(A_442) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_4455,plain,
    ( m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4291,c_4447])).

tff(c_4463,plain,
    ( m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_90,c_89,c_89,c_4455])).

tff(c_4465,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4327,c_4463])).

tff(c_4466,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_4518,plain,
    ( ~ m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0(k6_tmap_1('#skF_2','#skF_3')))))
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4466,c_95,c_4495,c_89,c_104,c_4495,c_89,c_60])).

tff(c_4519,plain,(
    ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_4518])).

tff(c_4650,plain,(
    ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4613,c_4519])).

tff(c_4687,plain,(
    ! [A_466,B_467] :
      ( v1_funct_2(k7_tmap_1(A_466,B_467),u1_struct_0(A_466),u1_struct_0(k6_tmap_1(A_466,B_467)))
      | ~ m1_subset_1(B_467,k1_zfmisc_1(u1_struct_0(A_466)))
      | ~ l1_pre_topc(A_466)
      | ~ v2_pre_topc(A_466)
      | v2_struct_0(A_466) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_4693,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),k2_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4612,c_4687])).

tff(c_4700,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_90,c_89,c_89,c_4693])).

tff(c_4702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4650,c_4700])).

tff(c_4704,plain,(
    v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_4518])).

tff(c_4467,plain,(
    ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_4497,plain,(
    ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4495,c_4467])).

tff(c_4723,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4704,c_4497])).

tff(c_4725,plain,(
    ~ v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2',k6_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_4774,plain,(
    ! [A_482,B_483] :
      ( u1_struct_0(k6_tmap_1(A_482,B_483)) = u1_struct_0(A_482)
      | ~ m1_subset_1(B_483,k1_zfmisc_1(u1_struct_0(A_482)))
      | ~ l1_pre_topc(A_482)
      | ~ v2_pre_topc(A_482)
      | v2_struct_0(A_482) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_4777,plain,(
    ! [B_483] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_483)) = u1_struct_0('#skF_2')
      | ~ m1_subset_1(B_483,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_4774])).

tff(c_4779,plain,(
    ! [B_483] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_483)) = k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_483,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_89,c_4777])).

tff(c_4819,plain,(
    ! [B_485] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_485)) = k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_485,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4779])).

tff(c_4823,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_90,c_4819])).

tff(c_4921,plain,(
    ! [A_493,B_494] :
      ( v1_funct_2(k7_tmap_1(A_493,B_494),u1_struct_0(A_493),u1_struct_0(k6_tmap_1(A_493,B_494)))
      | ~ m1_subset_1(B_494,k1_zfmisc_1(u1_struct_0(A_493)))
      | ~ l1_pre_topc(A_493)
      | ~ v2_pre_topc(A_493)
      | v2_struct_0(A_493) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_4927,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),k2_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4823,c_4921])).

tff(c_4934,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_90,c_89,c_89,c_4927])).

tff(c_4935,plain,(
    v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4934])).

tff(c_5004,plain,(
    ! [A_505,B_506] :
      ( m1_subset_1(k7_tmap_1(A_505,B_506),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_505),u1_struct_0(k6_tmap_1(A_505,B_506)))))
      | ~ m1_subset_1(B_506,k1_zfmisc_1(u1_struct_0(A_505)))
      | ~ l1_pre_topc(A_505)
      | ~ v2_pre_topc(A_505)
      | v2_struct_0(A_505) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_5012,plain,
    ( m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4823,c_5004])).

tff(c_5020,plain,
    ( m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_90,c_89,c_89,c_5012])).

tff(c_5021,plain,(
    m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_5020])).

tff(c_5037,plain,(
    ! [B_508,A_509,C_510] :
      ( k2_struct_0(B_508) = k1_xboole_0
      | v3_pre_topc('#skF_1'(A_509,B_508,C_510),B_508)
      | v5_pre_topc(C_510,A_509,B_508)
      | ~ m1_subset_1(C_510,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_509),u1_struct_0(B_508))))
      | ~ v1_funct_2(C_510,u1_struct_0(A_509),u1_struct_0(B_508))
      | ~ v1_funct_1(C_510)
      | ~ l1_pre_topc(B_508)
      | ~ l1_pre_topc(A_509) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_5045,plain,(
    ! [B_508,C_510] :
      ( k2_struct_0(B_508) = k1_xboole_0
      | v3_pre_topc('#skF_1'('#skF_2',B_508,C_510),B_508)
      | v5_pre_topc(C_510,'#skF_2',B_508)
      | ~ m1_subset_1(C_510,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(B_508))))
      | ~ v1_funct_2(C_510,u1_struct_0('#skF_2'),u1_struct_0(B_508))
      | ~ v1_funct_1(C_510)
      | ~ l1_pre_topc(B_508)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_5037])).

tff(c_5061,plain,(
    ! [B_511,C_512] :
      ( k2_struct_0(B_511) = k1_xboole_0
      | v3_pre_topc('#skF_1'('#skF_2',B_511,C_512),B_511)
      | v5_pre_topc(C_512,'#skF_2',B_511)
      | ~ m1_subset_1(C_512,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(B_511))))
      | ~ v1_funct_2(C_512,k2_struct_0('#skF_2'),u1_struct_0(B_511))
      | ~ v1_funct_1(C_512)
      | ~ l1_pre_topc(B_511) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_89,c_5045])).

tff(c_5067,plain,(
    ! [C_512] :
      ( k2_struct_0('#skF_2') = k1_xboole_0
      | v3_pre_topc('#skF_1'('#skF_2','#skF_2',C_512),'#skF_2')
      | v5_pre_topc(C_512,'#skF_2','#skF_2')
      | ~ m1_subset_1(C_512,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_512,k2_struct_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_512)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_5061])).

tff(c_5072,plain,(
    ! [C_512] :
      ( k2_struct_0('#skF_2') = k1_xboole_0
      | v3_pre_topc('#skF_1'('#skF_2','#skF_2',C_512),'#skF_2')
      | v5_pre_topc(C_512,'#skF_2','#skF_2')
      | ~ m1_subset_1(C_512,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_512,k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_512) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_89,c_5067])).

tff(c_5073,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_5072])).

tff(c_4860,plain,(
    ! [A_486,B_487] :
      ( k7_tmap_1(A_486,B_487) = k6_partfun1(u1_struct_0(A_486))
      | ~ m1_subset_1(B_487,k1_zfmisc_1(u1_struct_0(A_486)))
      | ~ l1_pre_topc(A_486)
      | ~ v2_pre_topc(A_486)
      | v2_struct_0(A_486) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_4866,plain,(
    ! [B_487] :
      ( k7_tmap_1('#skF_2',B_487) = k6_partfun1(u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_487,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_4860])).

tff(c_4870,plain,(
    ! [B_487] :
      ( k7_tmap_1('#skF_2',B_487) = k6_partfun1(k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_487,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_89,c_4866])).

tff(c_4872,plain,(
    ! [B_488] :
      ( k7_tmap_1('#skF_2',B_488) = k6_partfun1(k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_488,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4870])).

tff(c_4876,plain,(
    k6_partfun1(k2_struct_0('#skF_2')) = k7_tmap_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_4872])).

tff(c_5111,plain,(
    k7_tmap_1('#skF_2','#skF_3') = k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5073,c_4876])).

tff(c_5204,plain,(
    ~ v5_pre_topc(k6_partfun1(k1_xboole_0),'#skF_2',k6_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5111,c_4725])).

tff(c_5205,plain,(
    v1_funct_1(k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5111,c_95])).

tff(c_5119,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5073,c_90])).

tff(c_5120,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5073,c_89])).

tff(c_5113,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5073,c_4823])).

tff(c_5261,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),k1_xboole_0)
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5113,c_38])).

tff(c_5308,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_5119,c_5120,c_5111,c_5120,c_5261])).

tff(c_5309,plain,(
    v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_5308])).

tff(c_5248,plain,
    ( m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),k1_xboole_0)))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5113,c_36])).

tff(c_5296,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_5119,c_5120,c_5111,c_5120,c_5248])).

tff(c_5297,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_5296])).

tff(c_5222,plain,(
    ! [A_514,B_515,C_516] :
      ( k2_struct_0(A_514) != k1_xboole_0
      | v3_pre_topc('#skF_1'(A_514,B_515,C_516),B_515)
      | v5_pre_topc(C_516,A_514,B_515)
      | ~ m1_subset_1(C_516,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_514),u1_struct_0(B_515))))
      | ~ v1_funct_2(C_516,u1_struct_0(A_514),u1_struct_0(B_515))
      | ~ v1_funct_1(C_516)
      | ~ l1_pre_topc(B_515)
      | ~ l1_pre_topc(A_514) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_5224,plain,(
    ! [B_515,C_516] :
      ( k2_struct_0('#skF_2') != k1_xboole_0
      | v3_pre_topc('#skF_1'('#skF_2',B_515,C_516),B_515)
      | v5_pre_topc(C_516,'#skF_2',B_515)
      | ~ m1_subset_1(C_516,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(B_515))))
      | ~ v1_funct_2(C_516,u1_struct_0('#skF_2'),u1_struct_0(B_515))
      | ~ v1_funct_1(C_516)
      | ~ l1_pre_topc(B_515)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5120,c_5222])).

tff(c_5516,plain,(
    ! [B_540,C_541] :
      ( v3_pre_topc('#skF_1'('#skF_2',B_540,C_541),B_540)
      | v5_pre_topc(C_541,'#skF_2',B_540)
      | ~ m1_subset_1(C_541,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(B_540))))
      | ~ v1_funct_2(C_541,k1_xboole_0,u1_struct_0(B_540))
      | ~ v1_funct_1(C_541)
      | ~ l1_pre_topc(B_540) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_5120,c_5073,c_5224])).

tff(c_5522,plain,(
    ! [C_541] :
      ( v3_pre_topc('#skF_1'('#skF_2','#skF_2',C_541),'#skF_2')
      | v5_pre_topc(C_541,'#skF_2','#skF_2')
      | ~ m1_subset_1(C_541,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ v1_funct_2(C_541,k1_xboole_0,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_541)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5120,c_5516])).

tff(c_5528,plain,(
    ! [C_542] :
      ( v3_pre_topc('#skF_1'('#skF_2','#skF_2',C_542),'#skF_2')
      | v5_pre_topc(C_542,'#skF_2','#skF_2')
      | ~ m1_subset_1(C_542,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ v1_funct_2(C_542,k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_1(C_542) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_5120,c_5522])).

tff(c_5531,plain,
    ( v3_pre_topc('#skF_1'('#skF_2','#skF_2',k6_partfun1(k1_xboole_0)),'#skF_2')
    | v5_pre_topc(k6_partfun1(k1_xboole_0),'#skF_2','#skF_2')
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_5297,c_5528])).

tff(c_5534,plain,
    ( v3_pre_topc('#skF_1'('#skF_2','#skF_2',k6_partfun1(k1_xboole_0)),'#skF_2')
    | v5_pre_topc(k6_partfun1(k1_xboole_0),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5205,c_5309,c_5531])).

tff(c_5535,plain,(
    v5_pre_topc(k6_partfun1(k1_xboole_0),'#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_5534])).

tff(c_4724,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_4946,plain,(
    ! [A_496,B_497] :
      ( k6_tmap_1(A_496,B_497) = g1_pre_topc(u1_struct_0(A_496),u1_pre_topc(A_496))
      | ~ v3_pre_topc(B_497,A_496)
      | ~ m1_subset_1(B_497,k1_zfmisc_1(u1_struct_0(A_496)))
      | ~ l1_pre_topc(A_496)
      | ~ v2_pre_topc(A_496)
      | v2_struct_0(A_496) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_4950,plain,(
    ! [B_497] :
      ( k6_tmap_1('#skF_2',B_497) = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ v3_pre_topc(B_497,'#skF_2')
      | ~ m1_subset_1(B_497,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_4946])).

tff(c_4954,plain,(
    ! [B_497] :
      ( k6_tmap_1('#skF_2',B_497) = g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ v3_pre_topc(B_497,'#skF_2')
      | ~ m1_subset_1(B_497,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_89,c_4950])).

tff(c_4970,plain,(
    ! [B_500] :
      ( k6_tmap_1('#skF_2',B_500) = g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ v3_pre_topc(B_500,'#skF_2')
      | ~ m1_subset_1(B_500,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4954])).

tff(c_4973,plain,
    ( g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k6_tmap_1('#skF_2','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_90,c_4970])).

tff(c_4976,plain,(
    g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k6_tmap_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4724,c_4973])).

tff(c_5105,plain,(
    g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2')) = k6_tmap_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5073,c_4976])).

tff(c_6211,plain,(
    ! [D_573,A_574,B_575] :
      ( v5_pre_topc(D_573,A_574,g1_pre_topc(u1_struct_0(B_575),u1_pre_topc(B_575)))
      | ~ v5_pre_topc(D_573,A_574,B_575)
      | ~ m1_subset_1(D_573,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_574),u1_struct_0(g1_pre_topc(u1_struct_0(B_575),u1_pre_topc(B_575))))))
      | ~ v1_funct_2(D_573,u1_struct_0(A_574),u1_struct_0(g1_pre_topc(u1_struct_0(B_575),u1_pre_topc(B_575))))
      | ~ m1_subset_1(D_573,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_574),u1_struct_0(B_575))))
      | ~ v1_funct_2(D_573,u1_struct_0(A_574),u1_struct_0(B_575))
      | ~ v1_funct_1(D_573)
      | ~ l1_pre_topc(B_575)
      | ~ v2_pre_topc(B_575)
      | ~ l1_pre_topc(A_574)
      | ~ v2_pre_topc(A_574) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6238,plain,(
    ! [D_573,A_574] :
      ( v5_pre_topc(D_573,A_574,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_573,A_574,'#skF_2')
      | ~ m1_subset_1(D_573,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_574),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(D_573,u1_struct_0(A_574),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_573,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_574),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_573,u1_struct_0(A_574),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_573)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_574)
      | ~ v2_pre_topc(A_574) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5120,c_6211])).

tff(c_6461,plain,(
    ! [D_579,A_580] :
      ( v5_pre_topc(D_579,A_580,k6_tmap_1('#skF_2','#skF_3'))
      | ~ v5_pre_topc(D_579,A_580,'#skF_2')
      | ~ m1_subset_1(D_579,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_580),k1_xboole_0)))
      | ~ v1_funct_2(D_579,u1_struct_0(A_580),k1_xboole_0)
      | ~ v1_funct_1(D_579)
      | ~ l1_pre_topc(A_580)
      | ~ v2_pre_topc(A_580) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_5120,c_5120,c_5113,c_5105,c_5120,c_5113,c_5105,c_5105,c_5120,c_6238])).

tff(c_6473,plain,(
    ! [D_579] :
      ( v5_pre_topc(D_579,'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
      | ~ v5_pre_topc(D_579,'#skF_2','#skF_2')
      | ~ m1_subset_1(D_579,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ v1_funct_2(D_579,u1_struct_0('#skF_2'),k1_xboole_0)
      | ~ v1_funct_1(D_579)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5120,c_6461])).

tff(c_6480,plain,(
    ! [D_581] :
      ( v5_pre_topc(D_581,'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
      | ~ v5_pre_topc(D_581,'#skF_2','#skF_2')
      | ~ m1_subset_1(D_581,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ v1_funct_2(D_581,k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_1(D_581) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_5120,c_6473])).

tff(c_6483,plain,
    ( v5_pre_topc(k6_partfun1(k1_xboole_0),'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
    | ~ v5_pre_topc(k6_partfun1(k1_xboole_0),'#skF_2','#skF_2')
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_5297,c_6480])).

tff(c_6486,plain,(
    v5_pre_topc(k6_partfun1(k1_xboole_0),'#skF_2',k6_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5205,c_5309,c_5535,c_6483])).

tff(c_6488,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5204,c_6486])).

tff(c_6490,plain,(
    ~ v5_pre_topc(k6_partfun1(k1_xboole_0),'#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_5534])).

tff(c_6489,plain,(
    v3_pre_topc('#skF_1'('#skF_2','#skF_2',k6_partfun1(k1_xboole_0)),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_5534])).

tff(c_5347,plain,(
    ! [A_518,B_519,C_520] :
      ( k2_struct_0(A_518) != k1_xboole_0
      | m1_subset_1('#skF_1'(A_518,B_519,C_520),k1_zfmisc_1(u1_struct_0(B_519)))
      | v5_pre_topc(C_520,A_518,B_519)
      | ~ m1_subset_1(C_520,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_518),u1_struct_0(B_519))))
      | ~ v1_funct_2(C_520,u1_struct_0(A_518),u1_struct_0(B_519))
      | ~ v1_funct_1(C_520)
      | ~ l1_pre_topc(B_519)
      | ~ l1_pre_topc(A_518) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_5353,plain,(
    ! [B_519,C_520] :
      ( k2_struct_0('#skF_2') != k1_xboole_0
      | m1_subset_1('#skF_1'('#skF_2',B_519,C_520),k1_zfmisc_1(u1_struct_0(B_519)))
      | v5_pre_topc(C_520,'#skF_2',B_519)
      | ~ m1_subset_1(C_520,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(B_519))))
      | ~ v1_funct_2(C_520,u1_struct_0('#skF_2'),u1_struct_0(B_519))
      | ~ v1_funct_1(C_520)
      | ~ l1_pre_topc(B_519)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5120,c_5347])).

tff(c_6491,plain,(
    ! [B_582,C_583] :
      ( m1_subset_1('#skF_1'('#skF_2',B_582,C_583),k1_zfmisc_1(u1_struct_0(B_582)))
      | v5_pre_topc(C_583,'#skF_2',B_582)
      | ~ m1_subset_1(C_583,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(B_582))))
      | ~ v1_funct_2(C_583,k1_xboole_0,u1_struct_0(B_582))
      | ~ v1_funct_1(C_583)
      | ~ l1_pre_topc(B_582) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_5120,c_5073,c_5353])).

tff(c_6522,plain,(
    ! [C_583] :
      ( m1_subset_1('#skF_1'('#skF_2','#skF_2',C_583),k1_zfmisc_1(k1_xboole_0))
      | v5_pre_topc(C_583,'#skF_2','#skF_2')
      | ~ m1_subset_1(C_583,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_583,k1_xboole_0,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_583)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5120,c_6491])).

tff(c_6535,plain,(
    ! [C_583] :
      ( m1_subset_1('#skF_1'('#skF_2','#skF_2',C_583),k1_zfmisc_1(k1_xboole_0))
      | v5_pre_topc(C_583,'#skF_2','#skF_2')
      | ~ m1_subset_1(C_583,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ v1_funct_2(C_583,k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_1(C_583) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_5120,c_5120,c_6522])).

tff(c_6556,plain,(
    ! [C_588] :
      ( m1_subset_1('#skF_1'('#skF_2','#skF_2',C_588),k1_zfmisc_1(k1_xboole_0))
      | v5_pre_topc(C_588,'#skF_2','#skF_2')
      | ~ m1_subset_1(C_588,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ v1_funct_2(C_588,k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_1(C_588) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_5120,c_5120,c_6522])).

tff(c_28,plain,(
    ! [A_42,B_44] :
      ( k7_tmap_1(A_42,B_44) = k6_partfun1(u1_struct_0(A_42))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42)
      | ~ v2_pre_topc(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_5145,plain,(
    ! [B_44] :
      ( k7_tmap_1('#skF_2',B_44) = k6_partfun1(u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(k1_xboole_0))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5120,c_28])).

tff(c_5183,plain,(
    ! [B_44] :
      ( k7_tmap_1('#skF_2',B_44) = k6_partfun1(k1_xboole_0)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(k1_xboole_0))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_5120,c_5145])).

tff(c_5184,plain,(
    ! [B_44] :
      ( k7_tmap_1('#skF_2',B_44) = k6_partfun1(k1_xboole_0)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_5183])).

tff(c_6604,plain,(
    ! [C_590] :
      ( k7_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_2',C_590)) = k6_partfun1(k1_xboole_0)
      | v5_pre_topc(C_590,'#skF_2','#skF_2')
      | ~ m1_subset_1(C_590,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ v1_funct_2(C_590,k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_1(C_590) ) ),
    inference(resolution,[status(thm)],[c_6556,c_5184])).

tff(c_6607,plain,
    ( k7_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_2',k6_partfun1(k1_xboole_0))) = k6_partfun1(k1_xboole_0)
    | v5_pre_topc(k6_partfun1(k1_xboole_0),'#skF_2','#skF_2')
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_5297,c_6604])).

tff(c_6610,plain,
    ( k7_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_2',k6_partfun1(k1_xboole_0))) = k6_partfun1(k1_xboole_0)
    | v5_pre_topc(k6_partfun1(k1_xboole_0),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5205,c_5309,c_6607])).

tff(c_6611,plain,(
    k7_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_2',k6_partfun1(k1_xboole_0))) = k6_partfun1(k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_6490,c_6610])).

tff(c_4930,plain,(
    ! [B_494] :
      ( v1_funct_2(k7_tmap_1('#skF_2',B_494),k2_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2',B_494)))
      | ~ m1_subset_1(B_494,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_4921])).

tff(c_4937,plain,(
    ! [B_494] :
      ( v1_funct_2(k7_tmap_1('#skF_2',B_494),k2_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2',B_494)))
      | ~ m1_subset_1(B_494,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_89,c_4930])).

tff(c_4938,plain,(
    ! [B_494] :
      ( v1_funct_2(k7_tmap_1('#skF_2',B_494),k2_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2',B_494)))
      | ~ m1_subset_1(B_494,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4937])).

tff(c_5106,plain,(
    ! [B_494] :
      ( v1_funct_2(k7_tmap_1('#skF_2',B_494),k1_xboole_0,u1_struct_0(k6_tmap_1('#skF_2',B_494)))
      | ~ m1_subset_1(B_494,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5073,c_5073,c_4938])).

tff(c_6618,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_2',k6_partfun1(k1_xboole_0)))))
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_2',k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6611,c_5106])).

tff(c_6634,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_2',k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_6618])).

tff(c_6637,plain,
    ( v5_pre_topc(k6_partfun1(k1_xboole_0),'#skF_2','#skF_2')
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_6535,c_6634])).

tff(c_6640,plain,(
    v5_pre_topc(k6_partfun1(k1_xboole_0),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5205,c_5309,c_5297,c_6637])).

tff(c_6642,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6490,c_6640])).

tff(c_6644,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_2',k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_6618])).

tff(c_6689,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),'#skF_1'('#skF_2','#skF_2',k6_partfun1(k1_xboole_0))) = '#skF_1'('#skF_2','#skF_2',k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_6644,c_2])).

tff(c_5495,plain,(
    ! [A_537,B_538,C_539] :
      ( k2_struct_0(A_537) != k1_xboole_0
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(A_537),u1_struct_0(B_538),C_539,'#skF_1'(A_537,B_538,C_539)),A_537)
      | v5_pre_topc(C_539,A_537,B_538)
      | ~ m1_subset_1(C_539,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_537),u1_struct_0(B_538))))
      | ~ v1_funct_2(C_539,u1_struct_0(A_537),u1_struct_0(B_538))
      | ~ v1_funct_1(C_539)
      | ~ l1_pre_topc(B_538)
      | ~ l1_pre_topc(A_537) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_5504,plain,(
    ! [B_538,C_539] :
      ( k2_struct_0('#skF_2') != k1_xboole_0
      | ~ v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(B_538),C_539,'#skF_1'('#skF_2',B_538,C_539)),'#skF_2')
      | v5_pre_topc(C_539,'#skF_2',B_538)
      | ~ m1_subset_1(C_539,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_538))))
      | ~ v1_funct_2(C_539,u1_struct_0('#skF_2'),u1_struct_0(B_538))
      | ~ v1_funct_1(C_539)
      | ~ l1_pre_topc(B_538)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5120,c_5495])).

tff(c_9399,plain,(
    ! [B_665,C_666] :
      ( ~ v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(B_665),C_666,'#skF_1'('#skF_2',B_665,C_666)),'#skF_2')
      | v5_pre_topc(C_666,'#skF_2',B_665)
      | ~ m1_subset_1(C_666,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(B_665))))
      | ~ v1_funct_2(C_666,k1_xboole_0,u1_struct_0(B_665))
      | ~ v1_funct_1(C_666)
      | ~ l1_pre_topc(B_665) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_5120,c_5120,c_5073,c_5504])).

tff(c_9417,plain,(
    ! [C_666] :
      ( ~ v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,C_666,'#skF_1'('#skF_2','#skF_2',C_666)),'#skF_2')
      | v5_pre_topc(C_666,'#skF_2','#skF_2')
      | ~ m1_subset_1(C_666,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_666,k1_xboole_0,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_666)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5120,c_9399])).

tff(c_9426,plain,(
    ! [C_667] :
      ( ~ v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,C_667,'#skF_1'('#skF_2','#skF_2',C_667)),'#skF_2')
      | v5_pre_topc(C_667,'#skF_2','#skF_2')
      | ~ m1_subset_1(C_667,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ v1_funct_2(C_667,k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_1(C_667) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_5120,c_5120,c_9417])).

tff(c_9429,plain,
    ( ~ v3_pre_topc('#skF_1'('#skF_2','#skF_2',k6_partfun1(k1_xboole_0)),'#skF_2')
    | v5_pre_topc(k6_partfun1(k1_xboole_0),'#skF_2','#skF_2')
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6689,c_9426])).

tff(c_9431,plain,(
    v5_pre_topc(k6_partfun1(k1_xboole_0),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5205,c_5309,c_5297,c_6489,c_9429])).

tff(c_9433,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6490,c_9431])).

tff(c_9436,plain,(
    ! [C_668] :
      ( v3_pre_topc('#skF_1'('#skF_2','#skF_2',C_668),'#skF_2')
      | v5_pre_topc(C_668,'#skF_2','#skF_2')
      | ~ m1_subset_1(C_668,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_668,k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_668) ) ),
    inference(splitRight,[status(thm)],[c_5072])).

tff(c_9439,plain,
    ( v3_pre_topc('#skF_1'('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3')),'#skF_2')
    | v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_5021,c_9436])).

tff(c_9442,plain,
    ( v3_pre_topc('#skF_1'('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3')),'#skF_2')
    | v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_4935,c_9439])).

tff(c_9463,plain,(
    v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_9442])).

tff(c_10283,plain,(
    ! [D_711,A_712,B_713] :
      ( v5_pre_topc(D_711,A_712,g1_pre_topc(u1_struct_0(B_713),u1_pre_topc(B_713)))
      | ~ v5_pre_topc(D_711,A_712,B_713)
      | ~ m1_subset_1(D_711,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_712),u1_struct_0(g1_pre_topc(u1_struct_0(B_713),u1_pre_topc(B_713))))))
      | ~ v1_funct_2(D_711,u1_struct_0(A_712),u1_struct_0(g1_pre_topc(u1_struct_0(B_713),u1_pre_topc(B_713))))
      | ~ m1_subset_1(D_711,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_712),u1_struct_0(B_713))))
      | ~ v1_funct_2(D_711,u1_struct_0(A_712),u1_struct_0(B_713))
      | ~ v1_funct_1(D_711)
      | ~ l1_pre_topc(B_713)
      | ~ v2_pre_topc(B_713)
      | ~ l1_pre_topc(A_712)
      | ~ v2_pre_topc(A_712) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10307,plain,(
    ! [D_711,A_712] :
      ( v5_pre_topc(D_711,A_712,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_711,A_712,'#skF_2')
      | ~ m1_subset_1(D_711,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_712),u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(D_711,u1_struct_0(A_712),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_711,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_712),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_711,u1_struct_0(A_712),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_711)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_712)
      | ~ v2_pre_topc(A_712) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_10283])).

tff(c_10324,plain,(
    ! [D_714,A_715] :
      ( v5_pre_topc(D_714,A_715,k6_tmap_1('#skF_2','#skF_3'))
      | ~ v5_pre_topc(D_714,A_715,'#skF_2')
      | ~ m1_subset_1(D_714,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_715),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_714,u1_struct_0(A_715),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(D_714)
      | ~ l1_pre_topc(A_715)
      | ~ v2_pre_topc(A_715) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_89,c_89,c_4823,c_4976,c_89,c_4823,c_4976,c_4976,c_89,c_10307])).

tff(c_10333,plain,(
    ! [D_714] :
      ( v5_pre_topc(D_714,'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
      | ~ v5_pre_topc(D_714,'#skF_2','#skF_2')
      | ~ m1_subset_1(D_714,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_714,u1_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(D_714)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_10324])).

tff(c_10340,plain,(
    ! [D_716] :
      ( v5_pre_topc(D_716,'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
      | ~ v5_pre_topc(D_716,'#skF_2','#skF_2')
      | ~ m1_subset_1(D_716,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_716,k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(D_716) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_89,c_10333])).

tff(c_10343,plain,
    ( v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2',k6_tmap_1('#skF_2','#skF_3'))
    | ~ v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_5021,c_10340])).

tff(c_10346,plain,(
    v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2',k6_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_4935,c_9463,c_10343])).

tff(c_10348,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4725,c_10346])).

tff(c_10350,plain,(
    ~ v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_9442])).

tff(c_10349,plain,(
    v3_pre_topc('#skF_1'('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_9442])).

tff(c_9435,plain,(
    k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_5072])).

tff(c_10395,plain,(
    ! [B_721,A_722,C_723] :
      ( k2_struct_0(B_721) = k1_xboole_0
      | m1_subset_1('#skF_1'(A_722,B_721,C_723),k1_zfmisc_1(u1_struct_0(B_721)))
      | v5_pre_topc(C_723,A_722,B_721)
      | ~ m1_subset_1(C_723,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_722),u1_struct_0(B_721))))
      | ~ v1_funct_2(C_723,u1_struct_0(A_722),u1_struct_0(B_721))
      | ~ v1_funct_1(C_723)
      | ~ l1_pre_topc(B_721)
      | ~ l1_pre_topc(A_722) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_10405,plain,(
    ! [A_722,C_723] :
      ( k2_struct_0('#skF_2') = k1_xboole_0
      | m1_subset_1('#skF_1'(A_722,'#skF_2',C_723),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v5_pre_topc(C_723,A_722,'#skF_2')
      | ~ m1_subset_1(C_723,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_722),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_723,u1_struct_0(A_722),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_723)
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_722) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_10395])).

tff(c_10415,plain,(
    ! [A_722,C_723] :
      ( k2_struct_0('#skF_2') = k1_xboole_0
      | m1_subset_1('#skF_1'(A_722,'#skF_2',C_723),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v5_pre_topc(C_723,A_722,'#skF_2')
      | ~ m1_subset_1(C_723,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_722),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_723,u1_struct_0(A_722),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_723)
      | ~ l1_pre_topc(A_722) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_89,c_89,c_10405])).

tff(c_10417,plain,(
    ! [A_724,C_725] :
      ( m1_subset_1('#skF_1'(A_724,'#skF_2',C_725),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v5_pre_topc(C_725,A_724,'#skF_2')
      | ~ m1_subset_1(C_725,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_724),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_725,u1_struct_0(A_724),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_725)
      | ~ l1_pre_topc(A_724) ) ),
    inference(negUnitSimplification,[status(thm)],[c_9435,c_10415])).

tff(c_10423,plain,(
    ! [C_725] :
      ( m1_subset_1('#skF_1'('#skF_2','#skF_2',C_725),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v5_pre_topc(C_725,'#skF_2','#skF_2')
      | ~ m1_subset_1(C_725,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_725,u1_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_725)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_10417])).

tff(c_10428,plain,(
    ! [C_726] :
      ( m1_subset_1('#skF_1'('#skF_2','#skF_2',C_726),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v5_pre_topc(C_726,'#skF_2','#skF_2')
      | ~ m1_subset_1(C_726,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_726,k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_726) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_89,c_10423])).

tff(c_10431,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3')),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_5021,c_10428])).

tff(c_10434,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3')),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_4935,c_10431])).

tff(c_10435,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3')),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_10350,c_10434])).

tff(c_10464,plain,(
    k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k6_partfun1(k2_struct_0('#skF_2')),'#skF_1'('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'))) = '#skF_1'('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_10435,c_2])).

tff(c_10478,plain,(
    k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),k7_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'))) = '#skF_1'('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4876,c_10464])).

tff(c_10609,plain,(
    ! [B_730,A_731,C_732] :
      ( k2_struct_0(B_730) = k1_xboole_0
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(A_731),u1_struct_0(B_730),C_732,'#skF_1'(A_731,B_730,C_732)),A_731)
      | v5_pre_topc(C_732,A_731,B_730)
      | ~ m1_subset_1(C_732,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_731),u1_struct_0(B_730))))
      | ~ v1_funct_2(C_732,u1_struct_0(A_731),u1_struct_0(B_730))
      | ~ v1_funct_1(C_732)
      | ~ l1_pre_topc(B_730)
      | ~ l1_pre_topc(A_731) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_10621,plain,(
    ! [A_731,C_732] :
      ( k2_struct_0('#skF_2') = k1_xboole_0
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(A_731),k2_struct_0('#skF_2'),C_732,'#skF_1'(A_731,'#skF_2',C_732)),A_731)
      | v5_pre_topc(C_732,A_731,'#skF_2')
      | ~ m1_subset_1(C_732,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_731),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_732,u1_struct_0(A_731),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_732)
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_731) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_10609])).

tff(c_10630,plain,(
    ! [A_731,C_732] :
      ( k2_struct_0('#skF_2') = k1_xboole_0
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(A_731),k2_struct_0('#skF_2'),C_732,'#skF_1'(A_731,'#skF_2',C_732)),A_731)
      | v5_pre_topc(C_732,A_731,'#skF_2')
      | ~ m1_subset_1(C_732,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_731),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_732,u1_struct_0(A_731),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_732)
      | ~ l1_pre_topc(A_731) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_89,c_89,c_10621])).

tff(c_11631,plain,(
    ! [A_776,C_777] :
      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(A_776),k2_struct_0('#skF_2'),C_777,'#skF_1'(A_776,'#skF_2',C_777)),A_776)
      | v5_pre_topc(C_777,A_776,'#skF_2')
      | ~ m1_subset_1(C_777,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_776),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_777,u1_struct_0(A_776),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_777)
      | ~ l1_pre_topc(A_776) ) ),
    inference(negUnitSimplification,[status(thm)],[c_9435,c_10630])).

tff(c_11640,plain,(
    ! [C_777] :
      ( ~ v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),C_777,'#skF_1'('#skF_2','#skF_2',C_777)),'#skF_2')
      | v5_pre_topc(C_777,'#skF_2','#skF_2')
      | ~ m1_subset_1(C_777,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_777,u1_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_777)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_11631])).

tff(c_11647,plain,(
    ! [C_778] :
      ( ~ v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),C_778,'#skF_1'('#skF_2','#skF_2',C_778)),'#skF_2')
      | v5_pre_topc(C_778,'#skF_2','#skF_2')
      | ~ m1_subset_1(C_778,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_778,k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_778) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_89,c_89,c_11640])).

tff(c_11650,plain,
    ( ~ v3_pre_topc('#skF_1'('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3')),'#skF_2')
    | v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10478,c_11647])).

tff(c_11652,plain,(
    v5_pre_topc(k7_tmap_1('#skF_2','#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_4935,c_5021,c_10349,c_11650])).

tff(c_11654,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10350,c_11652])).

tff(c_11656,plain,(
    ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_11667,plain,(
    ! [A_781,B_782] :
      ( v1_funct_1(k7_tmap_1(A_781,B_782))
      | ~ m1_subset_1(B_782,k1_zfmisc_1(u1_struct_0(A_781)))
      | ~ l1_pre_topc(A_781)
      | ~ v2_pre_topc(A_781)
      | v2_struct_0(A_781) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_11670,plain,(
    ! [B_782] :
      ( v1_funct_1(k7_tmap_1('#skF_2',B_782))
      | ~ m1_subset_1(B_782,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_11667])).

tff(c_11672,plain,(
    ! [B_782] :
      ( v1_funct_1(k7_tmap_1('#skF_2',B_782))
      | ~ m1_subset_1(B_782,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_11670])).

tff(c_11674,plain,(
    ! [B_783] :
      ( v1_funct_1(k7_tmap_1('#skF_2',B_783))
      | ~ m1_subset_1(B_783,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_11672])).

tff(c_11677,plain,(
    v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_90,c_11674])).

tff(c_11681,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11656,c_11677])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:22:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.74/3.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.74/3.96  
% 10.74/3.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.74/3.97  %$ v5_pre_topc > v1_funct_2 > v3_pre_topc > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k7_tmap_1 > k6_tmap_1 > k5_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k6_partfun1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 10.74/3.97  
% 10.74/3.97  %Foreground sorts:
% 10.74/3.97  
% 10.74/3.97  
% 10.74/3.97  %Background operators:
% 10.74/3.97  
% 10.74/3.97  
% 10.74/3.97  %Foreground operators:
% 10.74/3.97  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.74/3.97  tff(k7_tmap_1, type, k7_tmap_1: ($i * $i) > $i).
% 10.74/3.97  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.74/3.97  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 10.74/3.97  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.74/3.97  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 10.74/3.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.74/3.97  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 10.74/3.97  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 10.74/3.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.74/3.97  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.74/3.97  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.74/3.97  tff('#skF_2', type, '#skF_2': $i).
% 10.74/3.97  tff('#skF_3', type, '#skF_3': $i).
% 10.74/3.97  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 10.74/3.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.74/3.97  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 10.74/3.97  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 10.74/3.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.74/3.97  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.74/3.97  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 10.74/3.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.74/3.97  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 10.74/3.97  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.74/3.97  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 10.74/3.97  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.74/3.97  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 10.74/3.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.74/3.97  
% 11.21/4.01  tff(f_199, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (((v1_funct_1(k7_tmap_1(A, B)) & v1_funct_2(k7_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))) & v5_pre_topc(k7_tmap_1(A, B), A, k6_tmap_1(A, B))) & m1_subset_1(k7_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_tmap_1)).
% 11.21/4.01  tff(f_37, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 11.21/4.01  tff(f_33, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 11.21/4.01  tff(f_147, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 11.21/4.01  tff(f_118, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 11.21/4.01  tff(f_164, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k6_tmap_1(A, B)))) => ((C = B) => v3_pre_topc(C, k6_tmap_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_tmap_1)).
% 11.21/4.01  tff(f_103, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k7_tmap_1(A, B) = k6_partfun1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_tmap_1)).
% 11.21/4.01  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 11.21/4.01  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_struct_0(B) = k1_xboole_0) => (k2_struct_0(A) = k1_xboole_0)) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (v3_pre_topc(D, B) => v3_pre_topc(k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), A)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_2)).
% 11.21/4.01  tff(f_133, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_funct_1(k7_tmap_1(A, B)) & v1_funct_2(k7_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))) & m1_subset_1(k7_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 11.21/4.01  tff(f_178, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_tmap_1)).
% 11.21/4.01  tff(f_66, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(A), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))) => ((C = D) => (v5_pre_topc(C, A, B) <=> v5_pre_topc(D, A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_pre_topc)).
% 11.21/4.01  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 11.21/4.01  tff(c_54, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 11.21/4.01  tff(c_6, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.21/4.01  tff(c_80, plain, (![A_64]: (u1_struct_0(A_64)=k2_struct_0(A_64) | ~l1_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.21/4.01  tff(c_85, plain, (![A_65]: (u1_struct_0(A_65)=k2_struct_0(A_65) | ~l1_pre_topc(A_65))), inference(resolution, [status(thm)], [c_6, c_80])).
% 11.21/4.01  tff(c_89, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_85])).
% 11.21/4.01  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_199])).
% 11.21/4.01  tff(c_90, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_52])).
% 11.21/4.01  tff(c_56, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 11.21/4.01  tff(c_4596, plain, (![A_460, B_461]: (u1_struct_0(k6_tmap_1(A_460, B_461))=u1_struct_0(A_460) | ~m1_subset_1(B_461, k1_zfmisc_1(u1_struct_0(A_460))) | ~l1_pre_topc(A_460) | ~v2_pre_topc(A_460) | v2_struct_0(A_460))), inference(cnfTransformation, [status(thm)], [f_147])).
% 11.21/4.01  tff(c_4602, plain, (![B_461]: (u1_struct_0(k6_tmap_1('#skF_2', B_461))=u1_struct_0('#skF_2') | ~m1_subset_1(B_461, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_4596])).
% 11.21/4.01  tff(c_4606, plain, (![B_461]: (u1_struct_0(k6_tmap_1('#skF_2', B_461))=k2_struct_0('#skF_2') | ~m1_subset_1(B_461, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_89, c_4602])).
% 11.21/4.01  tff(c_4608, plain, (![B_462]: (u1_struct_0(k6_tmap_1('#skF_2', B_462))=k2_struct_0('#skF_2') | ~m1_subset_1(B_462, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_4606])).
% 11.21/4.01  tff(c_4612, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_90, c_4608])).
% 11.21/4.01  tff(c_4473, plain, (![A_444, B_445]: (l1_pre_topc(k6_tmap_1(A_444, B_445)) | ~m1_subset_1(B_445, k1_zfmisc_1(u1_struct_0(A_444))) | ~l1_pre_topc(A_444) | ~v2_pre_topc(A_444) | v2_struct_0(A_444))), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.21/4.01  tff(c_4476, plain, (![B_445]: (l1_pre_topc(k6_tmap_1('#skF_2', B_445)) | ~m1_subset_1(B_445, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_4473])).
% 11.21/4.01  tff(c_4478, plain, (![B_445]: (l1_pre_topc(k6_tmap_1('#skF_2', B_445)) | ~m1_subset_1(B_445, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_4476])).
% 11.21/4.01  tff(c_4480, plain, (![B_446]: (l1_pre_topc(k6_tmap_1('#skF_2', B_446)) | ~m1_subset_1(B_446, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_4478])).
% 11.21/4.01  tff(c_4484, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_90, c_4480])).
% 11.21/4.01  tff(c_84, plain, (![A_4]: (u1_struct_0(A_4)=k2_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(resolution, [status(thm)], [c_6, c_80])).
% 11.21/4.01  tff(c_4495, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4484, c_84])).
% 11.21/4.01  tff(c_4613, plain, (k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4612, c_4495])).
% 11.21/4.01  tff(c_4275, plain, (![A_423, B_424]: (u1_struct_0(k6_tmap_1(A_423, B_424))=u1_struct_0(A_423) | ~m1_subset_1(B_424, k1_zfmisc_1(u1_struct_0(A_423))) | ~l1_pre_topc(A_423) | ~v2_pre_topc(A_423) | v2_struct_0(A_423))), inference(cnfTransformation, [status(thm)], [f_147])).
% 11.21/4.01  tff(c_4281, plain, (![B_424]: (u1_struct_0(k6_tmap_1('#skF_2', B_424))=u1_struct_0('#skF_2') | ~m1_subset_1(B_424, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_4275])).
% 11.21/4.01  tff(c_4285, plain, (![B_424]: (u1_struct_0(k6_tmap_1('#skF_2', B_424))=k2_struct_0('#skF_2') | ~m1_subset_1(B_424, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_89, c_4281])).
% 11.21/4.01  tff(c_4287, plain, (![B_425]: (u1_struct_0(k6_tmap_1('#skF_2', B_425))=k2_struct_0('#skF_2') | ~m1_subset_1(B_425, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_4285])).
% 11.21/4.01  tff(c_4291, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_90, c_4287])).
% 11.21/4.01  tff(c_4183, plain, (![A_414, B_415]: (l1_pre_topc(k6_tmap_1(A_414, B_415)) | ~m1_subset_1(B_415, k1_zfmisc_1(u1_struct_0(A_414))) | ~l1_pre_topc(A_414) | ~v2_pre_topc(A_414) | v2_struct_0(A_414))), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.21/4.01  tff(c_4186, plain, (![B_415]: (l1_pre_topc(k6_tmap_1('#skF_2', B_415)) | ~m1_subset_1(B_415, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_4183])).
% 11.21/4.01  tff(c_4188, plain, (![B_415]: (l1_pre_topc(k6_tmap_1('#skF_2', B_415)) | ~m1_subset_1(B_415, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_4186])).
% 11.21/4.01  tff(c_4190, plain, (![B_416]: (l1_pre_topc(k6_tmap_1('#skF_2', B_416)) | ~m1_subset_1(B_416, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_4188])).
% 11.21/4.01  tff(c_4194, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_90, c_4190])).
% 11.21/4.01  tff(c_4198, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4194, c_84])).
% 11.21/4.01  tff(c_4292, plain, (k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4291, c_4198])).
% 11.21/4.01  tff(c_4068, plain, (![A_404, B_405]: (u1_struct_0(k6_tmap_1(A_404, B_405))=u1_struct_0(A_404) | ~m1_subset_1(B_405, k1_zfmisc_1(u1_struct_0(A_404))) | ~l1_pre_topc(A_404) | ~v2_pre_topc(A_404) | v2_struct_0(A_404))), inference(cnfTransformation, [status(thm)], [f_147])).
% 11.21/4.01  tff(c_4074, plain, (![B_405]: (u1_struct_0(k6_tmap_1('#skF_2', B_405))=u1_struct_0('#skF_2') | ~m1_subset_1(B_405, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_4068])).
% 11.21/4.01  tff(c_4078, plain, (![B_405]: (u1_struct_0(k6_tmap_1('#skF_2', B_405))=k2_struct_0('#skF_2') | ~m1_subset_1(B_405, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_89, c_4074])).
% 11.21/4.01  tff(c_4090, plain, (![B_406]: (u1_struct_0(k6_tmap_1('#skF_2', B_406))=k2_struct_0('#skF_2') | ~m1_subset_1(B_406, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_4078])).
% 11.21/4.01  tff(c_4094, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_90, c_4090])).
% 11.21/4.01  tff(c_137, plain, (![A_74, B_75]: (l1_pre_topc(k6_tmap_1(A_74, B_75)) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.21/4.01  tff(c_140, plain, (![B_75]: (l1_pre_topc(k6_tmap_1('#skF_2', B_75)) | ~m1_subset_1(B_75, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_137])).
% 11.21/4.01  tff(c_142, plain, (![B_75]: (l1_pre_topc(k6_tmap_1('#skF_2', B_75)) | ~m1_subset_1(B_75, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_140])).
% 11.21/4.01  tff(c_151, plain, (![B_78]: (l1_pre_topc(k6_tmap_1('#skF_2', B_78)) | ~m1_subset_1(B_78, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_142])).
% 11.21/4.01  tff(c_155, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_90, c_151])).
% 11.21/4.01  tff(c_159, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_155, c_84])).
% 11.21/4.01  tff(c_4095, plain, (k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4094, c_159])).
% 11.21/4.01  tff(c_66, plain, (v3_pre_topc('#skF_3', '#skF_2') | m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))))), inference(cnfTransformation, [status(thm)], [f_199])).
% 11.21/4.01  tff(c_120, plain, (v3_pre_topc('#skF_3', '#skF_2') | m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_66])).
% 11.21/4.01  tff(c_121, plain, (m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))))), inference(splitLeft, [status(thm)], [c_120])).
% 11.21/4.01  tff(c_160, plain, (m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0(k6_tmap_1('#skF_2', '#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_121])).
% 11.21/4.01  tff(c_4130, plain, (m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_4095, c_160])).
% 11.21/4.01  tff(c_74, plain, (v3_pre_topc('#skF_3', '#skF_2') | v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_199])).
% 11.21/4.01  tff(c_105, plain, (v3_pre_topc('#skF_3', '#skF_2') | v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_74])).
% 11.21/4.01  tff(c_106, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_105])).
% 11.21/4.01  tff(c_161, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0(k6_tmap_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_106])).
% 11.21/4.01  tff(c_4131, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4095, c_161])).
% 11.21/4.01  tff(c_78, plain, (v3_pre_topc('#skF_3', '#skF_2') | v1_funct_1(k7_tmap_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_199])).
% 11.21/4.01  tff(c_95, plain, (v1_funct_1(k7_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_78])).
% 11.21/4.01  tff(c_70, plain, (v3_pre_topc('#skF_3', '#skF_2') | v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', k6_tmap_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_199])).
% 11.21/4.01  tff(c_104, plain, (v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', k6_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_70])).
% 11.21/4.01  tff(c_60, plain, (~m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))))) | ~v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k7_tmap_1('#skF_2', '#skF_3')) | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 11.21/4.01  tff(c_187, plain, (~m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))))) | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))) | ~v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_159, c_89, c_104, c_159, c_89, c_60])).
% 11.21/4.01  tff(c_188, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_187])).
% 11.21/4.01  tff(c_230, plain, (![A_84, B_85]: (u1_struct_0(k6_tmap_1(A_84, B_85))=u1_struct_0(A_84) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84) | ~v2_pre_topc(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_147])).
% 11.21/4.01  tff(c_236, plain, (![B_85]: (u1_struct_0(k6_tmap_1('#skF_2', B_85))=u1_struct_0('#skF_2') | ~m1_subset_1(B_85, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_230])).
% 11.21/4.01  tff(c_240, plain, (![B_85]: (u1_struct_0(k6_tmap_1('#skF_2', B_85))=k2_struct_0('#skF_2') | ~m1_subset_1(B_85, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_89, c_236])).
% 11.21/4.01  tff(c_242, plain, (![B_86]: (u1_struct_0(k6_tmap_1('#skF_2', B_86))=k2_struct_0('#skF_2') | ~m1_subset_1(B_86, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_240])).
% 11.21/4.01  tff(c_246, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_90, c_242])).
% 11.21/4.01  tff(c_396, plain, (![C_99, A_100]: (v3_pre_topc(C_99, k6_tmap_1(A_100, C_99)) | ~m1_subset_1(C_99, k1_zfmisc_1(u1_struct_0(k6_tmap_1(A_100, C_99)))) | ~m1_subset_1(C_99, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100) | ~v2_pre_topc(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_164])).
% 11.21/4.01  tff(c_399, plain, (v3_pre_topc('#skF_3', k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_246, c_396])).
% 11.21/4.01  tff(c_401, plain, (v3_pre_topc('#skF_3', k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_90, c_89, c_90, c_399])).
% 11.21/4.01  tff(c_402, plain, (v3_pre_topc('#skF_3', k6_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_401])).
% 11.21/4.01  tff(c_197, plain, (![A_80, B_81]: (k7_tmap_1(A_80, B_81)=k6_partfun1(u1_struct_0(A_80)) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80) | ~v2_pre_topc(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.21/4.01  tff(c_203, plain, (![B_81]: (k7_tmap_1('#skF_2', B_81)=k6_partfun1(u1_struct_0('#skF_2')) | ~m1_subset_1(B_81, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_197])).
% 11.21/4.01  tff(c_207, plain, (![B_81]: (k7_tmap_1('#skF_2', B_81)=k6_partfun1(k2_struct_0('#skF_2')) | ~m1_subset_1(B_81, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_89, c_203])).
% 11.21/4.01  tff(c_209, plain, (![B_82]: (k7_tmap_1('#skF_2', B_82)=k6_partfun1(k2_struct_0('#skF_2')) | ~m1_subset_1(B_82, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_207])).
% 11.21/4.01  tff(c_213, plain, (k6_partfun1(k2_struct_0('#skF_2'))=k7_tmap_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_90, c_209])).
% 11.21/4.01  tff(c_96, plain, (![A_66, B_67]: (k8_relset_1(A_66, A_66, k6_partfun1(A_66), B_67)=B_67 | ~m1_subset_1(B_67, k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.21/4.01  tff(c_99, plain, (k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k6_partfun1(k2_struct_0('#skF_2')), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_90, c_96])).
% 11.21/4.01  tff(c_215, plain, (k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k7_tmap_1('#skF_2', '#skF_3'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_213, c_99])).
% 11.21/4.01  tff(c_247, plain, (k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_246, c_159])).
% 11.21/4.01  tff(c_283, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_247, c_161])).
% 11.21/4.01  tff(c_282, plain, (m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_247, c_160])).
% 11.21/4.01  tff(c_424, plain, (![A_103, B_104, C_105]: (k2_struct_0(A_103)!=k1_xboole_0 | v3_pre_topc('#skF_1'(A_103, B_104, C_105), B_104) | v5_pre_topc(C_105, A_103, B_104) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_103), u1_struct_0(B_104)))) | ~v1_funct_2(C_105, u1_struct_0(A_103), u1_struct_0(B_104)) | ~v1_funct_1(C_105) | ~l1_pre_topc(B_104) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.21/4.01  tff(c_432, plain, (![B_104, C_105]: (k2_struct_0('#skF_2')!=k1_xboole_0 | v3_pre_topc('#skF_1'('#skF_2', B_104, C_105), B_104) | v5_pre_topc(C_105, '#skF_2', B_104) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(B_104)))) | ~v1_funct_2(C_105, u1_struct_0('#skF_2'), u1_struct_0(B_104)) | ~v1_funct_1(C_105) | ~l1_pre_topc(B_104) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_424])).
% 11.21/4.01  tff(c_441, plain, (![B_104, C_105]: (k2_struct_0('#skF_2')!=k1_xboole_0 | v3_pre_topc('#skF_1'('#skF_2', B_104, C_105), B_104) | v5_pre_topc(C_105, '#skF_2', B_104) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(B_104)))) | ~v1_funct_2(C_105, k2_struct_0('#skF_2'), u1_struct_0(B_104)) | ~v1_funct_1(C_105) | ~l1_pre_topc(B_104))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_89, c_432])).
% 11.21/4.01  tff(c_454, plain, (k2_struct_0('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_441])).
% 11.21/4.01  tff(c_988, plain, (![B_172, A_173, C_174, D_175]: (k2_struct_0(B_172)=k1_xboole_0 | v3_pre_topc(k8_relset_1(u1_struct_0(A_173), u1_struct_0(B_172), C_174, D_175), A_173) | ~v3_pre_topc(D_175, B_172) | ~m1_subset_1(D_175, k1_zfmisc_1(u1_struct_0(B_172))) | ~v5_pre_topc(C_174, A_173, B_172) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_173), u1_struct_0(B_172)))) | ~v1_funct_2(C_174, u1_struct_0(A_173), u1_struct_0(B_172)) | ~v1_funct_1(C_174) | ~l1_pre_topc(B_172) | ~l1_pre_topc(A_173))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.21/4.01  tff(c_996, plain, (![B_172, C_174, D_175]: (k2_struct_0(B_172)=k1_xboole_0 | v3_pre_topc(k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_172), C_174, D_175), '#skF_2') | ~v3_pre_topc(D_175, B_172) | ~m1_subset_1(D_175, k1_zfmisc_1(u1_struct_0(B_172))) | ~v5_pre_topc(C_174, '#skF_2', B_172) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(B_172)))) | ~v1_funct_2(C_174, u1_struct_0('#skF_2'), u1_struct_0(B_172)) | ~v1_funct_1(C_174) | ~l1_pre_topc(B_172) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_988])).
% 11.21/4.01  tff(c_1446, plain, (![B_227, C_228, D_229]: (k2_struct_0(B_227)=k1_xboole_0 | v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'), u1_struct_0(B_227), C_228, D_229), '#skF_2') | ~v3_pre_topc(D_229, B_227) | ~m1_subset_1(D_229, k1_zfmisc_1(u1_struct_0(B_227))) | ~v5_pre_topc(C_228, '#skF_2', B_227) | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(B_227)))) | ~v1_funct_2(C_228, k2_struct_0('#skF_2'), u1_struct_0(B_227)) | ~v1_funct_1(C_228) | ~l1_pre_topc(B_227))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_89, c_89, c_996])).
% 11.21/4.01  tff(c_1450, plain, (![C_228, D_229]: (k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k1_xboole_0 | v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')), C_228, D_229), '#skF_2') | ~v3_pre_topc(D_229, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_229, k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))) | ~v5_pre_topc(C_228, '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_228, k2_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(C_228) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_246, c_1446])).
% 11.21/4.01  tff(c_1455, plain, (![C_228, D_229]: (k2_struct_0('#skF_2')=k1_xboole_0 | v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), C_228, D_229), '#skF_2') | ~v3_pre_topc(D_229, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_229, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v5_pre_topc(C_228, '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_228, k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_228))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_246, c_246, c_246, c_247, c_1450])).
% 11.21/4.01  tff(c_1478, plain, (![C_232, D_233]: (v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), C_232, D_233), '#skF_2') | ~v3_pre_topc(D_233, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_233, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v5_pre_topc(C_232, '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_232, k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_232))), inference(negUnitSimplification, [status(thm)], [c_454, c_1455])).
% 11.21/4.01  tff(c_1480, plain, (![D_233]: (v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k7_tmap_1('#skF_2', '#skF_3'), D_233), '#skF_2') | ~v3_pre_topc(D_233, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_233, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(k7_tmap_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_282, c_1478])).
% 11.21/4.01  tff(c_1484, plain, (![D_234]: (v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k7_tmap_1('#skF_2', '#skF_3'), D_234), '#skF_2') | ~v3_pre_topc(D_234, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_234, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_283, c_104, c_1480])).
% 11.21/4.01  tff(c_1495, plain, (v3_pre_topc('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_215, c_1484])).
% 11.21/4.01  tff(c_1503, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_402, c_1495])).
% 11.21/4.01  tff(c_1505, plain, $false, inference(negUnitSimplification, [status(thm)], [c_188, c_1503])).
% 11.21/4.01  tff(c_1507, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_441])).
% 11.21/4.01  tff(c_1527, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1507, c_90])).
% 11.21/4.01  tff(c_2, plain, (![A_1, B_2]: (k8_relset_1(A_1, A_1, k6_partfun1(A_1), B_2)=B_2 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.21/4.01  tff(c_1611, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, k6_partfun1(k1_xboole_0), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_1527, c_2])).
% 11.21/4.01  tff(c_1528, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1507, c_89])).
% 11.21/4.01  tff(c_1522, plain, (k7_tmap_1('#skF_2', '#skF_3')=k6_partfun1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1507, c_213])).
% 11.21/4.01  tff(c_1613, plain, (v1_funct_1(k6_partfun1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1522, c_95])).
% 11.21/4.01  tff(c_1518, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1507, c_246])).
% 11.21/4.01  tff(c_38, plain, (![A_47, B_48]: (v1_funct_2(k7_tmap_1(A_47, B_48), u1_struct_0(A_47), u1_struct_0(k6_tmap_1(A_47, B_48))) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_133])).
% 11.21/4.01  tff(c_1653, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), k1_xboole_0) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1518, c_38])).
% 11.21/4.01  tff(c_1696, plain, (v1_funct_2(k6_partfun1(k1_xboole_0), k1_xboole_0, k1_xboole_0) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1527, c_1528, c_1522, c_1528, c_1653])).
% 11.21/4.01  tff(c_1697, plain, (v1_funct_2(k6_partfun1(k1_xboole_0), k1_xboole_0, k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_58, c_1696])).
% 11.21/4.01  tff(c_1612, plain, (v5_pre_topc(k6_partfun1(k1_xboole_0), '#skF_2', k6_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1522, c_104])).
% 11.21/4.01  tff(c_36, plain, (![A_47, B_48]: (m1_subset_1(k7_tmap_1(A_47, B_48), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_47), u1_struct_0(k6_tmap_1(A_47, B_48))))) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_133])).
% 11.21/4.01  tff(c_2162, plain, (![A_283, B_284, C_285, D_286]: (k2_struct_0(A_283)!=k1_xboole_0 | v3_pre_topc(k8_relset_1(u1_struct_0(A_283), u1_struct_0(B_284), C_285, D_286), A_283) | ~v3_pre_topc(D_286, B_284) | ~m1_subset_1(D_286, k1_zfmisc_1(u1_struct_0(B_284))) | ~v5_pre_topc(C_285, A_283, B_284) | ~m1_subset_1(C_285, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_283), u1_struct_0(B_284)))) | ~v1_funct_2(C_285, u1_struct_0(A_283), u1_struct_0(B_284)) | ~v1_funct_1(C_285) | ~l1_pre_topc(B_284) | ~l1_pre_topc(A_283))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.21/4.01  tff(c_3919, plain, (![A_395, B_396, D_397]: (k2_struct_0(A_395)!=k1_xboole_0 | v3_pre_topc(k8_relset_1(u1_struct_0(A_395), u1_struct_0(k6_tmap_1(A_395, B_396)), k7_tmap_1(A_395, B_396), D_397), A_395) | ~v3_pre_topc(D_397, k6_tmap_1(A_395, B_396)) | ~m1_subset_1(D_397, k1_zfmisc_1(u1_struct_0(k6_tmap_1(A_395, B_396)))) | ~v5_pre_topc(k7_tmap_1(A_395, B_396), A_395, k6_tmap_1(A_395, B_396)) | ~v1_funct_2(k7_tmap_1(A_395, B_396), u1_struct_0(A_395), u1_struct_0(k6_tmap_1(A_395, B_396))) | ~v1_funct_1(k7_tmap_1(A_395, B_396)) | ~l1_pre_topc(k6_tmap_1(A_395, B_396)) | ~m1_subset_1(B_396, k1_zfmisc_1(u1_struct_0(A_395))) | ~l1_pre_topc(A_395) | ~v2_pre_topc(A_395) | v2_struct_0(A_395))), inference(resolution, [status(thm)], [c_36, c_2162])).
% 11.21/4.01  tff(c_3954, plain, (![D_397]: (k2_struct_0('#skF_2')!=k1_xboole_0 | v3_pre_topc(k8_relset_1(u1_struct_0('#skF_2'), k1_xboole_0, k7_tmap_1('#skF_2', '#skF_3'), D_397), '#skF_2') | ~v3_pre_topc(D_397, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_397, k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))) | ~v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k7_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1518, c_3919])).
% 11.21/4.01  tff(c_3978, plain, (![D_397]: (v3_pre_topc(k8_relset_1(k1_xboole_0, k1_xboole_0, k6_partfun1(k1_xboole_0), D_397), '#skF_2') | ~v3_pre_topc(D_397, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_397, k1_zfmisc_1(k1_xboole_0)) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1527, c_1528, c_155, c_1613, c_1522, c_1697, c_1518, c_1522, c_1528, c_1612, c_1522, c_1518, c_1522, c_1528, c_1507, c_3954])).
% 11.21/4.01  tff(c_4013, plain, (![D_399]: (v3_pre_topc(k8_relset_1(k1_xboole_0, k1_xboole_0, k6_partfun1(k1_xboole_0), D_399), '#skF_2') | ~v3_pre_topc(D_399, k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_399, k1_zfmisc_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_58, c_3978])).
% 11.21/4.01  tff(c_4030, plain, (v3_pre_topc('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1611, c_4013])).
% 11.21/4.01  tff(c_4038, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1527, c_402, c_4030])).
% 11.21/4.01  tff(c_4040, plain, $false, inference(negUnitSimplification, [status(thm)], [c_188, c_4038])).
% 11.21/4.01  tff(c_4041, plain, (~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))) | ~m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0(k6_tmap_1('#skF_2', '#skF_3')))))), inference(splitRight, [status(thm)], [c_187])).
% 11.21/4.01  tff(c_4168, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4130, c_4095, c_4131, c_4095, c_4041])).
% 11.21/4.01  tff(c_4170, plain, (~m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))))), inference(splitRight, [status(thm)], [c_120])).
% 11.21/4.01  tff(c_4199, plain, (~m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0(k6_tmap_1('#skF_2', '#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_4198, c_4170])).
% 11.21/4.01  tff(c_4327, plain, (~m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_4292, c_4199])).
% 11.21/4.01  tff(c_4447, plain, (![A_442, B_443]: (m1_subset_1(k7_tmap_1(A_442, B_443), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_442), u1_struct_0(k6_tmap_1(A_442, B_443))))) | ~m1_subset_1(B_443, k1_zfmisc_1(u1_struct_0(A_442))) | ~l1_pre_topc(A_442) | ~v2_pre_topc(A_442) | v2_struct_0(A_442))), inference(cnfTransformation, [status(thm)], [f_133])).
% 11.21/4.01  tff(c_4455, plain, (m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4291, c_4447])).
% 11.21/4.01  tff(c_4463, plain, (m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_90, c_89, c_89, c_4455])).
% 11.21/4.01  tff(c_4465, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_4327, c_4463])).
% 11.21/4.01  tff(c_4466, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_105])).
% 11.21/4.01  tff(c_4518, plain, (~m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))))) | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0(k6_tmap_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_4466, c_95, c_4495, c_89, c_104, c_4495, c_89, c_60])).
% 11.21/4.01  tff(c_4519, plain, (~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0(k6_tmap_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_4518])).
% 11.21/4.01  tff(c_4650, plain, (~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4613, c_4519])).
% 11.21/4.01  tff(c_4687, plain, (![A_466, B_467]: (v1_funct_2(k7_tmap_1(A_466, B_467), u1_struct_0(A_466), u1_struct_0(k6_tmap_1(A_466, B_467))) | ~m1_subset_1(B_467, k1_zfmisc_1(u1_struct_0(A_466))) | ~l1_pre_topc(A_466) | ~v2_pre_topc(A_466) | v2_struct_0(A_466))), inference(cnfTransformation, [status(thm)], [f_133])).
% 11.21/4.01  tff(c_4693, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4612, c_4687])).
% 11.21/4.01  tff(c_4700, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_90, c_89, c_89, c_4693])).
% 11.21/4.01  tff(c_4702, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_4650, c_4700])).
% 11.21/4.01  tff(c_4704, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0(k6_tmap_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_4518])).
% 11.21/4.01  tff(c_4467, plain, (~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_105])).
% 11.21/4.01  tff(c_4497, plain, (~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0(k6_tmap_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_4495, c_4467])).
% 11.21/4.01  tff(c_4723, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4704, c_4497])).
% 11.21/4.01  tff(c_4725, plain, (~v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', k6_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_70])).
% 11.21/4.01  tff(c_4774, plain, (![A_482, B_483]: (u1_struct_0(k6_tmap_1(A_482, B_483))=u1_struct_0(A_482) | ~m1_subset_1(B_483, k1_zfmisc_1(u1_struct_0(A_482))) | ~l1_pre_topc(A_482) | ~v2_pre_topc(A_482) | v2_struct_0(A_482))), inference(cnfTransformation, [status(thm)], [f_147])).
% 11.21/4.01  tff(c_4777, plain, (![B_483]: (u1_struct_0(k6_tmap_1('#skF_2', B_483))=u1_struct_0('#skF_2') | ~m1_subset_1(B_483, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_4774])).
% 11.21/4.01  tff(c_4779, plain, (![B_483]: (u1_struct_0(k6_tmap_1('#skF_2', B_483))=k2_struct_0('#skF_2') | ~m1_subset_1(B_483, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_89, c_4777])).
% 11.21/4.01  tff(c_4819, plain, (![B_485]: (u1_struct_0(k6_tmap_1('#skF_2', B_485))=k2_struct_0('#skF_2') | ~m1_subset_1(B_485, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_4779])).
% 11.21/4.01  tff(c_4823, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_90, c_4819])).
% 11.21/4.01  tff(c_4921, plain, (![A_493, B_494]: (v1_funct_2(k7_tmap_1(A_493, B_494), u1_struct_0(A_493), u1_struct_0(k6_tmap_1(A_493, B_494))) | ~m1_subset_1(B_494, k1_zfmisc_1(u1_struct_0(A_493))) | ~l1_pre_topc(A_493) | ~v2_pre_topc(A_493) | v2_struct_0(A_493))), inference(cnfTransformation, [status(thm)], [f_133])).
% 11.21/4.01  tff(c_4927, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4823, c_4921])).
% 11.21/4.01  tff(c_4934, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_90, c_89, c_89, c_4927])).
% 11.21/4.01  tff(c_4935, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_58, c_4934])).
% 11.21/4.01  tff(c_5004, plain, (![A_505, B_506]: (m1_subset_1(k7_tmap_1(A_505, B_506), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_505), u1_struct_0(k6_tmap_1(A_505, B_506))))) | ~m1_subset_1(B_506, k1_zfmisc_1(u1_struct_0(A_505))) | ~l1_pre_topc(A_505) | ~v2_pre_topc(A_505) | v2_struct_0(A_505))), inference(cnfTransformation, [status(thm)], [f_133])).
% 11.21/4.01  tff(c_5012, plain, (m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4823, c_5004])).
% 11.21/4.01  tff(c_5020, plain, (m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_90, c_89, c_89, c_5012])).
% 11.21/4.01  tff(c_5021, plain, (m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_5020])).
% 11.21/4.01  tff(c_5037, plain, (![B_508, A_509, C_510]: (k2_struct_0(B_508)=k1_xboole_0 | v3_pre_topc('#skF_1'(A_509, B_508, C_510), B_508) | v5_pre_topc(C_510, A_509, B_508) | ~m1_subset_1(C_510, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_509), u1_struct_0(B_508)))) | ~v1_funct_2(C_510, u1_struct_0(A_509), u1_struct_0(B_508)) | ~v1_funct_1(C_510) | ~l1_pre_topc(B_508) | ~l1_pre_topc(A_509))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.21/4.01  tff(c_5045, plain, (![B_508, C_510]: (k2_struct_0(B_508)=k1_xboole_0 | v3_pre_topc('#skF_1'('#skF_2', B_508, C_510), B_508) | v5_pre_topc(C_510, '#skF_2', B_508) | ~m1_subset_1(C_510, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(B_508)))) | ~v1_funct_2(C_510, u1_struct_0('#skF_2'), u1_struct_0(B_508)) | ~v1_funct_1(C_510) | ~l1_pre_topc(B_508) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_5037])).
% 11.21/4.01  tff(c_5061, plain, (![B_511, C_512]: (k2_struct_0(B_511)=k1_xboole_0 | v3_pre_topc('#skF_1'('#skF_2', B_511, C_512), B_511) | v5_pre_topc(C_512, '#skF_2', B_511) | ~m1_subset_1(C_512, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(B_511)))) | ~v1_funct_2(C_512, k2_struct_0('#skF_2'), u1_struct_0(B_511)) | ~v1_funct_1(C_512) | ~l1_pre_topc(B_511))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_89, c_5045])).
% 11.21/4.01  tff(c_5067, plain, (![C_512]: (k2_struct_0('#skF_2')=k1_xboole_0 | v3_pre_topc('#skF_1'('#skF_2', '#skF_2', C_512), '#skF_2') | v5_pre_topc(C_512, '#skF_2', '#skF_2') | ~m1_subset_1(C_512, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_512, k2_struct_0('#skF_2'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_512) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_5061])).
% 11.21/4.01  tff(c_5072, plain, (![C_512]: (k2_struct_0('#skF_2')=k1_xboole_0 | v3_pre_topc('#skF_1'('#skF_2', '#skF_2', C_512), '#skF_2') | v5_pre_topc(C_512, '#skF_2', '#skF_2') | ~m1_subset_1(C_512, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_512, k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_512))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_89, c_5067])).
% 11.21/4.01  tff(c_5073, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_5072])).
% 11.21/4.01  tff(c_4860, plain, (![A_486, B_487]: (k7_tmap_1(A_486, B_487)=k6_partfun1(u1_struct_0(A_486)) | ~m1_subset_1(B_487, k1_zfmisc_1(u1_struct_0(A_486))) | ~l1_pre_topc(A_486) | ~v2_pre_topc(A_486) | v2_struct_0(A_486))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.21/4.01  tff(c_4866, plain, (![B_487]: (k7_tmap_1('#skF_2', B_487)=k6_partfun1(u1_struct_0('#skF_2')) | ~m1_subset_1(B_487, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_4860])).
% 11.21/4.01  tff(c_4870, plain, (![B_487]: (k7_tmap_1('#skF_2', B_487)=k6_partfun1(k2_struct_0('#skF_2')) | ~m1_subset_1(B_487, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_89, c_4866])).
% 11.21/4.01  tff(c_4872, plain, (![B_488]: (k7_tmap_1('#skF_2', B_488)=k6_partfun1(k2_struct_0('#skF_2')) | ~m1_subset_1(B_488, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_4870])).
% 11.21/4.01  tff(c_4876, plain, (k6_partfun1(k2_struct_0('#skF_2'))=k7_tmap_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_90, c_4872])).
% 11.21/4.01  tff(c_5111, plain, (k7_tmap_1('#skF_2', '#skF_3')=k6_partfun1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5073, c_4876])).
% 11.21/4.01  tff(c_5204, plain, (~v5_pre_topc(k6_partfun1(k1_xboole_0), '#skF_2', k6_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5111, c_4725])).
% 11.21/4.01  tff(c_5205, plain, (v1_funct_1(k6_partfun1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_5111, c_95])).
% 11.21/4.01  tff(c_5119, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_5073, c_90])).
% 11.21/4.01  tff(c_5120, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5073, c_89])).
% 11.21/4.01  tff(c_5113, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5073, c_4823])).
% 11.21/4.01  tff(c_5261, plain, (v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), k1_xboole_0) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5113, c_38])).
% 11.21/4.01  tff(c_5308, plain, (v1_funct_2(k6_partfun1(k1_xboole_0), k1_xboole_0, k1_xboole_0) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_5119, c_5120, c_5111, c_5120, c_5261])).
% 11.21/4.01  tff(c_5309, plain, (v1_funct_2(k6_partfun1(k1_xboole_0), k1_xboole_0, k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_58, c_5308])).
% 11.21/4.01  tff(c_5248, plain, (m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), k1_xboole_0))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5113, c_36])).
% 11.21/4.01  tff(c_5296, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_5119, c_5120, c_5111, c_5120, c_5248])).
% 11.21/4.01  tff(c_5297, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_58, c_5296])).
% 11.21/4.01  tff(c_5222, plain, (![A_514, B_515, C_516]: (k2_struct_0(A_514)!=k1_xboole_0 | v3_pre_topc('#skF_1'(A_514, B_515, C_516), B_515) | v5_pre_topc(C_516, A_514, B_515) | ~m1_subset_1(C_516, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_514), u1_struct_0(B_515)))) | ~v1_funct_2(C_516, u1_struct_0(A_514), u1_struct_0(B_515)) | ~v1_funct_1(C_516) | ~l1_pre_topc(B_515) | ~l1_pre_topc(A_514))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.21/4.01  tff(c_5224, plain, (![B_515, C_516]: (k2_struct_0('#skF_2')!=k1_xboole_0 | v3_pre_topc('#skF_1'('#skF_2', B_515, C_516), B_515) | v5_pre_topc(C_516, '#skF_2', B_515) | ~m1_subset_1(C_516, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, u1_struct_0(B_515)))) | ~v1_funct_2(C_516, u1_struct_0('#skF_2'), u1_struct_0(B_515)) | ~v1_funct_1(C_516) | ~l1_pre_topc(B_515) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5120, c_5222])).
% 11.21/4.01  tff(c_5516, plain, (![B_540, C_541]: (v3_pre_topc('#skF_1'('#skF_2', B_540, C_541), B_540) | v5_pre_topc(C_541, '#skF_2', B_540) | ~m1_subset_1(C_541, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, u1_struct_0(B_540)))) | ~v1_funct_2(C_541, k1_xboole_0, u1_struct_0(B_540)) | ~v1_funct_1(C_541) | ~l1_pre_topc(B_540))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_5120, c_5073, c_5224])).
% 11.21/4.01  tff(c_5522, plain, (![C_541]: (v3_pre_topc('#skF_1'('#skF_2', '#skF_2', C_541), '#skF_2') | v5_pre_topc(C_541, '#skF_2', '#skF_2') | ~m1_subset_1(C_541, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~v1_funct_2(C_541, k1_xboole_0, u1_struct_0('#skF_2')) | ~v1_funct_1(C_541) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5120, c_5516])).
% 11.21/4.01  tff(c_5528, plain, (![C_542]: (v3_pre_topc('#skF_1'('#skF_2', '#skF_2', C_542), '#skF_2') | v5_pre_topc(C_542, '#skF_2', '#skF_2') | ~m1_subset_1(C_542, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~v1_funct_2(C_542, k1_xboole_0, k1_xboole_0) | ~v1_funct_1(C_542))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_5120, c_5522])).
% 11.21/4.01  tff(c_5531, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_2', k6_partfun1(k1_xboole_0)), '#skF_2') | v5_pre_topc(k6_partfun1(k1_xboole_0), '#skF_2', '#skF_2') | ~v1_funct_2(k6_partfun1(k1_xboole_0), k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_5297, c_5528])).
% 11.21/4.01  tff(c_5534, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_2', k6_partfun1(k1_xboole_0)), '#skF_2') | v5_pre_topc(k6_partfun1(k1_xboole_0), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5205, c_5309, c_5531])).
% 11.21/4.01  tff(c_5535, plain, (v5_pre_topc(k6_partfun1(k1_xboole_0), '#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_5534])).
% 11.21/4.01  tff(c_4724, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_70])).
% 11.21/4.01  tff(c_4946, plain, (![A_496, B_497]: (k6_tmap_1(A_496, B_497)=g1_pre_topc(u1_struct_0(A_496), u1_pre_topc(A_496)) | ~v3_pre_topc(B_497, A_496) | ~m1_subset_1(B_497, k1_zfmisc_1(u1_struct_0(A_496))) | ~l1_pre_topc(A_496) | ~v2_pre_topc(A_496) | v2_struct_0(A_496))), inference(cnfTransformation, [status(thm)], [f_178])).
% 11.21/4.01  tff(c_4950, plain, (![B_497]: (k6_tmap_1('#skF_2', B_497)=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v3_pre_topc(B_497, '#skF_2') | ~m1_subset_1(B_497, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_4946])).
% 11.21/4.01  tff(c_4954, plain, (![B_497]: (k6_tmap_1('#skF_2', B_497)=g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v3_pre_topc(B_497, '#skF_2') | ~m1_subset_1(B_497, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_89, c_4950])).
% 11.21/4.01  tff(c_4970, plain, (![B_500]: (k6_tmap_1('#skF_2', B_500)=g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v3_pre_topc(B_500, '#skF_2') | ~m1_subset_1(B_500, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_4954])).
% 11.21/4.01  tff(c_4973, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k6_tmap_1('#skF_2', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_90, c_4970])).
% 11.21/4.01  tff(c_4976, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k6_tmap_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4724, c_4973])).
% 11.21/4.01  tff(c_5105, plain, (g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2'))=k6_tmap_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5073, c_4976])).
% 11.21/4.01  tff(c_6211, plain, (![D_573, A_574, B_575]: (v5_pre_topc(D_573, A_574, g1_pre_topc(u1_struct_0(B_575), u1_pre_topc(B_575))) | ~v5_pre_topc(D_573, A_574, B_575) | ~m1_subset_1(D_573, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_574), u1_struct_0(g1_pre_topc(u1_struct_0(B_575), u1_pre_topc(B_575)))))) | ~v1_funct_2(D_573, u1_struct_0(A_574), u1_struct_0(g1_pre_topc(u1_struct_0(B_575), u1_pre_topc(B_575)))) | ~m1_subset_1(D_573, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_574), u1_struct_0(B_575)))) | ~v1_funct_2(D_573, u1_struct_0(A_574), u1_struct_0(B_575)) | ~v1_funct_1(D_573) | ~l1_pre_topc(B_575) | ~v2_pre_topc(B_575) | ~l1_pre_topc(A_574) | ~v2_pre_topc(A_574))), inference(cnfTransformation, [status(thm)], [f_66])).
% 11.21/4.01  tff(c_6238, plain, (![D_573, A_574]: (v5_pre_topc(D_573, A_574, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_573, A_574, '#skF_2') | ~m1_subset_1(D_573, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_574), u1_struct_0(g1_pre_topc(k1_xboole_0, u1_pre_topc('#skF_2')))))) | ~v1_funct_2(D_573, u1_struct_0(A_574), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_573, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_574), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_573, u1_struct_0(A_574), u1_struct_0('#skF_2')) | ~v1_funct_1(D_573) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_574) | ~v2_pre_topc(A_574))), inference(superposition, [status(thm), theory('equality')], [c_5120, c_6211])).
% 11.21/4.01  tff(c_6461, plain, (![D_579, A_580]: (v5_pre_topc(D_579, A_580, k6_tmap_1('#skF_2', '#skF_3')) | ~v5_pre_topc(D_579, A_580, '#skF_2') | ~m1_subset_1(D_579, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_580), k1_xboole_0))) | ~v1_funct_2(D_579, u1_struct_0(A_580), k1_xboole_0) | ~v1_funct_1(D_579) | ~l1_pre_topc(A_580) | ~v2_pre_topc(A_580))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_5120, c_5120, c_5113, c_5105, c_5120, c_5113, c_5105, c_5105, c_5120, c_6238])).
% 11.21/4.01  tff(c_6473, plain, (![D_579]: (v5_pre_topc(D_579, '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~v5_pre_topc(D_579, '#skF_2', '#skF_2') | ~m1_subset_1(D_579, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~v1_funct_2(D_579, u1_struct_0('#skF_2'), k1_xboole_0) | ~v1_funct_1(D_579) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5120, c_6461])).
% 11.21/4.01  tff(c_6480, plain, (![D_581]: (v5_pre_topc(D_581, '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~v5_pre_topc(D_581, '#skF_2', '#skF_2') | ~m1_subset_1(D_581, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~v1_funct_2(D_581, k1_xboole_0, k1_xboole_0) | ~v1_funct_1(D_581))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_5120, c_6473])).
% 11.21/4.01  tff(c_6483, plain, (v5_pre_topc(k6_partfun1(k1_xboole_0), '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~v5_pre_topc(k6_partfun1(k1_xboole_0), '#skF_2', '#skF_2') | ~v1_funct_2(k6_partfun1(k1_xboole_0), k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_5297, c_6480])).
% 11.21/4.01  tff(c_6486, plain, (v5_pre_topc(k6_partfun1(k1_xboole_0), '#skF_2', k6_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5205, c_5309, c_5535, c_6483])).
% 11.21/4.01  tff(c_6488, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5204, c_6486])).
% 11.21/4.01  tff(c_6490, plain, (~v5_pre_topc(k6_partfun1(k1_xboole_0), '#skF_2', '#skF_2')), inference(splitRight, [status(thm)], [c_5534])).
% 11.21/4.01  tff(c_6489, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_2', k6_partfun1(k1_xboole_0)), '#skF_2')), inference(splitRight, [status(thm)], [c_5534])).
% 11.21/4.01  tff(c_5347, plain, (![A_518, B_519, C_520]: (k2_struct_0(A_518)!=k1_xboole_0 | m1_subset_1('#skF_1'(A_518, B_519, C_520), k1_zfmisc_1(u1_struct_0(B_519))) | v5_pre_topc(C_520, A_518, B_519) | ~m1_subset_1(C_520, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_518), u1_struct_0(B_519)))) | ~v1_funct_2(C_520, u1_struct_0(A_518), u1_struct_0(B_519)) | ~v1_funct_1(C_520) | ~l1_pre_topc(B_519) | ~l1_pre_topc(A_518))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.21/4.01  tff(c_5353, plain, (![B_519, C_520]: (k2_struct_0('#skF_2')!=k1_xboole_0 | m1_subset_1('#skF_1'('#skF_2', B_519, C_520), k1_zfmisc_1(u1_struct_0(B_519))) | v5_pre_topc(C_520, '#skF_2', B_519) | ~m1_subset_1(C_520, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, u1_struct_0(B_519)))) | ~v1_funct_2(C_520, u1_struct_0('#skF_2'), u1_struct_0(B_519)) | ~v1_funct_1(C_520) | ~l1_pre_topc(B_519) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5120, c_5347])).
% 11.21/4.01  tff(c_6491, plain, (![B_582, C_583]: (m1_subset_1('#skF_1'('#skF_2', B_582, C_583), k1_zfmisc_1(u1_struct_0(B_582))) | v5_pre_topc(C_583, '#skF_2', B_582) | ~m1_subset_1(C_583, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, u1_struct_0(B_582)))) | ~v1_funct_2(C_583, k1_xboole_0, u1_struct_0(B_582)) | ~v1_funct_1(C_583) | ~l1_pre_topc(B_582))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_5120, c_5073, c_5353])).
% 11.21/4.01  tff(c_6522, plain, (![C_583]: (m1_subset_1('#skF_1'('#skF_2', '#skF_2', C_583), k1_zfmisc_1(k1_xboole_0)) | v5_pre_topc(C_583, '#skF_2', '#skF_2') | ~m1_subset_1(C_583, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, u1_struct_0('#skF_2')))) | ~v1_funct_2(C_583, k1_xboole_0, u1_struct_0('#skF_2')) | ~v1_funct_1(C_583) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5120, c_6491])).
% 11.21/4.01  tff(c_6535, plain, (![C_583]: (m1_subset_1('#skF_1'('#skF_2', '#skF_2', C_583), k1_zfmisc_1(k1_xboole_0)) | v5_pre_topc(C_583, '#skF_2', '#skF_2') | ~m1_subset_1(C_583, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~v1_funct_2(C_583, k1_xboole_0, k1_xboole_0) | ~v1_funct_1(C_583))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_5120, c_5120, c_6522])).
% 11.21/4.01  tff(c_6556, plain, (![C_588]: (m1_subset_1('#skF_1'('#skF_2', '#skF_2', C_588), k1_zfmisc_1(k1_xboole_0)) | v5_pre_topc(C_588, '#skF_2', '#skF_2') | ~m1_subset_1(C_588, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~v1_funct_2(C_588, k1_xboole_0, k1_xboole_0) | ~v1_funct_1(C_588))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_5120, c_5120, c_6522])).
% 11.21/4.01  tff(c_28, plain, (![A_42, B_44]: (k7_tmap_1(A_42, B_44)=k6_partfun1(u1_struct_0(A_42)) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42) | ~v2_pre_topc(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.21/4.01  tff(c_5145, plain, (![B_44]: (k7_tmap_1('#skF_2', B_44)=k6_partfun1(u1_struct_0('#skF_2')) | ~m1_subset_1(B_44, k1_zfmisc_1(k1_xboole_0)) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5120, c_28])).
% 11.21/4.01  tff(c_5183, plain, (![B_44]: (k7_tmap_1('#skF_2', B_44)=k6_partfun1(k1_xboole_0) | ~m1_subset_1(B_44, k1_zfmisc_1(k1_xboole_0)) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_5120, c_5145])).
% 11.21/4.01  tff(c_5184, plain, (![B_44]: (k7_tmap_1('#skF_2', B_44)=k6_partfun1(k1_xboole_0) | ~m1_subset_1(B_44, k1_zfmisc_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_58, c_5183])).
% 11.21/4.01  tff(c_6604, plain, (![C_590]: (k7_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_2', C_590))=k6_partfun1(k1_xboole_0) | v5_pre_topc(C_590, '#skF_2', '#skF_2') | ~m1_subset_1(C_590, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~v1_funct_2(C_590, k1_xboole_0, k1_xboole_0) | ~v1_funct_1(C_590))), inference(resolution, [status(thm)], [c_6556, c_5184])).
% 11.21/4.01  tff(c_6607, plain, (k7_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_2', k6_partfun1(k1_xboole_0)))=k6_partfun1(k1_xboole_0) | v5_pre_topc(k6_partfun1(k1_xboole_0), '#skF_2', '#skF_2') | ~v1_funct_2(k6_partfun1(k1_xboole_0), k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_5297, c_6604])).
% 11.21/4.01  tff(c_6610, plain, (k7_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_2', k6_partfun1(k1_xboole_0)))=k6_partfun1(k1_xboole_0) | v5_pre_topc(k6_partfun1(k1_xboole_0), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5205, c_5309, c_6607])).
% 11.21/4.01  tff(c_6611, plain, (k7_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_2', k6_partfun1(k1_xboole_0)))=k6_partfun1(k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_6490, c_6610])).
% 11.21/4.01  tff(c_4930, plain, (![B_494]: (v1_funct_2(k7_tmap_1('#skF_2', B_494), k2_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', B_494))) | ~m1_subset_1(B_494, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_4921])).
% 11.21/4.01  tff(c_4937, plain, (![B_494]: (v1_funct_2(k7_tmap_1('#skF_2', B_494), k2_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', B_494))) | ~m1_subset_1(B_494, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_89, c_4930])).
% 11.21/4.01  tff(c_4938, plain, (![B_494]: (v1_funct_2(k7_tmap_1('#skF_2', B_494), k2_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', B_494))) | ~m1_subset_1(B_494, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_4937])).
% 11.21/4.01  tff(c_5106, plain, (![B_494]: (v1_funct_2(k7_tmap_1('#skF_2', B_494), k1_xboole_0, u1_struct_0(k6_tmap_1('#skF_2', B_494))) | ~m1_subset_1(B_494, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_5073, c_5073, c_4938])).
% 11.21/4.01  tff(c_6618, plain, (v1_funct_2(k6_partfun1(k1_xboole_0), k1_xboole_0, u1_struct_0(k6_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_2', k6_partfun1(k1_xboole_0))))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_2', k6_partfun1(k1_xboole_0)), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6611, c_5106])).
% 11.21/4.01  tff(c_6634, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_2', k6_partfun1(k1_xboole_0)), k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_6618])).
% 11.21/4.01  tff(c_6637, plain, (v5_pre_topc(k6_partfun1(k1_xboole_0), '#skF_2', '#skF_2') | ~m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~v1_funct_2(k6_partfun1(k1_xboole_0), k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_6535, c_6634])).
% 11.21/4.01  tff(c_6640, plain, (v5_pre_topc(k6_partfun1(k1_xboole_0), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5205, c_5309, c_5297, c_6637])).
% 11.21/4.01  tff(c_6642, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6490, c_6640])).
% 11.21/4.01  tff(c_6644, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_2', k6_partfun1(k1_xboole_0)), k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_6618])).
% 11.21/4.01  tff(c_6689, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, k6_partfun1(k1_xboole_0), '#skF_1'('#skF_2', '#skF_2', k6_partfun1(k1_xboole_0)))='#skF_1'('#skF_2', '#skF_2', k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_6644, c_2])).
% 11.21/4.01  tff(c_5495, plain, (![A_537, B_538, C_539]: (k2_struct_0(A_537)!=k1_xboole_0 | ~v3_pre_topc(k8_relset_1(u1_struct_0(A_537), u1_struct_0(B_538), C_539, '#skF_1'(A_537, B_538, C_539)), A_537) | v5_pre_topc(C_539, A_537, B_538) | ~m1_subset_1(C_539, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_537), u1_struct_0(B_538)))) | ~v1_funct_2(C_539, u1_struct_0(A_537), u1_struct_0(B_538)) | ~v1_funct_1(C_539) | ~l1_pre_topc(B_538) | ~l1_pre_topc(A_537))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.21/4.01  tff(c_5504, plain, (![B_538, C_539]: (k2_struct_0('#skF_2')!=k1_xboole_0 | ~v3_pre_topc(k8_relset_1(k1_xboole_0, u1_struct_0(B_538), C_539, '#skF_1'('#skF_2', B_538, C_539)), '#skF_2') | v5_pre_topc(C_539, '#skF_2', B_538) | ~m1_subset_1(C_539, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_538)))) | ~v1_funct_2(C_539, u1_struct_0('#skF_2'), u1_struct_0(B_538)) | ~v1_funct_1(C_539) | ~l1_pre_topc(B_538) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5120, c_5495])).
% 11.21/4.01  tff(c_9399, plain, (![B_665, C_666]: (~v3_pre_topc(k8_relset_1(k1_xboole_0, u1_struct_0(B_665), C_666, '#skF_1'('#skF_2', B_665, C_666)), '#skF_2') | v5_pre_topc(C_666, '#skF_2', B_665) | ~m1_subset_1(C_666, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, u1_struct_0(B_665)))) | ~v1_funct_2(C_666, k1_xboole_0, u1_struct_0(B_665)) | ~v1_funct_1(C_666) | ~l1_pre_topc(B_665))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_5120, c_5120, c_5073, c_5504])).
% 11.21/4.01  tff(c_9417, plain, (![C_666]: (~v3_pre_topc(k8_relset_1(k1_xboole_0, k1_xboole_0, C_666, '#skF_1'('#skF_2', '#skF_2', C_666)), '#skF_2') | v5_pre_topc(C_666, '#skF_2', '#skF_2') | ~m1_subset_1(C_666, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, u1_struct_0('#skF_2')))) | ~v1_funct_2(C_666, k1_xboole_0, u1_struct_0('#skF_2')) | ~v1_funct_1(C_666) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5120, c_9399])).
% 11.21/4.01  tff(c_9426, plain, (![C_667]: (~v3_pre_topc(k8_relset_1(k1_xboole_0, k1_xboole_0, C_667, '#skF_1'('#skF_2', '#skF_2', C_667)), '#skF_2') | v5_pre_topc(C_667, '#skF_2', '#skF_2') | ~m1_subset_1(C_667, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~v1_funct_2(C_667, k1_xboole_0, k1_xboole_0) | ~v1_funct_1(C_667))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_5120, c_5120, c_9417])).
% 11.21/4.01  tff(c_9429, plain, (~v3_pre_topc('#skF_1'('#skF_2', '#skF_2', k6_partfun1(k1_xboole_0)), '#skF_2') | v5_pre_topc(k6_partfun1(k1_xboole_0), '#skF_2', '#skF_2') | ~m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~v1_funct_2(k6_partfun1(k1_xboole_0), k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k6_partfun1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6689, c_9426])).
% 11.21/4.01  tff(c_9431, plain, (v5_pre_topc(k6_partfun1(k1_xboole_0), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5205, c_5309, c_5297, c_6489, c_9429])).
% 11.21/4.01  tff(c_9433, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6490, c_9431])).
% 11.21/4.01  tff(c_9436, plain, (![C_668]: (v3_pre_topc('#skF_1'('#skF_2', '#skF_2', C_668), '#skF_2') | v5_pre_topc(C_668, '#skF_2', '#skF_2') | ~m1_subset_1(C_668, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_668, k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_668))), inference(splitRight, [status(thm)], [c_5072])).
% 11.21/4.01  tff(c_9439, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_2', k7_tmap_1('#skF_2', '#skF_3')), '#skF_2') | v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(k7_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_5021, c_9436])).
% 11.21/4.01  tff(c_9442, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_2', k7_tmap_1('#skF_2', '#skF_3')), '#skF_2') | v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_4935, c_9439])).
% 11.21/4.01  tff(c_9463, plain, (v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_9442])).
% 11.21/4.01  tff(c_10283, plain, (![D_711, A_712, B_713]: (v5_pre_topc(D_711, A_712, g1_pre_topc(u1_struct_0(B_713), u1_pre_topc(B_713))) | ~v5_pre_topc(D_711, A_712, B_713) | ~m1_subset_1(D_711, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_712), u1_struct_0(g1_pre_topc(u1_struct_0(B_713), u1_pre_topc(B_713)))))) | ~v1_funct_2(D_711, u1_struct_0(A_712), u1_struct_0(g1_pre_topc(u1_struct_0(B_713), u1_pre_topc(B_713)))) | ~m1_subset_1(D_711, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_712), u1_struct_0(B_713)))) | ~v1_funct_2(D_711, u1_struct_0(A_712), u1_struct_0(B_713)) | ~v1_funct_1(D_711) | ~l1_pre_topc(B_713) | ~v2_pre_topc(B_713) | ~l1_pre_topc(A_712) | ~v2_pre_topc(A_712))), inference(cnfTransformation, [status(thm)], [f_66])).
% 11.21/4.01  tff(c_10307, plain, (![D_711, A_712]: (v5_pre_topc(D_711, A_712, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_711, A_712, '#skF_2') | ~m1_subset_1(D_711, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_712), u1_struct_0(g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))) | ~v1_funct_2(D_711, u1_struct_0(A_712), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_711, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_712), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_711, u1_struct_0(A_712), u1_struct_0('#skF_2')) | ~v1_funct_1(D_711) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_712) | ~v2_pre_topc(A_712))), inference(superposition, [status(thm), theory('equality')], [c_89, c_10283])).
% 11.21/4.01  tff(c_10324, plain, (![D_714, A_715]: (v5_pre_topc(D_714, A_715, k6_tmap_1('#skF_2', '#skF_3')) | ~v5_pre_topc(D_714, A_715, '#skF_2') | ~m1_subset_1(D_714, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_715), k2_struct_0('#skF_2')))) | ~v1_funct_2(D_714, u1_struct_0(A_715), k2_struct_0('#skF_2')) | ~v1_funct_1(D_714) | ~l1_pre_topc(A_715) | ~v2_pre_topc(A_715))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_89, c_89, c_4823, c_4976, c_89, c_4823, c_4976, c_4976, c_89, c_10307])).
% 11.21/4.01  tff(c_10333, plain, (![D_714]: (v5_pre_topc(D_714, '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~v5_pre_topc(D_714, '#skF_2', '#skF_2') | ~m1_subset_1(D_714, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~v1_funct_2(D_714, u1_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(D_714) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_10324])).
% 11.21/4.01  tff(c_10340, plain, (![D_716]: (v5_pre_topc(D_716, '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~v5_pre_topc(D_716, '#skF_2', '#skF_2') | ~m1_subset_1(D_716, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~v1_funct_2(D_716, k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(D_716))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_89, c_10333])).
% 11.21/4.01  tff(c_10343, plain, (v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', k6_tmap_1('#skF_2', '#skF_3')) | ~v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(k7_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_5021, c_10340])).
% 11.21/4.01  tff(c_10346, plain, (v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', k6_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_4935, c_9463, c_10343])).
% 11.21/4.01  tff(c_10348, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4725, c_10346])).
% 11.21/4.01  tff(c_10350, plain, (~v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', '#skF_2')), inference(splitRight, [status(thm)], [c_9442])).
% 11.21/4.01  tff(c_10349, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_2', k7_tmap_1('#skF_2', '#skF_3')), '#skF_2')), inference(splitRight, [status(thm)], [c_9442])).
% 11.21/4.01  tff(c_9435, plain, (k2_struct_0('#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_5072])).
% 11.21/4.01  tff(c_10395, plain, (![B_721, A_722, C_723]: (k2_struct_0(B_721)=k1_xboole_0 | m1_subset_1('#skF_1'(A_722, B_721, C_723), k1_zfmisc_1(u1_struct_0(B_721))) | v5_pre_topc(C_723, A_722, B_721) | ~m1_subset_1(C_723, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_722), u1_struct_0(B_721)))) | ~v1_funct_2(C_723, u1_struct_0(A_722), u1_struct_0(B_721)) | ~v1_funct_1(C_723) | ~l1_pre_topc(B_721) | ~l1_pre_topc(A_722))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.21/4.01  tff(c_10405, plain, (![A_722, C_723]: (k2_struct_0('#skF_2')=k1_xboole_0 | m1_subset_1('#skF_1'(A_722, '#skF_2', C_723), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v5_pre_topc(C_723, A_722, '#skF_2') | ~m1_subset_1(C_723, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_722), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_723, u1_struct_0(A_722), u1_struct_0('#skF_2')) | ~v1_funct_1(C_723) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_722))), inference(superposition, [status(thm), theory('equality')], [c_89, c_10395])).
% 11.21/4.01  tff(c_10415, plain, (![A_722, C_723]: (k2_struct_0('#skF_2')=k1_xboole_0 | m1_subset_1('#skF_1'(A_722, '#skF_2', C_723), k1_zfmisc_1(k2_struct_0('#skF_2'))) | v5_pre_topc(C_723, A_722, '#skF_2') | ~m1_subset_1(C_723, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_722), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_723, u1_struct_0(A_722), k2_struct_0('#skF_2')) | ~v1_funct_1(C_723) | ~l1_pre_topc(A_722))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_89, c_89, c_10405])).
% 11.21/4.01  tff(c_10417, plain, (![A_724, C_725]: (m1_subset_1('#skF_1'(A_724, '#skF_2', C_725), k1_zfmisc_1(k2_struct_0('#skF_2'))) | v5_pre_topc(C_725, A_724, '#skF_2') | ~m1_subset_1(C_725, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_724), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_725, u1_struct_0(A_724), k2_struct_0('#skF_2')) | ~v1_funct_1(C_725) | ~l1_pre_topc(A_724))), inference(negUnitSimplification, [status(thm)], [c_9435, c_10415])).
% 11.21/4.01  tff(c_10423, plain, (![C_725]: (m1_subset_1('#skF_1'('#skF_2', '#skF_2', C_725), k1_zfmisc_1(k2_struct_0('#skF_2'))) | v5_pre_topc(C_725, '#skF_2', '#skF_2') | ~m1_subset_1(C_725, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_725, u1_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_725) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_10417])).
% 11.21/4.01  tff(c_10428, plain, (![C_726]: (m1_subset_1('#skF_1'('#skF_2', '#skF_2', C_726), k1_zfmisc_1(k2_struct_0('#skF_2'))) | v5_pre_topc(C_726, '#skF_2', '#skF_2') | ~m1_subset_1(C_726, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_726, k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_726))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_89, c_10423])).
% 11.21/4.01  tff(c_10431, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_2', k7_tmap_1('#skF_2', '#skF_3')), k1_zfmisc_1(k2_struct_0('#skF_2'))) | v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(k7_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_5021, c_10428])).
% 11.21/4.01  tff(c_10434, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_2', k7_tmap_1('#skF_2', '#skF_3')), k1_zfmisc_1(k2_struct_0('#skF_2'))) | v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_4935, c_10431])).
% 11.21/4.01  tff(c_10435, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_2', k7_tmap_1('#skF_2', '#skF_3')), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_10350, c_10434])).
% 11.21/4.01  tff(c_10464, plain, (k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k6_partfun1(k2_struct_0('#skF_2')), '#skF_1'('#skF_2', '#skF_2', k7_tmap_1('#skF_2', '#skF_3')))='#skF_1'('#skF_2', '#skF_2', k7_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_10435, c_2])).
% 11.21/4.01  tff(c_10478, plain, (k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), k7_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_2', '#skF_2', k7_tmap_1('#skF_2', '#skF_3')))='#skF_1'('#skF_2', '#skF_2', k7_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4876, c_10464])).
% 11.21/4.01  tff(c_10609, plain, (![B_730, A_731, C_732]: (k2_struct_0(B_730)=k1_xboole_0 | ~v3_pre_topc(k8_relset_1(u1_struct_0(A_731), u1_struct_0(B_730), C_732, '#skF_1'(A_731, B_730, C_732)), A_731) | v5_pre_topc(C_732, A_731, B_730) | ~m1_subset_1(C_732, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_731), u1_struct_0(B_730)))) | ~v1_funct_2(C_732, u1_struct_0(A_731), u1_struct_0(B_730)) | ~v1_funct_1(C_732) | ~l1_pre_topc(B_730) | ~l1_pre_topc(A_731))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.21/4.01  tff(c_10621, plain, (![A_731, C_732]: (k2_struct_0('#skF_2')=k1_xboole_0 | ~v3_pre_topc(k8_relset_1(u1_struct_0(A_731), k2_struct_0('#skF_2'), C_732, '#skF_1'(A_731, '#skF_2', C_732)), A_731) | v5_pre_topc(C_732, A_731, '#skF_2') | ~m1_subset_1(C_732, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_731), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_732, u1_struct_0(A_731), u1_struct_0('#skF_2')) | ~v1_funct_1(C_732) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_731))), inference(superposition, [status(thm), theory('equality')], [c_89, c_10609])).
% 11.21/4.01  tff(c_10630, plain, (![A_731, C_732]: (k2_struct_0('#skF_2')=k1_xboole_0 | ~v3_pre_topc(k8_relset_1(u1_struct_0(A_731), k2_struct_0('#skF_2'), C_732, '#skF_1'(A_731, '#skF_2', C_732)), A_731) | v5_pre_topc(C_732, A_731, '#skF_2') | ~m1_subset_1(C_732, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_731), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_732, u1_struct_0(A_731), k2_struct_0('#skF_2')) | ~v1_funct_1(C_732) | ~l1_pre_topc(A_731))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_89, c_89, c_10621])).
% 11.21/4.01  tff(c_11631, plain, (![A_776, C_777]: (~v3_pre_topc(k8_relset_1(u1_struct_0(A_776), k2_struct_0('#skF_2'), C_777, '#skF_1'(A_776, '#skF_2', C_777)), A_776) | v5_pre_topc(C_777, A_776, '#skF_2') | ~m1_subset_1(C_777, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_776), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_777, u1_struct_0(A_776), k2_struct_0('#skF_2')) | ~v1_funct_1(C_777) | ~l1_pre_topc(A_776))), inference(negUnitSimplification, [status(thm)], [c_9435, c_10630])).
% 11.21/4.01  tff(c_11640, plain, (![C_777]: (~v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), C_777, '#skF_1'('#skF_2', '#skF_2', C_777)), '#skF_2') | v5_pre_topc(C_777, '#skF_2', '#skF_2') | ~m1_subset_1(C_777, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_777, u1_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_777) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_11631])).
% 11.21/4.01  tff(c_11647, plain, (![C_778]: (~v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), C_778, '#skF_1'('#skF_2', '#skF_2', C_778)), '#skF_2') | v5_pre_topc(C_778, '#skF_2', '#skF_2') | ~m1_subset_1(C_778, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_778, k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_778))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_89, c_89, c_11640])).
% 11.21/4.01  tff(c_11650, plain, (~v3_pre_topc('#skF_1'('#skF_2', '#skF_2', k7_tmap_1('#skF_2', '#skF_3')), '#skF_2') | v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~m1_subset_1(k7_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')))) | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_funct_1(k7_tmap_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_10478, c_11647])).
% 11.21/4.01  tff(c_11652, plain, (v5_pre_topc(k7_tmap_1('#skF_2', '#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_4935, c_5021, c_10349, c_11650])).
% 11.21/4.01  tff(c_11654, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10350, c_11652])).
% 11.21/4.01  tff(c_11656, plain, (~v1_funct_1(k7_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_78])).
% 11.21/4.01  tff(c_11667, plain, (![A_781, B_782]: (v1_funct_1(k7_tmap_1(A_781, B_782)) | ~m1_subset_1(B_782, k1_zfmisc_1(u1_struct_0(A_781))) | ~l1_pre_topc(A_781) | ~v2_pre_topc(A_781) | v2_struct_0(A_781))), inference(cnfTransformation, [status(thm)], [f_133])).
% 11.21/4.01  tff(c_11670, plain, (![B_782]: (v1_funct_1(k7_tmap_1('#skF_2', B_782)) | ~m1_subset_1(B_782, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_11667])).
% 11.21/4.01  tff(c_11672, plain, (![B_782]: (v1_funct_1(k7_tmap_1('#skF_2', B_782)) | ~m1_subset_1(B_782, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_11670])).
% 11.21/4.01  tff(c_11674, plain, (![B_783]: (v1_funct_1(k7_tmap_1('#skF_2', B_783)) | ~m1_subset_1(B_783, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_11672])).
% 11.21/4.01  tff(c_11677, plain, (v1_funct_1(k7_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_90, c_11674])).
% 11.21/4.01  tff(c_11681, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11656, c_11677])).
% 11.21/4.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.21/4.01  
% 11.21/4.01  Inference rules
% 11.21/4.01  ----------------------
% 11.21/4.01  #Ref     : 0
% 11.21/4.01  #Sup     : 2537
% 11.21/4.01  #Fact    : 0
% 11.21/4.01  #Define  : 0
% 11.21/4.01  #Split   : 40
% 11.21/4.01  #Chain   : 0
% 11.21/4.01  #Close   : 0
% 11.21/4.01  
% 11.21/4.01  Ordering : KBO
% 11.21/4.01  
% 11.21/4.01  Simplification rules
% 11.21/4.01  ----------------------
% 11.21/4.01  #Subsume      : 190
% 11.21/4.01  #Demod        : 6831
% 11.21/4.01  #Tautology    : 782
% 11.21/4.01  #SimpNegUnit  : 478
% 11.21/4.01  #BackRed      : 96
% 11.21/4.01  
% 11.21/4.01  #Partial instantiations: 0
% 11.21/4.01  #Strategies tried      : 1
% 11.21/4.01  
% 11.21/4.01  Timing (in seconds)
% 11.21/4.01  ----------------------
% 11.21/4.02  Preprocessing        : 0.38
% 11.21/4.02  Parsing              : 0.19
% 11.21/4.02  CNF conversion       : 0.03
% 11.21/4.02  Main loop            : 2.80
% 11.21/4.02  Inferencing          : 0.78
% 11.21/4.02  Reduction            : 1.15
% 11.21/4.02  Demodulation         : 0.88
% 11.21/4.02  BG Simplification    : 0.10
% 11.21/4.02  Subsumption          : 0.62
% 11.21/4.02  Abstraction          : 0.14
% 11.21/4.02  MUC search           : 0.00
% 11.21/4.02  Cooper               : 0.00
% 11.21/4.02  Total                : 3.28
% 11.21/4.02  Index Insertion      : 0.00
% 11.21/4.02  Index Deletion       : 0.00
% 11.21/4.02  Index Matching       : 0.00
% 11.21/4.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
