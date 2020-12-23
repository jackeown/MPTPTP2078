%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1796+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:24 EST 2020

% Result     : Theorem 12.72s
% Output     : CNFRefutation 12.92s
% Verified   : 
% Statistics : Number of formulae       :  312 (5961 expanded)
%              Number of leaves         :   48 (2166 expanded)
%              Depth                    :   25
%              Number of atoms          :  923 (28184 expanded)
%              Number of equality atoms :   73 (3152 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > v1_partfun1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_tmap_1 > k6_tmap_1 > k5_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k6_partfun1 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_269,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ( u1_struct_0(C) = B
                 => ( v1_funct_1(k2_tmap_1(A,k6_tmap_1(A,B),k7_tmap_1(A,B),C))
                    & v1_funct_2(k2_tmap_1(A,k6_tmap_1(A,B),k7_tmap_1(A,B),C),u1_struct_0(C),u1_struct_0(k6_tmap_1(A,B)))
                    & v5_pre_topc(k2_tmap_1(A,k6_tmap_1(A,B),k7_tmap_1(A,B),C),C,k6_tmap_1(A,B))
                    & m1_subset_1(k2_tmap_1(A,k6_tmap_1(A,B),k7_tmap_1(A,B),C),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(k6_tmap_1(A,B))))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_tmap_1)).

tff(f_150,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_funct_1(k7_tmap_1(A,B))
        & v1_funct_2(k7_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B)))
        & m1_subset_1(k7_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

tff(f_135,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_181,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( ~ v2_struct_0(k6_tmap_1(A,B))
        & v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tmap_1)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_165,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_90,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k6_tmap_1(A,B) = g1_pre_topc(u1_struct_0(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).

tff(f_190,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_51,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k7_tmap_1(A,B) = k6_partfun1(u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_tmap_1)).

tff(f_120,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_78,axiom,(
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

tff(f_154,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_116,axiom,(
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

tff(f_161,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_39,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_242,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tmap_1)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_213,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( u1_struct_0(C) = B
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(C))
                   => r1_tmap_1(C,k6_tmap_1(A,B),k2_tmap_1(A,k6_tmap_1(A,B),k7_tmap_1(A,B),C),D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_tmap_1)).

tff(c_66,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_64,plain,(
    u1_struct_0('#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_74,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_72,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_6823,plain,(
    ! [A_733,B_734] :
      ( v1_funct_1(k7_tmap_1(A_733,B_734))
      | ~ m1_subset_1(B_734,k1_zfmisc_1(u1_struct_0(A_733)))
      | ~ l1_pre_topc(A_733)
      | ~ v2_pre_topc(A_733)
      | v2_struct_0(A_733) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_6826,plain,
    ( v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_6823])).

tff(c_6832,plain,
    ( v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_6826])).

tff(c_6833,plain,(
    v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_6832])).

tff(c_6793,plain,(
    ! [A_727,B_728] :
      ( l1_pre_topc(k6_tmap_1(A_727,B_728))
      | ~ m1_subset_1(B_728,k1_zfmisc_1(u1_struct_0(A_727)))
      | ~ l1_pre_topc(A_727)
      | ~ v2_pre_topc(A_727)
      | v2_struct_0(A_727) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_6796,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_6793])).

tff(c_6802,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_6796])).

tff(c_6803,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_6802])).

tff(c_6837,plain,(
    ! [A_735,B_736] :
      ( v1_pre_topc(k6_tmap_1(A_735,B_736))
      | ~ m1_subset_1(B_736,k1_zfmisc_1(u1_struct_0(A_735)))
      | ~ l1_pre_topc(A_735)
      | ~ v2_pre_topc(A_735)
      | v2_struct_0(A_735) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_6840,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_6837])).

tff(c_6846,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_6840])).

tff(c_6847,plain,(
    v1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_6846])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_42,plain,(
    ! [A_43] :
      ( m1_subset_1(u1_pre_topc(A_43),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_43))))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_6933,plain,(
    ! [A_757,B_758] :
      ( g1_pre_topc(u1_struct_0(A_757),k5_tmap_1(A_757,B_758)) = k6_tmap_1(A_757,B_758)
      | ~ m1_subset_1(B_758,k1_zfmisc_1(u1_struct_0(A_757)))
      | ~ l1_pre_topc(A_757)
      | ~ v2_pre_topc(A_757)
      | v2_struct_0(A_757) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6935,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_3')) = k6_tmap_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_6933])).

tff(c_6940,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_3')) = k6_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_6935])).

tff(c_6941,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_3')) = k6_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_6940])).

tff(c_52,plain,(
    ! [C_50,A_46,D_51,B_47] :
      ( C_50 = A_46
      | g1_pre_topc(C_50,D_51) != g1_pre_topc(A_46,B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(k1_zfmisc_1(A_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_6962,plain,(
    ! [A_760,B_761] :
      ( u1_struct_0('#skF_2') = A_760
      | k6_tmap_1('#skF_2','#skF_3') != g1_pre_topc(A_760,B_761)
      | ~ m1_subset_1(B_761,k1_zfmisc_1(k1_zfmisc_1(A_760))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6941,c_52])).

tff(c_6981,plain,(
    ! [A_764] :
      ( u1_struct_0(A_764) = u1_struct_0('#skF_2')
      | g1_pre_topc(u1_struct_0(A_764),u1_pre_topc(A_764)) != k6_tmap_1('#skF_2','#skF_3')
      | ~ l1_pre_topc(A_764) ) ),
    inference(resolution,[status(thm)],[c_42,c_6962])).

tff(c_6991,plain,(
    ! [A_765] :
      ( u1_struct_0(A_765) = u1_struct_0('#skF_2')
      | k6_tmap_1('#skF_2','#skF_3') != A_765
      | ~ l1_pre_topc(A_765)
      | ~ v1_pre_topc(A_765)
      | ~ l1_pre_topc(A_765) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_6981])).

tff(c_6994,plain,
    ( u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = u1_struct_0('#skF_2')
    | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6847,c_6991])).

tff(c_6997,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = u1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6803,c_6994])).

tff(c_34,plain,(
    ! [A_37,B_38] :
      ( v1_funct_2(k7_tmap_1(A_37,B_38),u1_struct_0(A_37),u1_struct_0(k6_tmap_1(A_37,B_38)))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_7013,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6997,c_34])).

tff(c_7049,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_7013])).

tff(c_7050,plain,(
    v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_7049])).

tff(c_6891,plain,(
    ! [A_748,B_749] :
      ( k7_tmap_1(A_748,B_749) = k6_partfun1(u1_struct_0(A_748))
      | ~ m1_subset_1(B_749,k1_zfmisc_1(u1_struct_0(A_748)))
      | ~ l1_pre_topc(A_748)
      | ~ v2_pre_topc(A_748)
      | v2_struct_0(A_748) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6894,plain,
    ( k6_partfun1(u1_struct_0('#skF_2')) = k7_tmap_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_6891])).

tff(c_6900,plain,
    ( k6_partfun1(u1_struct_0('#skF_2')) = k7_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_6894])).

tff(c_6901,plain,(
    k6_partfun1(u1_struct_0('#skF_2')) = k7_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_6900])).

tff(c_24,plain,(
    ! [A_34] : m1_subset_1(k6_partfun1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_6911,plain,(
    m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6901,c_24])).

tff(c_10408,plain,(
    ! [A_1067,B_1068,C_1069,D_1070] :
      ( k2_partfun1(u1_struct_0(A_1067),u1_struct_0(B_1068),C_1069,u1_struct_0(D_1070)) = k2_tmap_1(A_1067,B_1068,C_1069,D_1070)
      | ~ m1_pre_topc(D_1070,A_1067)
      | ~ m1_subset_1(C_1069,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1067),u1_struct_0(B_1068))))
      | ~ v1_funct_2(C_1069,u1_struct_0(A_1067),u1_struct_0(B_1068))
      | ~ v1_funct_1(C_1069)
      | ~ l1_pre_topc(B_1068)
      | ~ v2_pre_topc(B_1068)
      | v2_struct_0(B_1068)
      | ~ l1_pre_topc(A_1067)
      | ~ v2_pre_topc(A_1067)
      | v2_struct_0(A_1067) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_10425,plain,(
    ! [D_1070] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),k7_tmap_1('#skF_2','#skF_3'),u1_struct_0(D_1070)) = k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),D_1070)
      | ~ m1_pre_topc(D_1070,'#skF_2')
      | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6911,c_10408])).

tff(c_10452,plain,(
    ! [D_1070] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),k7_tmap_1('#skF_2','#skF_3'),u1_struct_0(D_1070)) = k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),D_1070)
      | ~ m1_pre_topc(D_1070,'#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_6833,c_7050,c_10425])).

tff(c_10461,plain,(
    ! [D_1071] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),k7_tmap_1('#skF_2','#skF_3'),u1_struct_0(D_1071)) = k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),D_1071)
      | ~ m1_pre_topc(D_1071,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_10452])).

tff(c_10478,plain,
    ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),k7_tmap_1('#skF_2','#skF_3'),'#skF_3') = k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_10461])).

tff(c_10484,plain,(
    k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),k7_tmap_1('#skF_2','#skF_3'),'#skF_3') = k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_10478])).

tff(c_6853,plain,(
    ! [A_739,B_740] :
      ( ~ v2_struct_0(k6_tmap_1(A_739,B_740))
      | ~ m1_subset_1(B_740,k1_zfmisc_1(u1_struct_0(A_739)))
      | ~ l1_pre_topc(A_739)
      | ~ v2_pre_topc(A_739)
      | v2_struct_0(A_739) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_6856,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_6853])).

tff(c_6862,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_6856])).

tff(c_6863,plain,(
    ~ v2_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_6862])).

tff(c_6808,plain,(
    ! [A_730,B_731] :
      ( v2_pre_topc(k6_tmap_1(A_730,B_731))
      | ~ m1_subset_1(B_731,k1_zfmisc_1(u1_struct_0(A_730)))
      | ~ l1_pre_topc(A_730)
      | ~ v2_pre_topc(A_730)
      | v2_struct_0(A_730) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_6811,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_6808])).

tff(c_6817,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_6811])).

tff(c_6818,plain,(
    v2_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_6817])).

tff(c_32,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1(k7_tmap_1(A_37,B_38),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_37),u1_struct_0(k6_tmap_1(A_37,B_38)))))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_13471,plain,(
    ! [A_1309,B_1310,D_1311] :
      ( k2_partfun1(u1_struct_0(A_1309),u1_struct_0(k6_tmap_1(A_1309,B_1310)),k7_tmap_1(A_1309,B_1310),u1_struct_0(D_1311)) = k2_tmap_1(A_1309,k6_tmap_1(A_1309,B_1310),k7_tmap_1(A_1309,B_1310),D_1311)
      | ~ m1_pre_topc(D_1311,A_1309)
      | ~ v1_funct_2(k7_tmap_1(A_1309,B_1310),u1_struct_0(A_1309),u1_struct_0(k6_tmap_1(A_1309,B_1310)))
      | ~ v1_funct_1(k7_tmap_1(A_1309,B_1310))
      | ~ l1_pre_topc(k6_tmap_1(A_1309,B_1310))
      | ~ v2_pre_topc(k6_tmap_1(A_1309,B_1310))
      | v2_struct_0(k6_tmap_1(A_1309,B_1310))
      | ~ m1_subset_1(B_1310,k1_zfmisc_1(u1_struct_0(A_1309)))
      | ~ l1_pre_topc(A_1309)
      | ~ v2_pre_topc(A_1309)
      | v2_struct_0(A_1309) ) ),
    inference(resolution,[status(thm)],[c_32,c_10408])).

tff(c_13503,plain,(
    ! [D_1311] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),k7_tmap_1('#skF_2','#skF_3'),u1_struct_0(D_1311)) = k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),D_1311)
      | ~ m1_pre_topc(D_1311,'#skF_2')
      | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
      | ~ v2_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
      | v2_struct_0(k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6997,c_13471])).

tff(c_13522,plain,(
    ! [D_1311] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),k7_tmap_1('#skF_2','#skF_3'),u1_struct_0(D_1311)) = k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),D_1311)
      | ~ m1_pre_topc(D_1311,'#skF_2')
      | v2_struct_0(k6_tmap_1('#skF_2','#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_6818,c_6803,c_6833,c_7050,c_6997,c_13503])).

tff(c_13527,plain,(
    ! [D_1312] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),k7_tmap_1('#skF_2','#skF_3'),u1_struct_0(D_1312)) = k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),D_1312)
      | ~ m1_pre_topc(D_1312,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_6863,c_13522])).

tff(c_13569,plain,
    ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),k7_tmap_1('#skF_2','#skF_3'),'#skF_3') = k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_13527])).

tff(c_13579,plain,(
    k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4') = k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_10484,c_13569])).

tff(c_38,plain,(
    ! [A_39] :
      ( l1_struct_0(A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_3500,plain,(
    ! [A_431,B_432] :
      ( v1_funct_1(k7_tmap_1(A_431,B_432))
      | ~ m1_subset_1(B_432,k1_zfmisc_1(u1_struct_0(A_431)))
      | ~ l1_pre_topc(A_431)
      | ~ v2_pre_topc(A_431)
      | v2_struct_0(A_431) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_3503,plain,
    ( v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_3500])).

tff(c_3509,plain,
    ( v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_3503])).

tff(c_3510,plain,(
    v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_3509])).

tff(c_3485,plain,(
    ! [A_428,B_429] :
      ( l1_pre_topc(k6_tmap_1(A_428,B_429))
      | ~ m1_subset_1(B_429,k1_zfmisc_1(u1_struct_0(A_428)))
      | ~ l1_pre_topc(A_428)
      | ~ v2_pre_topc(A_428)
      | v2_struct_0(A_428) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_3488,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_3485])).

tff(c_3494,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_3488])).

tff(c_3495,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_3494])).

tff(c_3469,plain,(
    ! [A_424,B_425] :
      ( v1_pre_topc(k6_tmap_1(A_424,B_425))
      | ~ m1_subset_1(B_425,k1_zfmisc_1(u1_struct_0(A_424)))
      | ~ l1_pre_topc(A_424)
      | ~ v2_pre_topc(A_424)
      | v2_struct_0(A_424) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_3472,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_3469])).

tff(c_3478,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_3472])).

tff(c_3479,plain,(
    v1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_3478])).

tff(c_3588,plain,(
    ! [A_451,B_452] :
      ( g1_pre_topc(u1_struct_0(A_451),k5_tmap_1(A_451,B_452)) = k6_tmap_1(A_451,B_452)
      | ~ m1_subset_1(B_452,k1_zfmisc_1(u1_struct_0(A_451)))
      | ~ l1_pre_topc(A_451)
      | ~ v2_pre_topc(A_451)
      | v2_struct_0(A_451) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3590,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_3')) = k6_tmap_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_3588])).

tff(c_3595,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_3')) = k6_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_3590])).

tff(c_3596,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_3')) = k6_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_3595])).

tff(c_3617,plain,(
    ! [A_454,B_455] :
      ( u1_struct_0('#skF_2') = A_454
      | k6_tmap_1('#skF_2','#skF_3') != g1_pre_topc(A_454,B_455)
      | ~ m1_subset_1(B_455,k1_zfmisc_1(k1_zfmisc_1(A_454))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3596,c_52])).

tff(c_3635,plain,(
    ! [A_459] :
      ( u1_struct_0(A_459) = u1_struct_0('#skF_2')
      | g1_pre_topc(u1_struct_0(A_459),u1_pre_topc(A_459)) != k6_tmap_1('#skF_2','#skF_3')
      | ~ l1_pre_topc(A_459) ) ),
    inference(resolution,[status(thm)],[c_42,c_3617])).

tff(c_3645,plain,(
    ! [A_460] :
      ( u1_struct_0(A_460) = u1_struct_0('#skF_2')
      | k6_tmap_1('#skF_2','#skF_3') != A_460
      | ~ l1_pre_topc(A_460)
      | ~ v1_pre_topc(A_460)
      | ~ l1_pre_topc(A_460) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3635])).

tff(c_3648,plain,
    ( u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = u1_struct_0('#skF_2')
    | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_3479,c_3645])).

tff(c_3651,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = u1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3495,c_3648])).

tff(c_3671,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3651,c_34])).

tff(c_3706,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_3671])).

tff(c_3707,plain,(
    v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_3706])).

tff(c_3548,plain,(
    ! [A_443,B_444] :
      ( k7_tmap_1(A_443,B_444) = k6_partfun1(u1_struct_0(A_443))
      | ~ m1_subset_1(B_444,k1_zfmisc_1(u1_struct_0(A_443)))
      | ~ l1_pre_topc(A_443)
      | ~ v2_pre_topc(A_443)
      | v2_struct_0(A_443) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3551,plain,
    ( k6_partfun1(u1_struct_0('#skF_2')) = k7_tmap_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_3548])).

tff(c_3557,plain,
    ( k6_partfun1(u1_struct_0('#skF_2')) = k7_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_3551])).

tff(c_3558,plain,(
    k6_partfun1(u1_struct_0('#skF_2')) = k7_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_3557])).

tff(c_3568,plain,(
    m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3558,c_24])).

tff(c_3832,plain,(
    ! [A_472,B_473,C_474,D_475] :
      ( v1_funct_1(k2_tmap_1(A_472,B_473,C_474,D_475))
      | ~ l1_struct_0(D_475)
      | ~ m1_subset_1(C_474,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_472),u1_struct_0(B_473))))
      | ~ v1_funct_2(C_474,u1_struct_0(A_472),u1_struct_0(B_473))
      | ~ v1_funct_1(C_474)
      | ~ l1_struct_0(B_473)
      | ~ l1_struct_0(A_472) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_3840,plain,(
    ! [D_475] :
      ( v1_funct_1(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),D_475))
      | ~ l1_struct_0(D_475)
      | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
      | ~ l1_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_3568,c_3832])).

tff(c_3856,plain,(
    ! [D_475] :
      ( v1_funct_1(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),D_475))
      | ~ l1_struct_0(D_475)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3510,c_3707,c_3840])).

tff(c_3910,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3856])).

tff(c_3913,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_3910])).

tff(c_3917,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3913])).

tff(c_3919,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3856])).

tff(c_3920,plain,(
    ! [A_481,B_482,C_483,D_484] :
      ( v1_funct_2(k2_tmap_1(A_481,B_482,C_483,D_484),u1_struct_0(D_484),u1_struct_0(B_482))
      | ~ l1_struct_0(D_484)
      | ~ m1_subset_1(C_483,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_481),u1_struct_0(B_482))))
      | ~ v1_funct_2(C_483,u1_struct_0(A_481),u1_struct_0(B_482))
      | ~ v1_funct_1(C_483)
      | ~ l1_struct_0(B_482)
      | ~ l1_struct_0(A_481) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_3928,plain,(
    ! [D_484] :
      ( v1_funct_2(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),D_484),u1_struct_0(D_484),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_484)
      | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
      | ~ l1_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_3568,c_3920])).

tff(c_3944,plain,(
    ! [D_484] :
      ( v1_funct_2(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),D_484),u1_struct_0(D_484),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_484)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3510,c_3707,c_3928])).

tff(c_4055,plain,(
    ! [D_494] :
      ( v1_funct_2(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),D_494),u1_struct_0(D_494),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_494) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3919,c_3944])).

tff(c_4058,plain,
    ( v1_funct_2(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3')),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
    | ~ l1_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3651,c_4055])).

tff(c_4256,plain,(
    ~ l1_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4058])).

tff(c_4281,plain,(
    ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_4256])).

tff(c_4285,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3495,c_4281])).

tff(c_4287,plain,(
    l1_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_4058])).

tff(c_3395,plain,(
    ! [B_401,A_402] :
      ( l1_pre_topc(B_401)
      | ~ m1_pre_topc(B_401,A_402)
      | ~ l1_pre_topc(A_402) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_3398,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_3395])).

tff(c_3401,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3398])).

tff(c_4002,plain,(
    ! [A_489,B_490,C_491,D_492] :
      ( m1_subset_1(k2_tmap_1(A_489,B_490,C_491,D_492),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_492),u1_struct_0(B_490))))
      | ~ l1_struct_0(D_492)
      | ~ m1_subset_1(C_491,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_489),u1_struct_0(B_490))))
      | ~ v1_funct_2(C_491,u1_struct_0(A_489),u1_struct_0(B_490))
      | ~ v1_funct_1(C_491)
      | ~ l1_struct_0(B_490)
      | ~ l1_struct_0(A_489) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_4017,plain,(
    ! [A_489,B_490,C_491] :
      ( m1_subset_1(k2_tmap_1(A_489,B_490,C_491,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',u1_struct_0(B_490))))
      | ~ l1_struct_0('#skF_4')
      | ~ m1_subset_1(C_491,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_489),u1_struct_0(B_490))))
      | ~ v1_funct_2(C_491,u1_struct_0(A_489),u1_struct_0(B_490))
      | ~ v1_funct_1(C_491)
      | ~ l1_struct_0(B_490)
      | ~ l1_struct_0(A_489) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_4002])).

tff(c_4043,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4017])).

tff(c_4046,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_4043])).

tff(c_4050,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3401,c_4046])).

tff(c_5888,plain,(
    ! [A_661,B_662,C_663] :
      ( m1_subset_1(k2_tmap_1(A_661,B_662,C_663,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',u1_struct_0(B_662))))
      | ~ m1_subset_1(C_663,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_661),u1_struct_0(B_662))))
      | ~ v1_funct_2(C_663,u1_struct_0(A_661),u1_struct_0(B_662))
      | ~ v1_funct_1(C_663)
      | ~ l1_struct_0(B_662)
      | ~ l1_struct_0(A_661) ) ),
    inference(splitRight,[status(thm)],[c_4017])).

tff(c_5916,plain,(
    ! [A_661,C_663] :
      ( m1_subset_1(k2_tmap_1(A_661,k6_tmap_1('#skF_2','#skF_3'),C_663,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',u1_struct_0('#skF_2'))))
      | ~ m1_subset_1(C_663,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_661),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))))
      | ~ v1_funct_2(C_663,u1_struct_0(A_661),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_663)
      | ~ l1_struct_0(k6_tmap_1('#skF_2','#skF_3'))
      | ~ l1_struct_0(A_661) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3651,c_5888])).

tff(c_6709,plain,(
    ! [A_711,C_712] :
      ( m1_subset_1(k2_tmap_1(A_711,k6_tmap_1('#skF_2','#skF_3'),C_712,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',u1_struct_0('#skF_2'))))
      | ~ m1_subset_1(C_712,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_711),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_712,u1_struct_0(A_711),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_712)
      | ~ l1_struct_0(A_711) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4287,c_3651,c_3651,c_5916])).

tff(c_85,plain,(
    ! [B_95,A_96] :
      ( l1_pre_topc(B_95)
      | ~ m1_pre_topc(B_95,A_96)
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_88,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_85])).

tff(c_91,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_88])).

tff(c_692,plain,(
    ! [A_183,B_184,C_185,D_186] :
      ( m1_subset_1(k2_tmap_1(A_183,B_184,C_185,D_186),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_186),u1_struct_0(B_184))))
      | ~ l1_struct_0(D_186)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_183),u1_struct_0(B_184))))
      | ~ v1_funct_2(C_185,u1_struct_0(A_183),u1_struct_0(B_184))
      | ~ v1_funct_1(C_185)
      | ~ l1_struct_0(B_184)
      | ~ l1_struct_0(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_707,plain,(
    ! [A_183,B_184,C_185] :
      ( m1_subset_1(k2_tmap_1(A_183,B_184,C_185,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',u1_struct_0(B_184))))
      | ~ l1_struct_0('#skF_4')
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_183),u1_struct_0(B_184))))
      | ~ v1_funct_2(C_185,u1_struct_0(A_183),u1_struct_0(B_184))
      | ~ v1_funct_1(C_185)
      | ~ l1_struct_0(B_184)
      | ~ l1_struct_0(A_183) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_692])).

tff(c_733,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_707])).

tff(c_736,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_733])).

tff(c_740,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_736])).

tff(c_742,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_707])).

tff(c_174,plain,(
    ! [A_122,B_123] :
      ( v1_funct_1(k7_tmap_1(A_122,B_123))
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_177,plain,
    ( v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_174])).

tff(c_183,plain,
    ( v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_177])).

tff(c_184,plain,(
    v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_183])).

tff(c_189,plain,(
    ! [A_125,B_126] :
      ( l1_pre_topc(k6_tmap_1(A_125,B_126))
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125)
      | ~ v2_pre_topc(A_125)
      | v2_struct_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_192,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_189])).

tff(c_198,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_192])).

tff(c_199,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_198])).

tff(c_144,plain,(
    ! [A_116,B_117] :
      ( v1_pre_topc(k6_tmap_1(A_116,B_117))
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116)
      | v2_struct_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_147,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_144])).

tff(c_153,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_147])).

tff(c_154,plain,(
    v1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_153])).

tff(c_277,plain,(
    ! [A_145,B_146] :
      ( g1_pre_topc(u1_struct_0(A_145),k5_tmap_1(A_145,B_146)) = k6_tmap_1(A_145,B_146)
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145)
      | v2_struct_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_279,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_3')) = k6_tmap_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_277])).

tff(c_284,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_3')) = k6_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_279])).

tff(c_285,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_3')) = k6_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_284])).

tff(c_306,plain,(
    ! [A_148,B_149] :
      ( u1_struct_0('#skF_2') = A_148
      | k6_tmap_1('#skF_2','#skF_3') != g1_pre_topc(A_148,B_149)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(k1_zfmisc_1(A_148))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_52])).

tff(c_324,plain,(
    ! [A_153] :
      ( u1_struct_0(A_153) = u1_struct_0('#skF_2')
      | g1_pre_topc(u1_struct_0(A_153),u1_pre_topc(A_153)) != k6_tmap_1('#skF_2','#skF_3')
      | ~ l1_pre_topc(A_153) ) ),
    inference(resolution,[status(thm)],[c_42,c_306])).

tff(c_334,plain,(
    ! [A_154] :
      ( u1_struct_0(A_154) = u1_struct_0('#skF_2')
      | k6_tmap_1('#skF_2','#skF_3') != A_154
      | ~ l1_pre_topc(A_154)
      | ~ v1_pre_topc(A_154)
      | ~ l1_pre_topc(A_154) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_324])).

tff(c_337,plain,
    ( u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = u1_struct_0('#skF_2')
    | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_154,c_334])).

tff(c_340,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = u1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_337])).

tff(c_359,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_34])).

tff(c_394,plain,
    ( v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_359])).

tff(c_395,plain,(
    v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_394])).

tff(c_237,plain,(
    ! [A_137,B_138] :
      ( k7_tmap_1(A_137,B_138) = k6_partfun1(u1_struct_0(A_137))
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_240,plain,
    ( k6_partfun1(u1_struct_0('#skF_2')) = k7_tmap_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_237])).

tff(c_246,plain,
    ( k6_partfun1(u1_struct_0('#skF_2')) = k7_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_240])).

tff(c_247,plain,(
    k6_partfun1(u1_struct_0('#skF_2')) = k7_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_246])).

tff(c_257,plain,(
    m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_24])).

tff(c_522,plain,(
    ! [A_166,B_167,C_168,D_169] :
      ( v1_funct_1(k2_tmap_1(A_166,B_167,C_168,D_169))
      | ~ l1_struct_0(D_169)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_166),u1_struct_0(B_167))))
      | ~ v1_funct_2(C_168,u1_struct_0(A_166),u1_struct_0(B_167))
      | ~ v1_funct_1(C_168)
      | ~ l1_struct_0(B_167)
      | ~ l1_struct_0(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_530,plain,(
    ! [D_169] :
      ( v1_funct_1(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),D_169))
      | ~ l1_struct_0(D_169)
      | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
      | ~ l1_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_257,c_522])).

tff(c_546,plain,(
    ! [D_169] :
      ( v1_funct_1(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),D_169))
      | ~ l1_struct_0(D_169)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_395,c_530])).

tff(c_600,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_546])).

tff(c_603,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_600])).

tff(c_607,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_603])).

tff(c_609,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_546])).

tff(c_610,plain,(
    ! [A_175,B_176,C_177,D_178] :
      ( v1_funct_2(k2_tmap_1(A_175,B_176,C_177,D_178),u1_struct_0(D_178),u1_struct_0(B_176))
      | ~ l1_struct_0(D_178)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_175),u1_struct_0(B_176))))
      | ~ v1_funct_2(C_177,u1_struct_0(A_175),u1_struct_0(B_176))
      | ~ v1_funct_1(C_177)
      | ~ l1_struct_0(B_176)
      | ~ l1_struct_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_618,plain,(
    ! [D_178] :
      ( v1_funct_2(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),D_178),u1_struct_0(D_178),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_178)
      | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
      | ~ l1_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_257,c_610])).

tff(c_634,plain,(
    ! [D_178] :
      ( v1_funct_2(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),D_178),u1_struct_0(D_178),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_178)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_395,c_618])).

tff(c_745,plain,(
    ! [D_188] :
      ( v1_funct_2(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),D_188),u1_struct_0(D_188),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_188) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_609,c_634])).

tff(c_748,plain,
    ( v1_funct_2(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3')),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
    | ~ l1_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_745])).

tff(c_946,plain,(
    ~ l1_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_748])).

tff(c_971,plain,(
    ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_946])).

tff(c_975,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_971])).

tff(c_977,plain,(
    l1_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_748])).

tff(c_3359,plain,(
    ! [A_397,B_398,D_399] :
      ( v1_funct_1(k2_tmap_1(A_397,k6_tmap_1(A_397,B_398),k7_tmap_1(A_397,B_398),D_399))
      | ~ l1_struct_0(D_399)
      | ~ v1_funct_2(k7_tmap_1(A_397,B_398),u1_struct_0(A_397),u1_struct_0(k6_tmap_1(A_397,B_398)))
      | ~ v1_funct_1(k7_tmap_1(A_397,B_398))
      | ~ l1_struct_0(k6_tmap_1(A_397,B_398))
      | ~ l1_struct_0(A_397)
      | ~ m1_subset_1(B_398,k1_zfmisc_1(u1_struct_0(A_397)))
      | ~ l1_pre_topc(A_397)
      | ~ v2_pre_topc(A_397)
      | v2_struct_0(A_397) ) ),
    inference(resolution,[status(thm)],[c_32,c_522])).

tff(c_3367,plain,(
    ! [D_399] :
      ( v1_funct_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),D_399))
      | ~ l1_struct_0(D_399)
      | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
      | ~ l1_struct_0(k6_tmap_1('#skF_2','#skF_3'))
      | ~ l1_struct_0('#skF_2')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_3359])).

tff(c_3379,plain,(
    ! [D_399] :
      ( v1_funct_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),D_399))
      | ~ l1_struct_0(D_399)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_609,c_977,c_184,c_395,c_3367])).

tff(c_3385,plain,(
    ! [D_400] :
      ( v1_funct_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),D_400))
      | ~ l1_struct_0(D_400) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_3379])).

tff(c_62,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k6_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_77,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k6_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_3',u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_64,c_62])).

tff(c_84,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_3388,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_3385,c_84])).

tff(c_3392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_742,c_3388])).

tff(c_3393,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_3',u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | ~ v5_pre_topc(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_3431,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitLeft,[status(thm)],[c_3393])).

tff(c_3661,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3651,c_3431])).

tff(c_6734,plain,
    ( ~ m1_subset_1(k7_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_6709,c_3661])).

tff(c_6767,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3919,c_3510,c_3707,c_3568,c_6734])).

tff(c_6768,plain,
    ( ~ v5_pre_topc(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k6_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_3',u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_3393])).

tff(c_7291,plain,
    ( ~ v5_pre_topc(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k6_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_3',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6997,c_6768])).

tff(c_7292,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_3',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_7291])).

tff(c_7194,plain,(
    ! [A_781,B_782,C_783,D_784] :
      ( v1_funct_1(k2_tmap_1(A_781,B_782,C_783,D_784))
      | ~ l1_struct_0(D_784)
      | ~ m1_subset_1(C_783,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_781),u1_struct_0(B_782))))
      | ~ v1_funct_2(C_783,u1_struct_0(A_781),u1_struct_0(B_782))
      | ~ v1_funct_1(C_783)
      | ~ l1_struct_0(B_782)
      | ~ l1_struct_0(A_781) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_7205,plain,(
    ! [D_784] :
      ( v1_funct_1(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),D_784))
      | ~ l1_struct_0(D_784)
      | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
      | ~ l1_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6911,c_7194])).

tff(c_7219,plain,(
    ! [D_784] :
      ( v1_funct_1(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),D_784))
      | ~ l1_struct_0(D_784)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6833,c_7050,c_7205])).

tff(c_7281,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_7219])).

tff(c_7284,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_7281])).

tff(c_7288,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_7284])).

tff(c_7290,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_7219])).

tff(c_7334,plain,(
    ! [A_791,B_792,C_793,D_794] :
      ( v1_funct_2(k2_tmap_1(A_791,B_792,C_793,D_794),u1_struct_0(D_794),u1_struct_0(B_792))
      | ~ l1_struct_0(D_794)
      | ~ m1_subset_1(C_793,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_791),u1_struct_0(B_792))))
      | ~ v1_funct_2(C_793,u1_struct_0(A_791),u1_struct_0(B_792))
      | ~ v1_funct_1(C_793)
      | ~ l1_struct_0(B_792)
      | ~ l1_struct_0(A_791) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_7347,plain,(
    ! [D_794] :
      ( v1_funct_2(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),D_794),u1_struct_0(D_794),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_794)
      | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
      | ~ l1_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6911,c_7334])).

tff(c_7368,plain,(
    ! [D_795] :
      ( v1_funct_2(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),D_795),u1_struct_0(D_795),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_795) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7290,c_6833,c_7050,c_7347])).

tff(c_7374,plain,
    ( v1_funct_2(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_7368])).

tff(c_7375,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_7374])).

tff(c_7378,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_7375])).

tff(c_7382,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3401,c_7378])).

tff(c_7384,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_7374])).

tff(c_7371,plain,
    ( v1_funct_2(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3')),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
    | ~ l1_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6997,c_7368])).

tff(c_7550,plain,(
    ~ l1_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_7371])).

tff(c_7553,plain,(
    ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_7550])).

tff(c_7557,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6803,c_7553])).

tff(c_7559,plain,(
    l1_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_7371])).

tff(c_9899,plain,(
    ! [A_1011,B_1012,D_1013] :
      ( v1_funct_2(k2_tmap_1(A_1011,k6_tmap_1(A_1011,B_1012),k7_tmap_1(A_1011,B_1012),D_1013),u1_struct_0(D_1013),u1_struct_0(k6_tmap_1(A_1011,B_1012)))
      | ~ l1_struct_0(D_1013)
      | ~ v1_funct_2(k7_tmap_1(A_1011,B_1012),u1_struct_0(A_1011),u1_struct_0(k6_tmap_1(A_1011,B_1012)))
      | ~ v1_funct_1(k7_tmap_1(A_1011,B_1012))
      | ~ l1_struct_0(k6_tmap_1(A_1011,B_1012))
      | ~ l1_struct_0(A_1011)
      | ~ m1_subset_1(B_1012,k1_zfmisc_1(u1_struct_0(A_1011)))
      | ~ l1_pre_topc(A_1011)
      | ~ v2_pre_topc(A_1011)
      | v2_struct_0(A_1011) ) ),
    inference(resolution,[status(thm)],[c_32,c_7334])).

tff(c_9911,plain,(
    ! [D_1013] :
      ( v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),D_1013),u1_struct_0(D_1013),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_1013)
      | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
      | ~ l1_struct_0(k6_tmap_1('#skF_2','#skF_3'))
      | ~ l1_struct_0('#skF_2')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6997,c_9899])).

tff(c_9921,plain,(
    ! [D_1013] :
      ( v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),D_1013),u1_struct_0(D_1013),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_1013)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_7290,c_7559,c_6833,c_7050,c_6997,c_9911])).

tff(c_9925,plain,(
    ! [D_1014] :
      ( v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),D_1014),u1_struct_0(D_1014),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_1014) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_9921])).

tff(c_9934,plain,
    ( v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_9925])).

tff(c_9938,plain,(
    v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_3',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7384,c_9934])).

tff(c_9940,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7292,c_9938])).

tff(c_9941,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k6_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_7291])).

tff(c_13594,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k6_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13579,c_9941])).

tff(c_3394,plain,(
    v1_funct_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4')) ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_9942,plain,(
    v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_3',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_7291])).

tff(c_6769,plain,(
    m1_subset_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitRight,[status(thm)],[c_3393])).

tff(c_7006,plain,(
    m1_subset_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6997,c_6769])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_3403,plain,(
    ! [B_404,A_405] :
      ( v2_pre_topc(B_404)
      | ~ m1_pre_topc(B_404,A_405)
      | ~ l1_pre_topc(A_405)
      | ~ v2_pre_topc(A_405) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3406,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_3403])).

tff(c_3409,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_3406])).

tff(c_10074,plain,(
    ! [A_1029,B_1030,C_1031] :
      ( m1_subset_1('#skF_1'(A_1029,B_1030,C_1031),u1_struct_0(B_1030))
      | v5_pre_topc(C_1031,B_1030,A_1029)
      | ~ m1_subset_1(C_1031,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_1030),u1_struct_0(A_1029))))
      | ~ v1_funct_2(C_1031,u1_struct_0(B_1030),u1_struct_0(A_1029))
      | ~ v1_funct_1(C_1031)
      | ~ l1_pre_topc(B_1030)
      | ~ v2_pre_topc(B_1030)
      | v2_struct_0(B_1030)
      | ~ l1_pre_topc(A_1029)
      | ~ v2_pre_topc(A_1029)
      | v2_struct_0(A_1029) ) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_10094,plain,(
    ! [A_1029,C_1031] :
      ( m1_subset_1('#skF_1'(A_1029,'#skF_4',C_1031),u1_struct_0('#skF_4'))
      | v5_pre_topc(C_1031,'#skF_4',A_1029)
      | ~ m1_subset_1(C_1031,k1_zfmisc_1(k2_zfmisc_1('#skF_3',u1_struct_0(A_1029))))
      | ~ v1_funct_2(C_1031,u1_struct_0('#skF_4'),u1_struct_0(A_1029))
      | ~ v1_funct_1(C_1031)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_1029)
      | ~ v2_pre_topc(A_1029)
      | v2_struct_0(A_1029) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_10074])).

tff(c_10116,plain,(
    ! [A_1029,C_1031] :
      ( m1_subset_1('#skF_1'(A_1029,'#skF_4',C_1031),'#skF_3')
      | v5_pre_topc(C_1031,'#skF_4',A_1029)
      | ~ m1_subset_1(C_1031,k1_zfmisc_1(k2_zfmisc_1('#skF_3',u1_struct_0(A_1029))))
      | ~ v1_funct_2(C_1031,'#skF_3',u1_struct_0(A_1029))
      | ~ v1_funct_1(C_1031)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_1029)
      | ~ v2_pre_topc(A_1029)
      | v2_struct_0(A_1029) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3409,c_3401,c_64,c_64,c_10094])).

tff(c_10207,plain,(
    ! [A_1045,C_1046] :
      ( m1_subset_1('#skF_1'(A_1045,'#skF_4',C_1046),'#skF_3')
      | v5_pre_topc(C_1046,'#skF_4',A_1045)
      | ~ m1_subset_1(C_1046,k1_zfmisc_1(k2_zfmisc_1('#skF_3',u1_struct_0(A_1045))))
      | ~ v1_funct_2(C_1046,'#skF_3',u1_struct_0(A_1045))
      | ~ v1_funct_1(C_1046)
      | ~ l1_pre_topc(A_1045)
      | ~ v2_pre_topc(A_1045)
      | v2_struct_0(A_1045) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_10116])).

tff(c_10216,plain,(
    ! [C_1046] :
      ( m1_subset_1('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),'#skF_4',C_1046),'#skF_3')
      | v5_pre_topc(C_1046,'#skF_4',k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_1046,k1_zfmisc_1(k2_zfmisc_1('#skF_3',u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_1046,'#skF_3',u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_1046)
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
      | ~ v2_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
      | v2_struct_0(k6_tmap_1('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6997,c_10207])).

tff(c_10230,plain,(
    ! [C_1046] :
      ( m1_subset_1('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),'#skF_4',C_1046),'#skF_3')
      | v5_pre_topc(C_1046,'#skF_4',k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_1046,k1_zfmisc_1(k2_zfmisc_1('#skF_3',u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_1046,'#skF_3',u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_1046)
      | v2_struct_0(k6_tmap_1('#skF_2','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6818,c_6803,c_6997,c_10216])).

tff(c_11869,plain,(
    ! [C_1190] :
      ( m1_subset_1('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),'#skF_4',C_1190),'#skF_3')
      | v5_pre_topc(C_1190,'#skF_4',k6_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_1190,k1_zfmisc_1(k2_zfmisc_1('#skF_3',u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_1190,'#skF_3',u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_1190) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6863,c_10230])).

tff(c_11875,plain,
    ( m1_subset_1('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),'#skF_4',k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4')),'#skF_3')
    | v5_pre_topc(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k6_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_3',u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_7006,c_11869])).

tff(c_11883,plain,
    ( m1_subset_1('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),'#skF_4',k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4')),'#skF_3')
    | v5_pre_topc(k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k6_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3394,c_9942,c_11875])).

tff(c_11884,plain,(
    m1_subset_1('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),'#skF_4',k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4')),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_9941,c_11883])).

tff(c_13581,plain,(
    m1_subset_1('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),'#skF_4',k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),'#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13579,c_11884])).

tff(c_13593,plain,(
    m1_subset_1(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13579,c_7006])).

tff(c_6788,plain,(
    ! [A_721,B_722,C_723,D_724] :
      ( v1_funct_1(k2_partfun1(A_721,B_722,C_723,D_724))
      | ~ m1_subset_1(C_723,k1_zfmisc_1(k2_zfmisc_1(A_721,B_722)))
      | ~ v1_funct_1(C_723) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6791,plain,(
    ! [A_34,D_724] :
      ( v1_funct_1(k2_partfun1(A_34,A_34,k6_partfun1(A_34),D_724))
      | ~ v1_funct_1(k6_partfun1(A_34)) ) ),
    inference(resolution,[status(thm)],[c_24,c_6788])).

tff(c_6908,plain,(
    ! [D_724] :
      ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),k7_tmap_1('#skF_2','#skF_3'),D_724))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6901,c_6791])).

tff(c_6918,plain,(
    ! [D_724] : v1_funct_1(k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),k7_tmap_1('#skF_2','#skF_3'),D_724)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6833,c_6901,c_6908])).

tff(c_10491,plain,(
    v1_funct_1(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10484,c_6918])).

tff(c_9971,plain,(
    ! [A_1018,B_1019,C_1020,D_1021] :
      ( v1_funct_2(k2_tmap_1(A_1018,B_1019,C_1020,D_1021),u1_struct_0(D_1021),u1_struct_0(B_1019))
      | ~ l1_struct_0(D_1021)
      | ~ m1_subset_1(C_1020,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1018),u1_struct_0(B_1019))))
      | ~ v1_funct_2(C_1020,u1_struct_0(A_1018),u1_struct_0(B_1019))
      | ~ v1_funct_1(C_1020)
      | ~ l1_struct_0(B_1019)
      | ~ l1_struct_0(A_1018) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_9982,plain,(
    ! [D_1021] :
      ( v1_funct_2(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),D_1021),u1_struct_0(D_1021),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_1021)
      | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
      | ~ l1_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6911,c_9971])).

tff(c_10000,plain,(
    ! [D_1022] :
      ( v1_funct_2(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),D_1022),u1_struct_0(D_1022),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_1022) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7290,c_6833,c_7050,c_9982])).

tff(c_10006,plain,
    ( v1_funct_2(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_10000])).

tff(c_10007,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_10006])).

tff(c_10010,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_10007])).

tff(c_10014,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3401,c_10010])).

tff(c_10015,plain,(
    v1_funct_2(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_3',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_10006])).

tff(c_10160,plain,(
    ! [C_1040,A_1041,D_1042] :
      ( r1_tmap_1(C_1040,k6_tmap_1(A_1041,u1_struct_0(C_1040)),k2_tmap_1(A_1041,k6_tmap_1(A_1041,u1_struct_0(C_1040)),k7_tmap_1(A_1041,u1_struct_0(C_1040)),C_1040),D_1042)
      | ~ m1_subset_1(D_1042,u1_struct_0(C_1040))
      | ~ m1_pre_topc(C_1040,A_1041)
      | v2_struct_0(C_1040)
      | ~ m1_subset_1(u1_struct_0(C_1040),k1_zfmisc_1(u1_struct_0(A_1041)))
      | ~ l1_pre_topc(A_1041)
      | ~ v2_pre_topc(A_1041)
      | v2_struct_0(A_1041) ) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_10172,plain,(
    ! [A_1041,D_1042] :
      ( r1_tmap_1('#skF_4',k6_tmap_1(A_1041,'#skF_3'),k2_tmap_1(A_1041,k6_tmap_1(A_1041,u1_struct_0('#skF_4')),k7_tmap_1(A_1041,u1_struct_0('#skF_4')),'#skF_4'),D_1042)
      | ~ m1_subset_1(D_1042,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc('#skF_4',A_1041)
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_1041)))
      | ~ l1_pre_topc(A_1041)
      | ~ v2_pre_topc(A_1041)
      | v2_struct_0(A_1041) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_10160])).

tff(c_10185,plain,(
    ! [A_1041,D_1042] :
      ( r1_tmap_1('#skF_4',k6_tmap_1(A_1041,'#skF_3'),k2_tmap_1(A_1041,k6_tmap_1(A_1041,'#skF_3'),k7_tmap_1(A_1041,'#skF_3'),'#skF_4'),D_1042)
      | ~ m1_subset_1(D_1042,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_1041)
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_1041)))
      | ~ l1_pre_topc(A_1041)
      | ~ v2_pre_topc(A_1041)
      | v2_struct_0(A_1041) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_64,c_64,c_64,c_10172])).

tff(c_10186,plain,(
    ! [A_1041,D_1042] :
      ( r1_tmap_1('#skF_4',k6_tmap_1(A_1041,'#skF_3'),k2_tmap_1(A_1041,k6_tmap_1(A_1041,'#skF_3'),k7_tmap_1(A_1041,'#skF_3'),'#skF_4'),D_1042)
      | ~ m1_subset_1(D_1042,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_1041)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_1041)))
      | ~ l1_pre_topc(A_1041)
      | ~ v2_pre_topc(A_1041)
      | v2_struct_0(A_1041) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_10185])).

tff(c_13626,plain,(
    ! [D_1042] :
      ( r1_tmap_1('#skF_4',k6_tmap_1('#skF_2','#skF_3'),k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),D_1042)
      | ~ m1_subset_1(D_1042,'#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13579,c_10186])).

tff(c_13650,plain,(
    ! [D_1042] :
      ( r1_tmap_1('#skF_4',k6_tmap_1('#skF_2','#skF_3'),k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),D_1042)
      | ~ m1_subset_1(D_1042,'#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_66,c_13626])).

tff(c_13655,plain,(
    ! [D_1314] :
      ( r1_tmap_1('#skF_4',k6_tmap_1('#skF_2','#skF_3'),k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),D_1314)
      | ~ m1_subset_1(D_1314,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_13650])).

tff(c_58,plain,(
    ! [B_79,A_67,C_85] :
      ( ~ r1_tmap_1(B_79,A_67,C_85,'#skF_1'(A_67,B_79,C_85))
      | v5_pre_topc(C_85,B_79,A_67)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_79),u1_struct_0(A_67))))
      | ~ v1_funct_2(C_85,u1_struct_0(B_79),u1_struct_0(A_67))
      | ~ v1_funct_1(C_85)
      | ~ l1_pre_topc(B_79)
      | ~ v2_pre_topc(B_79)
      | v2_struct_0(B_79)
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_13658,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))))
    | ~ v1_funct_2(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),'#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),'#skF_4',k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),'#skF_4')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_13655,c_58])).

tff(c_13661,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_4')
    | v2_struct_0(k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),'#skF_4',k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),'#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6818,c_6803,c_3409,c_3401,c_10491,c_10015,c_64,c_6997,c_64,c_6997,c_13658])).

tff(c_13662,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',u1_struct_0('#skF_2'))))
    | ~ m1_subset_1('#skF_1'(k6_tmap_1('#skF_2','#skF_3'),'#skF_4',k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),'#skF_4')),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_6863,c_68,c_13661])).

tff(c_15061,plain,(
    v5_pre_topc(k2_tmap_1('#skF_2','#skF_2',k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k6_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13581,c_13593,c_13662])).

tff(c_15062,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13594,c_15061])).

%------------------------------------------------------------------------------
