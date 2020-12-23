%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1796+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:24 EST 2020

% Result     : Theorem 13.85s
% Output     : CNFRefutation 14.21s
% Verified   : 
% Statistics : Number of formulae       :  384 (15121 expanded)
%              Number of leaves         :   48 (5578 expanded)
%              Depth                    :   26
%              Number of atoms          : 1199 (74919 expanded)
%              Number of equality atoms :   99 (8433 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_tmap_1 > k6_tmap_1 > k5_tmap_1 > k2_zfmisc_1 > g1_pre_topc > a_2_0_tmap_1 > #nlpp > u1_struct_0 > u1_pre_topc > k6_partfun1 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k7_tmap_1,type,(
    k7_tmap_1: ( $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(a_2_0_tmap_1,type,(
    a_2_0_tmap_1: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff(f_284,negated_conjecture,(
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

tff(f_161,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_funct_1(k7_tmap_1(A,B))
        & v1_funct_2(k7_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B)))
        & m1_subset_1(k7_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

tff(f_146,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_196,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( ~ v2_struct_0(k6_tmap_1(A,B))
        & v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tmap_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k5_tmap_1(A,B) = a_2_0_tmap_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tmap_1)).

tff(f_131,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k5_tmap_1(A,B),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_tmap_1)).

tff(f_102,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k6_tmap_1(A,B) = g1_pre_topc(u1_struct_0(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_205,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

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

tff(f_165,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_120,axiom,(
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

tff(f_172,axiom,(
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

tff(f_228,axiom,(
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

tff(f_257,axiom,(
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

tff(c_64,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_284])).

tff(c_62,plain,(
    u1_struct_0('#skF_6') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_284])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_284])).

tff(c_72,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_284])).

tff(c_70,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_284])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_284])).

tff(c_10524,plain,(
    ! [A_618,B_619] :
      ( v1_funct_1(k7_tmap_1(A_618,B_619))
      | ~ m1_subset_1(B_619,k1_zfmisc_1(u1_struct_0(A_618)))
      | ~ l1_pre_topc(A_618)
      | ~ v2_pre_topc(A_618)
      | v2_struct_0(A_618) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_10527,plain,
    ( v1_funct_1(k7_tmap_1('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_10524])).

tff(c_10537,plain,
    ( v1_funct_1(k7_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_10527])).

tff(c_10538,plain,(
    v1_funct_1(k7_tmap_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_10537])).

tff(c_14781,plain,(
    ! [A_830,B_831] :
      ( l1_pre_topc(k6_tmap_1(A_830,B_831))
      | ~ m1_subset_1(B_831,k1_zfmisc_1(u1_struct_0(A_830)))
      | ~ l1_pre_topc(A_830)
      | ~ v2_pre_topc(A_830)
      | v2_struct_0(A_830) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_14784,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_14781])).

tff(c_14794,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_14784])).

tff(c_14795,plain,(
    l1_pre_topc(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_14794])).

tff(c_10549,plain,(
    ! [A_621,B_622] :
      ( v1_pre_topc(k6_tmap_1(A_621,B_622))
      | ~ m1_subset_1(B_622,k1_zfmisc_1(u1_struct_0(A_621)))
      | ~ l1_pre_topc(A_621)
      | ~ v2_pre_topc(A_621)
      | v2_struct_0(A_621) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_10552,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_10549])).

tff(c_10562,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_10552])).

tff(c_10563,plain,(
    v1_pre_topc(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_10562])).

tff(c_14926,plain,(
    ! [A_849,B_850] :
      ( k5_tmap_1(A_849,B_850) = a_2_0_tmap_1(A_849,B_850)
      | ~ m1_subset_1(B_850,k1_zfmisc_1(u1_struct_0(A_849)))
      | ~ l1_pre_topc(A_849)
      | ~ v2_pre_topc(A_849)
      | v2_struct_0(A_849) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_14929,plain,
    ( k5_tmap_1('#skF_4','#skF_5') = a_2_0_tmap_1('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_14926])).

tff(c_14939,plain,
    ( k5_tmap_1('#skF_4','#skF_5') = a_2_0_tmap_1('#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_14929])).

tff(c_14940,plain,(
    k5_tmap_1('#skF_4','#skF_5') = a_2_0_tmap_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_14939])).

tff(c_14949,plain,(
    ! [A_851,B_852] :
      ( m1_subset_1(k5_tmap_1(A_851,B_852),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_851))))
      | ~ m1_subset_1(B_852,k1_zfmisc_1(u1_struct_0(A_851)))
      | ~ l1_pre_topc(A_851)
      | ~ v2_pre_topc(A_851)
      | v2_struct_0(A_851) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_14952,plain,
    ( m1_subset_1(a_2_0_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_14940,c_14949])).

tff(c_14957,plain,
    ( m1_subset_1(a_2_0_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_14952])).

tff(c_14958,plain,(
    m1_subset_1(a_2_0_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_14957])).

tff(c_15040,plain,(
    ! [A_863,B_864] :
      ( g1_pre_topc(u1_struct_0(A_863),k5_tmap_1(A_863,B_864)) = k6_tmap_1(A_863,B_864)
      | ~ m1_subset_1(B_864,k1_zfmisc_1(u1_struct_0(A_863)))
      | ~ l1_pre_topc(A_863)
      | ~ v2_pre_topc(A_863)
      | v2_struct_0(A_863) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_15042,plain,
    ( g1_pre_topc(u1_struct_0('#skF_4'),k5_tmap_1('#skF_4','#skF_5')) = k6_tmap_1('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_15040])).

tff(c_15050,plain,
    ( g1_pre_topc(u1_struct_0('#skF_4'),a_2_0_tmap_1('#skF_4','#skF_5')) = k6_tmap_1('#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_14940,c_15042])).

tff(c_15051,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),a_2_0_tmap_1('#skF_4','#skF_5')) = k6_tmap_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_15050])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_4384,plain,(
    ! [C_339,A_340,D_341,B_342] :
      ( C_339 = A_340
      | g1_pre_topc(C_339,D_341) != g1_pre_topc(A_340,B_342)
      | ~ m1_subset_1(B_342,k1_zfmisc_1(k1_zfmisc_1(A_340))) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_4386,plain,(
    ! [A_1,A_340,B_342] :
      ( u1_struct_0(A_1) = A_340
      | g1_pre_topc(A_340,B_342) != A_1
      | ~ m1_subset_1(B_342,k1_zfmisc_1(k1_zfmisc_1(A_340)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4384])).

tff(c_15062,plain,(
    ! [A_1] :
      ( u1_struct_0(A_1) = u1_struct_0('#skF_4')
      | k6_tmap_1('#skF_4','#skF_5') != A_1
      | ~ m1_subset_1(a_2_0_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15051,c_4386])).

tff(c_15110,plain,(
    ! [A_870] :
      ( u1_struct_0(A_870) = u1_struct_0('#skF_4')
      | k6_tmap_1('#skF_4','#skF_5') != A_870
      | ~ v1_pre_topc(A_870)
      | ~ l1_pre_topc(A_870) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14958,c_15062])).

tff(c_15119,plain,
    ( u1_struct_0(k6_tmap_1('#skF_4','#skF_5')) = u1_struct_0('#skF_4')
    | ~ l1_pre_topc(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_10563,c_15110])).

tff(c_15126,plain,(
    u1_struct_0(k6_tmap_1('#skF_4','#skF_5')) = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14795,c_15119])).

tff(c_15257,plain,(
    ! [A_871,B_872] :
      ( v1_funct_2(k7_tmap_1(A_871,B_872),u1_struct_0(A_871),u1_struct_0(k6_tmap_1(A_871,B_872)))
      | ~ m1_subset_1(B_872,k1_zfmisc_1(u1_struct_0(A_871)))
      | ~ l1_pre_topc(A_871)
      | ~ v2_pre_topc(A_871)
      | v2_struct_0(A_871) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_15263,plain,
    ( v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_15126,c_15257])).

tff(c_15277,plain,
    ( v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_15263])).

tff(c_15278,plain,(
    v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_15277])).

tff(c_15349,plain,(
    ! [A_874,B_875] :
      ( m1_subset_1(k7_tmap_1(A_874,B_875),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_874),u1_struct_0(k6_tmap_1(A_874,B_875)))))
      | ~ m1_subset_1(B_875,k1_zfmisc_1(u1_struct_0(A_874)))
      | ~ l1_pre_topc(A_874)
      | ~ v2_pre_topc(A_874)
      | v2_struct_0(A_874) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_15358,plain,
    ( m1_subset_1(k7_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_15126,c_15349])).

tff(c_15375,plain,
    ( m1_subset_1(k7_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_15358])).

tff(c_15376,plain,(
    m1_subset_1(k7_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')))) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_15375])).

tff(c_16233,plain,(
    ! [A_927,B_928,C_929,D_930] :
      ( k2_partfun1(u1_struct_0(A_927),u1_struct_0(B_928),C_929,u1_struct_0(D_930)) = k2_tmap_1(A_927,B_928,C_929,D_930)
      | ~ m1_pre_topc(D_930,A_927)
      | ~ m1_subset_1(C_929,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_927),u1_struct_0(B_928))))
      | ~ v1_funct_2(C_929,u1_struct_0(A_927),u1_struct_0(B_928))
      | ~ v1_funct_1(C_929)
      | ~ l1_pre_topc(B_928)
      | ~ v2_pre_topc(B_928)
      | v2_struct_0(B_928)
      | ~ l1_pre_topc(A_927)
      | ~ v2_pre_topc(A_927)
      | v2_struct_0(A_927) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_16243,plain,(
    ! [D_930] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),k7_tmap_1('#skF_4','#skF_5'),u1_struct_0(D_930)) = k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),D_930)
      | ~ m1_pre_topc(D_930,'#skF_4')
      | ~ v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(k7_tmap_1('#skF_4','#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_15376,c_16233])).

tff(c_16270,plain,(
    ! [D_930] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),k7_tmap_1('#skF_4','#skF_5'),u1_struct_0(D_930)) = k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),D_930)
      | ~ m1_pre_topc(D_930,'#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_10538,c_15278,c_16243])).

tff(c_16309,plain,(
    ! [D_932] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),k7_tmap_1('#skF_4','#skF_5'),u1_struct_0(D_932)) = k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),D_932)
      | ~ m1_pre_topc(D_932,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_16270])).

tff(c_16324,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),k7_tmap_1('#skF_4','#skF_5'),'#skF_5') = k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),'#skF_6')
    | ~ m1_pre_topc('#skF_6','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_16309])).

tff(c_16328,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),k7_tmap_1('#skF_4','#skF_5'),'#skF_5') = k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_16324])).

tff(c_14800,plain,(
    ! [A_832,B_833] :
      ( ~ v2_struct_0(k6_tmap_1(A_832,B_833))
      | ~ m1_subset_1(B_833,k1_zfmisc_1(u1_struct_0(A_832)))
      | ~ l1_pre_topc(A_832)
      | ~ v2_pre_topc(A_832)
      | v2_struct_0(A_832) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_14803,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_14800])).

tff(c_14813,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_14803])).

tff(c_14814,plain,(
    ~ v2_struct_0(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_14813])).

tff(c_10492,plain,(
    ! [A_614,B_615] :
      ( v2_pre_topc(k6_tmap_1(A_614,B_615))
      | ~ m1_subset_1(B_615,k1_zfmisc_1(u1_struct_0(A_614)))
      | ~ l1_pre_topc(A_614)
      | ~ v2_pre_topc(A_614)
      | v2_struct_0(A_614) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_10495,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_10492])).

tff(c_10505,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_10495])).

tff(c_10506,plain,(
    v2_pre_topc(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_10505])).

tff(c_28,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1(k7_tmap_1(A_37,B_38),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_37),u1_struct_0(k6_tmap_1(A_37,B_38)))))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_20233,plain,(
    ! [A_1069,B_1070,D_1071] :
      ( k2_partfun1(u1_struct_0(A_1069),u1_struct_0(k6_tmap_1(A_1069,B_1070)),k7_tmap_1(A_1069,B_1070),u1_struct_0(D_1071)) = k2_tmap_1(A_1069,k6_tmap_1(A_1069,B_1070),k7_tmap_1(A_1069,B_1070),D_1071)
      | ~ m1_pre_topc(D_1071,A_1069)
      | ~ v1_funct_2(k7_tmap_1(A_1069,B_1070),u1_struct_0(A_1069),u1_struct_0(k6_tmap_1(A_1069,B_1070)))
      | ~ v1_funct_1(k7_tmap_1(A_1069,B_1070))
      | ~ l1_pre_topc(k6_tmap_1(A_1069,B_1070))
      | ~ v2_pre_topc(k6_tmap_1(A_1069,B_1070))
      | v2_struct_0(k6_tmap_1(A_1069,B_1070))
      | ~ m1_subset_1(B_1070,k1_zfmisc_1(u1_struct_0(A_1069)))
      | ~ l1_pre_topc(A_1069)
      | ~ v2_pre_topc(A_1069)
      | v2_struct_0(A_1069) ) ),
    inference(resolution,[status(thm)],[c_28,c_16233])).

tff(c_20311,plain,(
    ! [D_1071] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),k7_tmap_1('#skF_4','#skF_5'),u1_struct_0(D_1071)) = k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),D_1071)
      | ~ m1_pre_topc(D_1071,'#skF_4')
      | ~ v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_4','#skF_5')))
      | ~ v1_funct_1(k7_tmap_1('#skF_4','#skF_5'))
      | ~ l1_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
      | ~ v2_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
      | v2_struct_0(k6_tmap_1('#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15126,c_20233])).

tff(c_20387,plain,(
    ! [D_1071] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),k7_tmap_1('#skF_4','#skF_5'),u1_struct_0(D_1071)) = k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),D_1071)
      | ~ m1_pre_topc(D_1071,'#skF_4')
      | v2_struct_0(k6_tmap_1('#skF_4','#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_10506,c_14795,c_10538,c_15278,c_15126,c_20311])).

tff(c_20895,plain,(
    ! [D_1091] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),k7_tmap_1('#skF_4','#skF_5'),u1_struct_0(D_1091)) = k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),D_1091)
      | ~ m1_pre_topc(D_1091,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_14814,c_20387])).

tff(c_20925,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),k7_tmap_1('#skF_4','#skF_5'),'#skF_5') = k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_6')
    | ~ m1_pre_topc('#skF_6','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_20895])).

tff(c_20931,plain,(
    k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_6') = k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_16328,c_20925])).

tff(c_10589,plain,(
    ! [A_626,B_627] :
      ( l1_pre_topc(k6_tmap_1(A_626,B_627))
      | ~ m1_subset_1(B_627,k1_zfmisc_1(u1_struct_0(A_626)))
      | ~ l1_pre_topc(A_626)
      | ~ v2_pre_topc(A_626)
      | v2_struct_0(A_626) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_10592,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_10589])).

tff(c_10602,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_10592])).

tff(c_10603,plain,(
    l1_pre_topc(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_10602])).

tff(c_10735,plain,(
    ! [A_645,B_646] :
      ( k5_tmap_1(A_645,B_646) = a_2_0_tmap_1(A_645,B_646)
      | ~ m1_subset_1(B_646,k1_zfmisc_1(u1_struct_0(A_645)))
      | ~ l1_pre_topc(A_645)
      | ~ v2_pre_topc(A_645)
      | v2_struct_0(A_645) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_10738,plain,
    ( k5_tmap_1('#skF_4','#skF_5') = a_2_0_tmap_1('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_10735])).

tff(c_10748,plain,
    ( k5_tmap_1('#skF_4','#skF_5') = a_2_0_tmap_1('#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_10738])).

tff(c_10749,plain,(
    k5_tmap_1('#skF_4','#skF_5') = a_2_0_tmap_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_10748])).

tff(c_10764,plain,(
    ! [A_648,B_649] :
      ( m1_subset_1(k5_tmap_1(A_648,B_649),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_648))))
      | ~ m1_subset_1(B_649,k1_zfmisc_1(u1_struct_0(A_648)))
      | ~ l1_pre_topc(A_648)
      | ~ v2_pre_topc(A_648)
      | v2_struct_0(A_648) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_10767,plain,
    ( m1_subset_1(a_2_0_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10749,c_10764])).

tff(c_10772,plain,
    ( m1_subset_1(a_2_0_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_10767])).

tff(c_10773,plain,(
    m1_subset_1(a_2_0_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_10772])).

tff(c_10876,plain,(
    ! [A_661,B_662] :
      ( g1_pre_topc(u1_struct_0(A_661),k5_tmap_1(A_661,B_662)) = k6_tmap_1(A_661,B_662)
      | ~ m1_subset_1(B_662,k1_zfmisc_1(u1_struct_0(A_661)))
      | ~ l1_pre_topc(A_661)
      | ~ v2_pre_topc(A_661)
      | v2_struct_0(A_661) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_10878,plain,
    ( g1_pre_topc(u1_struct_0('#skF_4'),k5_tmap_1('#skF_4','#skF_5')) = k6_tmap_1('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_10876])).

tff(c_10886,plain,
    ( g1_pre_topc(u1_struct_0('#skF_4'),a_2_0_tmap_1('#skF_4','#skF_5')) = k6_tmap_1('#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_10749,c_10878])).

tff(c_10887,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),a_2_0_tmap_1('#skF_4','#skF_5')) = k6_tmap_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_10886])).

tff(c_10900,plain,(
    ! [A_1] :
      ( u1_struct_0(A_1) = u1_struct_0('#skF_4')
      | k6_tmap_1('#skF_4','#skF_5') != A_1
      | ~ m1_subset_1(a_2_0_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10887,c_4386])).

tff(c_10946,plain,(
    ! [A_668] :
      ( u1_struct_0(A_668) = u1_struct_0('#skF_4')
      | k6_tmap_1('#skF_4','#skF_5') != A_668
      | ~ v1_pre_topc(A_668)
      | ~ l1_pre_topc(A_668) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10773,c_10900])).

tff(c_10955,plain,
    ( u1_struct_0(k6_tmap_1('#skF_4','#skF_5')) = u1_struct_0('#skF_4')
    | ~ l1_pre_topc(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_10563,c_10946])).

tff(c_10962,plain,(
    u1_struct_0(k6_tmap_1('#skF_4','#skF_5')) = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10603,c_10955])).

tff(c_34,plain,(
    ! [A_39] :
      ( l1_struct_0(A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_4463,plain,(
    ! [A_355,B_356] :
      ( v1_funct_1(k7_tmap_1(A_355,B_356))
      | ~ m1_subset_1(B_356,k1_zfmisc_1(u1_struct_0(A_355)))
      | ~ l1_pre_topc(A_355)
      | ~ v2_pre_topc(A_355)
      | v2_struct_0(A_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_4466,plain,
    ( v1_funct_1(k7_tmap_1('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_4463])).

tff(c_4476,plain,
    ( v1_funct_1(k7_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_4466])).

tff(c_4477,plain,(
    v1_funct_1(k7_tmap_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4476])).

tff(c_4488,plain,(
    ! [A_358,B_359] :
      ( l1_pre_topc(k6_tmap_1(A_358,B_359))
      | ~ m1_subset_1(B_359,k1_zfmisc_1(u1_struct_0(A_358)))
      | ~ l1_pre_topc(A_358)
      | ~ v2_pre_topc(A_358)
      | v2_struct_0(A_358) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_4491,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_4488])).

tff(c_4501,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_4491])).

tff(c_4502,plain,(
    l1_pre_topc(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4501])).

tff(c_4527,plain,(
    ! [A_363,B_364] :
      ( v1_pre_topc(k6_tmap_1(A_363,B_364))
      | ~ m1_subset_1(B_364,k1_zfmisc_1(u1_struct_0(A_363)))
      | ~ l1_pre_topc(A_363)
      | ~ v2_pre_topc(A_363)
      | v2_struct_0(A_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_4530,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_4527])).

tff(c_4540,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_4530])).

tff(c_4541,plain,(
    v1_pre_topc(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4540])).

tff(c_4629,plain,(
    ! [A_377,B_378] :
      ( k5_tmap_1(A_377,B_378) = a_2_0_tmap_1(A_377,B_378)
      | ~ m1_subset_1(B_378,k1_zfmisc_1(u1_struct_0(A_377)))
      | ~ l1_pre_topc(A_377)
      | ~ v2_pre_topc(A_377)
      | v2_struct_0(A_377) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4632,plain,
    ( k5_tmap_1('#skF_4','#skF_5') = a_2_0_tmap_1('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_4629])).

tff(c_4642,plain,
    ( k5_tmap_1('#skF_4','#skF_5') = a_2_0_tmap_1('#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_4632])).

tff(c_4643,plain,(
    k5_tmap_1('#skF_4','#skF_5') = a_2_0_tmap_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4642])).

tff(c_4662,plain,(
    ! [A_380,B_381] :
      ( m1_subset_1(k5_tmap_1(A_380,B_381),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_380))))
      | ~ m1_subset_1(B_381,k1_zfmisc_1(u1_struct_0(A_380)))
      | ~ l1_pre_topc(A_380)
      | ~ v2_pre_topc(A_380)
      | v2_struct_0(A_380) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_4668,plain,
    ( m1_subset_1(a_2_0_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4643,c_4662])).

tff(c_4676,plain,
    ( m1_subset_1(a_2_0_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_4668])).

tff(c_4677,plain,(
    m1_subset_1(a_2_0_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4676])).

tff(c_4727,plain,(
    ! [A_385,B_386] :
      ( g1_pre_topc(u1_struct_0(A_385),k5_tmap_1(A_385,B_386)) = k6_tmap_1(A_385,B_386)
      | ~ m1_subset_1(B_386,k1_zfmisc_1(u1_struct_0(A_385)))
      | ~ l1_pre_topc(A_385)
      | ~ v2_pre_topc(A_385)
      | v2_struct_0(A_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_4729,plain,
    ( g1_pre_topc(u1_struct_0('#skF_4'),k5_tmap_1('#skF_4','#skF_5')) = k6_tmap_1('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_4727])).

tff(c_4737,plain,
    ( g1_pre_topc(u1_struct_0('#skF_4'),a_2_0_tmap_1('#skF_4','#skF_5')) = k6_tmap_1('#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_4643,c_4729])).

tff(c_4738,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),a_2_0_tmap_1('#skF_4','#skF_5')) = k6_tmap_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4737])).

tff(c_4745,plain,(
    ! [A_1] :
      ( u1_struct_0(A_1) = u1_struct_0('#skF_4')
      | k6_tmap_1('#skF_4','#skF_5') != A_1
      | ~ m1_subset_1(a_2_0_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4738,c_4386])).

tff(c_4793,plain,(
    ! [A_392] :
      ( u1_struct_0(A_392) = u1_struct_0('#skF_4')
      | k6_tmap_1('#skF_4','#skF_5') != A_392
      | ~ v1_pre_topc(A_392)
      | ~ l1_pre_topc(A_392) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4677,c_4745])).

tff(c_4802,plain,
    ( u1_struct_0(k6_tmap_1('#skF_4','#skF_5')) = u1_struct_0('#skF_4')
    | ~ l1_pre_topc(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_4541,c_4793])).

tff(c_4809,plain,(
    u1_struct_0(k6_tmap_1('#skF_4','#skF_5')) = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4502,c_4802])).

tff(c_4925,plain,(
    ! [A_393,B_394] :
      ( v1_funct_2(k7_tmap_1(A_393,B_394),u1_struct_0(A_393),u1_struct_0(k6_tmap_1(A_393,B_394)))
      | ~ m1_subset_1(B_394,k1_zfmisc_1(u1_struct_0(A_393)))
      | ~ l1_pre_topc(A_393)
      | ~ v2_pre_topc(A_393)
      | v2_struct_0(A_393) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_4931,plain,
    ( v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4809,c_4925])).

tff(c_4945,plain,
    ( v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_4931])).

tff(c_4946,plain,(
    v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4945])).

tff(c_5013,plain,(
    ! [A_397,B_398] :
      ( m1_subset_1(k7_tmap_1(A_397,B_398),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_397),u1_struct_0(k6_tmap_1(A_397,B_398)))))
      | ~ m1_subset_1(B_398,k1_zfmisc_1(u1_struct_0(A_397)))
      | ~ l1_pre_topc(A_397)
      | ~ v2_pre_topc(A_397)
      | v2_struct_0(A_397) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_5019,plain,
    ( m1_subset_1(k7_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4809,c_5013])).

tff(c_5033,plain,
    ( m1_subset_1(k7_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_5019])).

tff(c_5034,plain,(
    m1_subset_1(k7_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')))) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_5033])).

tff(c_5099,plain,(
    ! [A_402,B_403,C_404,D_405] :
      ( v1_funct_1(k2_tmap_1(A_402,B_403,C_404,D_405))
      | ~ l1_struct_0(D_405)
      | ~ m1_subset_1(C_404,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_402),u1_struct_0(B_403))))
      | ~ v1_funct_2(C_404,u1_struct_0(A_402),u1_struct_0(B_403))
      | ~ v1_funct_1(C_404)
      | ~ l1_struct_0(B_403)
      | ~ l1_struct_0(A_402) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_5101,plain,(
    ! [D_405] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),D_405))
      | ~ l1_struct_0(D_405)
      | ~ v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(k7_tmap_1('#skF_4','#skF_5'))
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5034,c_5099])).

tff(c_5117,plain,(
    ! [D_405] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),D_405))
      | ~ l1_struct_0(D_405)
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4477,c_4946,c_5101])).

tff(c_5177,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5117])).

tff(c_5180,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_5177])).

tff(c_5184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_5180])).

tff(c_5186,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_5117])).

tff(c_4341,plain,(
    ! [B_332,A_333] :
      ( l1_pre_topc(B_332)
      | ~ m1_pre_topc(B_332,A_333)
      | ~ l1_pre_topc(A_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_4347,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_4341])).

tff(c_4351,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_4347])).

tff(c_5187,plain,(
    ! [A_409,B_410,C_411,D_412] :
      ( v1_funct_2(k2_tmap_1(A_409,B_410,C_411,D_412),u1_struct_0(D_412),u1_struct_0(B_410))
      | ~ l1_struct_0(D_412)
      | ~ m1_subset_1(C_411,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_409),u1_struct_0(B_410))))
      | ~ v1_funct_2(C_411,u1_struct_0(A_409),u1_struct_0(B_410))
      | ~ v1_funct_1(C_411)
      | ~ l1_struct_0(B_410)
      | ~ l1_struct_0(A_409) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_5189,plain,(
    ! [D_412] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),D_412),u1_struct_0(D_412),u1_struct_0('#skF_4'))
      | ~ l1_struct_0(D_412)
      | ~ v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(k7_tmap_1('#skF_4','#skF_5'))
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5034,c_5187])).

tff(c_5205,plain,(
    ! [D_412] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),D_412),u1_struct_0(D_412),u1_struct_0('#skF_4'))
      | ~ l1_struct_0(D_412)
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4477,c_4946,c_5189])).

tff(c_5960,plain,(
    ! [D_454] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),D_454),u1_struct_0(D_454),u1_struct_0('#skF_4'))
      | ~ l1_struct_0(D_454) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5186,c_5205])).

tff(c_5969,plain,
    ( v1_funct_2(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),'#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_5960])).

tff(c_5970,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_5969])).

tff(c_5973,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_5970])).

tff(c_5977,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4351,c_5973])).

tff(c_5979,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_5969])).

tff(c_5422,plain,(
    ! [A_417,B_418,C_419,D_420] :
      ( m1_subset_1(k2_tmap_1(A_417,B_418,C_419,D_420),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_420),u1_struct_0(B_418))))
      | ~ l1_struct_0(D_420)
      | ~ m1_subset_1(C_419,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_417),u1_struct_0(B_418))))
      | ~ v1_funct_2(C_419,u1_struct_0(A_417),u1_struct_0(B_418))
      | ~ v1_funct_1(C_419)
      | ~ l1_struct_0(B_418)
      | ~ l1_struct_0(A_417) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_5441,plain,(
    ! [A_417,B_418,C_419] :
      ( m1_subset_1(k2_tmap_1(A_417,B_418,C_419,'#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',u1_struct_0(B_418))))
      | ~ l1_struct_0('#skF_6')
      | ~ m1_subset_1(C_419,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_417),u1_struct_0(B_418))))
      | ~ v1_funct_2(C_419,u1_struct_0(A_417),u1_struct_0(B_418))
      | ~ v1_funct_1(C_419)
      | ~ l1_struct_0(B_418)
      | ~ l1_struct_0(A_417) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_5422])).

tff(c_7277,plain,(
    ! [A_417,B_418,C_419] :
      ( m1_subset_1(k2_tmap_1(A_417,B_418,C_419,'#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',u1_struct_0(B_418))))
      | ~ m1_subset_1(C_419,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_417),u1_struct_0(B_418))))
      | ~ v1_funct_2(C_419,u1_struct_0(A_417),u1_struct_0(B_418))
      | ~ v1_funct_1(C_419)
      | ~ l1_struct_0(B_418)
      | ~ l1_struct_0(A_417) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5979,c_5441])).

tff(c_5868,plain,(
    ! [A_449,B_450,C_451,D_452] :
      ( k2_partfun1(u1_struct_0(A_449),u1_struct_0(B_450),C_451,u1_struct_0(D_452)) = k2_tmap_1(A_449,B_450,C_451,D_452)
      | ~ m1_pre_topc(D_452,A_449)
      | ~ m1_subset_1(C_451,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_449),u1_struct_0(B_450))))
      | ~ v1_funct_2(C_451,u1_struct_0(A_449),u1_struct_0(B_450))
      | ~ v1_funct_1(C_451)
      | ~ l1_pre_topc(B_450)
      | ~ v2_pre_topc(B_450)
      | v2_struct_0(B_450)
      | ~ l1_pre_topc(A_449)
      | ~ v2_pre_topc(A_449)
      | v2_struct_0(A_449) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_5878,plain,(
    ! [D_452] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),k7_tmap_1('#skF_4','#skF_5'),u1_struct_0(D_452)) = k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),D_452)
      | ~ m1_pre_topc(D_452,'#skF_4')
      | ~ v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(k7_tmap_1('#skF_4','#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5034,c_5868])).

tff(c_5905,plain,(
    ! [D_452] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),k7_tmap_1('#skF_4','#skF_5'),u1_struct_0(D_452)) = k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),D_452)
      | ~ m1_pre_topc(D_452,'#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_4477,c_4946,c_5878])).

tff(c_5922,plain,(
    ! [D_453] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),k7_tmap_1('#skF_4','#skF_5'),u1_struct_0(D_453)) = k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),D_453)
      | ~ m1_pre_topc(D_453,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_5905])).

tff(c_5937,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),k7_tmap_1('#skF_4','#skF_5'),'#skF_5') = k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),'#skF_6')
    | ~ m1_pre_topc('#skF_6','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_5922])).

tff(c_5941,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),k7_tmap_1('#skF_4','#skF_5'),'#skF_5') = k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_5937])).

tff(c_4424,plain,(
    ! [A_350,B_351] :
      ( ~ v2_struct_0(k6_tmap_1(A_350,B_351))
      | ~ m1_subset_1(B_351,k1_zfmisc_1(u1_struct_0(A_350)))
      | ~ l1_pre_topc(A_350)
      | ~ v2_pre_topc(A_350)
      | v2_struct_0(A_350) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_4427,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_4424])).

tff(c_4437,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_4427])).

tff(c_4438,plain,(
    ~ v2_struct_0(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4437])).

tff(c_4399,plain,(
    ! [A_347,B_348] :
      ( v2_pre_topc(k6_tmap_1(A_347,B_348))
      | ~ m1_subset_1(B_348,k1_zfmisc_1(u1_struct_0(A_347)))
      | ~ l1_pre_topc(A_347)
      | ~ v2_pre_topc(A_347)
      | v2_struct_0(A_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_4402,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_4399])).

tff(c_4412,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_4402])).

tff(c_4413,plain,(
    v2_pre_topc(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4412])).

tff(c_9989,plain,(
    ! [A_598,B_599,D_600] :
      ( k2_partfun1(u1_struct_0(A_598),u1_struct_0(k6_tmap_1(A_598,B_599)),k7_tmap_1(A_598,B_599),u1_struct_0(D_600)) = k2_tmap_1(A_598,k6_tmap_1(A_598,B_599),k7_tmap_1(A_598,B_599),D_600)
      | ~ m1_pre_topc(D_600,A_598)
      | ~ v1_funct_2(k7_tmap_1(A_598,B_599),u1_struct_0(A_598),u1_struct_0(k6_tmap_1(A_598,B_599)))
      | ~ v1_funct_1(k7_tmap_1(A_598,B_599))
      | ~ l1_pre_topc(k6_tmap_1(A_598,B_599))
      | ~ v2_pre_topc(k6_tmap_1(A_598,B_599))
      | v2_struct_0(k6_tmap_1(A_598,B_599))
      | ~ m1_subset_1(B_599,k1_zfmisc_1(u1_struct_0(A_598)))
      | ~ l1_pre_topc(A_598)
      | ~ v2_pre_topc(A_598)
      | v2_struct_0(A_598) ) ),
    inference(resolution,[status(thm)],[c_28,c_5868])).

tff(c_10067,plain,(
    ! [D_600] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),k7_tmap_1('#skF_4','#skF_5'),u1_struct_0(D_600)) = k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),D_600)
      | ~ m1_pre_topc(D_600,'#skF_4')
      | ~ v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_4','#skF_5')))
      | ~ v1_funct_1(k7_tmap_1('#skF_4','#skF_5'))
      | ~ l1_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
      | ~ v2_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
      | v2_struct_0(k6_tmap_1('#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4809,c_9989])).

tff(c_10143,plain,(
    ! [D_600] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),k7_tmap_1('#skF_4','#skF_5'),u1_struct_0(D_600)) = k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),D_600)
      | ~ m1_pre_topc(D_600,'#skF_4')
      | v2_struct_0(k6_tmap_1('#skF_4','#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_4413,c_4502,c_4477,c_4946,c_4809,c_10067])).

tff(c_10382,plain,(
    ! [D_609] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),k7_tmap_1('#skF_4','#skF_5'),u1_struct_0(D_609)) = k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),D_609)
      | ~ m1_pre_topc(D_609,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4438,c_10143])).

tff(c_10412,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),k7_tmap_1('#skF_4','#skF_5'),'#skF_5') = k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_6')
    | ~ m1_pre_topc('#skF_6','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_10382])).

tff(c_10418,plain,(
    k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_6') = k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_5941,c_10412])).

tff(c_84,plain,(
    ! [B_99,A_100] :
      ( l1_pre_topc(B_99)
      | ~ m1_pre_topc(B_99,A_100)
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_90,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_84])).

tff(c_94,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_90])).

tff(c_1122,plain,(
    ! [A_183,B_184,C_185,D_186] :
      ( m1_subset_1(k2_tmap_1(A_183,B_184,C_185,D_186),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_186),u1_struct_0(B_184))))
      | ~ l1_struct_0(D_186)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_183),u1_struct_0(B_184))))
      | ~ v1_funct_2(C_185,u1_struct_0(A_183),u1_struct_0(B_184))
      | ~ v1_funct_1(C_185)
      | ~ l1_struct_0(B_184)
      | ~ l1_struct_0(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1141,plain,(
    ! [A_183,B_184,C_185] :
      ( m1_subset_1(k2_tmap_1(A_183,B_184,C_185,'#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',u1_struct_0(B_184))))
      | ~ l1_struct_0('#skF_6')
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_183),u1_struct_0(B_184))))
      | ~ v1_funct_2(C_185,u1_struct_0(A_183),u1_struct_0(B_184))
      | ~ v1_funct_1(C_185)
      | ~ l1_struct_0(B_184)
      | ~ l1_struct_0(A_183) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_1122])).

tff(c_1152,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1141])).

tff(c_1155,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_1152])).

tff(c_1159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_1155])).

tff(c_1161,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1141])).

tff(c_224,plain,(
    ! [A_124,B_125] :
      ( v1_funct_1(k7_tmap_1(A_124,B_125))
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124)
      | ~ v2_pre_topc(A_124)
      | v2_struct_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_227,plain,
    ( v1_funct_1(k7_tmap_1('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_224])).

tff(c_237,plain,
    ( v1_funct_1(k7_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_227])).

tff(c_238,plain,(
    v1_funct_1(k7_tmap_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_237])).

tff(c_205,plain,(
    ! [A_122,B_123] :
      ( l1_pre_topc(k6_tmap_1(A_122,B_123))
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_208,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_205])).

tff(c_218,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_208])).

tff(c_219,plain,(
    l1_pre_topc(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_218])).

tff(c_269,plain,(
    ! [A_130,B_131] :
      ( v1_pre_topc(k6_tmap_1(A_130,B_131))
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130)
      | ~ v2_pre_topc(A_130)
      | v2_struct_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_272,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_269])).

tff(c_282,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_272])).

tff(c_283,plain,(
    v1_pre_topc(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_282])).

tff(c_362,plain,(
    ! [A_141,B_142] :
      ( k5_tmap_1(A_141,B_142) = a_2_0_tmap_1(A_141,B_142)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141)
      | v2_struct_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_365,plain,
    ( k5_tmap_1('#skF_4','#skF_5') = a_2_0_tmap_1('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_362])).

tff(c_375,plain,
    ( k5_tmap_1('#skF_4','#skF_5') = a_2_0_tmap_1('#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_365])).

tff(c_376,plain,(
    k5_tmap_1('#skF_4','#skF_5') = a_2_0_tmap_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_375])).

tff(c_395,plain,(
    ! [A_144,B_145] :
      ( m1_subset_1(k5_tmap_1(A_144,B_145),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_144))))
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144)
      | v2_struct_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_401,plain,
    ( m1_subset_1(a_2_0_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_395])).

tff(c_409,plain,
    ( m1_subset_1(a_2_0_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_401])).

tff(c_410,plain,(
    m1_subset_1(a_2_0_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_409])).

tff(c_442,plain,(
    ! [A_151,B_152] :
      ( g1_pre_topc(u1_struct_0(A_151),k5_tmap_1(A_151,B_152)) = k6_tmap_1(A_151,B_152)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151)
      | ~ v2_pre_topc(A_151)
      | v2_struct_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_444,plain,
    ( g1_pre_topc(u1_struct_0('#skF_4'),k5_tmap_1('#skF_4','#skF_5')) = k6_tmap_1('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_442])).

tff(c_452,plain,
    ( g1_pre_topc(u1_struct_0('#skF_4'),a_2_0_tmap_1('#skF_4','#skF_5')) = k6_tmap_1('#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_376,c_444])).

tff(c_453,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),a_2_0_tmap_1('#skF_4','#skF_5')) = k6_tmap_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_452])).

tff(c_127,plain,(
    ! [C_106,A_107,D_108,B_109] :
      ( C_106 = A_107
      | g1_pre_topc(C_106,D_108) != g1_pre_topc(A_107,B_109)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k1_zfmisc_1(A_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_129,plain,(
    ! [A_1,A_107,B_109] :
      ( u1_struct_0(A_1) = A_107
      | g1_pre_topc(A_107,B_109) != A_1
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k1_zfmisc_1(A_107)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_127])).

tff(c_460,plain,(
    ! [A_1] :
      ( u1_struct_0(A_1) = u1_struct_0('#skF_4')
      | k6_tmap_1('#skF_4','#skF_5') != A_1
      | ~ m1_subset_1(a_2_0_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_453,c_129])).

tff(c_508,plain,(
    ! [A_158] :
      ( u1_struct_0(A_158) = u1_struct_0('#skF_4')
      | k6_tmap_1('#skF_4','#skF_5') != A_158
      | ~ v1_pre_topc(A_158)
      | ~ l1_pre_topc(A_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_460])).

tff(c_517,plain,
    ( u1_struct_0(k6_tmap_1('#skF_4','#skF_5')) = u1_struct_0('#skF_4')
    | ~ l1_pre_topc(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_283,c_508])).

tff(c_524,plain,(
    u1_struct_0(k6_tmap_1('#skF_4','#skF_5')) = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_517])).

tff(c_633,plain,(
    ! [A_159,B_160] :
      ( v1_funct_2(k7_tmap_1(A_159,B_160),u1_struct_0(A_159),u1_struct_0(k6_tmap_1(A_159,B_160)))
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ l1_pre_topc(A_159)
      | ~ v2_pre_topc(A_159)
      | v2_struct_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_639,plain,
    ( v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_633])).

tff(c_653,plain,
    ( v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_639])).

tff(c_654,plain,(
    v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_653])).

tff(c_726,plain,(
    ! [A_162,B_163] :
      ( m1_subset_1(k7_tmap_1(A_162,B_163),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_162),u1_struct_0(k6_tmap_1(A_162,B_163)))))
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ l1_pre_topc(A_162)
      | ~ v2_pre_topc(A_162)
      | v2_struct_0(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_735,plain,
    ( m1_subset_1(k7_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_726])).

tff(c_752,plain,
    ( m1_subset_1(k7_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_735])).

tff(c_753,plain,(
    m1_subset_1(k7_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')))) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_752])).

tff(c_805,plain,(
    ! [A_168,B_169,C_170,D_171] :
      ( v1_funct_1(k2_tmap_1(A_168,B_169,C_170,D_171))
      | ~ l1_struct_0(D_171)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_168),u1_struct_0(B_169))))
      | ~ v1_funct_2(C_170,u1_struct_0(A_168),u1_struct_0(B_169))
      | ~ v1_funct_1(C_170)
      | ~ l1_struct_0(B_169)
      | ~ l1_struct_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_807,plain,(
    ! [D_171] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),D_171))
      | ~ l1_struct_0(D_171)
      | ~ v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(k7_tmap_1('#skF_4','#skF_5'))
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_753,c_805])).

tff(c_823,plain,(
    ! [D_171] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),D_171))
      | ~ l1_struct_0(D_171)
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_654,c_807])).

tff(c_883,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_823])).

tff(c_886,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_883])).

tff(c_890,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_886])).

tff(c_892,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_823])).

tff(c_893,plain,(
    ! [A_175,B_176,C_177,D_178] :
      ( v1_funct_2(k2_tmap_1(A_175,B_176,C_177,D_178),u1_struct_0(D_178),u1_struct_0(B_176))
      | ~ l1_struct_0(D_178)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_175),u1_struct_0(B_176))))
      | ~ v1_funct_2(C_177,u1_struct_0(A_175),u1_struct_0(B_176))
      | ~ v1_funct_1(C_177)
      | ~ l1_struct_0(B_176)
      | ~ l1_struct_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_895,plain,(
    ! [D_178] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),D_178),u1_struct_0(D_178),u1_struct_0('#skF_4'))
      | ~ l1_struct_0(D_178)
      | ~ v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(k7_tmap_1('#skF_4','#skF_5'))
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_753,c_893])).

tff(c_911,plain,(
    ! [D_178] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),D_178),u1_struct_0(D_178),u1_struct_0('#skF_4'))
      | ~ l1_struct_0(D_178)
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_654,c_895])).

tff(c_1640,plain,(
    ! [D_220] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),D_220),u1_struct_0(D_220),u1_struct_0('#skF_4'))
      | ~ l1_struct_0(D_220) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_892,c_911])).

tff(c_1646,plain,
    ( v1_funct_2(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),k6_tmap_1('#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))
    | ~ l1_struct_0(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_1640])).

tff(c_2884,plain,(
    ~ l1_struct_0(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1646])).

tff(c_2915,plain,(
    ~ l1_pre_topc(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_34,c_2884])).

tff(c_2919,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_2915])).

tff(c_2921,plain,(
    l1_struct_0(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1646])).

tff(c_4232,plain,(
    ! [A_327,B_328,D_329] :
      ( v1_funct_1(k2_tmap_1(A_327,k6_tmap_1(A_327,B_328),k7_tmap_1(A_327,B_328),D_329))
      | ~ l1_struct_0(D_329)
      | ~ v1_funct_2(k7_tmap_1(A_327,B_328),u1_struct_0(A_327),u1_struct_0(k6_tmap_1(A_327,B_328)))
      | ~ v1_funct_1(k7_tmap_1(A_327,B_328))
      | ~ l1_struct_0(k6_tmap_1(A_327,B_328))
      | ~ l1_struct_0(A_327)
      | ~ m1_subset_1(B_328,k1_zfmisc_1(u1_struct_0(A_327)))
      | ~ l1_pre_topc(A_327)
      | ~ v2_pre_topc(A_327)
      | v2_struct_0(A_327) ) ),
    inference(resolution,[status(thm)],[c_28,c_805])).

tff(c_4266,plain,(
    ! [D_329] :
      ( v1_funct_1(k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),D_329))
      | ~ l1_struct_0(D_329)
      | ~ v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(k7_tmap_1('#skF_4','#skF_5'))
      | ~ l1_struct_0(k6_tmap_1('#skF_4','#skF_5'))
      | ~ l1_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_4232])).

tff(c_4320,plain,(
    ! [D_329] :
      ( v1_funct_1(k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),D_329))
      | ~ l1_struct_0(D_329)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_892,c_2921,c_238,c_654,c_4266])).

tff(c_4330,plain,(
    ! [D_330] :
      ( v1_funct_1(k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),D_330))
      | ~ l1_struct_0(D_330) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4320])).

tff(c_60,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0(k6_tmap_1('#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),'#skF_6',k6_tmap_1('#skF_4','#skF_5'))
    | ~ v1_funct_2(k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),u1_struct_0('#skF_6'),u1_struct_0(k6_tmap_1('#skF_4','#skF_5')))
    | ~ v1_funct_1(k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_284])).

tff(c_75,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',u1_struct_0(k6_tmap_1('#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),'#skF_6',k6_tmap_1('#skF_4','#skF_5'))
    | ~ v1_funct_2(k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),'#skF_5',u1_struct_0(k6_tmap_1('#skF_4','#skF_5')))
    | ~ v1_funct_1(k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_62,c_60])).

tff(c_82,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_4333,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4330,c_82])).

tff(c_4337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1161,c_4333])).

tff(c_4338,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),'#skF_5',u1_struct_0(k6_tmap_1('#skF_4','#skF_5')))
    | ~ v5_pre_topc(k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),'#skF_6',k6_tmap_1('#skF_4','#skF_5'))
    | ~ m1_subset_1(k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',u1_struct_0(k6_tmap_1('#skF_4','#skF_5'))))) ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_4389,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',u1_struct_0(k6_tmap_1('#skF_4','#skF_5'))))) ),
    inference(splitLeft,[status(thm)],[c_4338])).

tff(c_4810,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4809,c_4389])).

tff(c_10420,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10418,c_4810])).

tff(c_10476,plain,
    ( ~ m1_subset_1(k7_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(k7_tmap_1('#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_7277,c_10420])).

tff(c_10480,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5186,c_4477,c_4946,c_5034,c_10476])).

tff(c_10481,plain,
    ( ~ v5_pre_topc(k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),'#skF_6',k6_tmap_1('#skF_4','#skF_5'))
    | ~ v1_funct_2(k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),'#skF_5',u1_struct_0(k6_tmap_1('#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_4338])).

tff(c_10574,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),'#skF_5',u1_struct_0(k6_tmap_1('#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_10481])).

tff(c_10963,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),'#skF_5',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10962,c_10574])).

tff(c_11610,plain,(
    ! [A_693,B_694,C_695,D_696] :
      ( m1_subset_1(k2_tmap_1(A_693,B_694,C_695,D_696),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_696),u1_struct_0(B_694))))
      | ~ l1_struct_0(D_696)
      | ~ m1_subset_1(C_695,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_693),u1_struct_0(B_694))))
      | ~ v1_funct_2(C_695,u1_struct_0(A_693),u1_struct_0(B_694))
      | ~ v1_funct_1(C_695)
      | ~ l1_struct_0(B_694)
      | ~ l1_struct_0(A_693) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_11629,plain,(
    ! [A_693,B_694,C_695] :
      ( m1_subset_1(k2_tmap_1(A_693,B_694,C_695,'#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',u1_struct_0(B_694))))
      | ~ l1_struct_0('#skF_6')
      | ~ m1_subset_1(C_695,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_693),u1_struct_0(B_694))))
      | ~ v1_funct_2(C_695,u1_struct_0(A_693),u1_struct_0(B_694))
      | ~ v1_funct_1(C_695)
      | ~ l1_struct_0(B_694)
      | ~ l1_struct_0(A_693) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_11610])).

tff(c_11640,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_11629])).

tff(c_11643,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_11640])).

tff(c_11647,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4351,c_11643])).

tff(c_11649,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_11629])).

tff(c_11093,plain,(
    ! [A_669,B_670] :
      ( v1_funct_2(k7_tmap_1(A_669,B_670),u1_struct_0(A_669),u1_struct_0(k6_tmap_1(A_669,B_670)))
      | ~ m1_subset_1(B_670,k1_zfmisc_1(u1_struct_0(A_669)))
      | ~ l1_pre_topc(A_669)
      | ~ v2_pre_topc(A_669)
      | v2_struct_0(A_669) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_11099,plain,
    ( v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10962,c_11093])).

tff(c_11113,plain,
    ( v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_11099])).

tff(c_11114,plain,(
    v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_11113])).

tff(c_11185,plain,(
    ! [A_673,B_674] :
      ( m1_subset_1(k7_tmap_1(A_673,B_674),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_673),u1_struct_0(k6_tmap_1(A_673,B_674)))))
      | ~ m1_subset_1(B_674,k1_zfmisc_1(u1_struct_0(A_673)))
      | ~ l1_pre_topc(A_673)
      | ~ v2_pre_topc(A_673)
      | v2_struct_0(A_673) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_11191,plain,
    ( m1_subset_1(k7_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10962,c_11185])).

tff(c_11205,plain,
    ( m1_subset_1(k7_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_11191])).

tff(c_11206,plain,(
    m1_subset_1(k7_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')))) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_11205])).

tff(c_11271,plain,(
    ! [A_678,B_679,C_680,D_681] :
      ( v1_funct_1(k2_tmap_1(A_678,B_679,C_680,D_681))
      | ~ l1_struct_0(D_681)
      | ~ m1_subset_1(C_680,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_678),u1_struct_0(B_679))))
      | ~ v1_funct_2(C_680,u1_struct_0(A_678),u1_struct_0(B_679))
      | ~ v1_funct_1(C_680)
      | ~ l1_struct_0(B_679)
      | ~ l1_struct_0(A_678) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_11273,plain,(
    ! [D_681] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),D_681))
      | ~ l1_struct_0(D_681)
      | ~ v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(k7_tmap_1('#skF_4','#skF_5'))
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_11206,c_11271])).

tff(c_11289,plain,(
    ! [D_681] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),D_681))
      | ~ l1_struct_0(D_681)
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10538,c_11114,c_11273])).

tff(c_11340,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_11289])).

tff(c_11343,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_11340])).

tff(c_11347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_11343])).

tff(c_11349,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_11289])).

tff(c_11350,plain,(
    ! [A_684,B_685,C_686,D_687] :
      ( v1_funct_2(k2_tmap_1(A_684,B_685,C_686,D_687),u1_struct_0(D_687),u1_struct_0(B_685))
      | ~ l1_struct_0(D_687)
      | ~ m1_subset_1(C_686,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_684),u1_struct_0(B_685))))
      | ~ v1_funct_2(C_686,u1_struct_0(A_684),u1_struct_0(B_685))
      | ~ v1_funct_1(C_686)
      | ~ l1_struct_0(B_685)
      | ~ l1_struct_0(A_684) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_11352,plain,(
    ! [D_687] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),D_687),u1_struct_0(D_687),u1_struct_0('#skF_4'))
      | ~ l1_struct_0(D_687)
      | ~ v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(k7_tmap_1('#skF_4','#skF_5'))
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_11206,c_11350])).

tff(c_11981,plain,(
    ! [D_717] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),D_717),u1_struct_0(D_717),u1_struct_0('#skF_4'))
      | ~ l1_struct_0(D_717) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11349,c_10538,c_11114,c_11352])).

tff(c_11987,plain,
    ( v1_funct_2(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),k6_tmap_1('#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))
    | ~ l1_struct_0(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10962,c_11981])).

tff(c_13319,plain,(
    ~ l1_struct_0(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_11987])).

tff(c_13322,plain,(
    ~ l1_pre_topc(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_34,c_13319])).

tff(c_13326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10603,c_13322])).

tff(c_13328,plain,(
    l1_struct_0(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_11987])).

tff(c_14614,plain,(
    ! [A_823,B_824,D_825] :
      ( v1_funct_2(k2_tmap_1(A_823,k6_tmap_1(A_823,B_824),k7_tmap_1(A_823,B_824),D_825),u1_struct_0(D_825),u1_struct_0(k6_tmap_1(A_823,B_824)))
      | ~ l1_struct_0(D_825)
      | ~ v1_funct_2(k7_tmap_1(A_823,B_824),u1_struct_0(A_823),u1_struct_0(k6_tmap_1(A_823,B_824)))
      | ~ v1_funct_1(k7_tmap_1(A_823,B_824))
      | ~ l1_struct_0(k6_tmap_1(A_823,B_824))
      | ~ l1_struct_0(A_823)
      | ~ m1_subset_1(B_824,k1_zfmisc_1(u1_struct_0(A_823)))
      | ~ l1_pre_topc(A_823)
      | ~ v2_pre_topc(A_823)
      | v2_struct_0(A_823) ) ),
    inference(resolution,[status(thm)],[c_28,c_11350])).

tff(c_14662,plain,(
    ! [D_825] :
      ( v1_funct_2(k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),D_825),u1_struct_0(D_825),u1_struct_0('#skF_4'))
      | ~ l1_struct_0(D_825)
      | ~ v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_4','#skF_5')))
      | ~ v1_funct_1(k7_tmap_1('#skF_4','#skF_5'))
      | ~ l1_struct_0(k6_tmap_1('#skF_4','#skF_5'))
      | ~ l1_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10962,c_14614])).

tff(c_14710,plain,(
    ! [D_825] :
      ( v1_funct_2(k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),D_825),u1_struct_0(D_825),u1_struct_0('#skF_4'))
      | ~ l1_struct_0(D_825)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_11349,c_13328,c_10538,c_11114,c_10962,c_14662])).

tff(c_14741,plain,(
    ! [D_827] :
      ( v1_funct_2(k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),D_827),u1_struct_0(D_827),u1_struct_0('#skF_4'))
      | ~ l1_struct_0(D_827) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_14710])).

tff(c_14756,plain,
    ( v1_funct_2(k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),'#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_14741])).

tff(c_14762,plain,(
    v1_funct_2(k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),'#skF_5',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11649,c_14756])).

tff(c_14764,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10963,c_14762])).

tff(c_14765,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),'#skF_6',k6_tmap_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_10481])).

tff(c_20939,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),'#skF_6',k6_tmap_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20931,c_14765])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_284])).

tff(c_4353,plain,(
    ! [B_335,A_336] :
      ( v2_pre_topc(B_335)
      | ~ m1_pre_topc(B_335,A_336)
      | ~ l1_pre_topc(A_336)
      | ~ v2_pre_topc(A_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4359,plain,
    ( v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_4353])).

tff(c_4363,plain,(
    v2_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_4359])).

tff(c_4339,plain,(
    v1_funct_1(k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_6')) ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_20940,plain,(
    v1_funct_1(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20931,c_4339])).

tff(c_15772,plain,(
    ! [A_895,B_896,C_897,D_898] :
      ( m1_subset_1(k2_tmap_1(A_895,B_896,C_897,D_898),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_898),u1_struct_0(B_896))))
      | ~ l1_struct_0(D_898)
      | ~ m1_subset_1(C_897,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_895),u1_struct_0(B_896))))
      | ~ v1_funct_2(C_897,u1_struct_0(A_895),u1_struct_0(B_896))
      | ~ v1_funct_1(C_897)
      | ~ l1_struct_0(B_896)
      | ~ l1_struct_0(A_895) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_15791,plain,(
    ! [A_895,B_896,C_897] :
      ( m1_subset_1(k2_tmap_1(A_895,B_896,C_897,'#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',u1_struct_0(B_896))))
      | ~ l1_struct_0('#skF_6')
      | ~ m1_subset_1(C_897,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_895),u1_struct_0(B_896))))
      | ~ v1_funct_2(C_897,u1_struct_0(A_895),u1_struct_0(B_896))
      | ~ v1_funct_1(C_897)
      | ~ l1_struct_0(B_896)
      | ~ l1_struct_0(A_895) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_15772])).

tff(c_15802,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_15791])).

tff(c_15805,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_15802])).

tff(c_15809,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4351,c_15805])).

tff(c_15811,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_15791])).

tff(c_15433,plain,(
    ! [A_880,B_881,C_882,D_883] :
      ( v1_funct_1(k2_tmap_1(A_880,B_881,C_882,D_883))
      | ~ l1_struct_0(D_883)
      | ~ m1_subset_1(C_882,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_880),u1_struct_0(B_881))))
      | ~ v1_funct_2(C_882,u1_struct_0(A_880),u1_struct_0(B_881))
      | ~ v1_funct_1(C_882)
      | ~ l1_struct_0(B_881)
      | ~ l1_struct_0(A_880) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_15435,plain,(
    ! [D_883] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),D_883))
      | ~ l1_struct_0(D_883)
      | ~ v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(k7_tmap_1('#skF_4','#skF_5'))
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_15376,c_15433])).

tff(c_15451,plain,(
    ! [D_883] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),D_883))
      | ~ l1_struct_0(D_883)
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10538,c_15278,c_15435])).

tff(c_15515,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_15451])).

tff(c_15518,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_15515])).

tff(c_15522,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_15518])).

tff(c_15524,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_15451])).

tff(c_15525,plain,(
    ! [A_887,B_888,C_889,D_890] :
      ( v1_funct_2(k2_tmap_1(A_887,B_888,C_889,D_890),u1_struct_0(D_890),u1_struct_0(B_888))
      | ~ l1_struct_0(D_890)
      | ~ m1_subset_1(C_889,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_887),u1_struct_0(B_888))))
      | ~ v1_funct_2(C_889,u1_struct_0(A_887),u1_struct_0(B_888))
      | ~ v1_funct_1(C_889)
      | ~ l1_struct_0(B_888)
      | ~ l1_struct_0(A_887) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_15527,plain,(
    ! [D_890] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),D_890),u1_struct_0(D_890),u1_struct_0('#skF_4'))
      | ~ l1_struct_0(D_890)
      | ~ v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(k7_tmap_1('#skF_4','#skF_5'))
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_15376,c_15525])).

tff(c_15543,plain,(
    ! [D_890] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),D_890),u1_struct_0(D_890),u1_struct_0('#skF_4'))
      | ~ l1_struct_0(D_890)
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10538,c_15278,c_15527])).

tff(c_16431,plain,(
    ! [D_935] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),D_935),u1_struct_0(D_935),u1_struct_0('#skF_4'))
      | ~ l1_struct_0(D_935) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15524,c_15543])).

tff(c_16440,plain,
    ( v1_funct_2(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),'#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_16431])).

tff(c_16442,plain,(
    v1_funct_2(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),'#skF_5',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15811,c_16440])).

tff(c_10482,plain,(
    m1_subset_1(k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',u1_struct_0(k6_tmap_1('#skF_4','#skF_5'))))) ),
    inference(splitRight,[status(thm)],[c_4338])).

tff(c_15128,plain,(
    m1_subset_1(k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15126,c_10482])).

tff(c_20937,plain,(
    m1_subset_1(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20931,c_15128])).

tff(c_15813,plain,(
    ! [C_899,A_900,D_901] :
      ( r1_tmap_1(C_899,k6_tmap_1(A_900,u1_struct_0(C_899)),k2_tmap_1(A_900,k6_tmap_1(A_900,u1_struct_0(C_899)),k7_tmap_1(A_900,u1_struct_0(C_899)),C_899),D_901)
      | ~ m1_subset_1(D_901,u1_struct_0(C_899))
      | ~ m1_pre_topc(C_899,A_900)
      | v2_struct_0(C_899)
      | ~ m1_subset_1(u1_struct_0(C_899),k1_zfmisc_1(u1_struct_0(A_900)))
      | ~ l1_pre_topc(A_900)
      | ~ v2_pre_topc(A_900)
      | v2_struct_0(A_900) ) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_15837,plain,(
    ! [A_900,D_901] :
      ( r1_tmap_1('#skF_6',k6_tmap_1(A_900,u1_struct_0('#skF_6')),k2_tmap_1(A_900,k6_tmap_1(A_900,'#skF_5'),k7_tmap_1(A_900,u1_struct_0('#skF_6')),'#skF_6'),D_901)
      | ~ m1_subset_1(D_901,u1_struct_0('#skF_6'))
      | ~ m1_pre_topc('#skF_6',A_900)
      | v2_struct_0('#skF_6')
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0(A_900)))
      | ~ l1_pre_topc(A_900)
      | ~ v2_pre_topc(A_900)
      | v2_struct_0(A_900) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_15813])).

tff(c_15855,plain,(
    ! [A_900,D_901] :
      ( r1_tmap_1('#skF_6',k6_tmap_1(A_900,'#skF_5'),k2_tmap_1(A_900,k6_tmap_1(A_900,'#skF_5'),k7_tmap_1(A_900,'#skF_5'),'#skF_6'),D_901)
      | ~ m1_subset_1(D_901,'#skF_5')
      | ~ m1_pre_topc('#skF_6',A_900)
      | v2_struct_0('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_900)))
      | ~ l1_pre_topc(A_900)
      | ~ v2_pre_topc(A_900)
      | v2_struct_0(A_900) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_62,c_62,c_62,c_15837])).

tff(c_15856,plain,(
    ! [A_900,D_901] :
      ( r1_tmap_1('#skF_6',k6_tmap_1(A_900,'#skF_5'),k2_tmap_1(A_900,k6_tmap_1(A_900,'#skF_5'),k7_tmap_1(A_900,'#skF_5'),'#skF_6'),D_901)
      | ~ m1_subset_1(D_901,'#skF_5')
      | ~ m1_pre_topc('#skF_6',A_900)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_900)))
      | ~ l1_pre_topc(A_900)
      | ~ v2_pre_topc(A_900)
      | v2_struct_0(A_900) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_15855])).

tff(c_20964,plain,(
    ! [D_901] :
      ( r1_tmap_1('#skF_6',k6_tmap_1('#skF_4','#skF_5'),k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),D_901)
      | ~ m1_subset_1(D_901,'#skF_5')
      | ~ m1_pre_topc('#skF_6','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20931,c_15856])).

tff(c_20987,plain,(
    ! [D_901] :
      ( r1_tmap_1('#skF_6',k6_tmap_1('#skF_4','#skF_5'),k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),D_901)
      | ~ m1_subset_1(D_901,'#skF_5')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_64,c_20964])).

tff(c_21178,plain,(
    ! [D_1096] :
      ( r1_tmap_1('#skF_6',k6_tmap_1('#skF_4','#skF_5'),k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),D_1096)
      | ~ m1_subset_1(D_1096,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_20987])).

tff(c_56,plain,(
    ! [B_82,A_70,C_88] :
      ( ~ r1_tmap_1(B_82,A_70,C_88,'#skF_3'(A_70,B_82,C_88))
      | v5_pre_topc(C_88,B_82,A_70)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_82),u1_struct_0(A_70))))
      | ~ v1_funct_2(C_88,u1_struct_0(B_82),u1_struct_0(A_70))
      | ~ v1_funct_1(C_88)
      | ~ l1_pre_topc(B_82)
      | ~ v2_pre_topc(B_82)
      | v2_struct_0(B_82)
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_21181,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),'#skF_6',k6_tmap_1('#skF_4','#skF_5'))
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0(k6_tmap_1('#skF_4','#skF_5')))))
    | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),u1_struct_0('#skF_6'),u1_struct_0(k6_tmap_1('#skF_4','#skF_5')))
    | ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),'#skF_6'))
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | ~ v2_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0(k6_tmap_1('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_3'(k6_tmap_1('#skF_4','#skF_5'),'#skF_6',k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),'#skF_6')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_21178,c_56])).

tff(c_21184,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),'#skF_6',k6_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0('#skF_6')
    | v2_struct_0(k6_tmap_1('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_3'(k6_tmap_1('#skF_4','#skF_5'),'#skF_6',k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),'#skF_6')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10506,c_14795,c_4363,c_4351,c_20940,c_16442,c_62,c_15126,c_20937,c_62,c_15126,c_21181])).

tff(c_21185,plain,(
    ~ m1_subset_1('#skF_3'(k6_tmap_1('#skF_4','#skF_5'),'#skF_6',k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),'#skF_6')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_14814,c_66,c_20939,c_21184])).

tff(c_16437,plain,
    ( v1_funct_2(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),k6_tmap_1('#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))
    | ~ l1_struct_0(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15126,c_16431])).

tff(c_17545,plain,(
    ~ l1_struct_0(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_16437])).

tff(c_17548,plain,(
    ~ l1_pre_topc(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_34,c_17545])).

tff(c_17552,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14795,c_17548])).

tff(c_17554,plain,(
    l1_struct_0(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_16437])).

tff(c_14,plain,(
    ! [A_29,B_30,C_31,D_32] :
      ( m1_subset_1(k2_tmap_1(A_29,B_30,C_31,D_32),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_32),u1_struct_0(B_30))))
      | ~ l1_struct_0(D_32)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_29),u1_struct_0(B_30))))
      | ~ v1_funct_2(C_31,u1_struct_0(A_29),u1_struct_0(B_30))
      | ~ v1_funct_1(C_31)
      | ~ l1_struct_0(B_30)
      | ~ l1_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_15914,plain,(
    ! [A_908,B_909,C_910] :
      ( m1_subset_1('#skF_3'(A_908,B_909,C_910),u1_struct_0(B_909))
      | v5_pre_topc(C_910,B_909,A_908)
      | ~ m1_subset_1(C_910,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_909),u1_struct_0(A_908))))
      | ~ v1_funct_2(C_910,u1_struct_0(B_909),u1_struct_0(A_908))
      | ~ v1_funct_1(C_910)
      | ~ l1_pre_topc(B_909)
      | ~ v2_pre_topc(B_909)
      | v2_struct_0(B_909)
      | ~ l1_pre_topc(A_908)
      | ~ v2_pre_topc(A_908)
      | v2_struct_0(A_908) ) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_15936,plain,(
    ! [B_30,D_32,A_29,C_31] :
      ( m1_subset_1('#skF_3'(B_30,D_32,k2_tmap_1(A_29,B_30,C_31,D_32)),u1_struct_0(D_32))
      | v5_pre_topc(k2_tmap_1(A_29,B_30,C_31,D_32),D_32,B_30)
      | ~ v1_funct_2(k2_tmap_1(A_29,B_30,C_31,D_32),u1_struct_0(D_32),u1_struct_0(B_30))
      | ~ v1_funct_1(k2_tmap_1(A_29,B_30,C_31,D_32))
      | ~ l1_pre_topc(D_32)
      | ~ v2_pre_topc(D_32)
      | v2_struct_0(D_32)
      | ~ l1_pre_topc(B_30)
      | ~ v2_pre_topc(B_30)
      | v2_struct_0(B_30)
      | ~ l1_struct_0(D_32)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_29),u1_struct_0(B_30))))
      | ~ v1_funct_2(C_31,u1_struct_0(A_29),u1_struct_0(B_30))
      | ~ v1_funct_1(C_31)
      | ~ l1_struct_0(B_30)
      | ~ l1_struct_0(A_29) ) ),
    inference(resolution,[status(thm)],[c_14,c_15914])).

tff(c_20944,plain,
    ( m1_subset_1('#skF_3'(k6_tmap_1('#skF_4','#skF_5'),'#skF_6',k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_6')),u1_struct_0('#skF_6'))
    | v5_pre_topc(k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),'#skF_6',k6_tmap_1('#skF_4','#skF_5'))
    | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),u1_struct_0('#skF_6'),u1_struct_0(k6_tmap_1('#skF_4','#skF_5')))
    | ~ v1_funct_1(k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_6'))
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | ~ v2_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0(k6_tmap_1('#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_6')
    | ~ m1_subset_1(k7_tmap_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_4','#skF_5')))))
    | ~ v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_4','#skF_5')))
    | ~ v1_funct_1(k7_tmap_1('#skF_4','#skF_5'))
    | ~ l1_struct_0(k6_tmap_1('#skF_4','#skF_5'))
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_20931,c_15936])).

tff(c_20971,plain,
    ( m1_subset_1('#skF_3'(k6_tmap_1('#skF_4','#skF_5'),'#skF_6',k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),'#skF_6')),'#skF_5')
    | v5_pre_topc(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),'#skF_6',k6_tmap_1('#skF_4','#skF_5'))
    | ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),'#skF_6'))
    | v2_struct_0('#skF_6')
    | v2_struct_0(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15524,c_17554,c_10538,c_15278,c_15126,c_15376,c_15126,c_15811,c_10506,c_14795,c_4363,c_4351,c_20931,c_16442,c_62,c_15126,c_20931,c_20931,c_62,c_20944])).

tff(c_20972,plain,
    ( m1_subset_1('#skF_3'(k6_tmap_1('#skF_4','#skF_5'),'#skF_6',k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),'#skF_6')),'#skF_5')
    | v5_pre_topc(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),'#skF_6',k6_tmap_1('#skF_4','#skF_5'))
    | ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_14814,c_66,c_20971])).

tff(c_21865,plain,
    ( m1_subset_1('#skF_3'(k6_tmap_1('#skF_4','#skF_5'),'#skF_6',k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),'#skF_6')),'#skF_5')
    | v5_pre_topc(k2_tmap_1('#skF_4','#skF_4',k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),'#skF_6',k6_tmap_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20940,c_20972])).

tff(c_21866,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20939,c_21185,c_21865])).

%------------------------------------------------------------------------------
