%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:52 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 841 expanded)
%              Number of leaves         :   49 ( 294 expanded)
%              Depth                    :   18
%              Number of atoms          :  321 (3125 expanded)
%              Number of equality atoms :   35 ( 332 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(r1_funct_2,type,(
    r1_funct_2: ( $i * $i * $i * $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_207,negated_conjecture,(
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
                  & m1_pre_topc(C,B) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(B),u1_struct_0(A))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
                   => ( g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                     => r1_funct_2(u1_struct_0(B),u1_struct_0(A),u1_struct_0(C),u1_struct_0(A),D,k2_tmap_1(B,A,D,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_tmap_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_98,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_136,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(B)
        & ~ v1_xboole_0(D)
        & v1_funct_1(E)
        & v1_funct_2(E,A,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,C,D)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( r1_funct_2(A,B,C,D,E,F)
      <=> E = F ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

tff(f_174,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_170,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

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
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(c_72,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_30,plain,(
    ! [A_23] :
      ( l1_struct_0(A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_107,plain,(
    ! [C_80,A_81,B_82] :
      ( v1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_115,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_107])).

tff(c_161,plain,(
    ! [C_98,A_99,B_100] :
      ( v4_relat_1(C_98,A_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_169,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_161])).

tff(c_199,plain,(
    ! [B_110,A_111] :
      ( k1_relat_1(B_110) = A_111
      | ~ v1_partfun1(B_110,A_111)
      | ~ v4_relat_1(B_110,A_111)
      | ~ v1_relat_1(B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_205,plain,
    ( u1_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_169,c_199])).

tff(c_211,plain,
    ( u1_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_205])).

tff(c_213,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_58,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_345,plain,(
    ! [C_133,A_134,B_135] :
      ( v1_partfun1(C_133,A_134)
      | ~ v1_funct_2(C_133,A_134,B_135)
      | ~ v1_funct_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135)))
      | v1_xboole_0(B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_348,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_2'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_56,c_345])).

tff(c_355,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_348])).

tff(c_356,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_213,c_355])).

tff(c_34,plain,(
    ! [A_27] :
      ( ~ v1_xboole_0(u1_struct_0(A_27))
      | ~ l1_struct_0(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_360,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_356,c_34])).

tff(c_363,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_360])).

tff(c_366,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_363])).

tff(c_370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_366])).

tff(c_371,plain,(
    u1_struct_0('#skF_2') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_379,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_58])).

tff(c_378,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_56])).

tff(c_931,plain,(
    ! [B_177,A_174,D_175,C_178,F_176] :
      ( r1_funct_2(A_174,B_177,C_178,D_175,F_176,F_176)
      | ~ m1_subset_1(F_176,k1_zfmisc_1(k2_zfmisc_1(C_178,D_175)))
      | ~ v1_funct_2(F_176,C_178,D_175)
      | ~ m1_subset_1(F_176,k1_zfmisc_1(k2_zfmisc_1(A_174,B_177)))
      | ~ v1_funct_2(F_176,A_174,B_177)
      | ~ v1_funct_1(F_176)
      | v1_xboole_0(D_175)
      | v1_xboole_0(B_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_933,plain,(
    ! [A_174,B_177] :
      ( r1_funct_2(A_174,B_177,k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_174,B_177)))
      | ~ v1_funct_2('#skF_4',A_174,B_177)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_177) ) ),
    inference(resolution,[status(thm)],[c_378,c_931])).

tff(c_939,plain,(
    ! [A_174,B_177] :
      ( r1_funct_2(A_174,B_177,k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_174,B_177)))
      | ~ v1_funct_2('#skF_4',A_174,B_177)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_379,c_933])).

tff(c_1068,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_939])).

tff(c_1071,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1068,c_34])).

tff(c_1074,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1071])).

tff(c_1077,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1074])).

tff(c_1081,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1077])).

tff(c_1083,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_939])).

tff(c_1472,plain,(
    ! [A_223,B_224] :
      ( r1_funct_2(A_223,B_224,k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_223,B_224)))
      | ~ v1_funct_2('#skF_4',A_223,B_224)
      | v1_xboole_0(B_224) ) ),
    inference(splitRight,[status(thm)],[c_939])).

tff(c_62,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_66,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_50,plain,(
    ! [A_58] :
      ( m1_pre_topc(A_58,A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_402,plain,(
    ! [B_136,A_137] :
      ( m1_subset_1(u1_struct_0(B_136),k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ m1_pre_topc(B_136,A_137)
      | ~ l1_pre_topc(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_411,plain,(
    ! [B_136] :
      ( m1_subset_1(u1_struct_0(B_136),k1_zfmisc_1(k1_relat_1('#skF_4')))
      | ~ m1_pre_topc(B_136,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_402])).

tff(c_463,plain,(
    ! [B_138] :
      ( m1_subset_1(u1_struct_0(B_138),k1_zfmisc_1(k1_relat_1('#skF_4')))
      | ~ m1_pre_topc(B_138,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_411])).

tff(c_469,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(k1_relat_1('#skF_4')))
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_463])).

tff(c_490,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_469])).

tff(c_493,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_490])).

tff(c_497,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_493])).

tff(c_499,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_469])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_520,plain,(
    ! [B_142,A_143] :
      ( r1_tarski(u1_struct_0(B_142),u1_struct_0(A_143))
      | ~ m1_pre_topc(B_142,A_143)
      | ~ l1_pre_topc(A_143) ) ),
    inference(resolution,[status(thm)],[c_402,c_8])).

tff(c_538,plain,(
    ! [A_145] :
      ( r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(A_145))
      | ~ m1_pre_topc('#skF_2',A_145)
      | ~ l1_pre_topc(A_145) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_520])).

tff(c_12,plain,(
    ! [B_6,A_5] :
      ( k7_relat_1(B_6,A_5) = B_6
      | ~ r1_tarski(k1_relat_1(B_6),A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_541,plain,(
    ! [A_145] :
      ( k7_relat_1('#skF_4',u1_struct_0(A_145)) = '#skF_4'
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc('#skF_2',A_145)
      | ~ l1_pre_topc(A_145) ) ),
    inference(resolution,[status(thm)],[c_538,c_12])).

tff(c_579,plain,(
    ! [A_151] :
      ( k7_relat_1('#skF_4',u1_struct_0(A_151)) = '#skF_4'
      | ~ m1_pre_topc('#skF_2',A_151)
      | ~ l1_pre_topc(A_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_541])).

tff(c_588,plain,
    ( k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_4'
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_579])).

tff(c_592,plain,(
    k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_499,c_588])).

tff(c_81,plain,(
    ! [B_73,A_74] :
      ( l1_pre_topc(B_73)
      | ~ m1_pre_topc(B_73,A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_87,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_81])).

tff(c_91,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_87])).

tff(c_553,plain,(
    ! [A_146,B_147] :
      ( m1_pre_topc(A_146,g1_pre_topc(u1_struct_0(B_147),u1_pre_topc(B_147)))
      | ~ m1_pre_topc(A_146,B_147)
      | ~ l1_pre_topc(B_147)
      | ~ l1_pre_topc(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_565,plain,(
    ! [A_146] :
      ( m1_pre_topc(A_146,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')))
      | ~ m1_pre_topc(A_146,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_553])).

tff(c_639,plain,(
    ! [A_155] :
      ( m1_pre_topc(A_155,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')))
      | ~ m1_pre_topc(A_155,'#skF_2')
      | ~ l1_pre_topc(A_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_565])).

tff(c_54,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_377,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_54])).

tff(c_36,plain,(
    ! [B_30,A_28] :
      ( m1_pre_topc(B_30,A_28)
      | ~ m1_pre_topc(B_30,g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_503,plain,(
    ! [B_30] :
      ( m1_pre_topc(B_30,'#skF_3')
      | ~ m1_pre_topc(B_30,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_36])).

tff(c_507,plain,(
    ! [B_30] :
      ( m1_pre_topc(B_30,'#skF_3')
      | ~ m1_pre_topc(B_30,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_503])).

tff(c_662,plain,(
    ! [A_160] :
      ( m1_pre_topc(A_160,'#skF_3')
      | ~ m1_pre_topc(A_160,'#skF_2')
      | ~ l1_pre_topc(A_160) ) ),
    inference(resolution,[status(thm)],[c_639,c_507])).

tff(c_668,plain,
    ( m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_499,c_662])).

tff(c_679,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_668])).

tff(c_525,plain,(
    ! [A_143] :
      ( r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(A_143))
      | ~ m1_pre_topc('#skF_2',A_143)
      | ~ l1_pre_topc(A_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_520])).

tff(c_482,plain,(
    ! [B_141] :
      ( r1_tarski(u1_struct_0(B_141),k1_relat_1('#skF_4'))
      | ~ m1_pre_topc(B_141,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_463,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_708,plain,(
    ! [B_162] :
      ( u1_struct_0(B_162) = k1_relat_1('#skF_4')
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(B_162))
      | ~ m1_pre_topc(B_162,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_482,c_2])).

tff(c_718,plain,(
    ! [A_163] :
      ( u1_struct_0(A_163) = k1_relat_1('#skF_4')
      | ~ m1_pre_topc(A_163,'#skF_2')
      | ~ m1_pre_topc('#skF_2',A_163)
      | ~ l1_pre_topc(A_163) ) ),
    inference(resolution,[status(thm)],[c_525,c_708])).

tff(c_727,plain,
    ( u1_struct_0('#skF_3') = k1_relat_1('#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_718])).

tff(c_737,plain,(
    u1_struct_0('#skF_3') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_679,c_727])).

tff(c_74,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_652,plain,(
    ! [A_156,B_157,C_158,D_159] :
      ( k2_partfun1(A_156,B_157,C_158,D_159) = k7_relat_1(C_158,D_159)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157)))
      | ~ v1_funct_1(C_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_654,plain,(
    ! [D_159] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',D_159) = k7_relat_1('#skF_4',D_159)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_378,c_652])).

tff(c_660,plain,(
    ! [D_159] : k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',D_159) = k7_relat_1('#skF_4',D_159) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_654])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_68,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_1084,plain,(
    ! [A_191,B_192,C_193,D_194] :
      ( k2_partfun1(u1_struct_0(A_191),u1_struct_0(B_192),C_193,u1_struct_0(D_194)) = k2_tmap_1(A_191,B_192,C_193,D_194)
      | ~ m1_pre_topc(D_194,A_191)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_191),u1_struct_0(B_192))))
      | ~ v1_funct_2(C_193,u1_struct_0(A_191),u1_struct_0(B_192))
      | ~ v1_funct_1(C_193)
      | ~ l1_pre_topc(B_192)
      | ~ v2_pre_topc(B_192)
      | v2_struct_0(B_192)
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_1090,plain,(
    ! [B_192,C_193,D_194] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_192),C_193,u1_struct_0(D_194)) = k2_tmap_1('#skF_2',B_192,C_193,D_194)
      | ~ m1_pre_topc(D_194,'#skF_2')
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_192))))
      | ~ v1_funct_2(C_193,u1_struct_0('#skF_2'),u1_struct_0(B_192))
      | ~ v1_funct_1(C_193)
      | ~ l1_pre_topc(B_192)
      | ~ v2_pre_topc(B_192)
      | v2_struct_0(B_192)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_1084])).

tff(c_1103,plain,(
    ! [B_192,C_193,D_194] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0(B_192),C_193,u1_struct_0(D_194)) = k2_tmap_1('#skF_2',B_192,C_193,D_194)
      | ~ m1_pre_topc(D_194,'#skF_2')
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_192))))
      | ~ v1_funct_2(C_193,k1_relat_1('#skF_4'),u1_struct_0(B_192))
      | ~ v1_funct_1(C_193)
      | ~ l1_pre_topc(B_192)
      | ~ v2_pre_topc(B_192)
      | v2_struct_0(B_192)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_371,c_371,c_1090])).

tff(c_1196,plain,(
    ! [B_200,C_201,D_202] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0(B_200),C_201,u1_struct_0(D_202)) = k2_tmap_1('#skF_2',B_200,C_201,D_202)
      | ~ m1_pre_topc(D_202,'#skF_2')
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_200))))
      | ~ v1_funct_2(C_201,k1_relat_1('#skF_4'),u1_struct_0(B_200))
      | ~ v1_funct_1(C_201)
      | ~ l1_pre_topc(B_200)
      | ~ v2_pre_topc(B_200)
      | v2_struct_0(B_200) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1103])).

tff(c_1200,plain,(
    ! [D_202] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_202)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_202)
      | ~ m1_pre_topc(D_202,'#skF_2')
      | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_378,c_1196])).

tff(c_1211,plain,(
    ! [D_202] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_202)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_202)
      | ~ m1_pre_topc(D_202,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_60,c_379,c_660,c_1200])).

tff(c_1217,plain,(
    ! [D_203] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_203)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_203)
      | ~ m1_pre_topc(D_203,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1211])).

tff(c_1235,plain,
    ( k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_737,c_1217])).

tff(c_1245,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_592,c_1235])).

tff(c_52,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_375,plain,(
    ~ r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_52])).

tff(c_738,plain,(
    ~ r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_375])).

tff(c_1252,plain,(
    ~ r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1245,c_738])).

tff(c_1475,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1472,c_1252])).

tff(c_1480,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_378,c_1475])).

tff(c_1482,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1083,c_1480])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:42:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.75/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.63  
% 3.75/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.63  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.75/1.63  
% 3.75/1.63  %Foreground sorts:
% 3.75/1.63  
% 3.75/1.63  
% 3.75/1.63  %Background operators:
% 3.75/1.63  
% 3.75/1.63  
% 3.75/1.63  %Foreground operators:
% 3.75/1.63  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.75/1.63  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.75/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.75/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.75/1.63  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.75/1.63  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.75/1.63  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.75/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.75/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.75/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.75/1.63  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.75/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.75/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.75/1.63  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.75/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.75/1.63  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.75/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.75/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.75/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.75/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.75/1.63  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 3.75/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.75/1.63  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.75/1.63  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.75/1.63  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.75/1.63  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.75/1.63  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.75/1.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.75/1.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.75/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.75/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.75/1.63  
% 3.75/1.66  tff(f_207, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_tmap_1)).
% 3.75/1.66  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.75/1.66  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.75/1.66  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.75/1.66  tff(f_73, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 3.75/1.66  tff(f_65, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.75/1.66  tff(f_98, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.75/1.66  tff(f_136, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 3.75/1.66  tff(f_174, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.75/1.66  tff(f_170, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.75/1.66  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.75/1.66  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 3.75/1.66  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.75/1.66  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 3.75/1.66  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 3.75/1.66  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.75/1.66  tff(f_79, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.75/1.66  tff(f_163, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.75/1.66  tff(c_72, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.75/1.66  tff(c_30, plain, (![A_23]: (l1_struct_0(A_23) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.75/1.66  tff(c_76, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.75/1.66  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.75/1.66  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.75/1.66  tff(c_107, plain, (![C_80, A_81, B_82]: (v1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.75/1.66  tff(c_115, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_107])).
% 3.75/1.66  tff(c_161, plain, (![C_98, A_99, B_100]: (v4_relat_1(C_98, A_99) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.75/1.66  tff(c_169, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_56, c_161])).
% 3.75/1.66  tff(c_199, plain, (![B_110, A_111]: (k1_relat_1(B_110)=A_111 | ~v1_partfun1(B_110, A_111) | ~v4_relat_1(B_110, A_111) | ~v1_relat_1(B_110))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.75/1.66  tff(c_205, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_2')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_169, c_199])).
% 3.75/1.66  tff(c_211, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_205])).
% 3.75/1.66  tff(c_213, plain, (~v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_211])).
% 3.75/1.66  tff(c_58, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.75/1.66  tff(c_345, plain, (![C_133, A_134, B_135]: (v1_partfun1(C_133, A_134) | ~v1_funct_2(C_133, A_134, B_135) | ~v1_funct_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))) | v1_xboole_0(B_135))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.75/1.66  tff(c_348, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_56, c_345])).
% 3.75/1.66  tff(c_355, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_348])).
% 3.75/1.66  tff(c_356, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_213, c_355])).
% 3.75/1.66  tff(c_34, plain, (![A_27]: (~v1_xboole_0(u1_struct_0(A_27)) | ~l1_struct_0(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.75/1.66  tff(c_360, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_356, c_34])).
% 3.75/1.66  tff(c_363, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_76, c_360])).
% 3.75/1.66  tff(c_366, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_363])).
% 3.75/1.66  tff(c_370, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_366])).
% 3.75/1.66  tff(c_371, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_211])).
% 3.75/1.66  tff(c_379, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_58])).
% 3.75/1.66  tff(c_378, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_56])).
% 3.75/1.66  tff(c_931, plain, (![B_177, A_174, D_175, C_178, F_176]: (r1_funct_2(A_174, B_177, C_178, D_175, F_176, F_176) | ~m1_subset_1(F_176, k1_zfmisc_1(k2_zfmisc_1(C_178, D_175))) | ~v1_funct_2(F_176, C_178, D_175) | ~m1_subset_1(F_176, k1_zfmisc_1(k2_zfmisc_1(A_174, B_177))) | ~v1_funct_2(F_176, A_174, B_177) | ~v1_funct_1(F_176) | v1_xboole_0(D_175) | v1_xboole_0(B_177))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.75/1.66  tff(c_933, plain, (![A_174, B_177]: (r1_funct_2(A_174, B_177, k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_174, B_177))) | ~v1_funct_2('#skF_4', A_174, B_177) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_177))), inference(resolution, [status(thm)], [c_378, c_931])).
% 3.75/1.66  tff(c_939, plain, (![A_174, B_177]: (r1_funct_2(A_174, B_177, k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_174, B_177))) | ~v1_funct_2('#skF_4', A_174, B_177) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_177))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_379, c_933])).
% 3.75/1.66  tff(c_1068, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_939])).
% 3.75/1.66  tff(c_1071, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1068, c_34])).
% 3.75/1.66  tff(c_1074, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_76, c_1071])).
% 3.75/1.66  tff(c_1077, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1074])).
% 3.75/1.66  tff(c_1081, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_1077])).
% 3.75/1.66  tff(c_1083, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_939])).
% 3.75/1.66  tff(c_1472, plain, (![A_223, B_224]: (r1_funct_2(A_223, B_224, k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_223, B_224))) | ~v1_funct_2('#skF_4', A_223, B_224) | v1_xboole_0(B_224))), inference(splitRight, [status(thm)], [c_939])).
% 3.75/1.66  tff(c_62, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.75/1.66  tff(c_66, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.75/1.66  tff(c_50, plain, (![A_58]: (m1_pre_topc(A_58, A_58) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.75/1.66  tff(c_402, plain, (![B_136, A_137]: (m1_subset_1(u1_struct_0(B_136), k1_zfmisc_1(u1_struct_0(A_137))) | ~m1_pre_topc(B_136, A_137) | ~l1_pre_topc(A_137))), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.75/1.66  tff(c_411, plain, (![B_136]: (m1_subset_1(u1_struct_0(B_136), k1_zfmisc_1(k1_relat_1('#skF_4'))) | ~m1_pre_topc(B_136, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_371, c_402])).
% 3.75/1.66  tff(c_463, plain, (![B_138]: (m1_subset_1(u1_struct_0(B_138), k1_zfmisc_1(k1_relat_1('#skF_4'))) | ~m1_pre_topc(B_138, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_411])).
% 3.75/1.66  tff(c_469, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(k1_relat_1('#skF_4'))) | ~m1_pre_topc('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_371, c_463])).
% 3.75/1.66  tff(c_490, plain, (~m1_pre_topc('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_469])).
% 3.75/1.66  tff(c_493, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_490])).
% 3.75/1.66  tff(c_497, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_493])).
% 3.75/1.66  tff(c_499, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(splitRight, [status(thm)], [c_469])).
% 3.75/1.66  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.75/1.66  tff(c_520, plain, (![B_142, A_143]: (r1_tarski(u1_struct_0(B_142), u1_struct_0(A_143)) | ~m1_pre_topc(B_142, A_143) | ~l1_pre_topc(A_143))), inference(resolution, [status(thm)], [c_402, c_8])).
% 3.75/1.66  tff(c_538, plain, (![A_145]: (r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(A_145)) | ~m1_pre_topc('#skF_2', A_145) | ~l1_pre_topc(A_145))), inference(superposition, [status(thm), theory('equality')], [c_371, c_520])).
% 3.75/1.66  tff(c_12, plain, (![B_6, A_5]: (k7_relat_1(B_6, A_5)=B_6 | ~r1_tarski(k1_relat_1(B_6), A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.75/1.66  tff(c_541, plain, (![A_145]: (k7_relat_1('#skF_4', u1_struct_0(A_145))='#skF_4' | ~v1_relat_1('#skF_4') | ~m1_pre_topc('#skF_2', A_145) | ~l1_pre_topc(A_145))), inference(resolution, [status(thm)], [c_538, c_12])).
% 3.75/1.66  tff(c_579, plain, (![A_151]: (k7_relat_1('#skF_4', u1_struct_0(A_151))='#skF_4' | ~m1_pre_topc('#skF_2', A_151) | ~l1_pre_topc(A_151))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_541])).
% 3.75/1.66  tff(c_588, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_4' | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_371, c_579])).
% 3.75/1.66  tff(c_592, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_499, c_588])).
% 3.75/1.66  tff(c_81, plain, (![B_73, A_74]: (l1_pre_topc(B_73) | ~m1_pre_topc(B_73, A_74) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.75/1.66  tff(c_87, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_81])).
% 3.75/1.66  tff(c_91, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_87])).
% 3.75/1.66  tff(c_553, plain, (![A_146, B_147]: (m1_pre_topc(A_146, g1_pre_topc(u1_struct_0(B_147), u1_pre_topc(B_147))) | ~m1_pre_topc(A_146, B_147) | ~l1_pre_topc(B_147) | ~l1_pre_topc(A_146))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.75/1.66  tff(c_565, plain, (![A_146]: (m1_pre_topc(A_146, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))) | ~m1_pre_topc(A_146, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_146))), inference(superposition, [status(thm), theory('equality')], [c_371, c_553])).
% 3.75/1.66  tff(c_639, plain, (![A_155]: (m1_pre_topc(A_155, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))) | ~m1_pre_topc(A_155, '#skF_2') | ~l1_pre_topc(A_155))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_565])).
% 3.75/1.66  tff(c_54, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.75/1.66  tff(c_377, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_54])).
% 3.75/1.66  tff(c_36, plain, (![B_30, A_28]: (m1_pre_topc(B_30, A_28) | ~m1_pre_topc(B_30, g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.75/1.66  tff(c_503, plain, (![B_30]: (m1_pre_topc(B_30, '#skF_3') | ~m1_pre_topc(B_30, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_377, c_36])).
% 3.75/1.66  tff(c_507, plain, (![B_30]: (m1_pre_topc(B_30, '#skF_3') | ~m1_pre_topc(B_30, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_503])).
% 3.75/1.66  tff(c_662, plain, (![A_160]: (m1_pre_topc(A_160, '#skF_3') | ~m1_pre_topc(A_160, '#skF_2') | ~l1_pre_topc(A_160))), inference(resolution, [status(thm)], [c_639, c_507])).
% 3.75/1.66  tff(c_668, plain, (m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_499, c_662])).
% 3.75/1.66  tff(c_679, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_668])).
% 3.75/1.66  tff(c_525, plain, (![A_143]: (r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(A_143)) | ~m1_pre_topc('#skF_2', A_143) | ~l1_pre_topc(A_143))), inference(superposition, [status(thm), theory('equality')], [c_371, c_520])).
% 3.75/1.66  tff(c_482, plain, (![B_141]: (r1_tarski(u1_struct_0(B_141), k1_relat_1('#skF_4')) | ~m1_pre_topc(B_141, '#skF_2'))), inference(resolution, [status(thm)], [c_463, c_8])).
% 3.75/1.66  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.75/1.66  tff(c_708, plain, (![B_162]: (u1_struct_0(B_162)=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(B_162)) | ~m1_pre_topc(B_162, '#skF_2'))), inference(resolution, [status(thm)], [c_482, c_2])).
% 3.75/1.66  tff(c_718, plain, (![A_163]: (u1_struct_0(A_163)=k1_relat_1('#skF_4') | ~m1_pre_topc(A_163, '#skF_2') | ~m1_pre_topc('#skF_2', A_163) | ~l1_pre_topc(A_163))), inference(resolution, [status(thm)], [c_525, c_708])).
% 3.75/1.66  tff(c_727, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_4') | ~m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_62, c_718])).
% 3.75/1.66  tff(c_737, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_679, c_727])).
% 3.75/1.66  tff(c_74, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.75/1.66  tff(c_652, plain, (![A_156, B_157, C_158, D_159]: (k2_partfun1(A_156, B_157, C_158, D_159)=k7_relat_1(C_158, D_159) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))) | ~v1_funct_1(C_158))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.75/1.66  tff(c_654, plain, (![D_159]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', D_159)=k7_relat_1('#skF_4', D_159) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_378, c_652])).
% 3.75/1.66  tff(c_660, plain, (![D_159]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', D_159)=k7_relat_1('#skF_4', D_159))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_654])).
% 3.75/1.66  tff(c_70, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.75/1.66  tff(c_68, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.75/1.66  tff(c_1084, plain, (![A_191, B_192, C_193, D_194]: (k2_partfun1(u1_struct_0(A_191), u1_struct_0(B_192), C_193, u1_struct_0(D_194))=k2_tmap_1(A_191, B_192, C_193, D_194) | ~m1_pre_topc(D_194, A_191) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_191), u1_struct_0(B_192)))) | ~v1_funct_2(C_193, u1_struct_0(A_191), u1_struct_0(B_192)) | ~v1_funct_1(C_193) | ~l1_pre_topc(B_192) | ~v2_pre_topc(B_192) | v2_struct_0(B_192) | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191) | v2_struct_0(A_191))), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.75/1.66  tff(c_1090, plain, (![B_192, C_193, D_194]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_192), C_193, u1_struct_0(D_194))=k2_tmap_1('#skF_2', B_192, C_193, D_194) | ~m1_pre_topc(D_194, '#skF_2') | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_192)))) | ~v1_funct_2(C_193, u1_struct_0('#skF_2'), u1_struct_0(B_192)) | ~v1_funct_1(C_193) | ~l1_pre_topc(B_192) | ~v2_pre_topc(B_192) | v2_struct_0(B_192) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_371, c_1084])).
% 3.75/1.66  tff(c_1103, plain, (![B_192, C_193, D_194]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0(B_192), C_193, u1_struct_0(D_194))=k2_tmap_1('#skF_2', B_192, C_193, D_194) | ~m1_pre_topc(D_194, '#skF_2') | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_192)))) | ~v1_funct_2(C_193, k1_relat_1('#skF_4'), u1_struct_0(B_192)) | ~v1_funct_1(C_193) | ~l1_pre_topc(B_192) | ~v2_pre_topc(B_192) | v2_struct_0(B_192) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_371, c_371, c_1090])).
% 3.75/1.66  tff(c_1196, plain, (![B_200, C_201, D_202]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0(B_200), C_201, u1_struct_0(D_202))=k2_tmap_1('#skF_2', B_200, C_201, D_202) | ~m1_pre_topc(D_202, '#skF_2') | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_200)))) | ~v1_funct_2(C_201, k1_relat_1('#skF_4'), u1_struct_0(B_200)) | ~v1_funct_1(C_201) | ~l1_pre_topc(B_200) | ~v2_pre_topc(B_200) | v2_struct_0(B_200))), inference(negUnitSimplification, [status(thm)], [c_70, c_1103])).
% 3.75/1.66  tff(c_1200, plain, (![D_202]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_202))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_202) | ~m1_pre_topc(D_202, '#skF_2') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_378, c_1196])).
% 3.75/1.66  tff(c_1211, plain, (![D_202]: (k7_relat_1('#skF_4', u1_struct_0(D_202))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_202) | ~m1_pre_topc(D_202, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_60, c_379, c_660, c_1200])).
% 3.75/1.66  tff(c_1217, plain, (![D_203]: (k7_relat_1('#skF_4', u1_struct_0(D_203))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_203) | ~m1_pre_topc(D_203, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_76, c_1211])).
% 3.75/1.66  tff(c_1235, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_737, c_1217])).
% 3.75/1.66  tff(c_1245, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_592, c_1235])).
% 3.75/1.66  tff(c_52, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.75/1.66  tff(c_375, plain, (~r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_52])).
% 3.75/1.66  tff(c_738, plain, (~r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_737, c_375])).
% 3.75/1.66  tff(c_1252, plain, (~r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1245, c_738])).
% 3.75/1.66  tff(c_1475, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1472, c_1252])).
% 3.75/1.66  tff(c_1480, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_379, c_378, c_1475])).
% 3.75/1.66  tff(c_1482, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1083, c_1480])).
% 3.75/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.66  
% 3.75/1.66  Inference rules
% 3.75/1.66  ----------------------
% 3.75/1.66  #Ref     : 0
% 3.75/1.66  #Sup     : 276
% 3.75/1.66  #Fact    : 0
% 3.75/1.66  #Define  : 0
% 3.75/1.66  #Split   : 7
% 3.75/1.66  #Chain   : 0
% 3.75/1.66  #Close   : 0
% 3.75/1.66  
% 3.75/1.66  Ordering : KBO
% 3.75/1.66  
% 3.75/1.66  Simplification rules
% 3.75/1.66  ----------------------
% 3.75/1.66  #Subsume      : 45
% 3.75/1.66  #Demod        : 352
% 3.75/1.66  #Tautology    : 131
% 3.75/1.66  #SimpNegUnit  : 14
% 3.75/1.66  #BackRed      : 14
% 3.75/1.66  
% 3.75/1.66  #Partial instantiations: 0
% 3.75/1.66  #Strategies tried      : 1
% 3.75/1.66  
% 3.75/1.66  Timing (in seconds)
% 3.75/1.66  ----------------------
% 3.75/1.66  Preprocessing        : 0.38
% 3.75/1.66  Parsing              : 0.20
% 3.75/1.66  CNF conversion       : 0.03
% 3.75/1.66  Main loop            : 0.49
% 3.75/1.66  Inferencing          : 0.18
% 3.75/1.66  Reduction            : 0.16
% 3.75/1.66  Demodulation         : 0.11
% 3.75/1.66  BG Simplification    : 0.02
% 3.75/1.66  Subsumption          : 0.09
% 3.75/1.66  Abstraction          : 0.02
% 3.75/1.66  MUC search           : 0.00
% 3.75/1.66  Cooper               : 0.00
% 3.75/1.66  Total                : 0.92
% 3.75/1.66  Index Insertion      : 0.00
% 3.75/1.66  Index Deletion       : 0.00
% 3.75/1.66  Index Matching       : 0.00
% 3.75/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
