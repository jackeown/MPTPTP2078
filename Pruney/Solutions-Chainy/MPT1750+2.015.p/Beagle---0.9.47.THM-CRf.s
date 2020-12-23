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
% DateTime   : Thu Dec  3 10:26:53 EST 2020

% Result     : Theorem 3.90s
% Output     : CNFRefutation 4.26s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 888 expanded)
%              Number of leaves         :   50 ( 311 expanded)
%              Depth                    :   20
%              Number of atoms          :  364 (3289 expanded)
%              Number of equality atoms :   38 ( 342 expanded)
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

tff(f_213,negated_conjecture,(
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

tff(f_89,axiom,(
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

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_104,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_142,axiom,(
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

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_180,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_120,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_176,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_169,axiom,(
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

tff(c_70,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_28,plain,(
    ! [A_27] :
      ( l1_struct_0(A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_10,plain,(
    ! [C_9,A_7,B_8] :
      ( v1_relat_1(C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_108,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_10])).

tff(c_131,plain,(
    ! [C_95,A_96,B_97] :
      ( v4_relat_1(C_95,A_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_139,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_131])).

tff(c_163,plain,(
    ! [B_104,A_105] :
      ( k1_relat_1(B_104) = A_105
      | ~ v1_partfun1(B_104,A_105)
      | ~ v4_relat_1(B_104,A_105)
      | ~ v1_relat_1(B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_166,plain,
    ( u1_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_139,c_163])).

tff(c_169,plain,
    ( u1_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_166])).

tff(c_170,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_56,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_356,plain,(
    ! [C_135,A_136,B_137] :
      ( v1_partfun1(C_135,A_136)
      | ~ v1_funct_2(C_135,A_136,B_137)
      | ~ v1_funct_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137)))
      | v1_xboole_0(B_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_362,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_2'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_54,c_356])).

tff(c_372,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_362])).

tff(c_373,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_372])).

tff(c_32,plain,(
    ! [A_31] :
      ( ~ v1_xboole_0(u1_struct_0(A_31))
      | ~ l1_struct_0(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_377,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_373,c_32])).

tff(c_380,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_377])).

tff(c_383,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_380])).

tff(c_387,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_383])).

tff(c_388,plain,(
    u1_struct_0('#skF_2') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_395,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_56])).

tff(c_394,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_54])).

tff(c_1115,plain,(
    ! [B_188,C_190,F_189,A_187,D_191] :
      ( r1_funct_2(A_187,B_188,C_190,D_191,F_189,F_189)
      | ~ m1_subset_1(F_189,k1_zfmisc_1(k2_zfmisc_1(C_190,D_191)))
      | ~ v1_funct_2(F_189,C_190,D_191)
      | ~ m1_subset_1(F_189,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ v1_funct_2(F_189,A_187,B_188)
      | ~ v1_funct_1(F_189)
      | v1_xboole_0(D_191)
      | v1_xboole_0(B_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1119,plain,(
    ! [A_187,B_188] :
      ( r1_funct_2(A_187,B_188,k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ v1_funct_2('#skF_4',A_187,B_188)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_188) ) ),
    inference(resolution,[status(thm)],[c_394,c_1115])).

tff(c_1128,plain,(
    ! [A_187,B_188] :
      ( r1_funct_2(A_187,B_188,k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ v1_funct_2('#skF_4',A_187,B_188)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_188) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_395,c_1119])).

tff(c_1184,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1128])).

tff(c_1187,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1184,c_32])).

tff(c_1190,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1187])).

tff(c_1193,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_1190])).

tff(c_1197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1193])).

tff(c_1199,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1128])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_109,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_393,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_109])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1557,plain,(
    ! [D_231,A_233,A_234,B_232,C_235] :
      ( r1_funct_2(A_233,B_232,C_235,D_231,A_234,A_234)
      | ~ v1_funct_2(A_234,C_235,D_231)
      | ~ m1_subset_1(A_234,k1_zfmisc_1(k2_zfmisc_1(A_233,B_232)))
      | ~ v1_funct_2(A_234,A_233,B_232)
      | ~ v1_funct_1(A_234)
      | v1_xboole_0(D_231)
      | v1_xboole_0(B_232)
      | ~ r1_tarski(A_234,k2_zfmisc_1(C_235,D_231)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1115])).

tff(c_1561,plain,(
    ! [C_235,D_231] :
      ( r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),C_235,D_231,'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',C_235,D_231)
      | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(D_231)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(C_235,D_231)) ) ),
    inference(resolution,[status(thm)],[c_394,c_1557])).

tff(c_1571,plain,(
    ! [C_235,D_231] :
      ( r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),C_235,D_231,'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',C_235,D_231)
      | v1_xboole_0(D_231)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(C_235,D_231)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_395,c_1561])).

tff(c_1759,plain,(
    ! [C_247,D_248] :
      ( r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),C_247,D_248,'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',C_247,D_248)
      | v1_xboole_0(D_248)
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(C_247,D_248)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1199,c_1571])).

tff(c_60,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_147,plain,(
    ! [B_101,A_102] :
      ( k7_relat_1(B_101,A_102) = B_101
      | ~ v4_relat_1(B_101,A_102)
      | ~ v1_relat_1(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_150,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_139,c_147])).

tff(c_153,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_150])).

tff(c_390,plain,(
    k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_153])).

tff(c_64,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_84,plain,(
    ! [B_81,A_82] :
      ( l1_pre_topc(B_81)
      | ~ m1_pre_topc(B_81,A_82)
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_90,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_84])).

tff(c_94,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_90])).

tff(c_48,plain,(
    ! [A_62] :
      ( m1_pre_topc(A_62,A_62)
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_615,plain,(
    ! [A_153,B_154] :
      ( m1_pre_topc(A_153,g1_pre_topc(u1_struct_0(B_154),u1_pre_topc(B_154)))
      | ~ m1_pre_topc(A_153,B_154)
      | ~ l1_pre_topc(B_154)
      | ~ l1_pre_topc(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_627,plain,(
    ! [A_153] :
      ( m1_pre_topc(A_153,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')))
      | ~ m1_pre_topc(A_153,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_153) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_615])).

tff(c_744,plain,(
    ! [A_166] :
      ( m1_pre_topc(A_166,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')))
      | ~ m1_pre_topc(A_166,'#skF_2')
      | ~ l1_pre_topc(A_166) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_627])).

tff(c_52,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_391,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_52])).

tff(c_576,plain,(
    ! [B_148,A_149] :
      ( m1_pre_topc(B_148,A_149)
      | ~ m1_pre_topc(B_148,g1_pre_topc(u1_struct_0(A_149),u1_pre_topc(A_149)))
      | ~ l1_pre_topc(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_579,plain,(
    ! [B_148] :
      ( m1_pre_topc(B_148,'#skF_3')
      | ~ m1_pre_topc(B_148,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_576])).

tff(c_588,plain,(
    ! [B_148] :
      ( m1_pre_topc(B_148,'#skF_3')
      | ~ m1_pre_topc(B_148,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_579])).

tff(c_757,plain,(
    ! [A_167] :
      ( m1_pre_topc(A_167,'#skF_3')
      | ~ m1_pre_topc(A_167,'#skF_2')
      | ~ l1_pre_topc(A_167) ) ),
    inference(resolution,[status(thm)],[c_744,c_588])).

tff(c_767,plain,
    ( m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_757])).

tff(c_777,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_767])).

tff(c_431,plain,(
    ! [B_138,A_139] :
      ( m1_subset_1(u1_struct_0(B_138),k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ m1_pre_topc(B_138,A_139)
      | ~ l1_pre_topc(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_541,plain,(
    ! [B_144,A_145] :
      ( r1_tarski(u1_struct_0(B_144),u1_struct_0(A_145))
      | ~ m1_pre_topc(B_144,A_145)
      | ~ l1_pre_topc(A_145) ) ),
    inference(resolution,[status(thm)],[c_431,c_2])).

tff(c_544,plain,(
    ! [A_145] :
      ( r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(A_145))
      | ~ m1_pre_topc('#skF_2',A_145)
      | ~ l1_pre_topc(A_145) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_541])).

tff(c_654,plain,(
    ! [D_157,B_158,C_159,A_160] :
      ( m1_subset_1(D_157,k1_zfmisc_1(k2_zfmisc_1(B_158,C_159)))
      | ~ r1_tarski(k1_relat_1(D_157),B_158)
      | ~ m1_subset_1(D_157,k1_zfmisc_1(k2_zfmisc_1(A_160,C_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_662,plain,(
    ! [B_161] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_161,u1_struct_0('#skF_1'))))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_161) ) ),
    inference(resolution,[status(thm)],[c_394,c_654])).

tff(c_14,plain,(
    ! [C_12,A_10,B_11] :
      ( v4_relat_1(C_12,A_10)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_684,plain,(
    ! [B_162] :
      ( v4_relat_1('#skF_4',B_162)
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_162) ) ),
    inference(resolution,[status(thm)],[c_662,c_14])).

tff(c_694,plain,(
    ! [A_163] :
      ( v4_relat_1('#skF_4',u1_struct_0(A_163))
      | ~ m1_pre_topc('#skF_2',A_163)
      | ~ l1_pre_topc(A_163) ) ),
    inference(resolution,[status(thm)],[c_544,c_684])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k7_relat_1(B_4,A_3) = B_4
      | ~ v4_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_700,plain,(
    ! [A_163] :
      ( k7_relat_1('#skF_4',u1_struct_0(A_163)) = '#skF_4'
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc('#skF_2',A_163)
      | ~ l1_pre_topc(A_163) ) ),
    inference(resolution,[status(thm)],[c_694,c_6])).

tff(c_727,plain,(
    ! [A_165] :
      ( k7_relat_1('#skF_4',u1_struct_0(A_165)) = '#skF_4'
      | ~ m1_pre_topc('#skF_2',A_165)
      | ~ l1_pre_topc(A_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_700])).

tff(c_440,plain,(
    ! [B_138] :
      ( m1_subset_1(u1_struct_0(B_138),k1_zfmisc_1(k1_relat_1('#skF_4')))
      | ~ m1_pre_topc(B_138,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_431])).

tff(c_489,plain,(
    ! [B_140] :
      ( m1_subset_1(u1_struct_0(B_140),k1_zfmisc_1(k1_relat_1('#skF_4')))
      | ~ m1_pre_topc(B_140,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_440])).

tff(c_496,plain,(
    ! [B_140] :
      ( r1_tarski(u1_struct_0(B_140),k1_relat_1('#skF_4'))
      | ~ m1_pre_topc(B_140,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_489,c_2])).

tff(c_501,plain,(
    ! [B_142,A_143] :
      ( k1_relat_1(k7_relat_1(B_142,A_143)) = A_143
      | ~ r1_tarski(A_143,k1_relat_1(B_142))
      | ~ v1_relat_1(B_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_504,plain,(
    ! [B_140] :
      ( k1_relat_1(k7_relat_1('#skF_4',u1_struct_0(B_140))) = u1_struct_0(B_140)
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(B_140,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_496,c_501])).

tff(c_507,plain,(
    ! [B_140] :
      ( k1_relat_1(k7_relat_1('#skF_4',u1_struct_0(B_140))) = u1_struct_0(B_140)
      | ~ m1_pre_topc(B_140,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_504])).

tff(c_818,plain,(
    ! [A_173] :
      ( u1_struct_0(A_173) = k1_relat_1('#skF_4')
      | ~ m1_pre_topc(A_173,'#skF_2')
      | ~ m1_pre_topc('#skF_2',A_173)
      | ~ l1_pre_topc(A_173) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_727,c_507])).

tff(c_827,plain,
    ( u1_struct_0('#skF_3') = k1_relat_1('#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_818])).

tff(c_837,plain,(
    u1_struct_0('#skF_3') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_777,c_827])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_497,plain,(
    ! [B_141] :
      ( r1_tarski(u1_struct_0(B_141),k1_relat_1('#skF_4'))
      | ~ m1_pre_topc(B_141,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_489,c_2])).

tff(c_500,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_497])).

tff(c_508,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_500])).

tff(c_511,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_508])).

tff(c_515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_511])).

tff(c_516,plain,(
    r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_500])).

tff(c_66,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_793,plain,(
    ! [A_168,B_169,C_170,D_171] :
      ( k2_partfun1(A_168,B_169,C_170,D_171) = k7_relat_1(C_170,D_171)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169)))
      | ~ v1_funct_1(C_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_797,plain,(
    ! [D_171] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',D_171) = k7_relat_1('#skF_4',D_171)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_394,c_793])).

tff(c_806,plain,(
    ! [D_171] : k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',D_171) = k7_relat_1('#skF_4',D_171) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_797])).

tff(c_72,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_660,plain,(
    ! [B_158] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_158,u1_struct_0('#skF_1'))))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_158) ) ),
    inference(resolution,[status(thm)],[c_394,c_654])).

tff(c_1352,plain,(
    ! [A_216,B_217,C_218,D_219] :
      ( k2_partfun1(u1_struct_0(A_216),u1_struct_0(B_217),C_218,u1_struct_0(D_219)) = k2_tmap_1(A_216,B_217,C_218,D_219)
      | ~ m1_pre_topc(D_219,A_216)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_216),u1_struct_0(B_217))))
      | ~ v1_funct_2(C_218,u1_struct_0(A_216),u1_struct_0(B_217))
      | ~ v1_funct_1(C_218)
      | ~ l1_pre_topc(B_217)
      | ~ v2_pre_topc(B_217)
      | v2_struct_0(B_217)
      | ~ l1_pre_topc(A_216)
      | ~ v2_pre_topc(A_216)
      | v2_struct_0(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_1359,plain,(
    ! [A_216,D_219] :
      ( k2_partfun1(u1_struct_0(A_216),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_219)) = k2_tmap_1(A_216,'#skF_1','#skF_4',D_219)
      | ~ m1_pre_topc(D_219,A_216)
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_216),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_216)
      | ~ v2_pre_topc(A_216)
      | v2_struct_0(A_216)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(A_216)) ) ),
    inference(resolution,[status(thm)],[c_660,c_1352])).

tff(c_1375,plain,(
    ! [A_216,D_219] :
      ( k2_partfun1(u1_struct_0(A_216),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_219)) = k2_tmap_1(A_216,'#skF_1','#skF_4',D_219)
      | ~ m1_pre_topc(D_219,A_216)
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_216),u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_216)
      | ~ v2_pre_topc(A_216)
      | v2_struct_0(A_216)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(A_216)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_58,c_1359])).

tff(c_1445,plain,(
    ! [A_227,D_228] :
      ( k2_partfun1(u1_struct_0(A_227),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_228)) = k2_tmap_1(A_227,'#skF_1','#skF_4',D_228)
      | ~ m1_pre_topc(D_228,A_227)
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_227),u1_struct_0('#skF_1'))
      | ~ l1_pre_topc(A_227)
      | ~ v2_pre_topc(A_227)
      | v2_struct_0(A_227)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(A_227)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1375])).

tff(c_1474,plain,(
    ! [D_228] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_228)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_228)
      | ~ m1_pre_topc(D_228,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_1445])).

tff(c_1484,plain,(
    ! [D_228] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_228)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_228)
      | ~ m1_pre_topc(D_228,'#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_516,c_388,c_66,c_64,c_395,c_388,c_806,c_1474])).

tff(c_1486,plain,(
    ! [D_229] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_229)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_229)
      | ~ m1_pre_topc(D_229,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1484])).

tff(c_1510,plain,
    ( k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_837,c_1486])).

tff(c_1520,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_390,c_1510])).

tff(c_50,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_404,plain,(
    ~ r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_50])).

tff(c_839,plain,(
    ~ r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_837,c_404])).

tff(c_1527,plain,(
    ~ r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1520,c_839])).

tff(c_1762,plain,
    ( ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1759,c_1527])).

tff(c_1767,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_395,c_1762])).

tff(c_1769,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1199,c_1767])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:46:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.90/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.90/1.74  
% 3.90/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.90/1.74  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.90/1.74  
% 3.90/1.74  %Foreground sorts:
% 3.90/1.74  
% 3.90/1.74  
% 3.90/1.74  %Background operators:
% 3.90/1.74  
% 3.90/1.74  
% 3.90/1.74  %Foreground operators:
% 3.90/1.74  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.90/1.74  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.90/1.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.90/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.90/1.74  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.90/1.74  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.90/1.74  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.90/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.90/1.74  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.90/1.74  tff('#skF_2', type, '#skF_2': $i).
% 3.90/1.74  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.90/1.74  tff('#skF_3', type, '#skF_3': $i).
% 3.90/1.74  tff('#skF_1', type, '#skF_1': $i).
% 3.90/1.74  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.90/1.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.90/1.74  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.90/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.90/1.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.90/1.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.90/1.74  tff('#skF_4', type, '#skF_4': $i).
% 3.90/1.74  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 3.90/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.90/1.74  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.90/1.74  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.90/1.74  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.90/1.74  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.90/1.74  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.90/1.74  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.90/1.74  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.90/1.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.90/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.90/1.74  
% 4.26/1.79  tff(f_213, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_tmap_1)).
% 4.26/1.79  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.26/1.79  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.26/1.79  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.26/1.79  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 4.26/1.79  tff(f_71, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 4.26/1.79  tff(f_104, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.26/1.79  tff(f_142, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 4.26/1.79  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.26/1.79  tff(f_35, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 4.26/1.79  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.26/1.79  tff(f_180, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.26/1.79  tff(f_120, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 4.26/1.79  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 4.26/1.79  tff(f_176, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.26/1.79  tff(f_57, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 4.26/1.79  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 4.26/1.79  tff(f_85, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 4.26/1.79  tff(f_169, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 4.26/1.79  tff(c_70, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_213])).
% 4.26/1.79  tff(c_28, plain, (![A_27]: (l1_struct_0(A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.26/1.79  tff(c_74, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_213])).
% 4.26/1.79  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_213])).
% 4.26/1.79  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_213])).
% 4.26/1.79  tff(c_10, plain, (![C_9, A_7, B_8]: (v1_relat_1(C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.26/1.79  tff(c_108, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_10])).
% 4.26/1.79  tff(c_131, plain, (![C_95, A_96, B_97]: (v4_relat_1(C_95, A_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.26/1.79  tff(c_139, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_131])).
% 4.26/1.79  tff(c_163, plain, (![B_104, A_105]: (k1_relat_1(B_104)=A_105 | ~v1_partfun1(B_104, A_105) | ~v4_relat_1(B_104, A_105) | ~v1_relat_1(B_104))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.26/1.79  tff(c_166, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_2')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_139, c_163])).
% 4.26/1.79  tff(c_169, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_166])).
% 4.26/1.79  tff(c_170, plain, (~v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_169])).
% 4.26/1.79  tff(c_56, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_213])).
% 4.26/1.79  tff(c_356, plain, (![C_135, A_136, B_137]: (v1_partfun1(C_135, A_136) | ~v1_funct_2(C_135, A_136, B_137) | ~v1_funct_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))) | v1_xboole_0(B_137))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.26/1.79  tff(c_362, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_54, c_356])).
% 4.26/1.79  tff(c_372, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_362])).
% 4.26/1.79  tff(c_373, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_170, c_372])).
% 4.26/1.79  tff(c_32, plain, (![A_31]: (~v1_xboole_0(u1_struct_0(A_31)) | ~l1_struct_0(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.26/1.79  tff(c_377, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_373, c_32])).
% 4.26/1.79  tff(c_380, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_74, c_377])).
% 4.26/1.79  tff(c_383, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_380])).
% 4.26/1.79  tff(c_387, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_383])).
% 4.26/1.79  tff(c_388, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_169])).
% 4.26/1.79  tff(c_395, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_388, c_56])).
% 4.26/1.79  tff(c_394, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_388, c_54])).
% 4.26/1.79  tff(c_1115, plain, (![B_188, C_190, F_189, A_187, D_191]: (r1_funct_2(A_187, B_188, C_190, D_191, F_189, F_189) | ~m1_subset_1(F_189, k1_zfmisc_1(k2_zfmisc_1(C_190, D_191))) | ~v1_funct_2(F_189, C_190, D_191) | ~m1_subset_1(F_189, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))) | ~v1_funct_2(F_189, A_187, B_188) | ~v1_funct_1(F_189) | v1_xboole_0(D_191) | v1_xboole_0(B_188))), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.26/1.79  tff(c_1119, plain, (![A_187, B_188]: (r1_funct_2(A_187, B_188, k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))) | ~v1_funct_2('#skF_4', A_187, B_188) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_188))), inference(resolution, [status(thm)], [c_394, c_1115])).
% 4.26/1.79  tff(c_1128, plain, (![A_187, B_188]: (r1_funct_2(A_187, B_188, k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))) | ~v1_funct_2('#skF_4', A_187, B_188) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_188))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_395, c_1119])).
% 4.26/1.79  tff(c_1184, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_1128])).
% 4.26/1.79  tff(c_1187, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1184, c_32])).
% 4.26/1.79  tff(c_1190, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_74, c_1187])).
% 4.26/1.79  tff(c_1193, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_1190])).
% 4.26/1.79  tff(c_1197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_1193])).
% 4.26/1.79  tff(c_1199, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_1128])).
% 4.26/1.79  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.26/1.79  tff(c_109, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_54, c_2])).
% 4.26/1.79  tff(c_393, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_388, c_109])).
% 4.26/1.79  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.26/1.79  tff(c_1557, plain, (![D_231, A_233, A_234, B_232, C_235]: (r1_funct_2(A_233, B_232, C_235, D_231, A_234, A_234) | ~v1_funct_2(A_234, C_235, D_231) | ~m1_subset_1(A_234, k1_zfmisc_1(k2_zfmisc_1(A_233, B_232))) | ~v1_funct_2(A_234, A_233, B_232) | ~v1_funct_1(A_234) | v1_xboole_0(D_231) | v1_xboole_0(B_232) | ~r1_tarski(A_234, k2_zfmisc_1(C_235, D_231)))), inference(resolution, [status(thm)], [c_4, c_1115])).
% 4.26/1.79  tff(c_1561, plain, (![C_235, D_231]: (r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), C_235, D_231, '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', C_235, D_231) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(D_231) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_zfmisc_1(C_235, D_231)))), inference(resolution, [status(thm)], [c_394, c_1557])).
% 4.26/1.79  tff(c_1571, plain, (![C_235, D_231]: (r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), C_235, D_231, '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', C_235, D_231) | v1_xboole_0(D_231) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_zfmisc_1(C_235, D_231)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_395, c_1561])).
% 4.26/1.79  tff(c_1759, plain, (![C_247, D_248]: (r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), C_247, D_248, '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', C_247, D_248) | v1_xboole_0(D_248) | ~r1_tarski('#skF_4', k2_zfmisc_1(C_247, D_248)))), inference(negUnitSimplification, [status(thm)], [c_1199, c_1571])).
% 4.26/1.79  tff(c_60, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_213])).
% 4.26/1.79  tff(c_147, plain, (![B_101, A_102]: (k7_relat_1(B_101, A_102)=B_101 | ~v4_relat_1(B_101, A_102) | ~v1_relat_1(B_101))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.26/1.79  tff(c_150, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_139, c_147])).
% 4.26/1.79  tff(c_153, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_150])).
% 4.26/1.79  tff(c_390, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_388, c_153])).
% 4.26/1.79  tff(c_64, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_213])).
% 4.26/1.79  tff(c_84, plain, (![B_81, A_82]: (l1_pre_topc(B_81) | ~m1_pre_topc(B_81, A_82) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.26/1.79  tff(c_90, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_84])).
% 4.26/1.79  tff(c_94, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_90])).
% 4.26/1.79  tff(c_48, plain, (![A_62]: (m1_pre_topc(A_62, A_62) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.26/1.79  tff(c_615, plain, (![A_153, B_154]: (m1_pre_topc(A_153, g1_pre_topc(u1_struct_0(B_154), u1_pre_topc(B_154))) | ~m1_pre_topc(A_153, B_154) | ~l1_pre_topc(B_154) | ~l1_pre_topc(A_153))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.26/1.79  tff(c_627, plain, (![A_153]: (m1_pre_topc(A_153, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))) | ~m1_pre_topc(A_153, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_153))), inference(superposition, [status(thm), theory('equality')], [c_388, c_615])).
% 4.26/1.79  tff(c_744, plain, (![A_166]: (m1_pre_topc(A_166, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))) | ~m1_pre_topc(A_166, '#skF_2') | ~l1_pre_topc(A_166))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_627])).
% 4.26/1.79  tff(c_52, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_213])).
% 4.26/1.79  tff(c_391, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_388, c_52])).
% 4.26/1.79  tff(c_576, plain, (![B_148, A_149]: (m1_pre_topc(B_148, A_149) | ~m1_pre_topc(B_148, g1_pre_topc(u1_struct_0(A_149), u1_pre_topc(A_149))) | ~l1_pre_topc(A_149))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.26/1.79  tff(c_579, plain, (![B_148]: (m1_pre_topc(B_148, '#skF_3') | ~m1_pre_topc(B_148, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_391, c_576])).
% 4.26/1.79  tff(c_588, plain, (![B_148]: (m1_pre_topc(B_148, '#skF_3') | ~m1_pre_topc(B_148, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_579])).
% 4.26/1.79  tff(c_757, plain, (![A_167]: (m1_pre_topc(A_167, '#skF_3') | ~m1_pre_topc(A_167, '#skF_2') | ~l1_pre_topc(A_167))), inference(resolution, [status(thm)], [c_744, c_588])).
% 4.26/1.79  tff(c_767, plain, (m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_757])).
% 4.26/1.79  tff(c_777, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_767])).
% 4.26/1.79  tff(c_431, plain, (![B_138, A_139]: (m1_subset_1(u1_struct_0(B_138), k1_zfmisc_1(u1_struct_0(A_139))) | ~m1_pre_topc(B_138, A_139) | ~l1_pre_topc(A_139))), inference(cnfTransformation, [status(thm)], [f_176])).
% 4.26/1.79  tff(c_541, plain, (![B_144, A_145]: (r1_tarski(u1_struct_0(B_144), u1_struct_0(A_145)) | ~m1_pre_topc(B_144, A_145) | ~l1_pre_topc(A_145))), inference(resolution, [status(thm)], [c_431, c_2])).
% 4.26/1.79  tff(c_544, plain, (![A_145]: (r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(A_145)) | ~m1_pre_topc('#skF_2', A_145) | ~l1_pre_topc(A_145))), inference(superposition, [status(thm), theory('equality')], [c_388, c_541])).
% 4.26/1.79  tff(c_654, plain, (![D_157, B_158, C_159, A_160]: (m1_subset_1(D_157, k1_zfmisc_1(k2_zfmisc_1(B_158, C_159))) | ~r1_tarski(k1_relat_1(D_157), B_158) | ~m1_subset_1(D_157, k1_zfmisc_1(k2_zfmisc_1(A_160, C_159))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.26/1.79  tff(c_662, plain, (![B_161]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_161, u1_struct_0('#skF_1')))) | ~r1_tarski(k1_relat_1('#skF_4'), B_161))), inference(resolution, [status(thm)], [c_394, c_654])).
% 4.26/1.79  tff(c_14, plain, (![C_12, A_10, B_11]: (v4_relat_1(C_12, A_10) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.26/1.79  tff(c_684, plain, (![B_162]: (v4_relat_1('#skF_4', B_162) | ~r1_tarski(k1_relat_1('#skF_4'), B_162))), inference(resolution, [status(thm)], [c_662, c_14])).
% 4.26/1.79  tff(c_694, plain, (![A_163]: (v4_relat_1('#skF_4', u1_struct_0(A_163)) | ~m1_pre_topc('#skF_2', A_163) | ~l1_pre_topc(A_163))), inference(resolution, [status(thm)], [c_544, c_684])).
% 4.26/1.79  tff(c_6, plain, (![B_4, A_3]: (k7_relat_1(B_4, A_3)=B_4 | ~v4_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.26/1.79  tff(c_700, plain, (![A_163]: (k7_relat_1('#skF_4', u1_struct_0(A_163))='#skF_4' | ~v1_relat_1('#skF_4') | ~m1_pre_topc('#skF_2', A_163) | ~l1_pre_topc(A_163))), inference(resolution, [status(thm)], [c_694, c_6])).
% 4.26/1.79  tff(c_727, plain, (![A_165]: (k7_relat_1('#skF_4', u1_struct_0(A_165))='#skF_4' | ~m1_pre_topc('#skF_2', A_165) | ~l1_pre_topc(A_165))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_700])).
% 4.26/1.79  tff(c_440, plain, (![B_138]: (m1_subset_1(u1_struct_0(B_138), k1_zfmisc_1(k1_relat_1('#skF_4'))) | ~m1_pre_topc(B_138, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_388, c_431])).
% 4.26/1.79  tff(c_489, plain, (![B_140]: (m1_subset_1(u1_struct_0(B_140), k1_zfmisc_1(k1_relat_1('#skF_4'))) | ~m1_pre_topc(B_140, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_440])).
% 4.26/1.79  tff(c_496, plain, (![B_140]: (r1_tarski(u1_struct_0(B_140), k1_relat_1('#skF_4')) | ~m1_pre_topc(B_140, '#skF_2'))), inference(resolution, [status(thm)], [c_489, c_2])).
% 4.26/1.79  tff(c_501, plain, (![B_142, A_143]: (k1_relat_1(k7_relat_1(B_142, A_143))=A_143 | ~r1_tarski(A_143, k1_relat_1(B_142)) | ~v1_relat_1(B_142))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.26/1.79  tff(c_504, plain, (![B_140]: (k1_relat_1(k7_relat_1('#skF_4', u1_struct_0(B_140)))=u1_struct_0(B_140) | ~v1_relat_1('#skF_4') | ~m1_pre_topc(B_140, '#skF_2'))), inference(resolution, [status(thm)], [c_496, c_501])).
% 4.26/1.79  tff(c_507, plain, (![B_140]: (k1_relat_1(k7_relat_1('#skF_4', u1_struct_0(B_140)))=u1_struct_0(B_140) | ~m1_pre_topc(B_140, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_504])).
% 4.26/1.79  tff(c_818, plain, (![A_173]: (u1_struct_0(A_173)=k1_relat_1('#skF_4') | ~m1_pre_topc(A_173, '#skF_2') | ~m1_pre_topc('#skF_2', A_173) | ~l1_pre_topc(A_173))), inference(superposition, [status(thm), theory('equality')], [c_727, c_507])).
% 4.26/1.79  tff(c_827, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_4') | ~m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_60, c_818])).
% 4.26/1.79  tff(c_837, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_777, c_827])).
% 4.26/1.79  tff(c_68, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_213])).
% 4.26/1.79  tff(c_497, plain, (![B_141]: (r1_tarski(u1_struct_0(B_141), k1_relat_1('#skF_4')) | ~m1_pre_topc(B_141, '#skF_2'))), inference(resolution, [status(thm)], [c_489, c_2])).
% 4.26/1.79  tff(c_500, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~m1_pre_topc('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_388, c_497])).
% 4.26/1.79  tff(c_508, plain, (~m1_pre_topc('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_500])).
% 4.26/1.79  tff(c_511, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_508])).
% 4.26/1.79  tff(c_515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_511])).
% 4.26/1.79  tff(c_516, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_500])).
% 4.26/1.79  tff(c_66, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_213])).
% 4.26/1.79  tff(c_793, plain, (![A_168, B_169, C_170, D_171]: (k2_partfun1(A_168, B_169, C_170, D_171)=k7_relat_1(C_170, D_171) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))) | ~v1_funct_1(C_170))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.26/1.79  tff(c_797, plain, (![D_171]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', D_171)=k7_relat_1('#skF_4', D_171) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_394, c_793])).
% 4.26/1.79  tff(c_806, plain, (![D_171]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', D_171)=k7_relat_1('#skF_4', D_171))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_797])).
% 4.26/1.79  tff(c_72, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_213])).
% 4.26/1.79  tff(c_660, plain, (![B_158]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_158, u1_struct_0('#skF_1')))) | ~r1_tarski(k1_relat_1('#skF_4'), B_158))), inference(resolution, [status(thm)], [c_394, c_654])).
% 4.26/1.79  tff(c_1352, plain, (![A_216, B_217, C_218, D_219]: (k2_partfun1(u1_struct_0(A_216), u1_struct_0(B_217), C_218, u1_struct_0(D_219))=k2_tmap_1(A_216, B_217, C_218, D_219) | ~m1_pre_topc(D_219, A_216) | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_216), u1_struct_0(B_217)))) | ~v1_funct_2(C_218, u1_struct_0(A_216), u1_struct_0(B_217)) | ~v1_funct_1(C_218) | ~l1_pre_topc(B_217) | ~v2_pre_topc(B_217) | v2_struct_0(B_217) | ~l1_pre_topc(A_216) | ~v2_pre_topc(A_216) | v2_struct_0(A_216))), inference(cnfTransformation, [status(thm)], [f_169])).
% 4.26/1.79  tff(c_1359, plain, (![A_216, D_219]: (k2_partfun1(u1_struct_0(A_216), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_219))=k2_tmap_1(A_216, '#skF_1', '#skF_4', D_219) | ~m1_pre_topc(D_219, A_216) | ~v1_funct_2('#skF_4', u1_struct_0(A_216), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_216) | ~v2_pre_topc(A_216) | v2_struct_0(A_216) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(A_216)))), inference(resolution, [status(thm)], [c_660, c_1352])).
% 4.26/1.79  tff(c_1375, plain, (![A_216, D_219]: (k2_partfun1(u1_struct_0(A_216), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_219))=k2_tmap_1(A_216, '#skF_1', '#skF_4', D_219) | ~m1_pre_topc(D_219, A_216) | ~v1_funct_2('#skF_4', u1_struct_0(A_216), u1_struct_0('#skF_1')) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_216) | ~v2_pre_topc(A_216) | v2_struct_0(A_216) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(A_216)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_58, c_1359])).
% 4.26/1.79  tff(c_1445, plain, (![A_227, D_228]: (k2_partfun1(u1_struct_0(A_227), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_228))=k2_tmap_1(A_227, '#skF_1', '#skF_4', D_228) | ~m1_pre_topc(D_228, A_227) | ~v1_funct_2('#skF_4', u1_struct_0(A_227), u1_struct_0('#skF_1')) | ~l1_pre_topc(A_227) | ~v2_pre_topc(A_227) | v2_struct_0(A_227) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(A_227)))), inference(negUnitSimplification, [status(thm)], [c_74, c_1375])).
% 4.26/1.79  tff(c_1474, plain, (![D_228]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_228))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_228) | ~m1_pre_topc(D_228, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_388, c_1445])).
% 4.26/1.79  tff(c_1484, plain, (![D_228]: (k7_relat_1('#skF_4', u1_struct_0(D_228))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_228) | ~m1_pre_topc(D_228, '#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_516, c_388, c_66, c_64, c_395, c_388, c_806, c_1474])).
% 4.26/1.79  tff(c_1486, plain, (![D_229]: (k7_relat_1('#skF_4', u1_struct_0(D_229))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_229) | ~m1_pre_topc(D_229, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_68, c_1484])).
% 4.26/1.79  tff(c_1510, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_837, c_1486])).
% 4.26/1.79  tff(c_1520, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_390, c_1510])).
% 4.26/1.79  tff(c_50, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_213])).
% 4.26/1.79  tff(c_404, plain, (~r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_388, c_50])).
% 4.26/1.79  tff(c_839, plain, (~r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_837, c_404])).
% 4.26/1.79  tff(c_1527, plain, (~r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1520, c_839])).
% 4.26/1.79  tff(c_1762, plain, (~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1759, c_1527])).
% 4.26/1.79  tff(c_1767, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_393, c_395, c_1762])).
% 4.26/1.79  tff(c_1769, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1199, c_1767])).
% 4.26/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.26/1.79  
% 4.26/1.79  Inference rules
% 4.26/1.79  ----------------------
% 4.26/1.79  #Ref     : 0
% 4.26/1.79  #Sup     : 339
% 4.26/1.79  #Fact    : 0
% 4.26/1.79  #Define  : 0
% 4.26/1.79  #Split   : 7
% 4.26/1.79  #Chain   : 0
% 4.26/1.79  #Close   : 0
% 4.26/1.79  
% 4.26/1.79  Ordering : KBO
% 4.26/1.79  
% 4.26/1.79  Simplification rules
% 4.26/1.79  ----------------------
% 4.26/1.79  #Subsume      : 52
% 4.26/1.79  #Demod        : 418
% 4.26/1.79  #Tautology    : 161
% 4.26/1.79  #SimpNegUnit  : 25
% 4.26/1.79  #BackRed      : 14
% 4.26/1.79  
% 4.26/1.79  #Partial instantiations: 0
% 4.26/1.79  #Strategies tried      : 1
% 4.26/1.79  
% 4.26/1.79  Timing (in seconds)
% 4.26/1.79  ----------------------
% 4.47/1.79  Preprocessing        : 0.37
% 4.47/1.79  Parsing              : 0.19
% 4.47/1.79  CNF conversion       : 0.03
% 4.47/1.80  Main loop            : 0.54
% 4.47/1.80  Inferencing          : 0.20
% 4.47/1.80  Reduction            : 0.18
% 4.47/1.80  Demodulation         : 0.13
% 4.47/1.80  BG Simplification    : 0.03
% 4.47/1.80  Subsumption          : 0.10
% 4.47/1.80  Abstraction          : 0.02
% 4.47/1.80  MUC search           : 0.00
% 4.47/1.80  Cooper               : 0.00
% 4.47/1.80  Total                : 1.00
% 4.47/1.80  Index Insertion      : 0.00
% 4.47/1.80  Index Deletion       : 0.00
% 4.47/1.80  Index Matching       : 0.00
% 4.47/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
