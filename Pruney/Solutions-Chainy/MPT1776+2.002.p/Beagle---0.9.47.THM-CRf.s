%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:29 EST 2020

% Result     : Theorem 4.48s
% Output     : CNFRefutation 4.87s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 437 expanded)
%              Number of leaves         :   44 ( 184 expanded)
%              Depth                    :   15
%              Number of atoms          :  510 (3366 expanded)
%              Number of equality atoms :   33 ( 164 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_326,negated_conjecture,(
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
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,B) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(D),u1_struct_0(A))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(A)))) )
                       => ( ( v1_tsep_1(C,B)
                            & m1_pre_topc(C,B)
                            & m1_pre_topc(C,D) )
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(D))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(C))
                                 => ( F = G
                                   => ( r1_tmap_1(D,A,E,F)
                                    <=> r1_tmap_1(C,A,k3_tmap_1(B,A,D,C,E),G) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_tmap_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_179,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_172,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_tsep_1(B,A)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
               => ( v1_tsep_1(B,C)
                  & m1_pre_topc(B,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tsep_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_148,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => k3_tmap_1(A,B,C,D,E) = k2_partfun1(u1_struct_0(C),u1_struct_0(B),E,u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_116,axiom,(
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

tff(f_261,axiom,(
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
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & v1_tsep_1(D,B)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(D))
                         => ( E = F
                           => ( r1_tmap_1(B,A,C,E)
                            <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).

tff(f_219,axiom,(
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
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(D))
                         => ( ( E = F
                              & r1_tmap_1(B,A,C,E) )
                           => r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_24,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_56,plain,(
    m1_pre_topc('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_54,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_50,plain,(
    '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_52,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_98,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52])).

tff(c_60,plain,(
    v1_tsep_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_72,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_76,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_68,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_126,plain,(
    ! [B_340,A_341] :
      ( l1_pre_topc(B_340)
      | ~ m1_pre_topc(B_340,A_341)
      | ~ l1_pre_topc(A_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_135,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_126])).

tff(c_142,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_135])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_78,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_40,plain,(
    ! [B_78,A_76] :
      ( m1_subset_1(u1_struct_0(B_78),k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ m1_pre_topc(B_78,A_76)
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_149,plain,(
    ! [B_344,A_345] :
      ( r2_hidden(B_344,A_345)
      | ~ m1_subset_1(B_344,A_345)
      | v1_xboole_0(A_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( r1_tarski(C_5,A_1)
      | ~ r2_hidden(C_5,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_191,plain,(
    ! [B_352,A_353] :
      ( r1_tarski(B_352,A_353)
      | ~ m1_subset_1(B_352,k1_zfmisc_1(A_353))
      | v1_xboole_0(k1_zfmisc_1(A_353)) ) ),
    inference(resolution,[status(thm)],[c_149,c_2])).

tff(c_202,plain,(
    ! [B_78,A_76] :
      ( r1_tarski(u1_struct_0(B_78),u1_struct_0(A_76))
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ m1_pre_topc(B_78,A_76)
      | ~ l1_pre_topc(A_76) ) ),
    inference(resolution,[status(thm)],[c_40,c_191])).

tff(c_486,plain,(
    ! [B_402,C_403,A_404] :
      ( v1_tsep_1(B_402,C_403)
      | ~ r1_tarski(u1_struct_0(B_402),u1_struct_0(C_403))
      | ~ m1_pre_topc(C_403,A_404)
      | v2_struct_0(C_403)
      | ~ m1_pre_topc(B_402,A_404)
      | ~ v1_tsep_1(B_402,A_404)
      | ~ l1_pre_topc(A_404)
      | ~ v2_pre_topc(A_404)
      | v2_struct_0(A_404) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_893,plain,(
    ! [B_445,A_446,A_447] :
      ( v1_tsep_1(B_445,A_446)
      | ~ m1_pre_topc(A_446,A_447)
      | v2_struct_0(A_446)
      | ~ m1_pre_topc(B_445,A_447)
      | ~ v1_tsep_1(B_445,A_447)
      | ~ l1_pre_topc(A_447)
      | ~ v2_pre_topc(A_447)
      | v2_struct_0(A_447)
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(A_446)))
      | ~ m1_pre_topc(B_445,A_446)
      | ~ l1_pre_topc(A_446) ) ),
    inference(resolution,[status(thm)],[c_202,c_486])).

tff(c_905,plain,(
    ! [B_445] :
      ( v1_tsep_1(B_445,'#skF_6')
      | v2_struct_0('#skF_6')
      | ~ m1_pre_topc(B_445,'#skF_4')
      | ~ v1_tsep_1(B_445,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_pre_topc(B_445,'#skF_6')
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_68,c_893])).

tff(c_928,plain,(
    ! [B_445] :
      ( v1_tsep_1(B_445,'#skF_6')
      | v2_struct_0('#skF_6')
      | ~ m1_pre_topc(B_445,'#skF_4')
      | ~ v1_tsep_1(B_445,'#skF_4')
      | v2_struct_0('#skF_4')
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_pre_topc(B_445,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_78,c_76,c_905])).

tff(c_929,plain,(
    ! [B_445] :
      ( v1_tsep_1(B_445,'#skF_6')
      | ~ m1_pre_topc(B_445,'#skF_4')
      | ~ v1_tsep_1(B_445,'#skF_4')
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_pre_topc(B_445,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_70,c_928])).

tff(c_974,plain,(
    v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_929])).

tff(c_183,plain,(
    ! [B_350,A_351] :
      ( m1_subset_1(u1_struct_0(B_350),k1_zfmisc_1(u1_struct_0(A_351)))
      | ~ m1_pre_topc(B_350,A_351)
      | ~ l1_pre_topc(A_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_20,plain,(
    ! [B_7,A_6] :
      ( v1_xboole_0(B_7)
      | ~ m1_subset_1(B_7,A_6)
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_187,plain,(
    ! [B_350,A_351] :
      ( v1_xboole_0(u1_struct_0(B_350))
      | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(A_351)))
      | ~ m1_pre_topc(B_350,A_351)
      | ~ l1_pre_topc(A_351) ) ),
    inference(resolution,[status(thm)],[c_183,c_20])).

tff(c_982,plain,(
    ! [B_350] :
      ( v1_xboole_0(u1_struct_0(B_350))
      | ~ m1_pre_topc(B_350,'#skF_6')
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_974,c_187])).

tff(c_986,plain,(
    ! [B_454] :
      ( v1_xboole_0(u1_struct_0(B_454))
      | ~ m1_pre_topc(B_454,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_982])).

tff(c_104,plain,(
    ! [B_333,A_334] :
      ( v1_xboole_0(B_333)
      | ~ m1_subset_1(B_333,A_334)
      | ~ v1_xboole_0(A_334) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_111,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_98,c_104])).

tff(c_118,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_992,plain,(
    ~ m1_pre_topc('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_986,c_118])).

tff(c_1000,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_992])).

tff(c_1036,plain,(
    ! [B_460] :
      ( v1_tsep_1(B_460,'#skF_6')
      | ~ m1_pre_topc(B_460,'#skF_4')
      | ~ v1_tsep_1(B_460,'#skF_4')
      | ~ m1_pre_topc(B_460,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_929])).

tff(c_86,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_88,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_3',k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7'),'#skF_9')
    | ~ r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_97,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_3',k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7'),'#skF_8')
    | ~ r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_88])).

tff(c_247,plain,(
    ~ r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_84,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_82,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_164,plain,(
    ! [B_348,A_349] :
      ( v2_pre_topc(B_348)
      | ~ m1_pre_topc(B_348,A_349)
      | ~ l1_pre_topc(A_349)
      | ~ v2_pre_topc(A_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_173,plain,
    ( v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_164])).

tff(c_182,plain,(
    v2_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_173])).

tff(c_66,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_64,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_62,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_747,plain,(
    ! [B_431,E_432,C_430,A_429,D_433] :
      ( k3_tmap_1(A_429,B_431,C_430,D_433,E_432) = k2_partfun1(u1_struct_0(C_430),u1_struct_0(B_431),E_432,u1_struct_0(D_433))
      | ~ m1_pre_topc(D_433,C_430)
      | ~ m1_subset_1(E_432,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_430),u1_struct_0(B_431))))
      | ~ v1_funct_2(E_432,u1_struct_0(C_430),u1_struct_0(B_431))
      | ~ v1_funct_1(E_432)
      | ~ m1_pre_topc(D_433,A_429)
      | ~ m1_pre_topc(C_430,A_429)
      | ~ l1_pre_topc(B_431)
      | ~ v2_pre_topc(B_431)
      | v2_struct_0(B_431)
      | ~ l1_pre_topc(A_429)
      | ~ v2_pre_topc(A_429)
      | v2_struct_0(A_429) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_764,plain,(
    ! [A_429,D_433] :
      ( k3_tmap_1(A_429,'#skF_3','#skF_6',D_433,'#skF_7') = k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0(D_433))
      | ~ m1_pre_topc(D_433,'#skF_6')
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_pre_topc(D_433,A_429)
      | ~ m1_pre_topc('#skF_6',A_429)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_429)
      | ~ v2_pre_topc(A_429)
      | v2_struct_0(A_429) ) ),
    inference(resolution,[status(thm)],[c_62,c_747])).

tff(c_772,plain,(
    ! [A_429,D_433] :
      ( k3_tmap_1(A_429,'#skF_3','#skF_6',D_433,'#skF_7') = k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0(D_433))
      | ~ m1_pre_topc(D_433,'#skF_6')
      | ~ m1_pre_topc(D_433,A_429)
      | ~ m1_pre_topc('#skF_6',A_429)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_429)
      | ~ v2_pre_topc(A_429)
      | v2_struct_0(A_429) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_66,c_64,c_764])).

tff(c_774,plain,(
    ! [A_434,D_435] :
      ( k3_tmap_1(A_434,'#skF_3','#skF_6',D_435,'#skF_7') = k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0(D_435))
      | ~ m1_pre_topc(D_435,'#skF_6')
      | ~ m1_pre_topc(D_435,A_434)
      | ~ m1_pre_topc('#skF_6',A_434)
      | ~ l1_pre_topc(A_434)
      | ~ v2_pre_topc(A_434)
      | v2_struct_0(A_434) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_772])).

tff(c_784,plain,
    ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7')
    | ~ m1_pre_topc('#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_774])).

tff(c_800,plain,
    ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_68,c_56,c_784])).

tff(c_801,plain,(
    k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_800])).

tff(c_579,plain,(
    ! [A_410,B_411,C_412,D_413] :
      ( k2_partfun1(u1_struct_0(A_410),u1_struct_0(B_411),C_412,u1_struct_0(D_413)) = k2_tmap_1(A_410,B_411,C_412,D_413)
      | ~ m1_pre_topc(D_413,A_410)
      | ~ m1_subset_1(C_412,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_410),u1_struct_0(B_411))))
      | ~ v1_funct_2(C_412,u1_struct_0(A_410),u1_struct_0(B_411))
      | ~ v1_funct_1(C_412)
      | ~ l1_pre_topc(B_411)
      | ~ v2_pre_topc(B_411)
      | v2_struct_0(B_411)
      | ~ l1_pre_topc(A_410)
      | ~ v2_pre_topc(A_410)
      | v2_struct_0(A_410) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_593,plain,(
    ! [D_413] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0(D_413)) = k2_tmap_1('#skF_6','#skF_3','#skF_7',D_413)
      | ~ m1_pre_topc(D_413,'#skF_6')
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_62,c_579])).

tff(c_600,plain,(
    ! [D_413] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0(D_413)) = k2_tmap_1('#skF_6','#skF_3','#skF_7',D_413)
      | ~ m1_pre_topc(D_413,'#skF_6')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_142,c_84,c_82,c_66,c_64,c_593])).

tff(c_601,plain,(
    ! [D_413] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0(D_413)) = k2_tmap_1('#skF_6','#skF_3','#skF_7',D_413)
      | ~ m1_pre_topc(D_413,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_86,c_600])).

tff(c_809,plain,
    ( k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7') = k2_tmap_1('#skF_6','#skF_3','#skF_7','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_801,c_601])).

tff(c_816,plain,(
    k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7') = k2_tmap_1('#skF_6','#skF_3','#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_809])).

tff(c_94,plain,
    ( r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8')
    | r1_tmap_1('#skF_5','#skF_3',k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_96,plain,
    ( r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8')
    | r1_tmap_1('#skF_5','#skF_3',k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_94])).

tff(c_300,plain,(
    r1_tmap_1('#skF_5','#skF_3',k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_247,c_96])).

tff(c_821,plain,(
    r1_tmap_1('#skF_5','#skF_3',k2_tmap_1('#skF_6','#skF_3','#skF_7','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_816,c_300])).

tff(c_936,plain,(
    ! [B_449,F_448,C_452,A_451,D_450] :
      ( r1_tmap_1(B_449,A_451,C_452,F_448)
      | ~ r1_tmap_1(D_450,A_451,k2_tmap_1(B_449,A_451,C_452,D_450),F_448)
      | ~ m1_subset_1(F_448,u1_struct_0(D_450))
      | ~ m1_subset_1(F_448,u1_struct_0(B_449))
      | ~ m1_pre_topc(D_450,B_449)
      | ~ v1_tsep_1(D_450,B_449)
      | v2_struct_0(D_450)
      | ~ m1_subset_1(C_452,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_449),u1_struct_0(A_451))))
      | ~ v1_funct_2(C_452,u1_struct_0(B_449),u1_struct_0(A_451))
      | ~ v1_funct_1(C_452)
      | ~ l1_pre_topc(B_449)
      | ~ v2_pre_topc(B_449)
      | v2_struct_0(B_449)
      | ~ l1_pre_topc(A_451)
      | ~ v2_pre_topc(A_451)
      | v2_struct_0(A_451) ) ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_940,plain,
    ( r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_pre_topc('#skF_5','#skF_6')
    | ~ v1_tsep_1('#skF_5','#skF_6')
    | v2_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_7')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_821,c_936])).

tff(c_947,plain,
    ( r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8')
    | ~ v1_tsep_1('#skF_5','#skF_6')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_182,c_142,c_66,c_64,c_62,c_56,c_54,c_98,c_940])).

tff(c_948,plain,(
    ~ v1_tsep_1('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_70,c_74,c_247,c_947])).

tff(c_1039,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ v1_tsep_1('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_1036,c_948])).

tff(c_1043,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_60,c_72,c_1039])).

tff(c_1045,plain,(
    r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_1611,plain,(
    ! [B_532,A_530,F_529,C_528,D_531] :
      ( r1_tmap_1(D_531,A_530,k2_tmap_1(B_532,A_530,C_528,D_531),F_529)
      | ~ r1_tmap_1(B_532,A_530,C_528,F_529)
      | ~ m1_subset_1(F_529,u1_struct_0(D_531))
      | ~ m1_subset_1(F_529,u1_struct_0(B_532))
      | ~ m1_pre_topc(D_531,B_532)
      | v2_struct_0(D_531)
      | ~ m1_subset_1(C_528,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_532),u1_struct_0(A_530))))
      | ~ v1_funct_2(C_528,u1_struct_0(B_532),u1_struct_0(A_530))
      | ~ v1_funct_1(C_528)
      | ~ l1_pre_topc(B_532)
      | ~ v2_pre_topc(B_532)
      | v2_struct_0(B_532)
      | ~ l1_pre_topc(A_530)
      | ~ v2_pre_topc(A_530)
      | v2_struct_0(A_530) ) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_1628,plain,(
    ! [D_531,F_529] :
      ( r1_tmap_1(D_531,'#skF_3',k2_tmap_1('#skF_6','#skF_3','#skF_7',D_531),F_529)
      | ~ r1_tmap_1('#skF_6','#skF_3','#skF_7',F_529)
      | ~ m1_subset_1(F_529,u1_struct_0(D_531))
      | ~ m1_subset_1(F_529,u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(D_531,'#skF_6')
      | v2_struct_0(D_531)
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_62,c_1611])).

tff(c_1636,plain,(
    ! [D_531,F_529] :
      ( r1_tmap_1(D_531,'#skF_3',k2_tmap_1('#skF_6','#skF_3','#skF_7',D_531),F_529)
      | ~ r1_tmap_1('#skF_6','#skF_3','#skF_7',F_529)
      | ~ m1_subset_1(F_529,u1_struct_0(D_531))
      | ~ m1_subset_1(F_529,u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(D_531,'#skF_6')
      | v2_struct_0(D_531)
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_182,c_142,c_66,c_64,c_1628])).

tff(c_1658,plain,(
    ! [D_533,F_534] :
      ( r1_tmap_1(D_533,'#skF_3',k2_tmap_1('#skF_6','#skF_3','#skF_7',D_533),F_534)
      | ~ r1_tmap_1('#skF_6','#skF_3','#skF_7',F_534)
      | ~ m1_subset_1(F_534,u1_struct_0(D_533))
      | ~ m1_subset_1(F_534,u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(D_533,'#skF_6')
      | v2_struct_0(D_533) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_70,c_1636])).

tff(c_1529,plain,(
    ! [A_517,C_518,E_520,D_521,B_519] :
      ( k3_tmap_1(A_517,B_519,C_518,D_521,E_520) = k2_partfun1(u1_struct_0(C_518),u1_struct_0(B_519),E_520,u1_struct_0(D_521))
      | ~ m1_pre_topc(D_521,C_518)
      | ~ m1_subset_1(E_520,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_518),u1_struct_0(B_519))))
      | ~ v1_funct_2(E_520,u1_struct_0(C_518),u1_struct_0(B_519))
      | ~ v1_funct_1(E_520)
      | ~ m1_pre_topc(D_521,A_517)
      | ~ m1_pre_topc(C_518,A_517)
      | ~ l1_pre_topc(B_519)
      | ~ v2_pre_topc(B_519)
      | v2_struct_0(B_519)
      | ~ l1_pre_topc(A_517)
      | ~ v2_pre_topc(A_517)
      | v2_struct_0(A_517) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1543,plain,(
    ! [A_517,D_521] :
      ( k3_tmap_1(A_517,'#skF_3','#skF_6',D_521,'#skF_7') = k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0(D_521))
      | ~ m1_pre_topc(D_521,'#skF_6')
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_pre_topc(D_521,A_517)
      | ~ m1_pre_topc('#skF_6',A_517)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_517)
      | ~ v2_pre_topc(A_517)
      | v2_struct_0(A_517) ) ),
    inference(resolution,[status(thm)],[c_62,c_1529])).

tff(c_1550,plain,(
    ! [A_517,D_521] :
      ( k3_tmap_1(A_517,'#skF_3','#skF_6',D_521,'#skF_7') = k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0(D_521))
      | ~ m1_pre_topc(D_521,'#skF_6')
      | ~ m1_pre_topc(D_521,A_517)
      | ~ m1_pre_topc('#skF_6',A_517)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_517)
      | ~ v2_pre_topc(A_517)
      | v2_struct_0(A_517) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_66,c_64,c_1543])).

tff(c_1579,plain,(
    ! [A_526,D_527] :
      ( k3_tmap_1(A_526,'#skF_3','#skF_6',D_527,'#skF_7') = k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0(D_527))
      | ~ m1_pre_topc(D_527,'#skF_6')
      | ~ m1_pre_topc(D_527,A_526)
      | ~ m1_pre_topc('#skF_6',A_526)
      | ~ l1_pre_topc(A_526)
      | ~ v2_pre_topc(A_526)
      | v2_struct_0(A_526) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1550])).

tff(c_1589,plain,
    ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7')
    | ~ m1_pre_topc('#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_1579])).

tff(c_1605,plain,
    ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_68,c_56,c_1589])).

tff(c_1606,plain,(
    k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1605])).

tff(c_1429,plain,(
    ! [A_507,B_508,C_509,D_510] :
      ( k2_partfun1(u1_struct_0(A_507),u1_struct_0(B_508),C_509,u1_struct_0(D_510)) = k2_tmap_1(A_507,B_508,C_509,D_510)
      | ~ m1_pre_topc(D_510,A_507)
      | ~ m1_subset_1(C_509,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_507),u1_struct_0(B_508))))
      | ~ v1_funct_2(C_509,u1_struct_0(A_507),u1_struct_0(B_508))
      | ~ v1_funct_1(C_509)
      | ~ l1_pre_topc(B_508)
      | ~ v2_pre_topc(B_508)
      | v2_struct_0(B_508)
      | ~ l1_pre_topc(A_507)
      | ~ v2_pre_topc(A_507)
      | v2_struct_0(A_507) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1443,plain,(
    ! [D_510] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0(D_510)) = k2_tmap_1('#skF_6','#skF_3','#skF_7',D_510)
      | ~ m1_pre_topc(D_510,'#skF_6')
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_62,c_1429])).

tff(c_1450,plain,(
    ! [D_510] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0(D_510)) = k2_tmap_1('#skF_6','#skF_3','#skF_7',D_510)
      | ~ m1_pre_topc(D_510,'#skF_6')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_142,c_84,c_82,c_66,c_64,c_1443])).

tff(c_1451,plain,(
    ! [D_510] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0(D_510)) = k2_tmap_1('#skF_6','#skF_3','#skF_7',D_510)
      | ~ m1_pre_topc(D_510,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_86,c_1450])).

tff(c_1641,plain,
    ( k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7') = k2_tmap_1('#skF_6','#skF_3','#skF_7','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1606,c_1451])).

tff(c_1648,plain,(
    k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7') = k2_tmap_1('#skF_6','#skF_3','#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1641])).

tff(c_1044,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3',k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_1653,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3',k2_tmap_1('#skF_6','#skF_3','#skF_7','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1648,c_1044])).

tff(c_1661,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_pre_topc('#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1658,c_1653])).

tff(c_1664,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_98,c_1045,c_1661])).

tff(c_1666,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1664])).

tff(c_1668,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_1674,plain,(
    ! [A_537] :
      ( ~ v1_xboole_0(u1_struct_0(A_537))
      | ~ l1_struct_0(A_537)
      | v2_struct_0(A_537) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1677,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1668,c_1674])).

tff(c_1680,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1677])).

tff(c_1684,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_1680])).

tff(c_1691,plain,(
    ! [B_542,A_543] :
      ( l1_pre_topc(B_542)
      | ~ m1_pre_topc(B_542,A_543)
      | ~ l1_pre_topc(A_543) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1697,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_1691])).

tff(c_1706,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1697])).

tff(c_1708,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1684,c_1706])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:43:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.48/1.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.48/1.91  
% 4.48/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.48/1.91  %$ r1_tmap_1 > v1_funct_2 > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1
% 4.48/1.91  
% 4.48/1.91  %Foreground sorts:
% 4.48/1.91  
% 4.48/1.91  
% 4.48/1.91  %Background operators:
% 4.48/1.91  
% 4.48/1.91  
% 4.48/1.91  %Foreground operators:
% 4.48/1.91  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.48/1.91  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.48/1.91  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.48/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.48/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.48/1.91  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.48/1.91  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.48/1.91  tff('#skF_7', type, '#skF_7': $i).
% 4.48/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.48/1.91  tff('#skF_5', type, '#skF_5': $i).
% 4.48/1.91  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.48/1.91  tff('#skF_6', type, '#skF_6': $i).
% 4.48/1.91  tff('#skF_3', type, '#skF_3': $i).
% 4.48/1.91  tff('#skF_9', type, '#skF_9': $i).
% 4.48/1.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.48/1.91  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.48/1.91  tff('#skF_8', type, '#skF_8': $i).
% 4.48/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.48/1.91  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.48/1.91  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 4.48/1.91  tff('#skF_4', type, '#skF_4': $i).
% 4.48/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.48/1.91  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.48/1.91  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.48/1.91  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 4.48/1.91  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.48/1.91  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 4.48/1.91  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.48/1.91  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.48/1.91  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.48/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.48/1.91  
% 4.87/1.94  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.87/1.94  tff(f_326, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (((v1_tsep_1(C, B) & m1_pre_topc(C, B)) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, A, E, F) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_tmap_1)).
% 4.87/1.94  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.87/1.94  tff(f_179, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.87/1.94  tff(f_45, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.87/1.94  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.87/1.94  tff(f_172, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) => (v1_tsep_1(B, C) & m1_pre_topc(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_tsep_1)).
% 4.87/1.94  tff(f_54, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.87/1.94  tff(f_148, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 4.87/1.94  tff(f_116, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 4.87/1.94  tff(f_261, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tmap_1)).
% 4.87/1.94  tff(f_219, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 4.87/1.94  tff(f_73, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.87/1.94  tff(c_24, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.87/1.94  tff(c_74, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_326])).
% 4.87/1.94  tff(c_56, plain, (m1_pre_topc('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_326])).
% 4.87/1.94  tff(c_54, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_326])).
% 4.87/1.94  tff(c_50, plain, ('#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_326])).
% 4.87/1.94  tff(c_52, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_326])).
% 4.87/1.94  tff(c_98, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52])).
% 4.87/1.94  tff(c_60, plain, (v1_tsep_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_326])).
% 4.87/1.94  tff(c_72, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_326])).
% 4.87/1.94  tff(c_76, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_326])).
% 4.87/1.94  tff(c_68, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_326])).
% 4.87/1.94  tff(c_126, plain, (![B_340, A_341]: (l1_pre_topc(B_340) | ~m1_pre_topc(B_340, A_341) | ~l1_pre_topc(A_341))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.87/1.94  tff(c_135, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_68, c_126])).
% 4.87/1.94  tff(c_142, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_135])).
% 4.87/1.94  tff(c_80, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_326])).
% 4.87/1.94  tff(c_70, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_326])).
% 4.87/1.94  tff(c_78, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_326])).
% 4.87/1.94  tff(c_40, plain, (![B_78, A_76]: (m1_subset_1(u1_struct_0(B_78), k1_zfmisc_1(u1_struct_0(A_76))) | ~m1_pre_topc(B_78, A_76) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.87/1.94  tff(c_149, plain, (![B_344, A_345]: (r2_hidden(B_344, A_345) | ~m1_subset_1(B_344, A_345) | v1_xboole_0(A_345))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.87/1.94  tff(c_2, plain, (![C_5, A_1]: (r1_tarski(C_5, A_1) | ~r2_hidden(C_5, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.87/1.94  tff(c_191, plain, (![B_352, A_353]: (r1_tarski(B_352, A_353) | ~m1_subset_1(B_352, k1_zfmisc_1(A_353)) | v1_xboole_0(k1_zfmisc_1(A_353)))), inference(resolution, [status(thm)], [c_149, c_2])).
% 4.87/1.94  tff(c_202, plain, (![B_78, A_76]: (r1_tarski(u1_struct_0(B_78), u1_struct_0(A_76)) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(A_76))) | ~m1_pre_topc(B_78, A_76) | ~l1_pre_topc(A_76))), inference(resolution, [status(thm)], [c_40, c_191])).
% 4.87/1.94  tff(c_486, plain, (![B_402, C_403, A_404]: (v1_tsep_1(B_402, C_403) | ~r1_tarski(u1_struct_0(B_402), u1_struct_0(C_403)) | ~m1_pre_topc(C_403, A_404) | v2_struct_0(C_403) | ~m1_pre_topc(B_402, A_404) | ~v1_tsep_1(B_402, A_404) | ~l1_pre_topc(A_404) | ~v2_pre_topc(A_404) | v2_struct_0(A_404))), inference(cnfTransformation, [status(thm)], [f_172])).
% 4.87/1.94  tff(c_893, plain, (![B_445, A_446, A_447]: (v1_tsep_1(B_445, A_446) | ~m1_pre_topc(A_446, A_447) | v2_struct_0(A_446) | ~m1_pre_topc(B_445, A_447) | ~v1_tsep_1(B_445, A_447) | ~l1_pre_topc(A_447) | ~v2_pre_topc(A_447) | v2_struct_0(A_447) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(A_446))) | ~m1_pre_topc(B_445, A_446) | ~l1_pre_topc(A_446))), inference(resolution, [status(thm)], [c_202, c_486])).
% 4.87/1.94  tff(c_905, plain, (![B_445]: (v1_tsep_1(B_445, '#skF_6') | v2_struct_0('#skF_6') | ~m1_pre_topc(B_445, '#skF_4') | ~v1_tsep_1(B_445, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_pre_topc(B_445, '#skF_6') | ~l1_pre_topc('#skF_6'))), inference(resolution, [status(thm)], [c_68, c_893])).
% 4.87/1.94  tff(c_928, plain, (![B_445]: (v1_tsep_1(B_445, '#skF_6') | v2_struct_0('#skF_6') | ~m1_pre_topc(B_445, '#skF_4') | ~v1_tsep_1(B_445, '#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_pre_topc(B_445, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_78, c_76, c_905])).
% 4.87/1.94  tff(c_929, plain, (![B_445]: (v1_tsep_1(B_445, '#skF_6') | ~m1_pre_topc(B_445, '#skF_4') | ~v1_tsep_1(B_445, '#skF_4') | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_pre_topc(B_445, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_80, c_70, c_928])).
% 4.87/1.94  tff(c_974, plain, (v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(splitLeft, [status(thm)], [c_929])).
% 4.87/1.94  tff(c_183, plain, (![B_350, A_351]: (m1_subset_1(u1_struct_0(B_350), k1_zfmisc_1(u1_struct_0(A_351))) | ~m1_pre_topc(B_350, A_351) | ~l1_pre_topc(A_351))), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.87/1.94  tff(c_20, plain, (![B_7, A_6]: (v1_xboole_0(B_7) | ~m1_subset_1(B_7, A_6) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.87/1.94  tff(c_187, plain, (![B_350, A_351]: (v1_xboole_0(u1_struct_0(B_350)) | ~v1_xboole_0(k1_zfmisc_1(u1_struct_0(A_351))) | ~m1_pre_topc(B_350, A_351) | ~l1_pre_topc(A_351))), inference(resolution, [status(thm)], [c_183, c_20])).
% 4.87/1.94  tff(c_982, plain, (![B_350]: (v1_xboole_0(u1_struct_0(B_350)) | ~m1_pre_topc(B_350, '#skF_6') | ~l1_pre_topc('#skF_6'))), inference(resolution, [status(thm)], [c_974, c_187])).
% 4.87/1.94  tff(c_986, plain, (![B_454]: (v1_xboole_0(u1_struct_0(B_454)) | ~m1_pre_topc(B_454, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_982])).
% 4.87/1.94  tff(c_104, plain, (![B_333, A_334]: (v1_xboole_0(B_333) | ~m1_subset_1(B_333, A_334) | ~v1_xboole_0(A_334))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.87/1.94  tff(c_111, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_98, c_104])).
% 4.87/1.94  tff(c_118, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_111])).
% 4.87/1.94  tff(c_992, plain, (~m1_pre_topc('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_986, c_118])).
% 4.87/1.94  tff(c_1000, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_992])).
% 4.87/1.94  tff(c_1036, plain, (![B_460]: (v1_tsep_1(B_460, '#skF_6') | ~m1_pre_topc(B_460, '#skF_4') | ~v1_tsep_1(B_460, '#skF_4') | ~m1_pre_topc(B_460, '#skF_6'))), inference(splitRight, [status(thm)], [c_929])).
% 4.87/1.94  tff(c_86, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_326])).
% 4.87/1.94  tff(c_88, plain, (~r1_tmap_1('#skF_5', '#skF_3', k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7'), '#skF_9') | ~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_326])).
% 4.87/1.94  tff(c_97, plain, (~r1_tmap_1('#skF_5', '#skF_3', k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7'), '#skF_8') | ~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_88])).
% 4.87/1.94  tff(c_247, plain, (~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_97])).
% 4.87/1.94  tff(c_84, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_326])).
% 4.87/1.94  tff(c_82, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_326])).
% 4.87/1.94  tff(c_164, plain, (![B_348, A_349]: (v2_pre_topc(B_348) | ~m1_pre_topc(B_348, A_349) | ~l1_pre_topc(A_349) | ~v2_pre_topc(A_349))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.87/1.94  tff(c_173, plain, (v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_68, c_164])).
% 4.87/1.94  tff(c_182, plain, (v2_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_173])).
% 4.87/1.94  tff(c_66, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_326])).
% 4.87/1.94  tff(c_64, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_326])).
% 4.87/1.94  tff(c_62, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_326])).
% 4.87/1.94  tff(c_747, plain, (![B_431, E_432, C_430, A_429, D_433]: (k3_tmap_1(A_429, B_431, C_430, D_433, E_432)=k2_partfun1(u1_struct_0(C_430), u1_struct_0(B_431), E_432, u1_struct_0(D_433)) | ~m1_pre_topc(D_433, C_430) | ~m1_subset_1(E_432, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_430), u1_struct_0(B_431)))) | ~v1_funct_2(E_432, u1_struct_0(C_430), u1_struct_0(B_431)) | ~v1_funct_1(E_432) | ~m1_pre_topc(D_433, A_429) | ~m1_pre_topc(C_430, A_429) | ~l1_pre_topc(B_431) | ~v2_pre_topc(B_431) | v2_struct_0(B_431) | ~l1_pre_topc(A_429) | ~v2_pre_topc(A_429) | v2_struct_0(A_429))), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.87/1.94  tff(c_764, plain, (![A_429, D_433]: (k3_tmap_1(A_429, '#skF_3', '#skF_6', D_433, '#skF_7')=k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0(D_433)) | ~m1_pre_topc(D_433, '#skF_6') | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~m1_pre_topc(D_433, A_429) | ~m1_pre_topc('#skF_6', A_429) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_429) | ~v2_pre_topc(A_429) | v2_struct_0(A_429))), inference(resolution, [status(thm)], [c_62, c_747])).
% 4.87/1.94  tff(c_772, plain, (![A_429, D_433]: (k3_tmap_1(A_429, '#skF_3', '#skF_6', D_433, '#skF_7')=k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0(D_433)) | ~m1_pre_topc(D_433, '#skF_6') | ~m1_pre_topc(D_433, A_429) | ~m1_pre_topc('#skF_6', A_429) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_429) | ~v2_pre_topc(A_429) | v2_struct_0(A_429))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_66, c_64, c_764])).
% 4.87/1.94  tff(c_774, plain, (![A_434, D_435]: (k3_tmap_1(A_434, '#skF_3', '#skF_6', D_435, '#skF_7')=k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0(D_435)) | ~m1_pre_topc(D_435, '#skF_6') | ~m1_pre_topc(D_435, A_434) | ~m1_pre_topc('#skF_6', A_434) | ~l1_pre_topc(A_434) | ~v2_pre_topc(A_434) | v2_struct_0(A_434))), inference(negUnitSimplification, [status(thm)], [c_86, c_772])).
% 4.87/1.94  tff(c_784, plain, (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7') | ~m1_pre_topc('#skF_5', '#skF_6') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_72, c_774])).
% 4.87/1.94  tff(c_800, plain, (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_68, c_56, c_784])).
% 4.87/1.94  tff(c_801, plain, (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_80, c_800])).
% 4.87/1.94  tff(c_579, plain, (![A_410, B_411, C_412, D_413]: (k2_partfun1(u1_struct_0(A_410), u1_struct_0(B_411), C_412, u1_struct_0(D_413))=k2_tmap_1(A_410, B_411, C_412, D_413) | ~m1_pre_topc(D_413, A_410) | ~m1_subset_1(C_412, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_410), u1_struct_0(B_411)))) | ~v1_funct_2(C_412, u1_struct_0(A_410), u1_struct_0(B_411)) | ~v1_funct_1(C_412) | ~l1_pre_topc(B_411) | ~v2_pre_topc(B_411) | v2_struct_0(B_411) | ~l1_pre_topc(A_410) | ~v2_pre_topc(A_410) | v2_struct_0(A_410))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.87/1.94  tff(c_593, plain, (![D_413]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0(D_413))=k2_tmap_1('#skF_6', '#skF_3', '#skF_7', D_413) | ~m1_pre_topc(D_413, '#skF_6') | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_62, c_579])).
% 4.87/1.94  tff(c_600, plain, (![D_413]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0(D_413))=k2_tmap_1('#skF_6', '#skF_3', '#skF_7', D_413) | ~m1_pre_topc(D_413, '#skF_6') | v2_struct_0('#skF_3') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_142, c_84, c_82, c_66, c_64, c_593])).
% 4.87/1.94  tff(c_601, plain, (![D_413]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0(D_413))=k2_tmap_1('#skF_6', '#skF_3', '#skF_7', D_413) | ~m1_pre_topc(D_413, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_70, c_86, c_600])).
% 4.87/1.94  tff(c_809, plain, (k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7')=k2_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_801, c_601])).
% 4.87/1.94  tff(c_816, plain, (k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7')=k2_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_809])).
% 4.87/1.94  tff(c_94, plain, (r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8') | r1_tmap_1('#skF_5', '#skF_3', k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_326])).
% 4.87/1.94  tff(c_96, plain, (r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8') | r1_tmap_1('#skF_5', '#skF_3', k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_94])).
% 4.87/1.94  tff(c_300, plain, (r1_tmap_1('#skF_5', '#skF_3', k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_247, c_96])).
% 4.87/1.94  tff(c_821, plain, (r1_tmap_1('#skF_5', '#skF_3', k2_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_816, c_300])).
% 4.87/1.94  tff(c_936, plain, (![B_449, F_448, C_452, A_451, D_450]: (r1_tmap_1(B_449, A_451, C_452, F_448) | ~r1_tmap_1(D_450, A_451, k2_tmap_1(B_449, A_451, C_452, D_450), F_448) | ~m1_subset_1(F_448, u1_struct_0(D_450)) | ~m1_subset_1(F_448, u1_struct_0(B_449)) | ~m1_pre_topc(D_450, B_449) | ~v1_tsep_1(D_450, B_449) | v2_struct_0(D_450) | ~m1_subset_1(C_452, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_449), u1_struct_0(A_451)))) | ~v1_funct_2(C_452, u1_struct_0(B_449), u1_struct_0(A_451)) | ~v1_funct_1(C_452) | ~l1_pre_topc(B_449) | ~v2_pre_topc(B_449) | v2_struct_0(B_449) | ~l1_pre_topc(A_451) | ~v2_pre_topc(A_451) | v2_struct_0(A_451))), inference(cnfTransformation, [status(thm)], [f_261])).
% 4.87/1.94  tff(c_940, plain, (r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_pre_topc('#skF_5', '#skF_6') | ~v1_tsep_1('#skF_5', '#skF_6') | v2_struct_0('#skF_5') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_821, c_936])).
% 4.87/1.94  tff(c_947, plain, (r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8') | ~v1_tsep_1('#skF_5', '#skF_6') | v2_struct_0('#skF_5') | v2_struct_0('#skF_6') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_182, c_142, c_66, c_64, c_62, c_56, c_54, c_98, c_940])).
% 4.87/1.94  tff(c_948, plain, (~v1_tsep_1('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_86, c_70, c_74, c_247, c_947])).
% 4.87/1.94  tff(c_1039, plain, (~m1_pre_topc('#skF_5', '#skF_4') | ~v1_tsep_1('#skF_5', '#skF_4') | ~m1_pre_topc('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_1036, c_948])).
% 4.87/1.94  tff(c_1043, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_60, c_72, c_1039])).
% 4.87/1.94  tff(c_1045, plain, (r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_97])).
% 4.87/1.94  tff(c_1611, plain, (![B_532, A_530, F_529, C_528, D_531]: (r1_tmap_1(D_531, A_530, k2_tmap_1(B_532, A_530, C_528, D_531), F_529) | ~r1_tmap_1(B_532, A_530, C_528, F_529) | ~m1_subset_1(F_529, u1_struct_0(D_531)) | ~m1_subset_1(F_529, u1_struct_0(B_532)) | ~m1_pre_topc(D_531, B_532) | v2_struct_0(D_531) | ~m1_subset_1(C_528, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_532), u1_struct_0(A_530)))) | ~v1_funct_2(C_528, u1_struct_0(B_532), u1_struct_0(A_530)) | ~v1_funct_1(C_528) | ~l1_pre_topc(B_532) | ~v2_pre_topc(B_532) | v2_struct_0(B_532) | ~l1_pre_topc(A_530) | ~v2_pre_topc(A_530) | v2_struct_0(A_530))), inference(cnfTransformation, [status(thm)], [f_219])).
% 4.87/1.94  tff(c_1628, plain, (![D_531, F_529]: (r1_tmap_1(D_531, '#skF_3', k2_tmap_1('#skF_6', '#skF_3', '#skF_7', D_531), F_529) | ~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', F_529) | ~m1_subset_1(F_529, u1_struct_0(D_531)) | ~m1_subset_1(F_529, u1_struct_0('#skF_6')) | ~m1_pre_topc(D_531, '#skF_6') | v2_struct_0(D_531) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_62, c_1611])).
% 4.87/1.94  tff(c_1636, plain, (![D_531, F_529]: (r1_tmap_1(D_531, '#skF_3', k2_tmap_1('#skF_6', '#skF_3', '#skF_7', D_531), F_529) | ~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', F_529) | ~m1_subset_1(F_529, u1_struct_0(D_531)) | ~m1_subset_1(F_529, u1_struct_0('#skF_6')) | ~m1_pre_topc(D_531, '#skF_6') | v2_struct_0(D_531) | v2_struct_0('#skF_6') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_182, c_142, c_66, c_64, c_1628])).
% 4.87/1.94  tff(c_1658, plain, (![D_533, F_534]: (r1_tmap_1(D_533, '#skF_3', k2_tmap_1('#skF_6', '#skF_3', '#skF_7', D_533), F_534) | ~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', F_534) | ~m1_subset_1(F_534, u1_struct_0(D_533)) | ~m1_subset_1(F_534, u1_struct_0('#skF_6')) | ~m1_pre_topc(D_533, '#skF_6') | v2_struct_0(D_533))), inference(negUnitSimplification, [status(thm)], [c_86, c_70, c_1636])).
% 4.87/1.94  tff(c_1529, plain, (![A_517, C_518, E_520, D_521, B_519]: (k3_tmap_1(A_517, B_519, C_518, D_521, E_520)=k2_partfun1(u1_struct_0(C_518), u1_struct_0(B_519), E_520, u1_struct_0(D_521)) | ~m1_pre_topc(D_521, C_518) | ~m1_subset_1(E_520, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_518), u1_struct_0(B_519)))) | ~v1_funct_2(E_520, u1_struct_0(C_518), u1_struct_0(B_519)) | ~v1_funct_1(E_520) | ~m1_pre_topc(D_521, A_517) | ~m1_pre_topc(C_518, A_517) | ~l1_pre_topc(B_519) | ~v2_pre_topc(B_519) | v2_struct_0(B_519) | ~l1_pre_topc(A_517) | ~v2_pre_topc(A_517) | v2_struct_0(A_517))), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.87/1.94  tff(c_1543, plain, (![A_517, D_521]: (k3_tmap_1(A_517, '#skF_3', '#skF_6', D_521, '#skF_7')=k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0(D_521)) | ~m1_pre_topc(D_521, '#skF_6') | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~m1_pre_topc(D_521, A_517) | ~m1_pre_topc('#skF_6', A_517) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_517) | ~v2_pre_topc(A_517) | v2_struct_0(A_517))), inference(resolution, [status(thm)], [c_62, c_1529])).
% 4.87/1.94  tff(c_1550, plain, (![A_517, D_521]: (k3_tmap_1(A_517, '#skF_3', '#skF_6', D_521, '#skF_7')=k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0(D_521)) | ~m1_pre_topc(D_521, '#skF_6') | ~m1_pre_topc(D_521, A_517) | ~m1_pre_topc('#skF_6', A_517) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_517) | ~v2_pre_topc(A_517) | v2_struct_0(A_517))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_66, c_64, c_1543])).
% 4.87/1.94  tff(c_1579, plain, (![A_526, D_527]: (k3_tmap_1(A_526, '#skF_3', '#skF_6', D_527, '#skF_7')=k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0(D_527)) | ~m1_pre_topc(D_527, '#skF_6') | ~m1_pre_topc(D_527, A_526) | ~m1_pre_topc('#skF_6', A_526) | ~l1_pre_topc(A_526) | ~v2_pre_topc(A_526) | v2_struct_0(A_526))), inference(negUnitSimplification, [status(thm)], [c_86, c_1550])).
% 4.87/1.94  tff(c_1589, plain, (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7') | ~m1_pre_topc('#skF_5', '#skF_6') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_72, c_1579])).
% 4.87/1.94  tff(c_1605, plain, (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_68, c_56, c_1589])).
% 4.87/1.94  tff(c_1606, plain, (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_80, c_1605])).
% 4.87/1.94  tff(c_1429, plain, (![A_507, B_508, C_509, D_510]: (k2_partfun1(u1_struct_0(A_507), u1_struct_0(B_508), C_509, u1_struct_0(D_510))=k2_tmap_1(A_507, B_508, C_509, D_510) | ~m1_pre_topc(D_510, A_507) | ~m1_subset_1(C_509, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_507), u1_struct_0(B_508)))) | ~v1_funct_2(C_509, u1_struct_0(A_507), u1_struct_0(B_508)) | ~v1_funct_1(C_509) | ~l1_pre_topc(B_508) | ~v2_pre_topc(B_508) | v2_struct_0(B_508) | ~l1_pre_topc(A_507) | ~v2_pre_topc(A_507) | v2_struct_0(A_507))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.87/1.94  tff(c_1443, plain, (![D_510]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0(D_510))=k2_tmap_1('#skF_6', '#skF_3', '#skF_7', D_510) | ~m1_pre_topc(D_510, '#skF_6') | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_62, c_1429])).
% 4.87/1.94  tff(c_1450, plain, (![D_510]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0(D_510))=k2_tmap_1('#skF_6', '#skF_3', '#skF_7', D_510) | ~m1_pre_topc(D_510, '#skF_6') | v2_struct_0('#skF_3') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_142, c_84, c_82, c_66, c_64, c_1443])).
% 4.87/1.94  tff(c_1451, plain, (![D_510]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0(D_510))=k2_tmap_1('#skF_6', '#skF_3', '#skF_7', D_510) | ~m1_pre_topc(D_510, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_70, c_86, c_1450])).
% 4.87/1.94  tff(c_1641, plain, (k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7')=k2_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1606, c_1451])).
% 4.87/1.94  tff(c_1648, plain, (k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7')=k2_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1641])).
% 4.87/1.94  tff(c_1044, plain, (~r1_tmap_1('#skF_5', '#skF_3', k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7'), '#skF_8')), inference(splitRight, [status(thm)], [c_97])).
% 4.87/1.94  tff(c_1653, plain, (~r1_tmap_1('#skF_5', '#skF_3', k2_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1648, c_1044])).
% 4.87/1.94  tff(c_1661, plain, (~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_pre_topc('#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1658, c_1653])).
% 4.87/1.94  tff(c_1664, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_98, c_1045, c_1661])).
% 4.87/1.94  tff(c_1666, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_1664])).
% 4.87/1.94  tff(c_1668, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_111])).
% 4.87/1.94  tff(c_1674, plain, (![A_537]: (~v1_xboole_0(u1_struct_0(A_537)) | ~l1_struct_0(A_537) | v2_struct_0(A_537))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.87/1.94  tff(c_1677, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1668, c_1674])).
% 4.87/1.94  tff(c_1680, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_74, c_1677])).
% 4.87/1.94  tff(c_1684, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_24, c_1680])).
% 4.87/1.94  tff(c_1691, plain, (![B_542, A_543]: (l1_pre_topc(B_542) | ~m1_pre_topc(B_542, A_543) | ~l1_pre_topc(A_543))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.87/1.94  tff(c_1697, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_72, c_1691])).
% 4.87/1.94  tff(c_1706, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1697])).
% 4.87/1.94  tff(c_1708, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1684, c_1706])).
% 4.87/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.87/1.94  
% 4.87/1.94  Inference rules
% 4.87/1.94  ----------------------
% 4.87/1.94  #Ref     : 0
% 4.87/1.94  #Sup     : 309
% 4.87/1.94  #Fact    : 0
% 4.87/1.94  #Define  : 0
% 4.87/1.94  #Split   : 15
% 4.87/1.94  #Chain   : 0
% 4.87/1.94  #Close   : 0
% 4.87/1.94  
% 4.87/1.94  Ordering : KBO
% 4.87/1.94  
% 4.87/1.94  Simplification rules
% 4.87/1.94  ----------------------
% 4.87/1.94  #Subsume      : 77
% 4.87/1.94  #Demod        : 368
% 4.87/1.94  #Tautology    : 101
% 4.87/1.94  #SimpNegUnit  : 85
% 4.87/1.94  #BackRed      : 4
% 4.87/1.94  
% 4.87/1.94  #Partial instantiations: 0
% 4.87/1.94  #Strategies tried      : 1
% 4.87/1.94  
% 4.87/1.94  Timing (in seconds)
% 4.87/1.94  ----------------------
% 4.87/1.94  Preprocessing        : 0.48
% 4.87/1.94  Parsing              : 0.26
% 4.87/1.94  CNF conversion       : 0.05
% 4.87/1.94  Main loop            : 0.60
% 4.87/1.94  Inferencing          : 0.20
% 4.87/1.94  Reduction            : 0.19
% 4.87/1.94  Demodulation         : 0.13
% 4.87/1.94  BG Simplification    : 0.03
% 4.87/1.94  Subsumption          : 0.13
% 4.87/1.94  Abstraction          : 0.03
% 4.87/1.94  MUC search           : 0.00
% 4.87/1.94  Cooper               : 0.00
% 4.87/1.94  Total                : 1.13
% 4.87/1.94  Index Insertion      : 0.00
% 4.87/1.94  Index Deletion       : 0.00
% 4.87/1.94  Index Matching       : 0.00
% 4.87/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
