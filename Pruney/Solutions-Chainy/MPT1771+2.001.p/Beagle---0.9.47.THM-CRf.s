%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:20 EST 2020

% Result     : Theorem 8.27s
% Output     : CNFRefutation 8.27s
% Verified   : 
% Statistics : Number of formulae       :  218 (8765 expanded)
%              Number of leaves         :   38 (3442 expanded)
%              Depth                    :   32
%              Number of atoms          : 1068 (79326 expanded)
%              Number of equality atoms :   46 (4878 expanded)
%              Maximal formula depth    :   27 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > r1_tmap_1 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_335,negated_conjecture,(
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
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                       => ( m1_pre_topc(C,D)
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(D))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(C))
                                 => ( ( F = G
                                      & r1_tmap_1(D,B,k2_tmap_1(A,B,E,D),F) )
                                   => r1_tmap_1(C,B,k2_tmap_1(A,B,E,C),G) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_tmap_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_154,axiom,(
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

tff(f_188,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_136,axiom,(
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

tff(f_104,axiom,(
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

tff(f_184,axiom,(
    ! [A,B,C,D,E] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & m1_pre_topc(C,A)
        & m1_pre_topc(D,A)
        & v1_funct_1(E)
        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
     => ( v1_funct_1(k3_tmap_1(A,B,C,D,E))
        & v1_funct_2(k3_tmap_1(A,B,C,D,E),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k3_tmap_1(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_274,axiom,(
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
                 => ! [E] :
                      ( ( ~ v2_struct_0(E)
                        & m1_pre_topc(E,A) )
                     => ( ( m1_pre_topc(D,C)
                          & m1_pre_topc(E,D) )
                       => ! [F] :
                            ( ( v1_funct_1(F)
                              & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                              & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                           => r2_funct_2(u1_struct_0(E),u1_struct_0(B),k3_tmap_1(A,B,D,E,k3_tmap_1(A,B,C,D,F)),k3_tmap_1(A,B,C,E,F)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tmap_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_228,axiom,(
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

tff(c_46,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_335])).

tff(c_42,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_335])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_335])).

tff(c_75,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44])).

tff(c_40,plain,(
    r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_335])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_335])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_335])).

tff(c_70,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_335])).

tff(c_56,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_335])).

tff(c_83,plain,(
    ! [B_330,A_331] :
      ( l1_pre_topc(B_330)
      | ~ m1_pre_topc(B_330,A_331)
      | ~ l1_pre_topc(A_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_92,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_83])).

tff(c_102,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_92])).

tff(c_8,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_64,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_335])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_335])).

tff(c_52,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_335])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_335])).

tff(c_307,plain,(
    ! [A_355,B_356,C_357,D_358] :
      ( v1_funct_1(k2_tmap_1(A_355,B_356,C_357,D_358))
      | ~ l1_struct_0(D_358)
      | ~ m1_subset_1(C_357,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_355),u1_struct_0(B_356))))
      | ~ v1_funct_2(C_357,u1_struct_0(A_355),u1_struct_0(B_356))
      | ~ v1_funct_1(C_357)
      | ~ l1_struct_0(B_356)
      | ~ l1_struct_0(A_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_309,plain,(
    ! [D_358] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_358))
      | ~ l1_struct_0(D_358)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_50,c_307])).

tff(c_312,plain,(
    ! [D_358] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_358))
      | ~ l1_struct_0(D_358)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_309])).

tff(c_313,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_312])).

tff(c_316,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_313])).

tff(c_320,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_316])).

tff(c_321,plain,(
    ! [D_358] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_358))
      | ~ l1_struct_0(D_358) ) ),
    inference(splitRight,[status(thm)],[c_312])).

tff(c_357,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_321])).

tff(c_360,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_357])).

tff(c_364,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_360])).

tff(c_366,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_321])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_335])).

tff(c_72,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_335])).

tff(c_30,plain,(
    ! [A_74] :
      ( m1_pre_topc(A_74,A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_60,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_335])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_335])).

tff(c_66,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_335])).

tff(c_493,plain,(
    ! [C_410,A_408,D_411,B_409,E_412] :
      ( k3_tmap_1(A_408,B_409,C_410,D_411,E_412) = k2_partfun1(u1_struct_0(C_410),u1_struct_0(B_409),E_412,u1_struct_0(D_411))
      | ~ m1_pre_topc(D_411,C_410)
      | ~ m1_subset_1(E_412,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_410),u1_struct_0(B_409))))
      | ~ v1_funct_2(E_412,u1_struct_0(C_410),u1_struct_0(B_409))
      | ~ v1_funct_1(E_412)
      | ~ m1_pre_topc(D_411,A_408)
      | ~ m1_pre_topc(C_410,A_408)
      | ~ l1_pre_topc(B_409)
      | ~ v2_pre_topc(B_409)
      | v2_struct_0(B_409)
      | ~ l1_pre_topc(A_408)
      | ~ v2_pre_topc(A_408)
      | v2_struct_0(A_408) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_499,plain,(
    ! [A_408,D_411] :
      ( k3_tmap_1(A_408,'#skF_2','#skF_1',D_411,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_411))
      | ~ m1_pre_topc(D_411,'#skF_1')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_411,A_408)
      | ~ m1_pre_topc('#skF_1',A_408)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_408)
      | ~ v2_pre_topc(A_408)
      | v2_struct_0(A_408) ) ),
    inference(resolution,[status(thm)],[c_50,c_493])).

tff(c_504,plain,(
    ! [A_408,D_411] :
      ( k3_tmap_1(A_408,'#skF_2','#skF_1',D_411,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_411))
      | ~ m1_pre_topc(D_411,'#skF_1')
      | ~ m1_pre_topc(D_411,A_408)
      | ~ m1_pre_topc('#skF_1',A_408)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_408)
      | ~ v2_pre_topc(A_408)
      | v2_struct_0(A_408) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_54,c_52,c_499])).

tff(c_506,plain,(
    ! [A_413,D_414] :
      ( k3_tmap_1(A_413,'#skF_2','#skF_1',D_414,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_414))
      | ~ m1_pre_topc(D_414,'#skF_1')
      | ~ m1_pre_topc(D_414,A_413)
      | ~ m1_pre_topc('#skF_1',A_413)
      | ~ l1_pre_topc(A_413)
      | ~ v2_pre_topc(A_413)
      | v2_struct_0(A_413) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_504])).

tff(c_514,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_506])).

tff(c_528,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_60,c_514])).

tff(c_529,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_528])).

tff(c_538,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_529])).

tff(c_541,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_538])).

tff(c_545,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_541])).

tff(c_547,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_529])).

tff(c_516,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_506])).

tff(c_532,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_56,c_516])).

tff(c_533,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_532])).

tff(c_875,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_533])).

tff(c_437,plain,(
    ! [A_384,B_385,C_386,D_387] :
      ( k2_partfun1(u1_struct_0(A_384),u1_struct_0(B_385),C_386,u1_struct_0(D_387)) = k2_tmap_1(A_384,B_385,C_386,D_387)
      | ~ m1_pre_topc(D_387,A_384)
      | ~ m1_subset_1(C_386,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_384),u1_struct_0(B_385))))
      | ~ v1_funct_2(C_386,u1_struct_0(A_384),u1_struct_0(B_385))
      | ~ v1_funct_1(C_386)
      | ~ l1_pre_topc(B_385)
      | ~ v2_pre_topc(B_385)
      | v2_struct_0(B_385)
      | ~ l1_pre_topc(A_384)
      | ~ v2_pre_topc(A_384)
      | v2_struct_0(A_384) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_441,plain,(
    ! [D_387] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_387)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_387)
      | ~ m1_pre_topc(D_387,'#skF_1')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_50,c_437])).

tff(c_445,plain,(
    ! [D_387] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_387)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_387)
      | ~ m1_pre_topc(D_387,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_54,c_52,c_441])).

tff(c_446,plain,(
    ! [D_387] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_387)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_387)
      | ~ m1_pre_topc(D_387,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_445])).

tff(c_879,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_875,c_446])).

tff(c_886,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_879])).

tff(c_426,plain,(
    ! [C_381,D_379,A_378,B_377,E_380] :
      ( v1_funct_1(k3_tmap_1(A_378,B_377,C_381,D_379,E_380))
      | ~ m1_subset_1(E_380,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_381),u1_struct_0(B_377))))
      | ~ v1_funct_2(E_380,u1_struct_0(C_381),u1_struct_0(B_377))
      | ~ v1_funct_1(E_380)
      | ~ m1_pre_topc(D_379,A_378)
      | ~ m1_pre_topc(C_381,A_378)
      | ~ l1_pre_topc(B_377)
      | ~ v2_pre_topc(B_377)
      | v2_struct_0(B_377)
      | ~ l1_pre_topc(A_378)
      | ~ v2_pre_topc(A_378)
      | v2_struct_0(A_378) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_430,plain,(
    ! [A_378,D_379] :
      ( v1_funct_1(k3_tmap_1(A_378,'#skF_2','#skF_1',D_379,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_379,A_378)
      | ~ m1_pre_topc('#skF_1',A_378)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_378)
      | ~ v2_pre_topc(A_378)
      | v2_struct_0(A_378) ) ),
    inference(resolution,[status(thm)],[c_50,c_426])).

tff(c_434,plain,(
    ! [A_378,D_379] :
      ( v1_funct_1(k3_tmap_1(A_378,'#skF_2','#skF_1',D_379,'#skF_5'))
      | ~ m1_pre_topc(D_379,A_378)
      | ~ m1_pre_topc('#skF_1',A_378)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_378)
      | ~ v2_pre_topc(A_378)
      | v2_struct_0(A_378) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_54,c_52,c_430])).

tff(c_435,plain,(
    ! [A_378,D_379] :
      ( v1_funct_1(k3_tmap_1(A_378,'#skF_2','#skF_1',D_379,'#skF_5'))
      | ~ m1_pre_topc(D_379,A_378)
      | ~ m1_pre_topc('#skF_1',A_378)
      | ~ l1_pre_topc(A_378)
      | ~ v2_pre_topc(A_378)
      | v2_struct_0(A_378) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_434])).

tff(c_906,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_886,c_435])).

tff(c_922,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_547,c_56,c_906])).

tff(c_923,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_922])).

tff(c_456,plain,(
    ! [D_391,A_390,E_392,B_389,C_393] :
      ( v1_funct_2(k3_tmap_1(A_390,B_389,C_393,D_391,E_392),u1_struct_0(D_391),u1_struct_0(B_389))
      | ~ m1_subset_1(E_392,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_393),u1_struct_0(B_389))))
      | ~ v1_funct_2(E_392,u1_struct_0(C_393),u1_struct_0(B_389))
      | ~ v1_funct_1(E_392)
      | ~ m1_pre_topc(D_391,A_390)
      | ~ m1_pre_topc(C_393,A_390)
      | ~ l1_pre_topc(B_389)
      | ~ v2_pre_topc(B_389)
      | v2_struct_0(B_389)
      | ~ l1_pre_topc(A_390)
      | ~ v2_pre_topc(A_390)
      | v2_struct_0(A_390) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_460,plain,(
    ! [A_390,D_391] :
      ( v1_funct_2(k3_tmap_1(A_390,'#skF_2','#skF_1',D_391,'#skF_5'),u1_struct_0(D_391),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_391,A_390)
      | ~ m1_pre_topc('#skF_1',A_390)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_390)
      | ~ v2_pre_topc(A_390)
      | v2_struct_0(A_390) ) ),
    inference(resolution,[status(thm)],[c_50,c_456])).

tff(c_464,plain,(
    ! [A_390,D_391] :
      ( v1_funct_2(k3_tmap_1(A_390,'#skF_2','#skF_1',D_391,'#skF_5'),u1_struct_0(D_391),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_391,A_390)
      | ~ m1_pre_topc('#skF_1',A_390)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_390)
      | ~ v2_pre_topc(A_390)
      | v2_struct_0(A_390) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_54,c_52,c_460])).

tff(c_465,plain,(
    ! [A_390,D_391] :
      ( v1_funct_2(k3_tmap_1(A_390,'#skF_2','#skF_1',D_391,'#skF_5'),u1_struct_0(D_391),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_391,A_390)
      | ~ m1_pre_topc('#skF_1',A_390)
      | ~ l1_pre_topc(A_390)
      | ~ v2_pre_topc(A_390)
      | v2_struct_0(A_390) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_464])).

tff(c_903,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_886,c_465])).

tff(c_919,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_547,c_56,c_903])).

tff(c_920,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_919])).

tff(c_24,plain,(
    ! [B_70,E_73,D_72,C_71,A_69] :
      ( m1_subset_1(k3_tmap_1(A_69,B_70,C_71,D_72,E_73),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_72),u1_struct_0(B_70))))
      | ~ m1_subset_1(E_73,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_71),u1_struct_0(B_70))))
      | ~ v1_funct_2(E_73,u1_struct_0(C_71),u1_struct_0(B_70))
      | ~ v1_funct_1(E_73)
      | ~ m1_pre_topc(D_72,A_69)
      | ~ m1_pre_topc(C_71,A_69)
      | ~ l1_pre_topc(B_70)
      | ~ v2_pre_topc(B_70)
      | v2_struct_0(B_70)
      | ~ l1_pre_topc(A_69)
      | ~ v2_pre_topc(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_900,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_886,c_24])).

tff(c_916,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_547,c_56,c_54,c_52,c_50,c_900])).

tff(c_917,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_916])).

tff(c_22,plain,(
    ! [A_65,B_66,C_67,D_68] :
      ( v1_funct_1(k2_tmap_1(A_65,B_66,C_67,D_68))
      | ~ l1_struct_0(D_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_65),u1_struct_0(B_66))))
      | ~ v1_funct_2(C_67,u1_struct_0(A_65),u1_struct_0(B_66))
      | ~ v1_funct_1(C_67)
      | ~ l1_struct_0(B_66)
      | ~ l1_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_944,plain,(
    ! [D_68] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),D_68))
      | ~ l1_struct_0(D_68)
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_917,c_22])).

tff(c_972,plain,(
    ! [D_68] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),D_68))
      | ~ l1_struct_0(D_68)
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_923,c_920,c_944])).

tff(c_997,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_972])).

tff(c_1000,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_997])).

tff(c_1004,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_1000])).

tff(c_1006,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_972])).

tff(c_106,plain,(
    ! [B_332,A_333] :
      ( v2_pre_topc(B_332)
      | ~ m1_pre_topc(B_332,A_333)
      | ~ l1_pre_topc(A_333)
      | ~ v2_pre_topc(A_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_115,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_106])).

tff(c_125,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_115])).

tff(c_48,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_335])).

tff(c_322,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_312])).

tff(c_18,plain,(
    ! [A_65,B_66,C_67,D_68] :
      ( m1_subset_1(k2_tmap_1(A_65,B_66,C_67,D_68),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_68),u1_struct_0(B_66))))
      | ~ l1_struct_0(D_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_65),u1_struct_0(B_66))))
      | ~ v1_funct_2(C_67,u1_struct_0(A_65),u1_struct_0(B_66))
      | ~ v1_funct_1(C_67)
      | ~ l1_struct_0(B_66)
      | ~ l1_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1920,plain,(
    ! [C_518,D_517,D_516,B_519,A_520] :
      ( k2_partfun1(u1_struct_0(D_517),u1_struct_0(B_519),k2_tmap_1(A_520,B_519,C_518,D_517),u1_struct_0(D_516)) = k2_tmap_1(D_517,B_519,k2_tmap_1(A_520,B_519,C_518,D_517),D_516)
      | ~ m1_pre_topc(D_516,D_517)
      | ~ v1_funct_2(k2_tmap_1(A_520,B_519,C_518,D_517),u1_struct_0(D_517),u1_struct_0(B_519))
      | ~ v1_funct_1(k2_tmap_1(A_520,B_519,C_518,D_517))
      | ~ l1_pre_topc(B_519)
      | ~ v2_pre_topc(B_519)
      | v2_struct_0(B_519)
      | ~ l1_pre_topc(D_517)
      | ~ v2_pre_topc(D_517)
      | v2_struct_0(D_517)
      | ~ l1_struct_0(D_517)
      | ~ m1_subset_1(C_518,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_520),u1_struct_0(B_519))))
      | ~ v1_funct_2(C_518,u1_struct_0(A_520),u1_struct_0(B_519))
      | ~ v1_funct_1(C_518)
      | ~ l1_struct_0(B_519)
      | ~ l1_struct_0(A_520) ) ),
    inference(resolution,[status(thm)],[c_18,c_437])).

tff(c_1936,plain,(
    ! [D_517,D_516] :
      ( k2_partfun1(u1_struct_0(D_517),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_517),u1_struct_0(D_516)) = k2_tmap_1(D_517,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5',D_517),D_516)
      | ~ m1_pre_topc(D_516,D_517)
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_517),u1_struct_0(D_517),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_517))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(D_517)
      | ~ v2_pre_topc(D_517)
      | v2_struct_0(D_517)
      | ~ l1_struct_0(D_517)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_50,c_1920])).

tff(c_1961,plain,(
    ! [D_517,D_516] :
      ( k2_partfun1(u1_struct_0(D_517),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_517),u1_struct_0(D_516)) = k2_tmap_1(D_517,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5',D_517),D_516)
      | ~ m1_pre_topc(D_516,D_517)
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_517),u1_struct_0(D_517),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_517))
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(D_517)
      | ~ v2_pre_topc(D_517)
      | v2_struct_0(D_517)
      | ~ l1_struct_0(D_517) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_366,c_54,c_52,c_66,c_64,c_1936])).

tff(c_4041,plain,(
    ! [D_632,D_633] :
      ( k2_partfun1(u1_struct_0(D_632),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_632),u1_struct_0(D_633)) = k2_tmap_1(D_632,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5',D_632),D_633)
      | ~ m1_pre_topc(D_633,D_632)
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_632),u1_struct_0(D_632),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_632))
      | ~ l1_pre_topc(D_632)
      | ~ v2_pre_topc(D_632)
      | v2_struct_0(D_632)
      | ~ l1_struct_0(D_632) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1961])).

tff(c_16,plain,(
    ! [D_62,A_34,B_50,C_58,E_64] :
      ( k3_tmap_1(A_34,B_50,C_58,D_62,E_64) = k2_partfun1(u1_struct_0(C_58),u1_struct_0(B_50),E_64,u1_struct_0(D_62))
      | ~ m1_pre_topc(D_62,C_58)
      | ~ m1_subset_1(E_64,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_58),u1_struct_0(B_50))))
      | ~ v1_funct_2(E_64,u1_struct_0(C_58),u1_struct_0(B_50))
      | ~ v1_funct_1(E_64)
      | ~ m1_pre_topc(D_62,A_34)
      | ~ m1_pre_topc(C_58,A_34)
      | ~ l1_pre_topc(B_50)
      | ~ v2_pre_topc(B_50)
      | v2_struct_0(B_50)
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_934,plain,(
    ! [A_34,D_62] :
      ( k3_tmap_1(A_34,'#skF_2','#skF_4',D_62,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_62))
      | ~ m1_pre_topc(D_62,'#skF_4')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_pre_topc(D_62,A_34)
      | ~ m1_pre_topc('#skF_4',A_34)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(resolution,[status(thm)],[c_917,c_16])).

tff(c_953,plain,(
    ! [A_34,D_62] :
      ( k3_tmap_1(A_34,'#skF_2','#skF_4',D_62,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_62))
      | ~ m1_pre_topc(D_62,'#skF_4')
      | ~ m1_pre_topc(D_62,A_34)
      | ~ m1_pre_topc('#skF_4',A_34)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_923,c_920,c_934])).

tff(c_954,plain,(
    ! [A_34,D_62] :
      ( k3_tmap_1(A_34,'#skF_2','#skF_4',D_62,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_62))
      | ~ m1_pre_topc(D_62,'#skF_4')
      | ~ m1_pre_topc(D_62,A_34)
      | ~ m1_pre_topc('#skF_4',A_34)
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_953])).

tff(c_4064,plain,(
    ! [A_34,D_633] :
      ( k3_tmap_1(A_34,'#skF_2','#skF_4',D_633,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),D_633)
      | ~ m1_pre_topc(D_633,'#skF_4')
      | ~ m1_pre_topc(D_633,A_34)
      | ~ m1_pre_topc('#skF_4',A_34)
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34)
      | v2_struct_0(A_34)
      | ~ m1_pre_topc(D_633,'#skF_4')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4041,c_954])).

tff(c_4134,plain,(
    ! [A_34,D_633] :
      ( k3_tmap_1(A_34,'#skF_2','#skF_4',D_633,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),D_633)
      | ~ m1_pre_topc(D_633,A_34)
      | ~ m1_pre_topc('#skF_4',A_34)
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34)
      | v2_struct_0(A_34)
      | ~ m1_pre_topc(D_633,'#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1006,c_125,c_102,c_923,c_920,c_4064])).

tff(c_4324,plain,(
    ! [A_640,D_641] :
      ( k3_tmap_1(A_640,'#skF_2','#skF_4',D_641,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),D_641)
      | ~ m1_pre_topc(D_641,A_640)
      | ~ m1_pre_topc('#skF_4',A_640)
      | ~ l1_pre_topc(A_640)
      | ~ v2_pre_topc(A_640)
      | v2_struct_0(A_640)
      | ~ m1_pre_topc(D_641,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4134])).

tff(c_4390,plain,(
    ! [D_641,A_640] :
      ( m1_subset_1(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),D_641),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_641),u1_struct_0('#skF_2'))))
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_pre_topc(D_641,A_640)
      | ~ m1_pre_topc('#skF_4',A_640)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_640)
      | ~ v2_pre_topc(A_640)
      | v2_struct_0(A_640)
      | ~ m1_pre_topc(D_641,A_640)
      | ~ m1_pre_topc('#skF_4',A_640)
      | ~ l1_pre_topc(A_640)
      | ~ v2_pre_topc(A_640)
      | v2_struct_0(A_640)
      | ~ m1_pre_topc(D_641,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4324,c_24])).

tff(c_4447,plain,(
    ! [D_641,A_640] :
      ( m1_subset_1(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),D_641),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_641),u1_struct_0('#skF_2'))))
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(D_641,A_640)
      | ~ m1_pre_topc('#skF_4',A_640)
      | ~ l1_pre_topc(A_640)
      | ~ v2_pre_topc(A_640)
      | v2_struct_0(A_640)
      | ~ m1_pre_topc(D_641,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_923,c_920,c_917,c_4390])).

tff(c_5184,plain,(
    ! [D_660,A_661] :
      ( m1_subset_1(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),D_660),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_660),u1_struct_0('#skF_2'))))
      | ~ m1_pre_topc(D_660,A_661)
      | ~ m1_pre_topc('#skF_4',A_661)
      | ~ l1_pre_topc(A_661)
      | ~ v2_pre_topc(A_661)
      | v2_struct_0(A_661)
      | ~ m1_pre_topc(D_660,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4447])).

tff(c_5198,plain,
    ( m1_subset_1(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_5184])).

tff(c_5224,plain,
    ( m1_subset_1(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_72,c_70,c_56,c_5198])).

tff(c_5225,plain,(
    m1_subset_1(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_5224])).

tff(c_14,plain,(
    ! [A_19,B_27,C_31,D_33] :
      ( k2_partfun1(u1_struct_0(A_19),u1_struct_0(B_27),C_31,u1_struct_0(D_33)) = k2_tmap_1(A_19,B_27,C_31,D_33)
      | ~ m1_pre_topc(D_33,A_19)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_19),u1_struct_0(B_27))))
      | ~ v1_funct_2(C_31,u1_struct_0(A_19),u1_struct_0(B_27))
      | ~ v1_funct_1(C_31)
      | ~ l1_pre_topc(B_27)
      | ~ v2_pre_topc(B_27)
      | v2_struct_0(B_27)
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_938,plain,(
    ! [D_33] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_33)) = k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),D_33)
      | ~ m1_pre_topc(D_33,'#skF_4')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_917,c_14])).

tff(c_961,plain,(
    ! [D_33] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_33)) = k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),D_33)
      | ~ m1_pre_topc(D_33,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_102,c_66,c_64,c_923,c_920,c_938])).

tff(c_962,plain,(
    ! [D_33] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_33)) = k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),D_33)
      | ~ m1_pre_topc(D_33,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_68,c_961])).

tff(c_34,plain,(
    ! [E_198,A_138,D_194,C_186,B_170,F_200] :
      ( r2_funct_2(u1_struct_0(E_198),u1_struct_0(B_170),k3_tmap_1(A_138,B_170,D_194,E_198,k3_tmap_1(A_138,B_170,C_186,D_194,F_200)),k3_tmap_1(A_138,B_170,C_186,E_198,F_200))
      | ~ m1_subset_1(F_200,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_186),u1_struct_0(B_170))))
      | ~ v1_funct_2(F_200,u1_struct_0(C_186),u1_struct_0(B_170))
      | ~ v1_funct_1(F_200)
      | ~ m1_pre_topc(E_198,D_194)
      | ~ m1_pre_topc(D_194,C_186)
      | ~ m1_pre_topc(E_198,A_138)
      | v2_struct_0(E_198)
      | ~ m1_pre_topc(D_194,A_138)
      | v2_struct_0(D_194)
      | ~ m1_pre_topc(C_186,A_138)
      | v2_struct_0(C_186)
      | ~ l1_pre_topc(B_170)
      | ~ v2_pre_topc(B_170)
      | v2_struct_0(B_170)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_274])).

tff(c_897,plain,(
    ! [D_194] :
      ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',D_194,'#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_1',D_194,'#skF_5')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',D_194)
      | ~ m1_pre_topc(D_194,'#skF_1')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(D_194,'#skF_1')
      | v2_struct_0(D_194)
      | ~ m1_pre_topc('#skF_1','#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_886,c_34])).

tff(c_913,plain,(
    ! [D_194] :
      ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',D_194,'#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_1',D_194,'#skF_5')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_pre_topc('#skF_4',D_194)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(D_194,'#skF_1')
      | v2_struct_0(D_194)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_547,c_56,c_54,c_52,c_50,c_897])).

tff(c_1518,plain,(
    ! [D_492] :
      ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',D_492,'#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_1',D_492,'#skF_5')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_pre_topc('#skF_4',D_492)
      | ~ m1_pre_topc(D_492,'#skF_1')
      | v2_struct_0(D_492) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_58,c_913])).

tff(c_1523,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_886,c_1518])).

tff(c_1534,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1523])).

tff(c_1535,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1534])).

tff(c_1542,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1535])).

tff(c_1545,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_1542])).

tff(c_1549,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_1545])).

tff(c_1551,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1535])).

tff(c_3651,plain,(
    ! [A_606,D_607] :
      ( k3_tmap_1(A_606,'#skF_2','#skF_4',D_607,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_607))
      | ~ m1_pre_topc(D_607,'#skF_4')
      | ~ m1_pre_topc(D_607,A_606)
      | ~ m1_pre_topc('#skF_4',A_606)
      | ~ l1_pre_topc(A_606)
      | ~ v2_pre_topc(A_606)
      | v2_struct_0(A_606) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_953])).

tff(c_409,plain,(
    ! [A_368,B_369,C_370,D_371] :
      ( v1_funct_2(k2_tmap_1(A_368,B_369,C_370,D_371),u1_struct_0(D_371),u1_struct_0(B_369))
      | ~ l1_struct_0(D_371)
      | ~ m1_subset_1(C_370,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_368),u1_struct_0(B_369))))
      | ~ v1_funct_2(C_370,u1_struct_0(A_368),u1_struct_0(B_369))
      | ~ v1_funct_1(C_370)
      | ~ l1_struct_0(B_369)
      | ~ l1_struct_0(A_368) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_411,plain,(
    ! [D_371] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_371),u1_struct_0(D_371),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_371)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_50,c_409])).

tff(c_414,plain,(
    ! [D_371] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_371),u1_struct_0(D_371),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_371) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_366,c_54,c_52,c_411])).

tff(c_1085,plain,(
    ! [D_452,A_454,C_453,B_455,A_456,D_451] :
      ( v1_funct_1(k3_tmap_1(A_454,B_455,D_452,D_451,k2_tmap_1(A_456,B_455,C_453,D_452)))
      | ~ v1_funct_2(k2_tmap_1(A_456,B_455,C_453,D_452),u1_struct_0(D_452),u1_struct_0(B_455))
      | ~ v1_funct_1(k2_tmap_1(A_456,B_455,C_453,D_452))
      | ~ m1_pre_topc(D_451,A_454)
      | ~ m1_pre_topc(D_452,A_454)
      | ~ l1_pre_topc(B_455)
      | ~ v2_pre_topc(B_455)
      | v2_struct_0(B_455)
      | ~ l1_pre_topc(A_454)
      | ~ v2_pre_topc(A_454)
      | v2_struct_0(A_454)
      | ~ l1_struct_0(D_452)
      | ~ m1_subset_1(C_453,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_456),u1_struct_0(B_455))))
      | ~ v1_funct_2(C_453,u1_struct_0(A_456),u1_struct_0(B_455))
      | ~ v1_funct_1(C_453)
      | ~ l1_struct_0(B_455)
      | ~ l1_struct_0(A_456) ) ),
    inference(resolution,[status(thm)],[c_18,c_426])).

tff(c_1101,plain,(
    ! [A_454,D_371,D_451] :
      ( v1_funct_1(k3_tmap_1(A_454,'#skF_2',D_371,D_451,k2_tmap_1('#skF_1','#skF_2','#skF_5',D_371)))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_371))
      | ~ m1_pre_topc(D_451,A_454)
      | ~ m1_pre_topc(D_371,A_454)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_454)
      | ~ v2_pre_topc(A_454)
      | v2_struct_0(A_454)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1')
      | ~ l1_struct_0(D_371) ) ),
    inference(resolution,[status(thm)],[c_414,c_1085])).

tff(c_1129,plain,(
    ! [A_454,D_371,D_451] :
      ( v1_funct_1(k3_tmap_1(A_454,'#skF_2',D_371,D_451,k2_tmap_1('#skF_1','#skF_2','#skF_5',D_371)))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_371))
      | ~ m1_pre_topc(D_451,A_454)
      | ~ m1_pre_topc(D_371,A_454)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_454)
      | ~ v2_pre_topc(A_454)
      | v2_struct_0(A_454)
      | ~ l1_struct_0(D_371) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_366,c_54,c_52,c_50,c_66,c_64,c_1101])).

tff(c_1130,plain,(
    ! [A_454,D_371,D_451] :
      ( v1_funct_1(k3_tmap_1(A_454,'#skF_2',D_371,D_451,k2_tmap_1('#skF_1','#skF_2','#skF_5',D_371)))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_371))
      | ~ m1_pre_topc(D_451,A_454)
      | ~ m1_pre_topc(D_371,A_454)
      | ~ l1_pre_topc(A_454)
      | ~ v2_pre_topc(A_454)
      | v2_struct_0(A_454)
      | ~ l1_struct_0(D_371) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1129])).

tff(c_3667,plain,(
    ! [D_607,A_606] :
      ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_607)))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_pre_topc(D_607,A_606)
      | ~ m1_pre_topc('#skF_4',A_606)
      | ~ l1_pre_topc(A_606)
      | ~ v2_pre_topc(A_606)
      | v2_struct_0(A_606)
      | ~ l1_struct_0('#skF_4')
      | ~ m1_pre_topc(D_607,'#skF_4')
      | ~ m1_pre_topc(D_607,A_606)
      | ~ m1_pre_topc('#skF_4',A_606)
      | ~ l1_pre_topc(A_606)
      | ~ v2_pre_topc(A_606)
      | v2_struct_0(A_606) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3651,c_1130])).

tff(c_3746,plain,(
    ! [D_608,A_609] :
      ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_608)))
      | ~ m1_pre_topc(D_608,'#skF_4')
      | ~ m1_pre_topc(D_608,A_609)
      | ~ m1_pre_topc('#skF_4',A_609)
      | ~ l1_pre_topc(A_609)
      | ~ v2_pre_topc(A_609)
      | v2_struct_0(A_609) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1006,c_923,c_3667])).

tff(c_3764,plain,
    ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_3746])).

tff(c_3794,plain,
    ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_102,c_1551,c_48,c_3764])).

tff(c_3795,plain,(
    v1_funct_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3794])).

tff(c_3811,plain,
    ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_962,c_3795])).

tff(c_3815,plain,(
    v1_funct_1(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3811])).

tff(c_461,plain,(
    ! [B_66,D_391,A_390,A_65,C_67,D_68] :
      ( v1_funct_2(k3_tmap_1(A_390,B_66,D_68,D_391,k2_tmap_1(A_65,B_66,C_67,D_68)),u1_struct_0(D_391),u1_struct_0(B_66))
      | ~ v1_funct_2(k2_tmap_1(A_65,B_66,C_67,D_68),u1_struct_0(D_68),u1_struct_0(B_66))
      | ~ v1_funct_1(k2_tmap_1(A_65,B_66,C_67,D_68))
      | ~ m1_pre_topc(D_391,A_390)
      | ~ m1_pre_topc(D_68,A_390)
      | ~ l1_pre_topc(B_66)
      | ~ v2_pre_topc(B_66)
      | v2_struct_0(B_66)
      | ~ l1_pre_topc(A_390)
      | ~ v2_pre_topc(A_390)
      | v2_struct_0(A_390)
      | ~ l1_struct_0(D_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_65),u1_struct_0(B_66))))
      | ~ v1_funct_2(C_67,u1_struct_0(A_65),u1_struct_0(B_66))
      | ~ v1_funct_1(C_67)
      | ~ l1_struct_0(B_66)
      | ~ l1_struct_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_18,c_456])).

tff(c_3673,plain,(
    ! [D_607,A_606] :
      ( v1_funct_2(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_607)),u1_struct_0(D_607),u1_struct_0('#skF_2'))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_pre_topc(D_607,A_606)
      | ~ m1_pre_topc('#skF_4',A_606)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_606)
      | ~ v2_pre_topc(A_606)
      | v2_struct_0(A_606)
      | ~ l1_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1')
      | ~ m1_pre_topc(D_607,'#skF_4')
      | ~ m1_pre_topc(D_607,A_606)
      | ~ m1_pre_topc('#skF_4',A_606)
      | ~ l1_pre_topc(A_606)
      | ~ v2_pre_topc(A_606)
      | v2_struct_0(A_606) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3651,c_461])).

tff(c_3725,plain,(
    ! [D_607,A_606] :
      ( v1_funct_2(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_607)),u1_struct_0(D_607),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(D_607,'#skF_4')
      | ~ m1_pre_topc(D_607,A_606)
      | ~ m1_pre_topc('#skF_4',A_606)
      | ~ l1_pre_topc(A_606)
      | ~ v2_pre_topc(A_606)
      | v2_struct_0(A_606) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_366,c_54,c_52,c_50,c_1006,c_66,c_64,c_923,c_920,c_3673])).

tff(c_3881,plain,(
    ! [D_618,A_619] :
      ( v1_funct_2(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_618)),u1_struct_0(D_618),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_618,'#skF_4')
      | ~ m1_pre_topc(D_618,A_619)
      | ~ m1_pre_topc('#skF_4',A_619)
      | ~ l1_pre_topc(A_619)
      | ~ v2_pre_topc(A_619)
      | v2_struct_0(A_619) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3725])).

tff(c_3895,plain,
    ( v1_funct_2(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_3881])).

tff(c_3921,plain,
    ( v1_funct_2(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_56,c_48,c_3895])).

tff(c_3922,plain,(
    v1_funct_2(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_3921])).

tff(c_3964,plain,
    ( v1_funct_2(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_962,c_3922])).

tff(c_3968,plain,(
    v1_funct_2(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3964])).

tff(c_546,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_529])).

tff(c_606,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_546,c_446])).

tff(c_613,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_606])).

tff(c_627,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_613,c_435])).

tff(c_637,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_547,c_60,c_627])).

tff(c_638,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_637])).

tff(c_624,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_613,c_465])).

tff(c_634,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_547,c_60,c_624])).

tff(c_635,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_634])).

tff(c_621,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_613,c_24])).

tff(c_631,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_547,c_60,c_54,c_52,c_50,c_621])).

tff(c_632,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_631])).

tff(c_762,plain,(
    ! [A_420,E_421,F_424,C_422,D_425,B_423] :
      ( r2_funct_2(u1_struct_0(E_421),u1_struct_0(B_423),k3_tmap_1(A_420,B_423,D_425,E_421,k3_tmap_1(A_420,B_423,C_422,D_425,F_424)),k3_tmap_1(A_420,B_423,C_422,E_421,F_424))
      | ~ m1_subset_1(F_424,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_422),u1_struct_0(B_423))))
      | ~ v1_funct_2(F_424,u1_struct_0(C_422),u1_struct_0(B_423))
      | ~ v1_funct_1(F_424)
      | ~ m1_pre_topc(E_421,D_425)
      | ~ m1_pre_topc(D_425,C_422)
      | ~ m1_pre_topc(E_421,A_420)
      | v2_struct_0(E_421)
      | ~ m1_pre_topc(D_425,A_420)
      | v2_struct_0(D_425)
      | ~ m1_pre_topc(C_422,A_420)
      | v2_struct_0(C_422)
      | ~ l1_pre_topc(B_423)
      | ~ v2_pre_topc(B_423)
      | v2_struct_0(B_423)
      | ~ l1_pre_topc(A_420)
      | ~ v2_pre_topc(A_420)
      | v2_struct_0(A_420) ) ),
    inference(cnfTransformation,[status(thm)],[f_274])).

tff(c_776,plain,(
    ! [D_425] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',D_425,'#skF_3',k3_tmap_1('#skF_1','#skF_2','#skF_1',D_425,'#skF_5')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_3',D_425)
      | ~ m1_pre_topc(D_425,'#skF_1')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(D_425,'#skF_1')
      | v2_struct_0(D_425)
      | ~ m1_pre_topc('#skF_1','#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_613,c_762])).

tff(c_788,plain,(
    ! [D_425] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',D_425,'#skF_3',k3_tmap_1('#skF_1','#skF_2','#skF_1',D_425,'#skF_5')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
      | ~ m1_pre_topc('#skF_3',D_425)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(D_425,'#skF_1')
      | v2_struct_0(D_425)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_547,c_60,c_54,c_52,c_50,c_776])).

tff(c_1552,plain,(
    ! [D_493] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',D_493,'#skF_3',k3_tmap_1('#skF_1','#skF_2','#skF_1',D_493,'#skF_5')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
      | ~ m1_pre_topc('#skF_3',D_493)
      | ~ m1_pre_topc(D_493,'#skF_1')
      | v2_struct_0(D_493) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_62,c_788])).

tff(c_1557,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_886,c_1552])).

tff(c_1568,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_48,c_1557])).

tff(c_1569,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1568])).

tff(c_4361,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4324,c_1569])).

tff(c_4423,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_72,c_70,c_56,c_60,c_4361])).

tff(c_4424,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4423])).

tff(c_4,plain,(
    ! [D_4,C_3,A_1,B_2] :
      ( D_4 = C_3
      | ~ r2_funct_2(A_1,B_2,C_3,D_4)
      | ~ m1_subset_1(D_4,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(D_4,A_1,B_2)
      | ~ v1_funct_1(D_4)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(C_3,A_1,B_2)
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4458,plain,
    ( k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_4424,c_4])).

tff(c_4461,plain,
    ( k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3815,c_3968,c_638,c_635,c_632,c_4458])).

tff(c_5473,plain,(
    k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5225,c_4461])).

tff(c_640,plain,(
    ! [D_416,C_419,A_415,B_418,F_417] :
      ( r1_tmap_1(D_416,A_415,k2_tmap_1(B_418,A_415,C_419,D_416),F_417)
      | ~ r1_tmap_1(B_418,A_415,C_419,F_417)
      | ~ m1_subset_1(F_417,u1_struct_0(D_416))
      | ~ m1_subset_1(F_417,u1_struct_0(B_418))
      | ~ m1_pre_topc(D_416,B_418)
      | v2_struct_0(D_416)
      | ~ m1_subset_1(C_419,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_418),u1_struct_0(A_415))))
      | ~ v1_funct_2(C_419,u1_struct_0(B_418),u1_struct_0(A_415))
      | ~ v1_funct_1(C_419)
      | ~ l1_pre_topc(B_418)
      | ~ v2_pre_topc(B_418)
      | v2_struct_0(B_418)
      | ~ l1_pre_topc(A_415)
      | ~ v2_pre_topc(A_415)
      | v2_struct_0(A_415) ) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_3078,plain,(
    ! [D_578,D_583,C_580,F_579,A_582,B_581] :
      ( r1_tmap_1(D_583,B_581,k2_tmap_1(D_578,B_581,k2_tmap_1(A_582,B_581,C_580,D_578),D_583),F_579)
      | ~ r1_tmap_1(D_578,B_581,k2_tmap_1(A_582,B_581,C_580,D_578),F_579)
      | ~ m1_subset_1(F_579,u1_struct_0(D_583))
      | ~ m1_subset_1(F_579,u1_struct_0(D_578))
      | ~ m1_pre_topc(D_583,D_578)
      | v2_struct_0(D_583)
      | ~ v1_funct_2(k2_tmap_1(A_582,B_581,C_580,D_578),u1_struct_0(D_578),u1_struct_0(B_581))
      | ~ v1_funct_1(k2_tmap_1(A_582,B_581,C_580,D_578))
      | ~ l1_pre_topc(D_578)
      | ~ v2_pre_topc(D_578)
      | v2_struct_0(D_578)
      | ~ l1_pre_topc(B_581)
      | ~ v2_pre_topc(B_581)
      | v2_struct_0(B_581)
      | ~ l1_struct_0(D_578)
      | ~ m1_subset_1(C_580,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_582),u1_struct_0(B_581))))
      | ~ v1_funct_2(C_580,u1_struct_0(A_582),u1_struct_0(B_581))
      | ~ v1_funct_1(C_580)
      | ~ l1_struct_0(B_581)
      | ~ l1_struct_0(A_582) ) ),
    inference(resolution,[status(thm)],[c_18,c_640])).

tff(c_3100,plain,(
    ! [D_583,D_371,F_579] :
      ( r1_tmap_1(D_583,'#skF_2',k2_tmap_1(D_371,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5',D_371),D_583),F_579)
      | ~ r1_tmap_1(D_371,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5',D_371),F_579)
      | ~ m1_subset_1(F_579,u1_struct_0(D_583))
      | ~ m1_subset_1(F_579,u1_struct_0(D_371))
      | ~ m1_pre_topc(D_583,D_371)
      | v2_struct_0(D_583)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_371))
      | ~ l1_pre_topc(D_371)
      | ~ v2_pre_topc(D_371)
      | v2_struct_0(D_371)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1')
      | ~ l1_struct_0(D_371) ) ),
    inference(resolution,[status(thm)],[c_414,c_3078])).

tff(c_3136,plain,(
    ! [D_583,D_371,F_579] :
      ( r1_tmap_1(D_583,'#skF_2',k2_tmap_1(D_371,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5',D_371),D_583),F_579)
      | ~ r1_tmap_1(D_371,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5',D_371),F_579)
      | ~ m1_subset_1(F_579,u1_struct_0(D_583))
      | ~ m1_subset_1(F_579,u1_struct_0(D_371))
      | ~ m1_pre_topc(D_583,D_371)
      | v2_struct_0(D_583)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_371))
      | ~ l1_pre_topc(D_371)
      | ~ v2_pre_topc(D_371)
      | v2_struct_0(D_371)
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(D_371) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_366,c_54,c_52,c_50,c_66,c_64,c_3100])).

tff(c_3137,plain,(
    ! [D_583,D_371,F_579] :
      ( r1_tmap_1(D_583,'#skF_2',k2_tmap_1(D_371,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5',D_371),D_583),F_579)
      | ~ r1_tmap_1(D_371,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5',D_371),F_579)
      | ~ m1_subset_1(F_579,u1_struct_0(D_583))
      | ~ m1_subset_1(F_579,u1_struct_0(D_371))
      | ~ m1_pre_topc(D_583,D_371)
      | v2_struct_0(D_583)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_371))
      | ~ l1_pre_topc(D_371)
      | ~ v2_pre_topc(D_371)
      | v2_struct_0(D_371)
      | ~ l1_struct_0(D_371) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3136])).

tff(c_5497,plain,(
    ! [F_579] :
      ( r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),F_579)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),F_579)
      | ~ m1_subset_1(F_579,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_579,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | v2_struct_0('#skF_3')
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5473,c_3137])).

tff(c_5552,plain,(
    ! [F_579] :
      ( r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),F_579)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),F_579)
      | ~ m1_subset_1(F_579,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_579,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1006,c_125,c_102,c_923,c_48,c_5497])).

tff(c_5593,plain,(
    ! [F_671] :
      ( r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),F_671)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),F_671)
      | ~ m1_subset_1(F_671,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_671,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_62,c_5552])).

tff(c_38,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_335])).

tff(c_76,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38])).

tff(c_5596,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_5593,c_76])).

tff(c_5600,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_75,c_40,c_5596])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:36:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.27/3.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.27/3.06  
% 8.27/3.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.27/3.06  %$ r2_funct_2 > r1_tmap_1 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.27/3.06  
% 8.27/3.06  %Foreground sorts:
% 8.27/3.06  
% 8.27/3.06  
% 8.27/3.06  %Background operators:
% 8.27/3.06  
% 8.27/3.06  
% 8.27/3.06  %Foreground operators:
% 8.27/3.06  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.27/3.06  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 8.27/3.06  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.27/3.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.27/3.06  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 8.27/3.06  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.27/3.06  tff('#skF_7', type, '#skF_7': $i).
% 8.27/3.06  tff('#skF_5', type, '#skF_5': $i).
% 8.27/3.06  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.27/3.06  tff('#skF_6', type, '#skF_6': $i).
% 8.27/3.06  tff('#skF_2', type, '#skF_2': $i).
% 8.27/3.06  tff('#skF_3', type, '#skF_3': $i).
% 8.27/3.06  tff('#skF_1', type, '#skF_1': $i).
% 8.27/3.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.27/3.06  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.27/3.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.27/3.06  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.27/3.06  tff('#skF_4', type, '#skF_4': $i).
% 8.27/3.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.27/3.06  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.27/3.06  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 8.27/3.06  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.27/3.06  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 8.27/3.06  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.27/3.06  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 8.27/3.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.27/3.06  
% 8.27/3.09  tff(f_335, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(D, B, k2_tmap_1(A, B, E, D), F)) => r1_tmap_1(C, B, k2_tmap_1(A, B, E, C), G))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_tmap_1)).
% 8.27/3.09  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 8.27/3.09  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 8.27/3.09  tff(f_154, axiom, (![A, B, C, D]: ((((((l1_struct_0(A) & l1_struct_0(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & l1_struct_0(D)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 8.27/3.09  tff(f_188, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 8.27/3.09  tff(f_136, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 8.27/3.09  tff(f_104, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 8.27/3.09  tff(f_184, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 8.27/3.09  tff(f_50, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 8.27/3.09  tff(f_274, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => ((m1_pre_topc(D, C) & m1_pre_topc(E, D)) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(E), u1_struct_0(B), k3_tmap_1(A, B, D, E, k3_tmap_1(A, B, C, D, F)), k3_tmap_1(A, B, C, E, F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_tmap_1)).
% 8.27/3.09  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 8.27/3.09  tff(f_228, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 8.27/3.09  tff(c_46, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_335])).
% 8.27/3.09  tff(c_42, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_335])).
% 8.27/3.09  tff(c_44, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_335])).
% 8.27/3.09  tff(c_75, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44])).
% 8.27/3.09  tff(c_40, plain, (r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_335])).
% 8.27/3.09  tff(c_58, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_335])).
% 8.27/3.09  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_335])).
% 8.27/3.09  tff(c_70, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_335])).
% 8.27/3.09  tff(c_56, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_335])).
% 8.27/3.09  tff(c_83, plain, (![B_330, A_331]: (l1_pre_topc(B_330) | ~m1_pre_topc(B_330, A_331) | ~l1_pre_topc(A_331))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.27/3.09  tff(c_92, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_83])).
% 8.27/3.09  tff(c_102, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_92])).
% 8.27/3.09  tff(c_8, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.27/3.09  tff(c_64, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_335])).
% 8.27/3.09  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_335])).
% 8.27/3.09  tff(c_52, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_335])).
% 8.27/3.09  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_335])).
% 8.27/3.09  tff(c_307, plain, (![A_355, B_356, C_357, D_358]: (v1_funct_1(k2_tmap_1(A_355, B_356, C_357, D_358)) | ~l1_struct_0(D_358) | ~m1_subset_1(C_357, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_355), u1_struct_0(B_356)))) | ~v1_funct_2(C_357, u1_struct_0(A_355), u1_struct_0(B_356)) | ~v1_funct_1(C_357) | ~l1_struct_0(B_356) | ~l1_struct_0(A_355))), inference(cnfTransformation, [status(thm)], [f_154])).
% 8.27/3.09  tff(c_309, plain, (![D_358]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_358)) | ~l1_struct_0(D_358) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_50, c_307])).
% 8.27/3.09  tff(c_312, plain, (![D_358]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_358)) | ~l1_struct_0(D_358) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_309])).
% 8.27/3.09  tff(c_313, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_312])).
% 8.27/3.09  tff(c_316, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_313])).
% 8.27/3.09  tff(c_320, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_316])).
% 8.27/3.09  tff(c_321, plain, (![D_358]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_358)) | ~l1_struct_0(D_358))), inference(splitRight, [status(thm)], [c_312])).
% 8.27/3.09  tff(c_357, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_321])).
% 8.27/3.09  tff(c_360, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_8, c_357])).
% 8.27/3.09  tff(c_364, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_360])).
% 8.27/3.09  tff(c_366, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_321])).
% 8.27/3.09  tff(c_74, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_335])).
% 8.27/3.09  tff(c_72, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_335])).
% 8.27/3.09  tff(c_30, plain, (![A_74]: (m1_pre_topc(A_74, A_74) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_188])).
% 8.27/3.09  tff(c_60, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_335])).
% 8.27/3.09  tff(c_68, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_335])).
% 8.27/3.09  tff(c_66, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_335])).
% 8.27/3.09  tff(c_493, plain, (![C_410, A_408, D_411, B_409, E_412]: (k3_tmap_1(A_408, B_409, C_410, D_411, E_412)=k2_partfun1(u1_struct_0(C_410), u1_struct_0(B_409), E_412, u1_struct_0(D_411)) | ~m1_pre_topc(D_411, C_410) | ~m1_subset_1(E_412, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_410), u1_struct_0(B_409)))) | ~v1_funct_2(E_412, u1_struct_0(C_410), u1_struct_0(B_409)) | ~v1_funct_1(E_412) | ~m1_pre_topc(D_411, A_408) | ~m1_pre_topc(C_410, A_408) | ~l1_pre_topc(B_409) | ~v2_pre_topc(B_409) | v2_struct_0(B_409) | ~l1_pre_topc(A_408) | ~v2_pre_topc(A_408) | v2_struct_0(A_408))), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.27/3.09  tff(c_499, plain, (![A_408, D_411]: (k3_tmap_1(A_408, '#skF_2', '#skF_1', D_411, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_411)) | ~m1_pre_topc(D_411, '#skF_1') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_411, A_408) | ~m1_pre_topc('#skF_1', A_408) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_408) | ~v2_pre_topc(A_408) | v2_struct_0(A_408))), inference(resolution, [status(thm)], [c_50, c_493])).
% 8.27/3.09  tff(c_504, plain, (![A_408, D_411]: (k3_tmap_1(A_408, '#skF_2', '#skF_1', D_411, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_411)) | ~m1_pre_topc(D_411, '#skF_1') | ~m1_pre_topc(D_411, A_408) | ~m1_pre_topc('#skF_1', A_408) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_408) | ~v2_pre_topc(A_408) | v2_struct_0(A_408))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_54, c_52, c_499])).
% 8.27/3.09  tff(c_506, plain, (![A_413, D_414]: (k3_tmap_1(A_413, '#skF_2', '#skF_1', D_414, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_414)) | ~m1_pre_topc(D_414, '#skF_1') | ~m1_pre_topc(D_414, A_413) | ~m1_pre_topc('#skF_1', A_413) | ~l1_pre_topc(A_413) | ~v2_pre_topc(A_413) | v2_struct_0(A_413))), inference(negUnitSimplification, [status(thm)], [c_68, c_504])).
% 8.27/3.09  tff(c_514, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_506])).
% 8.27/3.09  tff(c_528, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_60, c_514])).
% 8.27/3.09  tff(c_529, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_74, c_528])).
% 8.27/3.09  tff(c_538, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_529])).
% 8.27/3.09  tff(c_541, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_538])).
% 8.27/3.09  tff(c_545, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_541])).
% 8.27/3.09  tff(c_547, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_529])).
% 8.27/3.09  tff(c_516, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_506])).
% 8.27/3.09  tff(c_532, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_56, c_516])).
% 8.27/3.09  tff(c_533, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_74, c_532])).
% 8.27/3.09  tff(c_875, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_547, c_533])).
% 8.27/3.09  tff(c_437, plain, (![A_384, B_385, C_386, D_387]: (k2_partfun1(u1_struct_0(A_384), u1_struct_0(B_385), C_386, u1_struct_0(D_387))=k2_tmap_1(A_384, B_385, C_386, D_387) | ~m1_pre_topc(D_387, A_384) | ~m1_subset_1(C_386, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_384), u1_struct_0(B_385)))) | ~v1_funct_2(C_386, u1_struct_0(A_384), u1_struct_0(B_385)) | ~v1_funct_1(C_386) | ~l1_pre_topc(B_385) | ~v2_pre_topc(B_385) | v2_struct_0(B_385) | ~l1_pre_topc(A_384) | ~v2_pre_topc(A_384) | v2_struct_0(A_384))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.27/3.09  tff(c_441, plain, (![D_387]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_387))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_387) | ~m1_pre_topc(D_387, '#skF_1') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_50, c_437])).
% 8.27/3.09  tff(c_445, plain, (![D_387]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_387))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_387) | ~m1_pre_topc(D_387, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_54, c_52, c_441])).
% 8.27/3.09  tff(c_446, plain, (![D_387]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_387))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_387) | ~m1_pre_topc(D_387, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_445])).
% 8.27/3.09  tff(c_879, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_875, c_446])).
% 8.27/3.09  tff(c_886, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_879])).
% 8.27/3.09  tff(c_426, plain, (![C_381, D_379, A_378, B_377, E_380]: (v1_funct_1(k3_tmap_1(A_378, B_377, C_381, D_379, E_380)) | ~m1_subset_1(E_380, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_381), u1_struct_0(B_377)))) | ~v1_funct_2(E_380, u1_struct_0(C_381), u1_struct_0(B_377)) | ~v1_funct_1(E_380) | ~m1_pre_topc(D_379, A_378) | ~m1_pre_topc(C_381, A_378) | ~l1_pre_topc(B_377) | ~v2_pre_topc(B_377) | v2_struct_0(B_377) | ~l1_pre_topc(A_378) | ~v2_pre_topc(A_378) | v2_struct_0(A_378))), inference(cnfTransformation, [status(thm)], [f_184])).
% 8.27/3.09  tff(c_430, plain, (![A_378, D_379]: (v1_funct_1(k3_tmap_1(A_378, '#skF_2', '#skF_1', D_379, '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_379, A_378) | ~m1_pre_topc('#skF_1', A_378) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_378) | ~v2_pre_topc(A_378) | v2_struct_0(A_378))), inference(resolution, [status(thm)], [c_50, c_426])).
% 8.27/3.09  tff(c_434, plain, (![A_378, D_379]: (v1_funct_1(k3_tmap_1(A_378, '#skF_2', '#skF_1', D_379, '#skF_5')) | ~m1_pre_topc(D_379, A_378) | ~m1_pre_topc('#skF_1', A_378) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_378) | ~v2_pre_topc(A_378) | v2_struct_0(A_378))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_54, c_52, c_430])).
% 8.27/3.09  tff(c_435, plain, (![A_378, D_379]: (v1_funct_1(k3_tmap_1(A_378, '#skF_2', '#skF_1', D_379, '#skF_5')) | ~m1_pre_topc(D_379, A_378) | ~m1_pre_topc('#skF_1', A_378) | ~l1_pre_topc(A_378) | ~v2_pre_topc(A_378) | v2_struct_0(A_378))), inference(negUnitSimplification, [status(thm)], [c_68, c_434])).
% 8.27/3.09  tff(c_906, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_886, c_435])).
% 8.27/3.09  tff(c_922, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_547, c_56, c_906])).
% 8.27/3.09  tff(c_923, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_74, c_922])).
% 8.27/3.09  tff(c_456, plain, (![D_391, A_390, E_392, B_389, C_393]: (v1_funct_2(k3_tmap_1(A_390, B_389, C_393, D_391, E_392), u1_struct_0(D_391), u1_struct_0(B_389)) | ~m1_subset_1(E_392, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_393), u1_struct_0(B_389)))) | ~v1_funct_2(E_392, u1_struct_0(C_393), u1_struct_0(B_389)) | ~v1_funct_1(E_392) | ~m1_pre_topc(D_391, A_390) | ~m1_pre_topc(C_393, A_390) | ~l1_pre_topc(B_389) | ~v2_pre_topc(B_389) | v2_struct_0(B_389) | ~l1_pre_topc(A_390) | ~v2_pre_topc(A_390) | v2_struct_0(A_390))), inference(cnfTransformation, [status(thm)], [f_184])).
% 8.27/3.09  tff(c_460, plain, (![A_390, D_391]: (v1_funct_2(k3_tmap_1(A_390, '#skF_2', '#skF_1', D_391, '#skF_5'), u1_struct_0(D_391), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_391, A_390) | ~m1_pre_topc('#skF_1', A_390) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_390) | ~v2_pre_topc(A_390) | v2_struct_0(A_390))), inference(resolution, [status(thm)], [c_50, c_456])).
% 8.27/3.09  tff(c_464, plain, (![A_390, D_391]: (v1_funct_2(k3_tmap_1(A_390, '#skF_2', '#skF_1', D_391, '#skF_5'), u1_struct_0(D_391), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_391, A_390) | ~m1_pre_topc('#skF_1', A_390) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_390) | ~v2_pre_topc(A_390) | v2_struct_0(A_390))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_54, c_52, c_460])).
% 8.27/3.09  tff(c_465, plain, (![A_390, D_391]: (v1_funct_2(k3_tmap_1(A_390, '#skF_2', '#skF_1', D_391, '#skF_5'), u1_struct_0(D_391), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_391, A_390) | ~m1_pre_topc('#skF_1', A_390) | ~l1_pre_topc(A_390) | ~v2_pre_topc(A_390) | v2_struct_0(A_390))), inference(negUnitSimplification, [status(thm)], [c_68, c_464])).
% 8.27/3.09  tff(c_903, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_886, c_465])).
% 8.27/3.09  tff(c_919, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_547, c_56, c_903])).
% 8.27/3.09  tff(c_920, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_74, c_919])).
% 8.27/3.09  tff(c_24, plain, (![B_70, E_73, D_72, C_71, A_69]: (m1_subset_1(k3_tmap_1(A_69, B_70, C_71, D_72, E_73), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_72), u1_struct_0(B_70)))) | ~m1_subset_1(E_73, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_71), u1_struct_0(B_70)))) | ~v1_funct_2(E_73, u1_struct_0(C_71), u1_struct_0(B_70)) | ~v1_funct_1(E_73) | ~m1_pre_topc(D_72, A_69) | ~m1_pre_topc(C_71, A_69) | ~l1_pre_topc(B_70) | ~v2_pre_topc(B_70) | v2_struct_0(B_70) | ~l1_pre_topc(A_69) | ~v2_pre_topc(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_184])).
% 8.27/3.09  tff(c_900, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_886, c_24])).
% 8.27/3.09  tff(c_916, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_547, c_56, c_54, c_52, c_50, c_900])).
% 8.27/3.09  tff(c_917, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_916])).
% 8.27/3.09  tff(c_22, plain, (![A_65, B_66, C_67, D_68]: (v1_funct_1(k2_tmap_1(A_65, B_66, C_67, D_68)) | ~l1_struct_0(D_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_65), u1_struct_0(B_66)))) | ~v1_funct_2(C_67, u1_struct_0(A_65), u1_struct_0(B_66)) | ~v1_funct_1(C_67) | ~l1_struct_0(B_66) | ~l1_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_154])).
% 8.27/3.09  tff(c_944, plain, (![D_68]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), D_68)) | ~l1_struct_0(D_68) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_917, c_22])).
% 8.27/3.09  tff(c_972, plain, (![D_68]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), D_68)) | ~l1_struct_0(D_68) | ~l1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_366, c_923, c_920, c_944])).
% 8.27/3.09  tff(c_997, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_972])).
% 8.27/3.09  tff(c_1000, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_8, c_997])).
% 8.27/3.09  tff(c_1004, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_1000])).
% 8.27/3.09  tff(c_1006, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_972])).
% 8.27/3.09  tff(c_106, plain, (![B_332, A_333]: (v2_pre_topc(B_332) | ~m1_pre_topc(B_332, A_333) | ~l1_pre_topc(A_333) | ~v2_pre_topc(A_333))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.27/3.09  tff(c_115, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_106])).
% 8.27/3.09  tff(c_125, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_115])).
% 8.27/3.09  tff(c_48, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_335])).
% 8.27/3.09  tff(c_322, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_312])).
% 8.27/3.09  tff(c_18, plain, (![A_65, B_66, C_67, D_68]: (m1_subset_1(k2_tmap_1(A_65, B_66, C_67, D_68), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_68), u1_struct_0(B_66)))) | ~l1_struct_0(D_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_65), u1_struct_0(B_66)))) | ~v1_funct_2(C_67, u1_struct_0(A_65), u1_struct_0(B_66)) | ~v1_funct_1(C_67) | ~l1_struct_0(B_66) | ~l1_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_154])).
% 8.27/3.09  tff(c_1920, plain, (![C_518, D_517, D_516, B_519, A_520]: (k2_partfun1(u1_struct_0(D_517), u1_struct_0(B_519), k2_tmap_1(A_520, B_519, C_518, D_517), u1_struct_0(D_516))=k2_tmap_1(D_517, B_519, k2_tmap_1(A_520, B_519, C_518, D_517), D_516) | ~m1_pre_topc(D_516, D_517) | ~v1_funct_2(k2_tmap_1(A_520, B_519, C_518, D_517), u1_struct_0(D_517), u1_struct_0(B_519)) | ~v1_funct_1(k2_tmap_1(A_520, B_519, C_518, D_517)) | ~l1_pre_topc(B_519) | ~v2_pre_topc(B_519) | v2_struct_0(B_519) | ~l1_pre_topc(D_517) | ~v2_pre_topc(D_517) | v2_struct_0(D_517) | ~l1_struct_0(D_517) | ~m1_subset_1(C_518, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_520), u1_struct_0(B_519)))) | ~v1_funct_2(C_518, u1_struct_0(A_520), u1_struct_0(B_519)) | ~v1_funct_1(C_518) | ~l1_struct_0(B_519) | ~l1_struct_0(A_520))), inference(resolution, [status(thm)], [c_18, c_437])).
% 8.27/3.09  tff(c_1936, plain, (![D_517, D_516]: (k2_partfun1(u1_struct_0(D_517), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_517), u1_struct_0(D_516))=k2_tmap_1(D_517, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_517), D_516) | ~m1_pre_topc(D_516, D_517) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_517), u1_struct_0(D_517), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_517)) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(D_517) | ~v2_pre_topc(D_517) | v2_struct_0(D_517) | ~l1_struct_0(D_517) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_50, c_1920])).
% 8.27/3.09  tff(c_1961, plain, (![D_517, D_516]: (k2_partfun1(u1_struct_0(D_517), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_517), u1_struct_0(D_516))=k2_tmap_1(D_517, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_517), D_516) | ~m1_pre_topc(D_516, D_517) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_517), u1_struct_0(D_517), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_517)) | v2_struct_0('#skF_2') | ~l1_pre_topc(D_517) | ~v2_pre_topc(D_517) | v2_struct_0(D_517) | ~l1_struct_0(D_517))), inference(demodulation, [status(thm), theory('equality')], [c_322, c_366, c_54, c_52, c_66, c_64, c_1936])).
% 8.27/3.09  tff(c_4041, plain, (![D_632, D_633]: (k2_partfun1(u1_struct_0(D_632), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_632), u1_struct_0(D_633))=k2_tmap_1(D_632, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_632), D_633) | ~m1_pre_topc(D_633, D_632) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_632), u1_struct_0(D_632), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_632)) | ~l1_pre_topc(D_632) | ~v2_pre_topc(D_632) | v2_struct_0(D_632) | ~l1_struct_0(D_632))), inference(negUnitSimplification, [status(thm)], [c_68, c_1961])).
% 8.27/3.09  tff(c_16, plain, (![D_62, A_34, B_50, C_58, E_64]: (k3_tmap_1(A_34, B_50, C_58, D_62, E_64)=k2_partfun1(u1_struct_0(C_58), u1_struct_0(B_50), E_64, u1_struct_0(D_62)) | ~m1_pre_topc(D_62, C_58) | ~m1_subset_1(E_64, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_58), u1_struct_0(B_50)))) | ~v1_funct_2(E_64, u1_struct_0(C_58), u1_struct_0(B_50)) | ~v1_funct_1(E_64) | ~m1_pre_topc(D_62, A_34) | ~m1_pre_topc(C_58, A_34) | ~l1_pre_topc(B_50) | ~v2_pre_topc(B_50) | v2_struct_0(B_50) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.27/3.09  tff(c_934, plain, (![A_34, D_62]: (k3_tmap_1(A_34, '#skF_2', '#skF_4', D_62, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_62)) | ~m1_pre_topc(D_62, '#skF_4') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc(D_62, A_34) | ~m1_pre_topc('#skF_4', A_34) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34))), inference(resolution, [status(thm)], [c_917, c_16])).
% 8.27/3.09  tff(c_953, plain, (![A_34, D_62]: (k3_tmap_1(A_34, '#skF_2', '#skF_4', D_62, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_62)) | ~m1_pre_topc(D_62, '#skF_4') | ~m1_pre_topc(D_62, A_34) | ~m1_pre_topc('#skF_4', A_34) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_923, c_920, c_934])).
% 8.27/3.09  tff(c_954, plain, (![A_34, D_62]: (k3_tmap_1(A_34, '#skF_2', '#skF_4', D_62, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_62)) | ~m1_pre_topc(D_62, '#skF_4') | ~m1_pre_topc(D_62, A_34) | ~m1_pre_topc('#skF_4', A_34) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34))), inference(negUnitSimplification, [status(thm)], [c_68, c_953])).
% 8.27/3.09  tff(c_4064, plain, (![A_34, D_633]: (k3_tmap_1(A_34, '#skF_2', '#skF_4', D_633, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), D_633) | ~m1_pre_topc(D_633, '#skF_4') | ~m1_pre_topc(D_633, A_34) | ~m1_pre_topc('#skF_4', A_34) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34) | ~m1_pre_topc(D_633, '#skF_4') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4041, c_954])).
% 8.27/3.09  tff(c_4134, plain, (![A_34, D_633]: (k3_tmap_1(A_34, '#skF_2', '#skF_4', D_633, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), D_633) | ~m1_pre_topc(D_633, A_34) | ~m1_pre_topc('#skF_4', A_34) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34) | ~m1_pre_topc(D_633, '#skF_4') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1006, c_125, c_102, c_923, c_920, c_4064])).
% 8.27/3.09  tff(c_4324, plain, (![A_640, D_641]: (k3_tmap_1(A_640, '#skF_2', '#skF_4', D_641, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), D_641) | ~m1_pre_topc(D_641, A_640) | ~m1_pre_topc('#skF_4', A_640) | ~l1_pre_topc(A_640) | ~v2_pre_topc(A_640) | v2_struct_0(A_640) | ~m1_pre_topc(D_641, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_4134])).
% 8.27/3.09  tff(c_4390, plain, (![D_641, A_640]: (m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), D_641), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_641), u1_struct_0('#skF_2')))) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc(D_641, A_640) | ~m1_pre_topc('#skF_4', A_640) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_640) | ~v2_pre_topc(A_640) | v2_struct_0(A_640) | ~m1_pre_topc(D_641, A_640) | ~m1_pre_topc('#skF_4', A_640) | ~l1_pre_topc(A_640) | ~v2_pre_topc(A_640) | v2_struct_0(A_640) | ~m1_pre_topc(D_641, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4324, c_24])).
% 8.27/3.09  tff(c_4447, plain, (![D_641, A_640]: (m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), D_641), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_641), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2') | ~m1_pre_topc(D_641, A_640) | ~m1_pre_topc('#skF_4', A_640) | ~l1_pre_topc(A_640) | ~v2_pre_topc(A_640) | v2_struct_0(A_640) | ~m1_pre_topc(D_641, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_923, c_920, c_917, c_4390])).
% 8.27/3.09  tff(c_5184, plain, (![D_660, A_661]: (m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), D_660), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_660), u1_struct_0('#skF_2')))) | ~m1_pre_topc(D_660, A_661) | ~m1_pre_topc('#skF_4', A_661) | ~l1_pre_topc(A_661) | ~v2_pre_topc(A_661) | v2_struct_0(A_661) | ~m1_pre_topc(D_660, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_68, c_4447])).
% 8.27/3.09  tff(c_5198, plain, (m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_5184])).
% 8.27/3.09  tff(c_5224, plain, (m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_72, c_70, c_56, c_5198])).
% 8.27/3.09  tff(c_5225, plain, (m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_5224])).
% 8.27/3.09  tff(c_14, plain, (![A_19, B_27, C_31, D_33]: (k2_partfun1(u1_struct_0(A_19), u1_struct_0(B_27), C_31, u1_struct_0(D_33))=k2_tmap_1(A_19, B_27, C_31, D_33) | ~m1_pre_topc(D_33, A_19) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_19), u1_struct_0(B_27)))) | ~v1_funct_2(C_31, u1_struct_0(A_19), u1_struct_0(B_27)) | ~v1_funct_1(C_31) | ~l1_pre_topc(B_27) | ~v2_pre_topc(B_27) | v2_struct_0(B_27) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.27/3.09  tff(c_938, plain, (![D_33]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_33))=k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), D_33) | ~m1_pre_topc(D_33, '#skF_4') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_917, c_14])).
% 8.27/3.09  tff(c_961, plain, (![D_33]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_33))=k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), D_33) | ~m1_pre_topc(D_33, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_102, c_66, c_64, c_923, c_920, c_938])).
% 8.27/3.09  tff(c_962, plain, (![D_33]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_33))=k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), D_33) | ~m1_pre_topc(D_33, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_68, c_961])).
% 8.27/3.09  tff(c_34, plain, (![E_198, A_138, D_194, C_186, B_170, F_200]: (r2_funct_2(u1_struct_0(E_198), u1_struct_0(B_170), k3_tmap_1(A_138, B_170, D_194, E_198, k3_tmap_1(A_138, B_170, C_186, D_194, F_200)), k3_tmap_1(A_138, B_170, C_186, E_198, F_200)) | ~m1_subset_1(F_200, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_186), u1_struct_0(B_170)))) | ~v1_funct_2(F_200, u1_struct_0(C_186), u1_struct_0(B_170)) | ~v1_funct_1(F_200) | ~m1_pre_topc(E_198, D_194) | ~m1_pre_topc(D_194, C_186) | ~m1_pre_topc(E_198, A_138) | v2_struct_0(E_198) | ~m1_pre_topc(D_194, A_138) | v2_struct_0(D_194) | ~m1_pre_topc(C_186, A_138) | v2_struct_0(C_186) | ~l1_pre_topc(B_170) | ~v2_pre_topc(B_170) | v2_struct_0(B_170) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_274])).
% 8.27/3.09  tff(c_897, plain, (![D_194]: (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', D_194, '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', D_194, '#skF_5')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', D_194) | ~m1_pre_topc(D_194, '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc(D_194, '#skF_1') | v2_struct_0(D_194) | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_886, c_34])).
% 8.27/3.09  tff(c_913, plain, (![D_194]: (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', D_194, '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', D_194, '#skF_5')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc('#skF_4', D_194) | v2_struct_0('#skF_4') | ~m1_pre_topc(D_194, '#skF_1') | v2_struct_0(D_194) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_547, c_56, c_54, c_52, c_50, c_897])).
% 8.27/3.09  tff(c_1518, plain, (![D_492]: (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', D_492, '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', D_492, '#skF_5')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc('#skF_4', D_492) | ~m1_pre_topc(D_492, '#skF_1') | v2_struct_0(D_492))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_58, c_913])).
% 8.27/3.09  tff(c_1523, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_886, c_1518])).
% 8.27/3.09  tff(c_1534, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1523])).
% 8.27/3.09  tff(c_1535, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_58, c_1534])).
% 8.27/3.09  tff(c_1542, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_1535])).
% 8.27/3.09  tff(c_1545, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_30, c_1542])).
% 8.27/3.09  tff(c_1549, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_1545])).
% 8.27/3.09  tff(c_1551, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_1535])).
% 8.27/3.09  tff(c_3651, plain, (![A_606, D_607]: (k3_tmap_1(A_606, '#skF_2', '#skF_4', D_607, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_607)) | ~m1_pre_topc(D_607, '#skF_4') | ~m1_pre_topc(D_607, A_606) | ~m1_pre_topc('#skF_4', A_606) | ~l1_pre_topc(A_606) | ~v2_pre_topc(A_606) | v2_struct_0(A_606))), inference(negUnitSimplification, [status(thm)], [c_68, c_953])).
% 8.27/3.09  tff(c_409, plain, (![A_368, B_369, C_370, D_371]: (v1_funct_2(k2_tmap_1(A_368, B_369, C_370, D_371), u1_struct_0(D_371), u1_struct_0(B_369)) | ~l1_struct_0(D_371) | ~m1_subset_1(C_370, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_368), u1_struct_0(B_369)))) | ~v1_funct_2(C_370, u1_struct_0(A_368), u1_struct_0(B_369)) | ~v1_funct_1(C_370) | ~l1_struct_0(B_369) | ~l1_struct_0(A_368))), inference(cnfTransformation, [status(thm)], [f_154])).
% 8.27/3.09  tff(c_411, plain, (![D_371]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_371), u1_struct_0(D_371), u1_struct_0('#skF_2')) | ~l1_struct_0(D_371) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_50, c_409])).
% 8.27/3.09  tff(c_414, plain, (![D_371]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_371), u1_struct_0(D_371), u1_struct_0('#skF_2')) | ~l1_struct_0(D_371))), inference(demodulation, [status(thm), theory('equality')], [c_322, c_366, c_54, c_52, c_411])).
% 8.27/3.09  tff(c_1085, plain, (![D_452, A_454, C_453, B_455, A_456, D_451]: (v1_funct_1(k3_tmap_1(A_454, B_455, D_452, D_451, k2_tmap_1(A_456, B_455, C_453, D_452))) | ~v1_funct_2(k2_tmap_1(A_456, B_455, C_453, D_452), u1_struct_0(D_452), u1_struct_0(B_455)) | ~v1_funct_1(k2_tmap_1(A_456, B_455, C_453, D_452)) | ~m1_pre_topc(D_451, A_454) | ~m1_pre_topc(D_452, A_454) | ~l1_pre_topc(B_455) | ~v2_pre_topc(B_455) | v2_struct_0(B_455) | ~l1_pre_topc(A_454) | ~v2_pre_topc(A_454) | v2_struct_0(A_454) | ~l1_struct_0(D_452) | ~m1_subset_1(C_453, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_456), u1_struct_0(B_455)))) | ~v1_funct_2(C_453, u1_struct_0(A_456), u1_struct_0(B_455)) | ~v1_funct_1(C_453) | ~l1_struct_0(B_455) | ~l1_struct_0(A_456))), inference(resolution, [status(thm)], [c_18, c_426])).
% 8.27/3.09  tff(c_1101, plain, (![A_454, D_371, D_451]: (v1_funct_1(k3_tmap_1(A_454, '#skF_2', D_371, D_451, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_371))) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_371)) | ~m1_pre_topc(D_451, A_454) | ~m1_pre_topc(D_371, A_454) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_454) | ~v2_pre_topc(A_454) | v2_struct_0(A_454) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1') | ~l1_struct_0(D_371))), inference(resolution, [status(thm)], [c_414, c_1085])).
% 8.27/3.09  tff(c_1129, plain, (![A_454, D_371, D_451]: (v1_funct_1(k3_tmap_1(A_454, '#skF_2', D_371, D_451, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_371))) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_371)) | ~m1_pre_topc(D_451, A_454) | ~m1_pre_topc(D_371, A_454) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_454) | ~v2_pre_topc(A_454) | v2_struct_0(A_454) | ~l1_struct_0(D_371))), inference(demodulation, [status(thm), theory('equality')], [c_322, c_366, c_54, c_52, c_50, c_66, c_64, c_1101])).
% 8.27/3.09  tff(c_1130, plain, (![A_454, D_371, D_451]: (v1_funct_1(k3_tmap_1(A_454, '#skF_2', D_371, D_451, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_371))) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_371)) | ~m1_pre_topc(D_451, A_454) | ~m1_pre_topc(D_371, A_454) | ~l1_pre_topc(A_454) | ~v2_pre_topc(A_454) | v2_struct_0(A_454) | ~l1_struct_0(D_371))), inference(negUnitSimplification, [status(thm)], [c_68, c_1129])).
% 8.27/3.09  tff(c_3667, plain, (![D_607, A_606]: (v1_funct_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_607))) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc(D_607, A_606) | ~m1_pre_topc('#skF_4', A_606) | ~l1_pre_topc(A_606) | ~v2_pre_topc(A_606) | v2_struct_0(A_606) | ~l1_struct_0('#skF_4') | ~m1_pre_topc(D_607, '#skF_4') | ~m1_pre_topc(D_607, A_606) | ~m1_pre_topc('#skF_4', A_606) | ~l1_pre_topc(A_606) | ~v2_pre_topc(A_606) | v2_struct_0(A_606))), inference(superposition, [status(thm), theory('equality')], [c_3651, c_1130])).
% 8.27/3.09  tff(c_3746, plain, (![D_608, A_609]: (v1_funct_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_608))) | ~m1_pre_topc(D_608, '#skF_4') | ~m1_pre_topc(D_608, A_609) | ~m1_pre_topc('#skF_4', A_609) | ~l1_pre_topc(A_609) | ~v2_pre_topc(A_609) | v2_struct_0(A_609))), inference(demodulation, [status(thm), theory('equality')], [c_1006, c_923, c_3667])).
% 8.27/3.09  tff(c_3764, plain, (v1_funct_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_3746])).
% 8.27/3.09  tff(c_3794, plain, (v1_funct_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_102, c_1551, c_48, c_3764])).
% 8.27/3.09  tff(c_3795, plain, (v1_funct_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_58, c_3794])).
% 8.27/3.09  tff(c_3811, plain, (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_962, c_3795])).
% 8.27/3.09  tff(c_3815, plain, (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_3811])).
% 8.27/3.09  tff(c_461, plain, (![B_66, D_391, A_390, A_65, C_67, D_68]: (v1_funct_2(k3_tmap_1(A_390, B_66, D_68, D_391, k2_tmap_1(A_65, B_66, C_67, D_68)), u1_struct_0(D_391), u1_struct_0(B_66)) | ~v1_funct_2(k2_tmap_1(A_65, B_66, C_67, D_68), u1_struct_0(D_68), u1_struct_0(B_66)) | ~v1_funct_1(k2_tmap_1(A_65, B_66, C_67, D_68)) | ~m1_pre_topc(D_391, A_390) | ~m1_pre_topc(D_68, A_390) | ~l1_pre_topc(B_66) | ~v2_pre_topc(B_66) | v2_struct_0(B_66) | ~l1_pre_topc(A_390) | ~v2_pre_topc(A_390) | v2_struct_0(A_390) | ~l1_struct_0(D_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_65), u1_struct_0(B_66)))) | ~v1_funct_2(C_67, u1_struct_0(A_65), u1_struct_0(B_66)) | ~v1_funct_1(C_67) | ~l1_struct_0(B_66) | ~l1_struct_0(A_65))), inference(resolution, [status(thm)], [c_18, c_456])).
% 8.27/3.09  tff(c_3673, plain, (![D_607, A_606]: (v1_funct_2(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_607)), u1_struct_0(D_607), u1_struct_0('#skF_2')) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc(D_607, A_606) | ~m1_pre_topc('#skF_4', A_606) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_606) | ~v2_pre_topc(A_606) | v2_struct_0(A_606) | ~l1_struct_0('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1') | ~m1_pre_topc(D_607, '#skF_4') | ~m1_pre_topc(D_607, A_606) | ~m1_pre_topc('#skF_4', A_606) | ~l1_pre_topc(A_606) | ~v2_pre_topc(A_606) | v2_struct_0(A_606))), inference(superposition, [status(thm), theory('equality')], [c_3651, c_461])).
% 8.27/3.09  tff(c_3725, plain, (![D_607, A_606]: (v1_funct_2(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_607)), u1_struct_0(D_607), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_pre_topc(D_607, '#skF_4') | ~m1_pre_topc(D_607, A_606) | ~m1_pre_topc('#skF_4', A_606) | ~l1_pre_topc(A_606) | ~v2_pre_topc(A_606) | v2_struct_0(A_606))), inference(demodulation, [status(thm), theory('equality')], [c_322, c_366, c_54, c_52, c_50, c_1006, c_66, c_64, c_923, c_920, c_3673])).
% 8.27/3.09  tff(c_3881, plain, (![D_618, A_619]: (v1_funct_2(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_618)), u1_struct_0(D_618), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_618, '#skF_4') | ~m1_pre_topc(D_618, A_619) | ~m1_pre_topc('#skF_4', A_619) | ~l1_pre_topc(A_619) | ~v2_pre_topc(A_619) | v2_struct_0(A_619))), inference(negUnitSimplification, [status(thm)], [c_68, c_3725])).
% 8.27/3.09  tff(c_3895, plain, (v1_funct_2(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_3881])).
% 8.27/3.09  tff(c_3921, plain, (v1_funct_2(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_56, c_48, c_3895])).
% 8.27/3.09  tff(c_3922, plain, (v1_funct_2(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_74, c_3921])).
% 8.27/3.09  tff(c_3964, plain, (v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_962, c_3922])).
% 8.27/3.09  tff(c_3968, plain, (v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_3964])).
% 8.27/3.09  tff(c_546, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_529])).
% 8.27/3.09  tff(c_606, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_546, c_446])).
% 8.27/3.09  tff(c_613, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_606])).
% 8.27/3.09  tff(c_627, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_613, c_435])).
% 8.27/3.09  tff(c_637, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_547, c_60, c_627])).
% 8.27/3.09  tff(c_638, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_74, c_637])).
% 8.27/3.09  tff(c_624, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_613, c_465])).
% 8.27/3.09  tff(c_634, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_547, c_60, c_624])).
% 8.27/3.09  tff(c_635, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_74, c_634])).
% 8.27/3.09  tff(c_621, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_613, c_24])).
% 8.27/3.09  tff(c_631, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_547, c_60, c_54, c_52, c_50, c_621])).
% 8.27/3.09  tff(c_632, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_631])).
% 8.27/3.09  tff(c_762, plain, (![A_420, E_421, F_424, C_422, D_425, B_423]: (r2_funct_2(u1_struct_0(E_421), u1_struct_0(B_423), k3_tmap_1(A_420, B_423, D_425, E_421, k3_tmap_1(A_420, B_423, C_422, D_425, F_424)), k3_tmap_1(A_420, B_423, C_422, E_421, F_424)) | ~m1_subset_1(F_424, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_422), u1_struct_0(B_423)))) | ~v1_funct_2(F_424, u1_struct_0(C_422), u1_struct_0(B_423)) | ~v1_funct_1(F_424) | ~m1_pre_topc(E_421, D_425) | ~m1_pre_topc(D_425, C_422) | ~m1_pre_topc(E_421, A_420) | v2_struct_0(E_421) | ~m1_pre_topc(D_425, A_420) | v2_struct_0(D_425) | ~m1_pre_topc(C_422, A_420) | v2_struct_0(C_422) | ~l1_pre_topc(B_423) | ~v2_pre_topc(B_423) | v2_struct_0(B_423) | ~l1_pre_topc(A_420) | ~v2_pre_topc(A_420) | v2_struct_0(A_420))), inference(cnfTransformation, [status(thm)], [f_274])).
% 8.27/3.09  tff(c_776, plain, (![D_425]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', D_425, '#skF_3', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', D_425, '#skF_5')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_3', D_425) | ~m1_pre_topc(D_425, '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc(D_425, '#skF_1') | v2_struct_0(D_425) | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_613, c_762])).
% 8.27/3.09  tff(c_788, plain, (![D_425]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', D_425, '#skF_3', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', D_425, '#skF_5')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc('#skF_3', D_425) | v2_struct_0('#skF_3') | ~m1_pre_topc(D_425, '#skF_1') | v2_struct_0(D_425) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_547, c_60, c_54, c_52, c_50, c_776])).
% 8.27/3.09  tff(c_1552, plain, (![D_493]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', D_493, '#skF_3', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', D_493, '#skF_5')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc('#skF_3', D_493) | ~m1_pre_topc(D_493, '#skF_1') | v2_struct_0(D_493))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_62, c_788])).
% 8.27/3.09  tff(c_1557, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_886, c_1552])).
% 8.27/3.09  tff(c_1568, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_48, c_1557])).
% 8.27/3.09  tff(c_1569, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_1568])).
% 8.27/3.09  tff(c_4361, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4324, c_1569])).
% 8.27/3.09  tff(c_4423, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_72, c_70, c_56, c_60, c_4361])).
% 8.27/3.09  tff(c_4424, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_74, c_4423])).
% 8.27/3.09  tff(c_4, plain, (![D_4, C_3, A_1, B_2]: (D_4=C_3 | ~r2_funct_2(A_1, B_2, C_3, D_4) | ~m1_subset_1(D_4, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_4, A_1, B_2) | ~v1_funct_1(D_4) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(C_3, A_1, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.27/3.09  tff(c_4458, plain, (k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_4424, c_4])).
% 8.27/3.09  tff(c_4461, plain, (k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3') | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_3815, c_3968, c_638, c_635, c_632, c_4458])).
% 8.27/3.09  tff(c_5473, plain, (k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5225, c_4461])).
% 8.27/3.09  tff(c_640, plain, (![D_416, C_419, A_415, B_418, F_417]: (r1_tmap_1(D_416, A_415, k2_tmap_1(B_418, A_415, C_419, D_416), F_417) | ~r1_tmap_1(B_418, A_415, C_419, F_417) | ~m1_subset_1(F_417, u1_struct_0(D_416)) | ~m1_subset_1(F_417, u1_struct_0(B_418)) | ~m1_pre_topc(D_416, B_418) | v2_struct_0(D_416) | ~m1_subset_1(C_419, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_418), u1_struct_0(A_415)))) | ~v1_funct_2(C_419, u1_struct_0(B_418), u1_struct_0(A_415)) | ~v1_funct_1(C_419) | ~l1_pre_topc(B_418) | ~v2_pre_topc(B_418) | v2_struct_0(B_418) | ~l1_pre_topc(A_415) | ~v2_pre_topc(A_415) | v2_struct_0(A_415))), inference(cnfTransformation, [status(thm)], [f_228])).
% 8.27/3.09  tff(c_3078, plain, (![D_578, D_583, C_580, F_579, A_582, B_581]: (r1_tmap_1(D_583, B_581, k2_tmap_1(D_578, B_581, k2_tmap_1(A_582, B_581, C_580, D_578), D_583), F_579) | ~r1_tmap_1(D_578, B_581, k2_tmap_1(A_582, B_581, C_580, D_578), F_579) | ~m1_subset_1(F_579, u1_struct_0(D_583)) | ~m1_subset_1(F_579, u1_struct_0(D_578)) | ~m1_pre_topc(D_583, D_578) | v2_struct_0(D_583) | ~v1_funct_2(k2_tmap_1(A_582, B_581, C_580, D_578), u1_struct_0(D_578), u1_struct_0(B_581)) | ~v1_funct_1(k2_tmap_1(A_582, B_581, C_580, D_578)) | ~l1_pre_topc(D_578) | ~v2_pre_topc(D_578) | v2_struct_0(D_578) | ~l1_pre_topc(B_581) | ~v2_pre_topc(B_581) | v2_struct_0(B_581) | ~l1_struct_0(D_578) | ~m1_subset_1(C_580, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_582), u1_struct_0(B_581)))) | ~v1_funct_2(C_580, u1_struct_0(A_582), u1_struct_0(B_581)) | ~v1_funct_1(C_580) | ~l1_struct_0(B_581) | ~l1_struct_0(A_582))), inference(resolution, [status(thm)], [c_18, c_640])).
% 8.27/3.09  tff(c_3100, plain, (![D_583, D_371, F_579]: (r1_tmap_1(D_583, '#skF_2', k2_tmap_1(D_371, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_371), D_583), F_579) | ~r1_tmap_1(D_371, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_371), F_579) | ~m1_subset_1(F_579, u1_struct_0(D_583)) | ~m1_subset_1(F_579, u1_struct_0(D_371)) | ~m1_pre_topc(D_583, D_371) | v2_struct_0(D_583) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_371)) | ~l1_pre_topc(D_371) | ~v2_pre_topc(D_371) | v2_struct_0(D_371) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1') | ~l1_struct_0(D_371))), inference(resolution, [status(thm)], [c_414, c_3078])).
% 8.27/3.09  tff(c_3136, plain, (![D_583, D_371, F_579]: (r1_tmap_1(D_583, '#skF_2', k2_tmap_1(D_371, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_371), D_583), F_579) | ~r1_tmap_1(D_371, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_371), F_579) | ~m1_subset_1(F_579, u1_struct_0(D_583)) | ~m1_subset_1(F_579, u1_struct_0(D_371)) | ~m1_pre_topc(D_583, D_371) | v2_struct_0(D_583) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_371)) | ~l1_pre_topc(D_371) | ~v2_pre_topc(D_371) | v2_struct_0(D_371) | v2_struct_0('#skF_2') | ~l1_struct_0(D_371))), inference(demodulation, [status(thm), theory('equality')], [c_322, c_366, c_54, c_52, c_50, c_66, c_64, c_3100])).
% 8.27/3.09  tff(c_3137, plain, (![D_583, D_371, F_579]: (r1_tmap_1(D_583, '#skF_2', k2_tmap_1(D_371, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_371), D_583), F_579) | ~r1_tmap_1(D_371, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_371), F_579) | ~m1_subset_1(F_579, u1_struct_0(D_583)) | ~m1_subset_1(F_579, u1_struct_0(D_371)) | ~m1_pre_topc(D_583, D_371) | v2_struct_0(D_583) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_371)) | ~l1_pre_topc(D_371) | ~v2_pre_topc(D_371) | v2_struct_0(D_371) | ~l1_struct_0(D_371))), inference(negUnitSimplification, [status(thm)], [c_68, c_3136])).
% 8.27/3.09  tff(c_5497, plain, (![F_579]: (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), F_579) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), F_579) | ~m1_subset_1(F_579, u1_struct_0('#skF_3')) | ~m1_subset_1(F_579, u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5473, c_3137])).
% 8.27/3.09  tff(c_5552, plain, (![F_579]: (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), F_579) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), F_579) | ~m1_subset_1(F_579, u1_struct_0('#skF_3')) | ~m1_subset_1(F_579, u1_struct_0('#skF_4')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1006, c_125, c_102, c_923, c_48, c_5497])).
% 8.27/3.09  tff(c_5593, plain, (![F_671]: (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), F_671) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), F_671) | ~m1_subset_1(F_671, u1_struct_0('#skF_3')) | ~m1_subset_1(F_671, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_58, c_62, c_5552])).
% 8.27/3.09  tff(c_38, plain, (~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_335])).
% 8.27/3.09  tff(c_76, plain, (~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38])).
% 8.27/3.09  tff(c_5596, plain, (~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_5593, c_76])).
% 8.27/3.09  tff(c_5600, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_75, c_40, c_5596])).
% 8.27/3.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.27/3.09  
% 8.27/3.09  Inference rules
% 8.27/3.09  ----------------------
% 8.27/3.09  #Ref     : 0
% 8.27/3.09  #Sup     : 1003
% 8.27/3.09  #Fact    : 0
% 8.27/3.09  #Define  : 0
% 8.27/3.09  #Split   : 11
% 8.27/3.09  #Chain   : 0
% 8.27/3.09  #Close   : 0
% 8.27/3.09  
% 8.27/3.09  Ordering : KBO
% 8.27/3.09  
% 8.27/3.09  Simplification rules
% 8.27/3.09  ----------------------
% 8.27/3.09  #Subsume      : 217
% 8.27/3.09  #Demod        : 3669
% 8.27/3.09  #Tautology    : 314
% 8.27/3.09  #SimpNegUnit  : 514
% 8.27/3.09  #BackRed      : 35
% 8.27/3.09  
% 8.27/3.09  #Partial instantiations: 0
% 8.27/3.09  #Strategies tried      : 1
% 8.27/3.09  
% 8.27/3.09  Timing (in seconds)
% 8.27/3.09  ----------------------
% 8.27/3.10  Preprocessing        : 0.41
% 8.27/3.10  Parsing              : 0.21
% 8.27/3.10  CNF conversion       : 0.05
% 8.27/3.10  Main loop            : 1.82
% 8.27/3.10  Inferencing          : 0.56
% 8.27/3.10  Reduction            : 0.74
% 8.27/3.10  Demodulation         : 0.57
% 8.27/3.10  BG Simplification    : 0.06
% 8.27/3.10  Subsumption          : 0.38
% 8.27/3.10  Abstraction          : 0.08
% 8.27/3.10  MUC search           : 0.00
% 8.27/3.10  Cooper               : 0.00
% 8.27/3.10  Total                : 2.31
% 8.27/3.10  Index Insertion      : 0.00
% 8.27/3.10  Index Deletion       : 0.00
% 8.27/3.10  Index Matching       : 0.00
% 8.27/3.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
