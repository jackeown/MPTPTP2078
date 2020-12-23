%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:36 EST 2020

% Result     : Theorem 24.26s
% Output     : CNFRefutation 24.43s
% Verified   : 
% Statistics : Number of formulae       :  168 (2712 expanded)
%              Number of leaves         :   54 ( 956 expanded)
%              Depth                    :   26
%              Number of atoms          :  496 (14844 expanded)
%              Number of equality atoms :   44 (1408 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k9_subset_1 > k5_setfam_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_315,negated_conjecture,(
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
                          & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                       => ( g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) = D
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(D))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(C))
                                 => ( ( F = G
                                      & r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),G) )
                                   => r1_tmap_1(D,B,E,F) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_205,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_101,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

tff(f_117,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_212,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_144,axiom,(
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

tff(f_176,axiom,(
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

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(A)
      <=> ( r2_hidden(u1_struct_0(A),u1_pre_topc(A))
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( r1_tarski(B,u1_pre_topc(A))
               => r2_hidden(k5_setfam_1(u1_struct_0(A),B),u1_pre_topc(A)) ) )
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r2_hidden(B,u1_pre_topc(A))
                      & r2_hidden(C,u1_pre_topc(A)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(A),B,C),u1_pre_topc(A)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_201,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_194,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_tsep_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

tff(f_254,axiom,(
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

tff(c_86,plain,(
    ~ r1_tmap_1('#skF_7','#skF_5','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_90,plain,(
    '#skF_10' = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_92,plain,(
    m1_subset_1('#skF_10',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_123,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_92])).

tff(c_122,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_120,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_118,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_104,plain,(
    m1_pre_topc('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_108,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_147,plain,(
    ! [B_295,A_296] :
      ( l1_pre_topc(B_295)
      | ~ m1_pre_topc(B_295,A_296)
      | ~ l1_pre_topc(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_153,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_108,c_147])).

tff(c_160,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_153])).

tff(c_76,plain,(
    ! [A_97] :
      ( m1_pre_topc(A_97,A_97)
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_110,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_533,plain,(
    ! [C_330,A_331,B_332] :
      ( m1_subset_1(C_330,u1_struct_0(A_331))
      | ~ m1_subset_1(C_330,u1_struct_0(B_332))
      | ~ m1_pre_topc(B_332,A_331)
      | v2_struct_0(B_332)
      | ~ l1_pre_topc(A_331)
      | v2_struct_0(A_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_537,plain,(
    ! [A_331] :
      ( m1_subset_1('#skF_9',u1_struct_0(A_331))
      | ~ m1_pre_topc('#skF_6',A_331)
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc(A_331)
      | v2_struct_0(A_331) ) ),
    inference(resolution,[status(thm)],[c_123,c_533])).

tff(c_549,plain,(
    ! [A_335] :
      ( m1_subset_1('#skF_9',u1_struct_0(A_335))
      | ~ m1_pre_topc('#skF_6',A_335)
      | ~ l1_pre_topc(A_335)
      | v2_struct_0(A_335) ) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_537])).

tff(c_56,plain,(
    ! [C_34,A_28,B_32] :
      ( m1_subset_1(C_34,u1_struct_0(A_28))
      | ~ m1_subset_1(C_34,u1_struct_0(B_32))
      | ~ m1_pre_topc(B_32,A_28)
      | v2_struct_0(B_32)
      | ~ l1_pre_topc(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_553,plain,(
    ! [A_336,A_337] :
      ( m1_subset_1('#skF_9',u1_struct_0(A_336))
      | ~ m1_pre_topc(A_337,A_336)
      | ~ l1_pre_topc(A_336)
      | v2_struct_0(A_336)
      | ~ m1_pre_topc('#skF_6',A_337)
      | ~ l1_pre_topc(A_337)
      | v2_struct_0(A_337) ) ),
    inference(resolution,[status(thm)],[c_549,c_56])).

tff(c_569,plain,
    ( m1_subset_1('#skF_9',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_108,c_553])).

tff(c_596,plain,
    ( m1_subset_1('#skF_9',u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_118,c_569])).

tff(c_597,plain,
    ( m1_subset_1('#skF_9',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_6','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_122,c_596])).

tff(c_602,plain,(
    ~ m1_pre_topc('#skF_6','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_597])).

tff(c_608,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_602])).

tff(c_615,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_608])).

tff(c_617,plain,(
    m1_pre_topc('#skF_6','#skF_6') ),
    inference(splitRight,[status(thm)],[c_597])).

tff(c_96,plain,(
    g1_pre_topc(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_351,plain,(
    ! [A_317,B_318] :
      ( m1_pre_topc(A_317,g1_pre_topc(u1_struct_0(B_318),u1_pre_topc(B_318)))
      | ~ m1_pre_topc(A_317,B_318)
      | ~ l1_pre_topc(B_318)
      | ~ l1_pre_topc(A_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_367,plain,(
    ! [A_317] :
      ( m1_pre_topc(A_317,'#skF_7')
      | ~ m1_pre_topc(A_317,'#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ l1_pre_topc(A_317) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_351])).

tff(c_374,plain,(
    ! [A_317] :
      ( m1_pre_topc(A_317,'#skF_7')
      | ~ m1_pre_topc(A_317,'#skF_6')
      | ~ l1_pre_topc(A_317) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_367])).

tff(c_156,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_104,c_147])).

tff(c_163,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_156])).

tff(c_194,plain,(
    ! [B_306,A_307] :
      ( m1_pre_topc(B_306,A_307)
      | ~ m1_pre_topc(B_306,g1_pre_topc(u1_struct_0(A_307),u1_pre_topc(A_307)))
      | ~ l1_pre_topc(A_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_197,plain,(
    ! [B_306] :
      ( m1_pre_topc(B_306,'#skF_6')
      | ~ m1_pre_topc(B_306,'#skF_7')
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_194])).

tff(c_205,plain,(
    ! [B_308] :
      ( m1_pre_topc(B_308,'#skF_6')
      | ~ m1_pre_topc(B_308,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_197])).

tff(c_209,plain,
    ( m1_pre_topc('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_76,c_205])).

tff(c_212,plain,(
    m1_pre_topc('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_209])).

tff(c_78,plain,(
    ! [B_100,A_98] :
      ( r1_tarski(u1_struct_0(B_100),u1_struct_0(A_98))
      | ~ m1_pre_topc(B_100,A_98)
      | ~ l1_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_189,plain,(
    ! [B_302,A_303] :
      ( r1_tarski(u1_struct_0(B_302),u1_struct_0(A_303))
      | ~ m1_pre_topc(B_302,A_303)
      | ~ l1_pre_topc(A_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_700,plain,(
    ! [B_344,A_345] :
      ( u1_struct_0(B_344) = u1_struct_0(A_345)
      | ~ r1_tarski(u1_struct_0(A_345),u1_struct_0(B_344))
      | ~ m1_pre_topc(B_344,A_345)
      | ~ l1_pre_topc(A_345) ) ),
    inference(resolution,[status(thm)],[c_189,c_2])).

tff(c_711,plain,(
    ! [B_346,A_347] :
      ( u1_struct_0(B_346) = u1_struct_0(A_347)
      | ~ m1_pre_topc(A_347,B_346)
      | ~ l1_pre_topc(B_346)
      | ~ m1_pre_topc(B_346,A_347)
      | ~ l1_pre_topc(A_347) ) ),
    inference(resolution,[status(thm)],[c_78,c_700])).

tff(c_725,plain,
    ( u1_struct_0('#skF_7') = u1_struct_0('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ m1_pre_topc('#skF_6','#skF_7')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_212,c_711])).

tff(c_751,plain,
    ( u1_struct_0('#skF_7') = u1_struct_0('#skF_6')
    | ~ m1_pre_topc('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_160,c_725])).

tff(c_760,plain,(
    ~ m1_pre_topc('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_751])).

tff(c_763,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_374,c_760])).

tff(c_770,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_617,c_763])).

tff(c_772,plain,(
    m1_pre_topc('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_751])).

tff(c_771,plain,(
    u1_struct_0('#skF_7') = u1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_751])).

tff(c_116,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_172,plain,(
    ! [B_300,A_301] :
      ( v2_pre_topc(B_300)
      | ~ m1_pre_topc(B_300,A_301)
      | ~ l1_pre_topc(A_301)
      | ~ v2_pre_topc(A_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_178,plain,
    ( v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_108,c_172])).

tff(c_185,plain,(
    v2_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_118,c_178])).

tff(c_114,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_112,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_102,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_100,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_7'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_829,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_100])).

tff(c_98,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_828,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_98])).

tff(c_5087,plain,(
    ! [A_503,B_504,C_505,D_506] :
      ( k2_partfun1(u1_struct_0(A_503),u1_struct_0(B_504),C_505,u1_struct_0(D_506)) = k2_tmap_1(A_503,B_504,C_505,D_506)
      | ~ m1_pre_topc(D_506,A_503)
      | ~ m1_subset_1(C_505,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_503),u1_struct_0(B_504))))
      | ~ v1_funct_2(C_505,u1_struct_0(A_503),u1_struct_0(B_504))
      | ~ v1_funct_1(C_505)
      | ~ l1_pre_topc(B_504)
      | ~ v2_pre_topc(B_504)
      | v2_struct_0(B_504)
      | ~ l1_pre_topc(A_503)
      | ~ v2_pre_topc(A_503)
      | v2_struct_0(A_503) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_5089,plain,(
    ! [D_506] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'),'#skF_8',u1_struct_0(D_506)) = k2_tmap_1('#skF_6','#skF_5','#skF_8',D_506)
      | ~ m1_pre_topc(D_506,'#skF_6')
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_8')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_828,c_5087])).

tff(c_5099,plain,(
    ! [D_506] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'),'#skF_8',u1_struct_0(D_506)) = k2_tmap_1('#skF_6','#skF_5','#skF_8',D_506)
      | ~ m1_pre_topc(D_506,'#skF_6')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_160,c_114,c_112,c_102,c_829,c_5089])).

tff(c_5108,plain,(
    ! [D_507] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'),'#skF_8',u1_struct_0(D_507)) = k2_tmap_1('#skF_6','#skF_5','#skF_8',D_507)
      | ~ m1_pre_topc(D_507,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_116,c_5099])).

tff(c_5117,plain,
    ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'),'#skF_8',u1_struct_0('#skF_6')) = k2_tmap_1('#skF_6','#skF_5','#skF_8','#skF_7')
    | ~ m1_pre_topc('#skF_7','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_771,c_5108])).

tff(c_5121,plain,(
    k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'),'#skF_8',u1_struct_0('#skF_6')) = k2_tmap_1('#skF_6','#skF_5','#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_5117])).

tff(c_5100,plain,(
    ! [D_506] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'),'#skF_8',u1_struct_0(D_506)) = k2_tmap_1('#skF_6','#skF_5','#skF_8',D_506)
      | ~ m1_pre_topc(D_506,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_116,c_5099])).

tff(c_5125,plain,
    ( k2_tmap_1('#skF_6','#skF_5','#skF_8','#skF_7') = k2_tmap_1('#skF_6','#skF_5','#skF_8','#skF_6')
    | ~ m1_pre_topc('#skF_6','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_5121,c_5100])).

tff(c_5132,plain,(
    k2_tmap_1('#skF_6','#skF_5','#skF_8','#skF_7') = k2_tmap_1('#skF_6','#skF_5','#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_617,c_5125])).

tff(c_5136,plain,(
    k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'),'#skF_8',u1_struct_0('#skF_6')) = k2_tmap_1('#skF_6','#skF_5','#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5132,c_5121])).

tff(c_5590,plain,(
    ! [D_518,B_515,C_514,A_516,E_517] :
      ( k3_tmap_1(A_516,B_515,C_514,D_518,E_517) = k2_partfun1(u1_struct_0(C_514),u1_struct_0(B_515),E_517,u1_struct_0(D_518))
      | ~ m1_pre_topc(D_518,C_514)
      | ~ m1_subset_1(E_517,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_514),u1_struct_0(B_515))))
      | ~ v1_funct_2(E_517,u1_struct_0(C_514),u1_struct_0(B_515))
      | ~ v1_funct_1(E_517)
      | ~ m1_pre_topc(D_518,A_516)
      | ~ m1_pre_topc(C_514,A_516)
      | ~ l1_pre_topc(B_515)
      | ~ v2_pre_topc(B_515)
      | v2_struct_0(B_515)
      | ~ l1_pre_topc(A_516)
      | ~ v2_pre_topc(A_516)
      | v2_struct_0(A_516) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_5594,plain,(
    ! [A_516,B_515,D_518,E_517] :
      ( k3_tmap_1(A_516,B_515,'#skF_7',D_518,E_517) = k2_partfun1(u1_struct_0('#skF_7'),u1_struct_0(B_515),E_517,u1_struct_0(D_518))
      | ~ m1_pre_topc(D_518,'#skF_7')
      | ~ m1_subset_1(E_517,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0(B_515))))
      | ~ v1_funct_2(E_517,u1_struct_0('#skF_7'),u1_struct_0(B_515))
      | ~ v1_funct_1(E_517)
      | ~ m1_pre_topc(D_518,A_516)
      | ~ m1_pre_topc('#skF_7',A_516)
      | ~ l1_pre_topc(B_515)
      | ~ v2_pre_topc(B_515)
      | v2_struct_0(B_515)
      | ~ l1_pre_topc(A_516)
      | ~ v2_pre_topc(A_516)
      | v2_struct_0(A_516) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_771,c_5590])).

tff(c_43004,plain,(
    ! [A_1269,B_1270,D_1271,E_1272] :
      ( k3_tmap_1(A_1269,B_1270,'#skF_7',D_1271,E_1272) = k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0(B_1270),E_1272,u1_struct_0(D_1271))
      | ~ m1_pre_topc(D_1271,'#skF_7')
      | ~ m1_subset_1(E_1272,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0(B_1270))))
      | ~ v1_funct_2(E_1272,u1_struct_0('#skF_6'),u1_struct_0(B_1270))
      | ~ v1_funct_1(E_1272)
      | ~ m1_pre_topc(D_1271,A_1269)
      | ~ m1_pre_topc('#skF_7',A_1269)
      | ~ l1_pre_topc(B_1270)
      | ~ v2_pre_topc(B_1270)
      | v2_struct_0(B_1270)
      | ~ l1_pre_topc(A_1269)
      | ~ v2_pre_topc(A_1269)
      | v2_struct_0(A_1269) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_771,c_5594])).

tff(c_43006,plain,(
    ! [A_1269,D_1271] :
      ( k3_tmap_1(A_1269,'#skF_5','#skF_7',D_1271,'#skF_8') = k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'),'#skF_8',u1_struct_0(D_1271))
      | ~ m1_pre_topc(D_1271,'#skF_7')
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_8')
      | ~ m1_pre_topc(D_1271,A_1269)
      | ~ m1_pre_topc('#skF_7',A_1269)
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_1269)
      | ~ v2_pre_topc(A_1269)
      | v2_struct_0(A_1269) ) ),
    inference(resolution,[status(thm)],[c_828,c_43004])).

tff(c_43014,plain,(
    ! [A_1269,D_1271] :
      ( k3_tmap_1(A_1269,'#skF_5','#skF_7',D_1271,'#skF_8') = k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'),'#skF_8',u1_struct_0(D_1271))
      | ~ m1_pre_topc(D_1271,'#skF_7')
      | ~ m1_pre_topc(D_1271,A_1269)
      | ~ m1_pre_topc('#skF_7',A_1269)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_1269)
      | ~ v2_pre_topc(A_1269)
      | v2_struct_0(A_1269) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_112,c_102,c_829,c_43006])).

tff(c_43020,plain,(
    ! [A_1273,D_1274] :
      ( k3_tmap_1(A_1273,'#skF_5','#skF_7',D_1274,'#skF_8') = k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'),'#skF_8',u1_struct_0(D_1274))
      | ~ m1_pre_topc(D_1274,'#skF_7')
      | ~ m1_pre_topc(D_1274,A_1273)
      | ~ m1_pre_topc('#skF_7',A_1273)
      | ~ l1_pre_topc(A_1273)
      | ~ v2_pre_topc(A_1273)
      | v2_struct_0(A_1273) ) ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_43014])).

tff(c_43130,plain,
    ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'),'#skF_8',u1_struct_0('#skF_6')) = k3_tmap_1('#skF_4','#skF_5','#skF_7','#skF_6','#skF_8')
    | ~ m1_pre_topc('#skF_6','#skF_7')
    | ~ m1_pre_topc('#skF_7','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_108,c_43020])).

tff(c_43249,plain,
    ( k3_tmap_1('#skF_4','#skF_5','#skF_7','#skF_6','#skF_8') = k2_tmap_1('#skF_6','#skF_5','#skF_8','#skF_6')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_118,c_104,c_772,c_5136,c_43130])).

tff(c_43250,plain,(
    k3_tmap_1('#skF_4','#skF_5','#skF_7','#skF_6','#skF_8') = k2_tmap_1('#skF_6','#skF_5','#skF_8','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_43249])).

tff(c_88,plain,(
    r1_tmap_1('#skF_6','#skF_5',k3_tmap_1('#skF_4','#skF_5','#skF_7','#skF_6','#skF_8'),'#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_124,plain,(
    r1_tmap_1('#skF_6','#skF_5',k3_tmap_1('#skF_4','#skF_5','#skF_7','#skF_6','#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88])).

tff(c_43271,plain,(
    r1_tmap_1('#skF_6','#skF_5',k2_tmap_1('#skF_6','#skF_5','#skF_8','#skF_6'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_43250,c_124])).

tff(c_106,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_181,plain,
    ( v2_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_104,c_172])).

tff(c_188,plain,(
    v2_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_118,c_181])).

tff(c_48,plain,(
    ! [A_8] :
      ( r2_hidden(u1_struct_0(A_8),u1_pre_topc(A_8))
      | ~ v2_pre_topc(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_125,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_514,plain,(
    ! [B_327,A_328] :
      ( v3_pre_topc(B_327,A_328)
      | ~ r2_hidden(B_327,u1_pre_topc(A_328))
      | ~ m1_subset_1(B_327,k1_zfmisc_1(u1_struct_0(A_328)))
      | ~ l1_pre_topc(A_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_524,plain,(
    ! [A_329] :
      ( v3_pre_topc(u1_struct_0(A_329),A_329)
      | ~ r2_hidden(u1_struct_0(A_329),u1_pre_topc(A_329))
      | ~ l1_pre_topc(A_329) ) ),
    inference(resolution,[status(thm)],[c_125,c_514])).

tff(c_532,plain,(
    ! [A_8] :
      ( v3_pre_topc(u1_struct_0(A_8),A_8)
      | ~ v2_pre_topc(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(resolution,[status(thm)],[c_48,c_524])).

tff(c_862,plain,
    ( v3_pre_topc(u1_struct_0('#skF_6'),'#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_771,c_532])).

tff(c_919,plain,(
    v3_pre_topc(u1_struct_0('#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_188,c_862])).

tff(c_74,plain,(
    ! [B_96,A_94] :
      ( m1_subset_1(u1_struct_0(B_96),k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ m1_pre_topc(B_96,A_94)
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_1213,plain,(
    ! [B_361,A_362] :
      ( v1_tsep_1(B_361,A_362)
      | ~ v3_pre_topc(u1_struct_0(B_361),A_362)
      | ~ m1_subset_1(u1_struct_0(B_361),k1_zfmisc_1(u1_struct_0(A_362)))
      | ~ m1_pre_topc(B_361,A_362)
      | ~ l1_pre_topc(A_362)
      | ~ v2_pre_topc(A_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_2020,plain,(
    ! [B_385,A_386] :
      ( v1_tsep_1(B_385,A_386)
      | ~ v3_pre_topc(u1_struct_0(B_385),A_386)
      | ~ v2_pre_topc(A_386)
      | ~ m1_pre_topc(B_385,A_386)
      | ~ l1_pre_topc(A_386) ) ),
    inference(resolution,[status(thm)],[c_74,c_1213])).

tff(c_2029,plain,
    ( v1_tsep_1('#skF_6','#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | ~ m1_pre_topc('#skF_6','#skF_7')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_919,c_2020])).

tff(c_2044,plain,(
    v1_tsep_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_772,c_188,c_2029])).

tff(c_5091,plain,(
    ! [B_504,C_505,D_506] :
      ( k2_partfun1(u1_struct_0('#skF_7'),u1_struct_0(B_504),C_505,u1_struct_0(D_506)) = k2_tmap_1('#skF_7',B_504,C_505,D_506)
      | ~ m1_pre_topc(D_506,'#skF_7')
      | ~ m1_subset_1(C_505,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0(B_504))))
      | ~ v1_funct_2(C_505,u1_struct_0('#skF_7'),u1_struct_0(B_504))
      | ~ v1_funct_1(C_505)
      | ~ l1_pre_topc(B_504)
      | ~ v2_pre_topc(B_504)
      | v2_struct_0(B_504)
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_771,c_5087])).

tff(c_5102,plain,(
    ! [B_504,C_505,D_506] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0(B_504),C_505,u1_struct_0(D_506)) = k2_tmap_1('#skF_7',B_504,C_505,D_506)
      | ~ m1_pre_topc(D_506,'#skF_7')
      | ~ m1_subset_1(C_505,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0(B_504))))
      | ~ v1_funct_2(C_505,u1_struct_0('#skF_6'),u1_struct_0(B_504))
      | ~ v1_funct_1(C_505)
      | ~ l1_pre_topc(B_504)
      | ~ v2_pre_topc(B_504)
      | v2_struct_0(B_504)
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_163,c_771,c_771,c_5091])).

tff(c_6085,plain,(
    ! [B_543,C_544,D_545] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0(B_543),C_544,u1_struct_0(D_545)) = k2_tmap_1('#skF_7',B_543,C_544,D_545)
      | ~ m1_pre_topc(D_545,'#skF_7')
      | ~ m1_subset_1(C_544,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0(B_543))))
      | ~ v1_funct_2(C_544,u1_struct_0('#skF_6'),u1_struct_0(B_543))
      | ~ v1_funct_1(C_544)
      | ~ l1_pre_topc(B_543)
      | ~ v2_pre_topc(B_543)
      | v2_struct_0(B_543) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_5102])).

tff(c_6087,plain,(
    ! [D_545] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'),'#skF_8',u1_struct_0(D_545)) = k2_tmap_1('#skF_7','#skF_5','#skF_8',D_545)
      | ~ m1_pre_topc(D_545,'#skF_7')
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_8')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_828,c_6085])).

tff(c_6095,plain,(
    ! [D_545] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'),'#skF_8',u1_struct_0(D_545)) = k2_tmap_1('#skF_7','#skF_5','#skF_8',D_545)
      | ~ m1_pre_topc(D_545,'#skF_7')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_112,c_102,c_829,c_6087])).

tff(c_6101,plain,(
    ! [D_546] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'),'#skF_8',u1_struct_0(D_546)) = k2_tmap_1('#skF_7','#skF_5','#skF_8',D_546)
      | ~ m1_pre_topc(D_546,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_6095])).

tff(c_6110,plain,
    ( k2_tmap_1('#skF_7','#skF_5','#skF_8','#skF_6') = k2_tmap_1('#skF_6','#skF_5','#skF_8','#skF_6')
    | ~ m1_pre_topc('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_6101,c_5136])).

tff(c_6131,plain,(
    k2_tmap_1('#skF_7','#skF_5','#skF_8','#skF_6') = k2_tmap_1('#skF_6','#skF_5','#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_772,c_6110])).

tff(c_80,plain,(
    ! [F_163,B_133,D_157,A_101,C_149] :
      ( r1_tmap_1(B_133,A_101,C_149,F_163)
      | ~ r1_tmap_1(D_157,A_101,k2_tmap_1(B_133,A_101,C_149,D_157),F_163)
      | ~ m1_subset_1(F_163,u1_struct_0(D_157))
      | ~ m1_subset_1(F_163,u1_struct_0(B_133))
      | ~ m1_pre_topc(D_157,B_133)
      | ~ v1_tsep_1(D_157,B_133)
      | v2_struct_0(D_157)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_133),u1_struct_0(A_101))))
      | ~ v1_funct_2(C_149,u1_struct_0(B_133),u1_struct_0(A_101))
      | ~ v1_funct_1(C_149)
      | ~ l1_pre_topc(B_133)
      | ~ v2_pre_topc(B_133)
      | v2_struct_0(B_133)
      | ~ l1_pre_topc(A_101)
      | ~ v2_pre_topc(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_6148,plain,(
    ! [F_163] :
      ( r1_tmap_1('#skF_7','#skF_5','#skF_8',F_163)
      | ~ r1_tmap_1('#skF_6','#skF_5',k2_tmap_1('#skF_6','#skF_5','#skF_8','#skF_6'),F_163)
      | ~ m1_subset_1(F_163,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(F_163,u1_struct_0('#skF_7'))
      | ~ m1_pre_topc('#skF_6','#skF_7')
      | ~ v1_tsep_1('#skF_6','#skF_7')
      | v2_struct_0('#skF_6')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_7'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_8')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6131,c_80])).

tff(c_6152,plain,(
    ! [F_163] :
      ( r1_tmap_1('#skF_7','#skF_5','#skF_8',F_163)
      | ~ r1_tmap_1('#skF_6','#skF_5',k2_tmap_1('#skF_6','#skF_5','#skF_8','#skF_6'),F_163)
      | ~ m1_subset_1(F_163,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_7')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_112,c_188,c_163,c_102,c_829,c_771,c_828,c_771,c_2044,c_772,c_771,c_6148])).

tff(c_6153,plain,(
    ! [F_163] :
      ( r1_tmap_1('#skF_7','#skF_5','#skF_8',F_163)
      | ~ r1_tmap_1('#skF_6','#skF_5',k2_tmap_1('#skF_6','#skF_5','#skF_8','#skF_6'),F_163)
      | ~ m1_subset_1(F_163,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_106,c_110,c_6152])).

tff(c_43278,plain,
    ( r1_tmap_1('#skF_7','#skF_5','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_43271,c_6153])).

tff(c_43283,plain,(
    r1_tmap_1('#skF_7','#skF_5','#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_43278])).

tff(c_43285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_43283])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:53:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 24.26/15.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.26/15.63  
% 24.26/15.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.26/15.63  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k9_subset_1 > k5_setfam_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_3
% 24.26/15.63  
% 24.26/15.63  %Foreground sorts:
% 24.26/15.63  
% 24.26/15.63  
% 24.26/15.63  %Background operators:
% 24.26/15.63  
% 24.26/15.63  
% 24.26/15.63  %Foreground operators:
% 24.26/15.63  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 24.26/15.63  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 24.26/15.63  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 24.26/15.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 24.26/15.63  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 24.26/15.63  tff('#skF_2', type, '#skF_2': $i > $i).
% 24.26/15.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 24.26/15.63  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 24.26/15.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 24.26/15.63  tff('#skF_1', type, '#skF_1': $i > $i).
% 24.26/15.63  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 24.26/15.63  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 24.26/15.63  tff('#skF_7', type, '#skF_7': $i).
% 24.26/15.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 24.26/15.63  tff('#skF_10', type, '#skF_10': $i).
% 24.26/15.63  tff('#skF_5', type, '#skF_5': $i).
% 24.26/15.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 24.26/15.63  tff('#skF_6', type, '#skF_6': $i).
% 24.26/15.63  tff('#skF_9', type, '#skF_9': $i).
% 24.26/15.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 24.26/15.63  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 24.26/15.63  tff('#skF_8', type, '#skF_8': $i).
% 24.26/15.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 24.26/15.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 24.26/15.63  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 24.26/15.63  tff('#skF_4', type, '#skF_4': $i).
% 24.26/15.63  tff('#skF_3', type, '#skF_3': $i > $i).
% 24.26/15.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 24.26/15.63  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 24.26/15.63  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 24.26/15.63  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 24.26/15.63  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 24.26/15.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 24.26/15.63  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 24.26/15.63  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 24.26/15.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 24.26/15.63  
% 24.43/15.66  tff(f_315, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 24.43/15.66  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 24.43/15.66  tff(f_205, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 24.43/15.66  tff(f_101, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 24.43/15.66  tff(f_117, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 24.43/15.66  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 24.43/15.66  tff(f_212, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 24.43/15.66  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 24.43/15.66  tff(f_44, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 24.43/15.66  tff(f_144, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 24.43/15.66  tff(f_176, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 24.43/15.66  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 24.43/15.66  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 24.43/15.66  tff(f_35, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 24.43/15.66  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 24.43/15.66  tff(f_201, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 24.43/15.66  tff(f_194, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 24.43/15.66  tff(f_254, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tmap_1)).
% 24.43/15.66  tff(c_86, plain, (~r1_tmap_1('#skF_7', '#skF_5', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.43/15.66  tff(c_90, plain, ('#skF_10'='#skF_9'), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.43/15.66  tff(c_92, plain, (m1_subset_1('#skF_10', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.43/15.66  tff(c_123, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_92])).
% 24.43/15.66  tff(c_122, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.43/15.66  tff(c_120, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.43/15.66  tff(c_118, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.43/15.66  tff(c_104, plain, (m1_pre_topc('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.43/15.66  tff(c_108, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.43/15.66  tff(c_147, plain, (![B_295, A_296]: (l1_pre_topc(B_295) | ~m1_pre_topc(B_295, A_296) | ~l1_pre_topc(A_296))), inference(cnfTransformation, [status(thm)], [f_85])).
% 24.43/15.66  tff(c_153, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_108, c_147])).
% 24.43/15.66  tff(c_160, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_153])).
% 24.43/15.66  tff(c_76, plain, (![A_97]: (m1_pre_topc(A_97, A_97) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_205])).
% 24.43/15.66  tff(c_110, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.43/15.66  tff(c_533, plain, (![C_330, A_331, B_332]: (m1_subset_1(C_330, u1_struct_0(A_331)) | ~m1_subset_1(C_330, u1_struct_0(B_332)) | ~m1_pre_topc(B_332, A_331) | v2_struct_0(B_332) | ~l1_pre_topc(A_331) | v2_struct_0(A_331))), inference(cnfTransformation, [status(thm)], [f_101])).
% 24.43/15.66  tff(c_537, plain, (![A_331]: (m1_subset_1('#skF_9', u1_struct_0(A_331)) | ~m1_pre_topc('#skF_6', A_331) | v2_struct_0('#skF_6') | ~l1_pre_topc(A_331) | v2_struct_0(A_331))), inference(resolution, [status(thm)], [c_123, c_533])).
% 24.43/15.66  tff(c_549, plain, (![A_335]: (m1_subset_1('#skF_9', u1_struct_0(A_335)) | ~m1_pre_topc('#skF_6', A_335) | ~l1_pre_topc(A_335) | v2_struct_0(A_335))), inference(negUnitSimplification, [status(thm)], [c_110, c_537])).
% 24.43/15.66  tff(c_56, plain, (![C_34, A_28, B_32]: (m1_subset_1(C_34, u1_struct_0(A_28)) | ~m1_subset_1(C_34, u1_struct_0(B_32)) | ~m1_pre_topc(B_32, A_28) | v2_struct_0(B_32) | ~l1_pre_topc(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_101])).
% 24.43/15.66  tff(c_553, plain, (![A_336, A_337]: (m1_subset_1('#skF_9', u1_struct_0(A_336)) | ~m1_pre_topc(A_337, A_336) | ~l1_pre_topc(A_336) | v2_struct_0(A_336) | ~m1_pre_topc('#skF_6', A_337) | ~l1_pre_topc(A_337) | v2_struct_0(A_337))), inference(resolution, [status(thm)], [c_549, c_56])).
% 24.43/15.66  tff(c_569, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_6', '#skF_6') | ~l1_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_108, c_553])).
% 24.43/15.66  tff(c_596, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_6', '#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_118, c_569])).
% 24.43/15.66  tff(c_597, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_6', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_110, c_122, c_596])).
% 24.43/15.66  tff(c_602, plain, (~m1_pre_topc('#skF_6', '#skF_6')), inference(splitLeft, [status(thm)], [c_597])).
% 24.43/15.66  tff(c_608, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_76, c_602])).
% 24.43/15.66  tff(c_615, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_160, c_608])).
% 24.43/15.66  tff(c_617, plain, (m1_pre_topc('#skF_6', '#skF_6')), inference(splitRight, [status(thm)], [c_597])).
% 24.43/15.66  tff(c_96, plain, (g1_pre_topc(u1_struct_0('#skF_6'), u1_pre_topc('#skF_6'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.43/15.66  tff(c_351, plain, (![A_317, B_318]: (m1_pre_topc(A_317, g1_pre_topc(u1_struct_0(B_318), u1_pre_topc(B_318))) | ~m1_pre_topc(A_317, B_318) | ~l1_pre_topc(B_318) | ~l1_pre_topc(A_317))), inference(cnfTransformation, [status(thm)], [f_117])).
% 24.43/15.66  tff(c_367, plain, (![A_317]: (m1_pre_topc(A_317, '#skF_7') | ~m1_pre_topc(A_317, '#skF_6') | ~l1_pre_topc('#skF_6') | ~l1_pre_topc(A_317))), inference(superposition, [status(thm), theory('equality')], [c_96, c_351])).
% 24.43/15.66  tff(c_374, plain, (![A_317]: (m1_pre_topc(A_317, '#skF_7') | ~m1_pre_topc(A_317, '#skF_6') | ~l1_pre_topc(A_317))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_367])).
% 24.43/15.66  tff(c_156, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_104, c_147])).
% 24.43/15.66  tff(c_163, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_156])).
% 24.43/15.66  tff(c_194, plain, (![B_306, A_307]: (m1_pre_topc(B_306, A_307) | ~m1_pre_topc(B_306, g1_pre_topc(u1_struct_0(A_307), u1_pre_topc(A_307))) | ~l1_pre_topc(A_307))), inference(cnfTransformation, [status(thm)], [f_108])).
% 24.43/15.66  tff(c_197, plain, (![B_306]: (m1_pre_topc(B_306, '#skF_6') | ~m1_pre_topc(B_306, '#skF_7') | ~l1_pre_topc('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_194])).
% 24.43/15.66  tff(c_205, plain, (![B_308]: (m1_pre_topc(B_308, '#skF_6') | ~m1_pre_topc(B_308, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_197])).
% 24.43/15.66  tff(c_209, plain, (m1_pre_topc('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_76, c_205])).
% 24.43/15.66  tff(c_212, plain, (m1_pre_topc('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_209])).
% 24.43/15.66  tff(c_78, plain, (![B_100, A_98]: (r1_tarski(u1_struct_0(B_100), u1_struct_0(A_98)) | ~m1_pre_topc(B_100, A_98) | ~l1_pre_topc(A_98))), inference(cnfTransformation, [status(thm)], [f_212])).
% 24.43/15.66  tff(c_189, plain, (![B_302, A_303]: (r1_tarski(u1_struct_0(B_302), u1_struct_0(A_303)) | ~m1_pre_topc(B_302, A_303) | ~l1_pre_topc(A_303))), inference(cnfTransformation, [status(thm)], [f_212])).
% 24.43/15.66  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 24.43/15.66  tff(c_700, plain, (![B_344, A_345]: (u1_struct_0(B_344)=u1_struct_0(A_345) | ~r1_tarski(u1_struct_0(A_345), u1_struct_0(B_344)) | ~m1_pre_topc(B_344, A_345) | ~l1_pre_topc(A_345))), inference(resolution, [status(thm)], [c_189, c_2])).
% 24.43/15.66  tff(c_711, plain, (![B_346, A_347]: (u1_struct_0(B_346)=u1_struct_0(A_347) | ~m1_pre_topc(A_347, B_346) | ~l1_pre_topc(B_346) | ~m1_pre_topc(B_346, A_347) | ~l1_pre_topc(A_347))), inference(resolution, [status(thm)], [c_78, c_700])).
% 24.43/15.66  tff(c_725, plain, (u1_struct_0('#skF_7')=u1_struct_0('#skF_6') | ~l1_pre_topc('#skF_6') | ~m1_pre_topc('#skF_6', '#skF_7') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_212, c_711])).
% 24.43/15.66  tff(c_751, plain, (u1_struct_0('#skF_7')=u1_struct_0('#skF_6') | ~m1_pre_topc('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_160, c_725])).
% 24.43/15.66  tff(c_760, plain, (~m1_pre_topc('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_751])).
% 24.43/15.66  tff(c_763, plain, (~m1_pre_topc('#skF_6', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_374, c_760])).
% 24.43/15.66  tff(c_770, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_160, c_617, c_763])).
% 24.43/15.66  tff(c_772, plain, (m1_pre_topc('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_751])).
% 24.43/15.66  tff(c_771, plain, (u1_struct_0('#skF_7')=u1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_751])).
% 24.43/15.66  tff(c_116, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.43/15.66  tff(c_172, plain, (![B_300, A_301]: (v2_pre_topc(B_300) | ~m1_pre_topc(B_300, A_301) | ~l1_pre_topc(A_301) | ~v2_pre_topc(A_301))), inference(cnfTransformation, [status(thm)], [f_44])).
% 24.43/15.66  tff(c_178, plain, (v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_108, c_172])).
% 24.43/15.66  tff(c_185, plain, (v2_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_118, c_178])).
% 24.43/15.66  tff(c_114, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.43/15.66  tff(c_112, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.43/15.66  tff(c_102, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.43/15.66  tff(c_100, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_7'), u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.43/15.66  tff(c_829, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_771, c_100])).
% 24.43/15.66  tff(c_98, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.43/15.66  tff(c_828, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_771, c_98])).
% 24.43/15.66  tff(c_5087, plain, (![A_503, B_504, C_505, D_506]: (k2_partfun1(u1_struct_0(A_503), u1_struct_0(B_504), C_505, u1_struct_0(D_506))=k2_tmap_1(A_503, B_504, C_505, D_506) | ~m1_pre_topc(D_506, A_503) | ~m1_subset_1(C_505, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_503), u1_struct_0(B_504)))) | ~v1_funct_2(C_505, u1_struct_0(A_503), u1_struct_0(B_504)) | ~v1_funct_1(C_505) | ~l1_pre_topc(B_504) | ~v2_pre_topc(B_504) | v2_struct_0(B_504) | ~l1_pre_topc(A_503) | ~v2_pre_topc(A_503) | v2_struct_0(A_503))), inference(cnfTransformation, [status(thm)], [f_144])).
% 24.43/15.66  tff(c_5089, plain, (![D_506]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'), '#skF_8', u1_struct_0(D_506))=k2_tmap_1('#skF_6', '#skF_5', '#skF_8', D_506) | ~m1_pre_topc(D_506, '#skF_6') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_6'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_8') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_828, c_5087])).
% 24.43/15.66  tff(c_5099, plain, (![D_506]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'), '#skF_8', u1_struct_0(D_506))=k2_tmap_1('#skF_6', '#skF_5', '#skF_8', D_506) | ~m1_pre_topc(D_506, '#skF_6') | v2_struct_0('#skF_5') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_160, c_114, c_112, c_102, c_829, c_5089])).
% 24.43/15.66  tff(c_5108, plain, (![D_507]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'), '#skF_8', u1_struct_0(D_507))=k2_tmap_1('#skF_6', '#skF_5', '#skF_8', D_507) | ~m1_pre_topc(D_507, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_110, c_116, c_5099])).
% 24.43/15.66  tff(c_5117, plain, (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'), '#skF_8', u1_struct_0('#skF_6'))=k2_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_7') | ~m1_pre_topc('#skF_7', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_771, c_5108])).
% 24.43/15.66  tff(c_5121, plain, (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'), '#skF_8', u1_struct_0('#skF_6'))=k2_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_212, c_5117])).
% 24.43/15.66  tff(c_5100, plain, (![D_506]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'), '#skF_8', u1_struct_0(D_506))=k2_tmap_1('#skF_6', '#skF_5', '#skF_8', D_506) | ~m1_pre_topc(D_506, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_110, c_116, c_5099])).
% 24.43/15.66  tff(c_5125, plain, (k2_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_7')=k2_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_6') | ~m1_pre_topc('#skF_6', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_5121, c_5100])).
% 24.43/15.66  tff(c_5132, plain, (k2_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_7')=k2_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_617, c_5125])).
% 24.43/15.66  tff(c_5136, plain, (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'), '#skF_8', u1_struct_0('#skF_6'))=k2_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5132, c_5121])).
% 24.43/15.66  tff(c_5590, plain, (![D_518, B_515, C_514, A_516, E_517]: (k3_tmap_1(A_516, B_515, C_514, D_518, E_517)=k2_partfun1(u1_struct_0(C_514), u1_struct_0(B_515), E_517, u1_struct_0(D_518)) | ~m1_pre_topc(D_518, C_514) | ~m1_subset_1(E_517, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_514), u1_struct_0(B_515)))) | ~v1_funct_2(E_517, u1_struct_0(C_514), u1_struct_0(B_515)) | ~v1_funct_1(E_517) | ~m1_pre_topc(D_518, A_516) | ~m1_pre_topc(C_514, A_516) | ~l1_pre_topc(B_515) | ~v2_pre_topc(B_515) | v2_struct_0(B_515) | ~l1_pre_topc(A_516) | ~v2_pre_topc(A_516) | v2_struct_0(A_516))), inference(cnfTransformation, [status(thm)], [f_176])).
% 24.43/15.66  tff(c_5594, plain, (![A_516, B_515, D_518, E_517]: (k3_tmap_1(A_516, B_515, '#skF_7', D_518, E_517)=k2_partfun1(u1_struct_0('#skF_7'), u1_struct_0(B_515), E_517, u1_struct_0(D_518)) | ~m1_pre_topc(D_518, '#skF_7') | ~m1_subset_1(E_517, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0(B_515)))) | ~v1_funct_2(E_517, u1_struct_0('#skF_7'), u1_struct_0(B_515)) | ~v1_funct_1(E_517) | ~m1_pre_topc(D_518, A_516) | ~m1_pre_topc('#skF_7', A_516) | ~l1_pre_topc(B_515) | ~v2_pre_topc(B_515) | v2_struct_0(B_515) | ~l1_pre_topc(A_516) | ~v2_pre_topc(A_516) | v2_struct_0(A_516))), inference(superposition, [status(thm), theory('equality')], [c_771, c_5590])).
% 24.43/15.66  tff(c_43004, plain, (![A_1269, B_1270, D_1271, E_1272]: (k3_tmap_1(A_1269, B_1270, '#skF_7', D_1271, E_1272)=k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0(B_1270), E_1272, u1_struct_0(D_1271)) | ~m1_pre_topc(D_1271, '#skF_7') | ~m1_subset_1(E_1272, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0(B_1270)))) | ~v1_funct_2(E_1272, u1_struct_0('#skF_6'), u1_struct_0(B_1270)) | ~v1_funct_1(E_1272) | ~m1_pre_topc(D_1271, A_1269) | ~m1_pre_topc('#skF_7', A_1269) | ~l1_pre_topc(B_1270) | ~v2_pre_topc(B_1270) | v2_struct_0(B_1270) | ~l1_pre_topc(A_1269) | ~v2_pre_topc(A_1269) | v2_struct_0(A_1269))), inference(demodulation, [status(thm), theory('equality')], [c_771, c_771, c_5594])).
% 24.43/15.66  tff(c_43006, plain, (![A_1269, D_1271]: (k3_tmap_1(A_1269, '#skF_5', '#skF_7', D_1271, '#skF_8')=k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'), '#skF_8', u1_struct_0(D_1271)) | ~m1_pre_topc(D_1271, '#skF_7') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_6'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_8') | ~m1_pre_topc(D_1271, A_1269) | ~m1_pre_topc('#skF_7', A_1269) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc(A_1269) | ~v2_pre_topc(A_1269) | v2_struct_0(A_1269))), inference(resolution, [status(thm)], [c_828, c_43004])).
% 24.43/15.66  tff(c_43014, plain, (![A_1269, D_1271]: (k3_tmap_1(A_1269, '#skF_5', '#skF_7', D_1271, '#skF_8')=k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'), '#skF_8', u1_struct_0(D_1271)) | ~m1_pre_topc(D_1271, '#skF_7') | ~m1_pre_topc(D_1271, A_1269) | ~m1_pre_topc('#skF_7', A_1269) | v2_struct_0('#skF_5') | ~l1_pre_topc(A_1269) | ~v2_pre_topc(A_1269) | v2_struct_0(A_1269))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_112, c_102, c_829, c_43006])).
% 24.43/15.66  tff(c_43020, plain, (![A_1273, D_1274]: (k3_tmap_1(A_1273, '#skF_5', '#skF_7', D_1274, '#skF_8')=k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'), '#skF_8', u1_struct_0(D_1274)) | ~m1_pre_topc(D_1274, '#skF_7') | ~m1_pre_topc(D_1274, A_1273) | ~m1_pre_topc('#skF_7', A_1273) | ~l1_pre_topc(A_1273) | ~v2_pre_topc(A_1273) | v2_struct_0(A_1273))), inference(negUnitSimplification, [status(thm)], [c_116, c_43014])).
% 24.43/15.66  tff(c_43130, plain, (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'), '#skF_8', u1_struct_0('#skF_6'))=k3_tmap_1('#skF_4', '#skF_5', '#skF_7', '#skF_6', '#skF_8') | ~m1_pre_topc('#skF_6', '#skF_7') | ~m1_pre_topc('#skF_7', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_108, c_43020])).
% 24.43/15.66  tff(c_43249, plain, (k3_tmap_1('#skF_4', '#skF_5', '#skF_7', '#skF_6', '#skF_8')=k2_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_6') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_118, c_104, c_772, c_5136, c_43130])).
% 24.43/15.66  tff(c_43250, plain, (k3_tmap_1('#skF_4', '#skF_5', '#skF_7', '#skF_6', '#skF_8')=k2_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_122, c_43249])).
% 24.43/15.66  tff(c_88, plain, (r1_tmap_1('#skF_6', '#skF_5', k3_tmap_1('#skF_4', '#skF_5', '#skF_7', '#skF_6', '#skF_8'), '#skF_10')), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.43/15.66  tff(c_124, plain, (r1_tmap_1('#skF_6', '#skF_5', k3_tmap_1('#skF_4', '#skF_5', '#skF_7', '#skF_6', '#skF_8'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88])).
% 24.43/15.66  tff(c_43271, plain, (r1_tmap_1('#skF_6', '#skF_5', k2_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_6'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_43250, c_124])).
% 24.43/15.66  tff(c_106, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_315])).
% 24.43/15.66  tff(c_181, plain, (v2_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_104, c_172])).
% 24.43/15.66  tff(c_188, plain, (v2_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_118, c_181])).
% 24.43/15.66  tff(c_48, plain, (![A_8]: (r2_hidden(u1_struct_0(A_8), u1_pre_topc(A_8)) | ~v2_pre_topc(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_69])).
% 24.43/15.66  tff(c_8, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 24.43/15.66  tff(c_10, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 24.43/15.66  tff(c_125, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 24.43/15.66  tff(c_514, plain, (![B_327, A_328]: (v3_pre_topc(B_327, A_328) | ~r2_hidden(B_327, u1_pre_topc(A_328)) | ~m1_subset_1(B_327, k1_zfmisc_1(u1_struct_0(A_328))) | ~l1_pre_topc(A_328))), inference(cnfTransformation, [status(thm)], [f_78])).
% 24.43/15.66  tff(c_524, plain, (![A_329]: (v3_pre_topc(u1_struct_0(A_329), A_329) | ~r2_hidden(u1_struct_0(A_329), u1_pre_topc(A_329)) | ~l1_pre_topc(A_329))), inference(resolution, [status(thm)], [c_125, c_514])).
% 24.43/15.66  tff(c_532, plain, (![A_8]: (v3_pre_topc(u1_struct_0(A_8), A_8) | ~v2_pre_topc(A_8) | ~l1_pre_topc(A_8))), inference(resolution, [status(thm)], [c_48, c_524])).
% 24.43/15.66  tff(c_862, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_7') | ~v2_pre_topc('#skF_7') | ~l1_pre_topc('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_771, c_532])).
% 24.43/15.66  tff(c_919, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_188, c_862])).
% 24.43/15.66  tff(c_74, plain, (![B_96, A_94]: (m1_subset_1(u1_struct_0(B_96), k1_zfmisc_1(u1_struct_0(A_94))) | ~m1_pre_topc(B_96, A_94) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_201])).
% 24.43/15.66  tff(c_1213, plain, (![B_361, A_362]: (v1_tsep_1(B_361, A_362) | ~v3_pre_topc(u1_struct_0(B_361), A_362) | ~m1_subset_1(u1_struct_0(B_361), k1_zfmisc_1(u1_struct_0(A_362))) | ~m1_pre_topc(B_361, A_362) | ~l1_pre_topc(A_362) | ~v2_pre_topc(A_362))), inference(cnfTransformation, [status(thm)], [f_194])).
% 24.43/15.66  tff(c_2020, plain, (![B_385, A_386]: (v1_tsep_1(B_385, A_386) | ~v3_pre_topc(u1_struct_0(B_385), A_386) | ~v2_pre_topc(A_386) | ~m1_pre_topc(B_385, A_386) | ~l1_pre_topc(A_386))), inference(resolution, [status(thm)], [c_74, c_1213])).
% 24.43/15.66  tff(c_2029, plain, (v1_tsep_1('#skF_6', '#skF_7') | ~v2_pre_topc('#skF_7') | ~m1_pre_topc('#skF_6', '#skF_7') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_919, c_2020])).
% 24.43/15.66  tff(c_2044, plain, (v1_tsep_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_772, c_188, c_2029])).
% 24.43/15.66  tff(c_5091, plain, (![B_504, C_505, D_506]: (k2_partfun1(u1_struct_0('#skF_7'), u1_struct_0(B_504), C_505, u1_struct_0(D_506))=k2_tmap_1('#skF_7', B_504, C_505, D_506) | ~m1_pre_topc(D_506, '#skF_7') | ~m1_subset_1(C_505, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0(B_504)))) | ~v1_funct_2(C_505, u1_struct_0('#skF_7'), u1_struct_0(B_504)) | ~v1_funct_1(C_505) | ~l1_pre_topc(B_504) | ~v2_pre_topc(B_504) | v2_struct_0(B_504) | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_771, c_5087])).
% 24.43/15.66  tff(c_5102, plain, (![B_504, C_505, D_506]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0(B_504), C_505, u1_struct_0(D_506))=k2_tmap_1('#skF_7', B_504, C_505, D_506) | ~m1_pre_topc(D_506, '#skF_7') | ~m1_subset_1(C_505, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0(B_504)))) | ~v1_funct_2(C_505, u1_struct_0('#skF_6'), u1_struct_0(B_504)) | ~v1_funct_1(C_505) | ~l1_pre_topc(B_504) | ~v2_pre_topc(B_504) | v2_struct_0(B_504) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_163, c_771, c_771, c_5091])).
% 24.43/15.66  tff(c_6085, plain, (![B_543, C_544, D_545]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0(B_543), C_544, u1_struct_0(D_545))=k2_tmap_1('#skF_7', B_543, C_544, D_545) | ~m1_pre_topc(D_545, '#skF_7') | ~m1_subset_1(C_544, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0(B_543)))) | ~v1_funct_2(C_544, u1_struct_0('#skF_6'), u1_struct_0(B_543)) | ~v1_funct_1(C_544) | ~l1_pre_topc(B_543) | ~v2_pre_topc(B_543) | v2_struct_0(B_543))), inference(negUnitSimplification, [status(thm)], [c_106, c_5102])).
% 24.43/15.66  tff(c_6087, plain, (![D_545]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'), '#skF_8', u1_struct_0(D_545))=k2_tmap_1('#skF_7', '#skF_5', '#skF_8', D_545) | ~m1_pre_topc(D_545, '#skF_7') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_6'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_8') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_828, c_6085])).
% 24.43/15.66  tff(c_6095, plain, (![D_545]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'), '#skF_8', u1_struct_0(D_545))=k2_tmap_1('#skF_7', '#skF_5', '#skF_8', D_545) | ~m1_pre_topc(D_545, '#skF_7') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_112, c_102, c_829, c_6087])).
% 24.43/15.66  tff(c_6101, plain, (![D_546]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'), '#skF_8', u1_struct_0(D_546))=k2_tmap_1('#skF_7', '#skF_5', '#skF_8', D_546) | ~m1_pre_topc(D_546, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_116, c_6095])).
% 24.43/15.66  tff(c_6110, plain, (k2_tmap_1('#skF_7', '#skF_5', '#skF_8', '#skF_6')=k2_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_6') | ~m1_pre_topc('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_6101, c_5136])).
% 24.43/15.66  tff(c_6131, plain, (k2_tmap_1('#skF_7', '#skF_5', '#skF_8', '#skF_6')=k2_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_772, c_6110])).
% 24.43/15.66  tff(c_80, plain, (![F_163, B_133, D_157, A_101, C_149]: (r1_tmap_1(B_133, A_101, C_149, F_163) | ~r1_tmap_1(D_157, A_101, k2_tmap_1(B_133, A_101, C_149, D_157), F_163) | ~m1_subset_1(F_163, u1_struct_0(D_157)) | ~m1_subset_1(F_163, u1_struct_0(B_133)) | ~m1_pre_topc(D_157, B_133) | ~v1_tsep_1(D_157, B_133) | v2_struct_0(D_157) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_133), u1_struct_0(A_101)))) | ~v1_funct_2(C_149, u1_struct_0(B_133), u1_struct_0(A_101)) | ~v1_funct_1(C_149) | ~l1_pre_topc(B_133) | ~v2_pre_topc(B_133) | v2_struct_0(B_133) | ~l1_pre_topc(A_101) | ~v2_pre_topc(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_254])).
% 24.43/15.66  tff(c_6148, plain, (![F_163]: (r1_tmap_1('#skF_7', '#skF_5', '#skF_8', F_163) | ~r1_tmap_1('#skF_6', '#skF_5', k2_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_6'), F_163) | ~m1_subset_1(F_163, u1_struct_0('#skF_6')) | ~m1_subset_1(F_163, u1_struct_0('#skF_7')) | ~m1_pre_topc('#skF_6', '#skF_7') | ~v1_tsep_1('#skF_6', '#skF_7') | v2_struct_0('#skF_6') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_7'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_8') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_6131, c_80])).
% 24.43/15.66  tff(c_6152, plain, (![F_163]: (r1_tmap_1('#skF_7', '#skF_5', '#skF_8', F_163) | ~r1_tmap_1('#skF_6', '#skF_5', k2_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_6'), F_163) | ~m1_subset_1(F_163, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6') | v2_struct_0('#skF_7') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_112, c_188, c_163, c_102, c_829, c_771, c_828, c_771, c_2044, c_772, c_771, c_6148])).
% 24.43/15.66  tff(c_6153, plain, (![F_163]: (r1_tmap_1('#skF_7', '#skF_5', '#skF_8', F_163) | ~r1_tmap_1('#skF_6', '#skF_5', k2_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_6'), F_163) | ~m1_subset_1(F_163, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_116, c_106, c_110, c_6152])).
% 24.43/15.66  tff(c_43278, plain, (r1_tmap_1('#skF_7', '#skF_5', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_43271, c_6153])).
% 24.43/15.66  tff(c_43283, plain, (r1_tmap_1('#skF_7', '#skF_5', '#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_43278])).
% 24.43/15.66  tff(c_43285, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_43283])).
% 24.43/15.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.43/15.66  
% 24.43/15.66  Inference rules
% 24.43/15.66  ----------------------
% 24.43/15.66  #Ref     : 0
% 24.43/15.66  #Sup     : 9655
% 24.43/15.66  #Fact    : 0
% 24.43/15.66  #Define  : 0
% 24.43/15.66  #Split   : 8
% 24.43/15.66  #Chain   : 0
% 24.43/15.66  #Close   : 0
% 24.43/15.66  
% 24.43/15.66  Ordering : KBO
% 24.43/15.66  
% 24.43/15.66  Simplification rules
% 24.43/15.66  ----------------------
% 24.43/15.66  #Subsume      : 5416
% 24.43/15.66  #Demod        : 18617
% 24.43/15.66  #Tautology    : 1135
% 24.43/15.66  #SimpNegUnit  : 418
% 24.43/15.66  #BackRed      : 5
% 24.43/15.66  
% 24.43/15.66  #Partial instantiations: 0
% 24.43/15.66  #Strategies tried      : 1
% 24.43/15.66  
% 24.43/15.66  Timing (in seconds)
% 24.43/15.66  ----------------------
% 24.43/15.66  Preprocessing        : 0.43
% 24.43/15.66  Parsing              : 0.22
% 24.43/15.66  CNF conversion       : 0.05
% 24.43/15.66  Main loop            : 14.44
% 24.43/15.66  Inferencing          : 1.68
% 24.43/15.66  Reduction            : 3.50
% 24.43/15.66  Demodulation         : 2.70
% 24.43/15.66  BG Simplification    : 0.16
% 24.43/15.66  Subsumption          : 8.67
% 24.43/15.66  Abstraction          : 0.44
% 24.43/15.66  MUC search           : 0.00
% 24.43/15.66  Cooper               : 0.00
% 24.43/15.66  Total                : 14.93
% 24.43/15.66  Index Insertion      : 0.00
% 24.43/15.66  Index Deletion       : 0.00
% 24.43/15.66  Index Matching       : 0.00
% 24.43/15.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
