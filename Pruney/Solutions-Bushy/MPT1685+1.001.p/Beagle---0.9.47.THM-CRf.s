%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1685+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:14 EST 2020

% Result     : Theorem 13.26s
% Output     : CNFRefutation 13.59s
% Verified   : 
% Statistics : Number of formulae       :  546 (11070 expanded)
%              Number of leaves         :   49 (3616 expanded)
%              Depth                    :   27
%              Number of atoms          : 1859 (71881 expanded)
%              Number of equality atoms :  317 (14641 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > r4_waybel_0 > r3_waybel_0 > v1_funct_2 > r2_yellow_0 > r1_yellow_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_orders_2 > k7_relset_1 > k3_funct_2 > k9_relat_1 > k2_zfmisc_1 > k2_yellow_0 > k1_yellow_0 > k1_funct_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r4_waybel_0,type,(
    r4_waybel_0: ( $i * $i * $i * $i ) > $o )).

tff(r3_waybel_0,type,(
    r3_waybel_0: ( $i * $i * $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k2_yellow_0,type,(
    k2_yellow_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(r1_funct_2,type,(
    r1_funct_2: ( $i * $i * $i * $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_254,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_orders_2(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & l1_orders_2(C) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & l1_orders_2(D) )
                   => ( ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(C),u1_orders_2(C))
                        & g1_orders_2(u1_struct_0(B),u1_orders_2(B)) = g1_orders_2(u1_struct_0(D),u1_orders_2(D)) )
                     => ! [E] :
                          ( ( v1_funct_1(E)
                            & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                         => ! [F] :
                              ( ( v1_funct_1(F)
                                & v1_funct_2(F,u1_struct_0(C),u1_struct_0(D))
                                & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(D)))) )
                             => ( r1_funct_2(u1_struct_0(A),u1_struct_0(B),u1_struct_0(C),u1_struct_0(D),E,F)
                               => ! [G] :
                                    ( m1_subset_1(G,k1_zfmisc_1(u1_struct_0(A)))
                                   => ! [H] :
                                        ( m1_subset_1(H,k1_zfmisc_1(u1_struct_0(C)))
                                       => ( G = H
                                         => ( ( r4_waybel_0(A,B,E,G)
                                             => r4_waybel_0(C,D,F,H) )
                                            & ( r3_waybel_0(A,B,E,G)
                                             => r3_waybel_0(C,D,F,H) ) ) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_waybel_0)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_115,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(f_132,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_orders_2(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r3_waybel_0(A,B,C,D)
                  <=> ( r2_yellow_0(A,D)
                     => ( r2_yellow_0(B,k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,D))
                        & k2_yellow_0(B,k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,D)) = k3_funct_2(u1_struct_0(A),u1_struct_0(B),C,k2_yellow_0(A,D)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d30_waybel_0)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_106,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_90,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k2_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_0)).

tff(f_128,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_154,axiom,(
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

tff(f_170,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(B),u1_orders_2(B))
           => ! [C] :
                ( ( r1_yellow_0(A,C)
                 => r1_yellow_0(B,C) )
                & ( r2_yellow_0(A,C)
                 => r2_yellow_0(B,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_0)).

tff(f_194,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(B),u1_orders_2(B))
           => ! [C] :
                ( r2_yellow_0(A,C)
               => k2_yellow_0(A,C) = k2_yellow_0(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_0)).

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_orders_2(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r4_waybel_0(A,B,C,D)
                  <=> ( r1_yellow_0(A,D)
                     => ( r1_yellow_0(B,k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,D))
                        & k1_yellow_0(B,k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,D)) = k3_funct_2(u1_struct_0(A),u1_struct_0(B),C,k1_yellow_0(A,D)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d31_waybel_0)).

tff(f_182,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(B),u1_orders_2(B))
           => ! [C] :
                ( r1_yellow_0(A,C)
               => k1_yellow_0(A,C) = k1_yellow_0(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_0)).

tff(f_86,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_48,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_90,plain,
    ( r4_waybel_0('#skF_1','#skF_2','#skF_5','#skF_7')
    | ~ r3_waybel_0('#skF_3','#skF_4','#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_95,plain,
    ( r4_waybel_0('#skF_1','#skF_2','#skF_5','#skF_8')
    | ~ r3_waybel_0('#skF_3','#skF_4','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_90])).

tff(c_111,plain,(
    ~ r3_waybel_0('#skF_3','#skF_4','#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_72,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_60,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_84,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_24,plain,(
    ! [A_36] :
      ( m1_subset_1(u1_orders_2(A_36),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_36),u1_struct_0(A_36))))
      | ~ l1_orders_2(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_70,plain,(
    g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_3')) = g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_151,plain,(
    ! [C_339,A_340,D_341,B_342] :
      ( C_339 = A_340
      | g1_orders_2(C_339,D_341) != g1_orders_2(A_340,B_342)
      | ~ m1_subset_1(B_342,k1_zfmisc_1(k2_zfmisc_1(A_340,A_340))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_205,plain,(
    ! [A_352,B_353] :
      ( u1_struct_0('#skF_3') = A_352
      | g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) != g1_orders_2(A_352,B_353)
      | ~ m1_subset_1(B_353,k1_zfmisc_1(k2_zfmisc_1(A_352,A_352))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_151])).

tff(c_209,plain,(
    ! [A_36] :
      ( u1_struct_0(A_36) = u1_struct_0('#skF_3')
      | g1_orders_2(u1_struct_0(A_36),u1_orders_2(A_36)) != g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
      | ~ l1_orders_2(A_36) ) ),
    inference(resolution,[status(thm)],[c_24,c_205])).

tff(c_398,plain,
    ( u1_struct_0('#skF_3') = u1_struct_0('#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_209])).

tff(c_400,plain,(
    u1_struct_0('#skF_3') = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_398])).

tff(c_58,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_425,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_58])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_424,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_56])).

tff(c_52,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_98,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52])).

tff(c_86,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_119,plain,(
    ! [A_333,B_334,C_335,D_336] :
      ( k7_relset_1(A_333,B_334,C_335,D_336) = k9_relat_1(C_335,D_336)
      | ~ m1_subset_1(C_335,k1_zfmisc_1(k2_zfmisc_1(A_333,B_334))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_127,plain,(
    ! [D_336] : k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_6',D_336) = k9_relat_1('#skF_6',D_336) ),
    inference(resolution,[status(thm)],[c_56,c_119])).

tff(c_422,plain,(
    ! [D_336] : k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',D_336) = k9_relat_1('#skF_6',D_336) ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_127])).

tff(c_842,plain,(
    ! [B_420,A_421,C_422,D_423] :
      ( r2_yellow_0(B_420,k7_relset_1(u1_struct_0(A_421),u1_struct_0(B_420),C_422,D_423))
      | ~ r2_yellow_0(A_421,D_423)
      | ~ r3_waybel_0(A_421,B_420,C_422,D_423)
      | ~ m1_subset_1(D_423,k1_zfmisc_1(u1_struct_0(A_421)))
      | ~ m1_subset_1(C_422,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_421),u1_struct_0(B_420))))
      | ~ v1_funct_2(C_422,u1_struct_0(A_421),u1_struct_0(B_420))
      | ~ v1_funct_1(C_422)
      | ~ l1_orders_2(B_420)
      | v2_struct_0(B_420)
      | ~ l1_orders_2(A_421)
      | v2_struct_0(A_421) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_846,plain,(
    ! [D_423] :
      ( r2_yellow_0('#skF_4',k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',D_423))
      | ~ r2_yellow_0('#skF_1',D_423)
      | ~ r3_waybel_0('#skF_1','#skF_4','#skF_6',D_423)
      | ~ m1_subset_1(D_423,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_424,c_842])).

tff(c_865,plain,(
    ! [D_423] :
      ( r2_yellow_0('#skF_4',k9_relat_1('#skF_6',D_423))
      | ~ r2_yellow_0('#skF_1',D_423)
      | ~ r3_waybel_0('#skF_1','#skF_4','#skF_6',D_423)
      | ~ m1_subset_1(D_423,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_72,c_60,c_425,c_422,c_846])).

tff(c_901,plain,(
    ! [D_424] :
      ( r2_yellow_0('#skF_4',k9_relat_1('#skF_6',D_424))
      | ~ r2_yellow_0('#skF_1',D_424)
      | ~ r3_waybel_0('#skF_1','#skF_4','#skF_6',D_424)
      | ~ m1_subset_1(D_424,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_74,c_865])).

tff(c_905,plain,
    ( r2_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8'))
    | ~ r2_yellow_0('#skF_1','#skF_8')
    | ~ r3_waybel_0('#skF_1','#skF_4','#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_98,c_901])).

tff(c_907,plain,(
    ~ r3_waybel_0('#skF_1','#skF_4','#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_905])).

tff(c_76,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_22,plain,(
    ! [A_35] :
      ( l1_struct_0(A_35)
      | ~ l1_orders_2(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_26,plain,(
    ! [A_37] :
      ( ~ v1_xboole_0(u1_struct_0(A_37))
      | ~ l1_struct_0(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_449,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_26])).

tff(c_464,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_449])).

tff(c_466,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_464])).

tff(c_469,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_466])).

tff(c_473,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_469])).

tff(c_474,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_464])).

tff(c_20,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(k2_yellow_0(A_33,B_34),u1_struct_0(A_33))
      | ~ l1_orders_2(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_477,plain,(
    ! [A_378,B_379,C_380,D_381] :
      ( k3_funct_2(A_378,B_379,C_380,D_381) = k1_funct_1(C_380,D_381)
      | ~ m1_subset_1(D_381,A_378)
      | ~ m1_subset_1(C_380,k1_zfmisc_1(k2_zfmisc_1(A_378,B_379)))
      | ~ v1_funct_2(C_380,A_378,B_379)
      | ~ v1_funct_1(C_380)
      | v1_xboole_0(A_378) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1324,plain,(
    ! [A_458,B_459,C_460,B_461] :
      ( k3_funct_2(u1_struct_0(A_458),B_459,C_460,k2_yellow_0(A_458,B_461)) = k1_funct_1(C_460,k2_yellow_0(A_458,B_461))
      | ~ m1_subset_1(C_460,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_458),B_459)))
      | ~ v1_funct_2(C_460,u1_struct_0(A_458),B_459)
      | ~ v1_funct_1(C_460)
      | v1_xboole_0(u1_struct_0(A_458))
      | ~ l1_orders_2(A_458) ) ),
    inference(resolution,[status(thm)],[c_20,c_477])).

tff(c_1328,plain,(
    ! [B_461] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k2_yellow_0('#skF_1',B_461)) = k1_funct_1('#skF_6',k2_yellow_0('#skF_1',B_461))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_424,c_1324])).

tff(c_1343,plain,(
    ! [B_461] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k2_yellow_0('#skF_1',B_461)) = k1_funct_1('#skF_6',k2_yellow_0('#skF_1',B_461))
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_60,c_425,c_1328])).

tff(c_1344,plain,(
    ! [B_461] : k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k2_yellow_0('#skF_1',B_461)) = k1_funct_1('#skF_6',k2_yellow_0('#skF_1',B_461)) ),
    inference(negUnitSimplification,[status(thm)],[c_474,c_1343])).

tff(c_1425,plain,(
    ! [A_466,B_467,C_468,D_469] :
      ( k3_funct_2(u1_struct_0(A_466),u1_struct_0(B_467),C_468,k2_yellow_0(A_466,D_469)) != k2_yellow_0(B_467,k7_relset_1(u1_struct_0(A_466),u1_struct_0(B_467),C_468,D_469))
      | ~ r2_yellow_0(B_467,k7_relset_1(u1_struct_0(A_466),u1_struct_0(B_467),C_468,D_469))
      | r3_waybel_0(A_466,B_467,C_468,D_469)
      | ~ m1_subset_1(D_469,k1_zfmisc_1(u1_struct_0(A_466)))
      | ~ m1_subset_1(C_468,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_466),u1_struct_0(B_467))))
      | ~ v1_funct_2(C_468,u1_struct_0(A_466),u1_struct_0(B_467))
      | ~ v1_funct_1(C_468)
      | ~ l1_orders_2(B_467)
      | v2_struct_0(B_467)
      | ~ l1_orders_2(A_466)
      | v2_struct_0(A_466) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1429,plain,(
    ! [B_461] :
      ( k2_yellow_0('#skF_4',k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',B_461)) != k1_funct_1('#skF_6',k2_yellow_0('#skF_1',B_461))
      | ~ r2_yellow_0('#skF_4',k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',B_461))
      | r3_waybel_0('#skF_1','#skF_4','#skF_6',B_461)
      | ~ m1_subset_1(B_461,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1344,c_1425])).

tff(c_1445,plain,(
    ! [B_461] :
      ( k2_yellow_0('#skF_4',k9_relat_1('#skF_6',B_461)) != k1_funct_1('#skF_6',k2_yellow_0('#skF_1',B_461))
      | ~ r2_yellow_0('#skF_4',k9_relat_1('#skF_6',B_461))
      | r3_waybel_0('#skF_1','#skF_4','#skF_6',B_461)
      | ~ m1_subset_1(B_461,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_72,c_60,c_425,c_424,c_422,c_422,c_1429])).

tff(c_1468,plain,(
    ! [B_470] :
      ( k2_yellow_0('#skF_4',k9_relat_1('#skF_6',B_470)) != k1_funct_1('#skF_6',k2_yellow_0('#skF_1',B_470))
      | ~ r2_yellow_0('#skF_4',k9_relat_1('#skF_6',B_470))
      | r3_waybel_0('#skF_1','#skF_4','#skF_6',B_470)
      | ~ m1_subset_1(B_470,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_74,c_1445])).

tff(c_1471,plain,
    ( k2_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) != k1_funct_1('#skF_6',k2_yellow_0('#skF_1','#skF_8'))
    | ~ r2_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8'))
    | r3_waybel_0('#skF_1','#skF_4','#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_98,c_1468])).

tff(c_1474,plain,
    ( k2_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) != k1_funct_1('#skF_6',k2_yellow_0('#skF_1','#skF_8'))
    | ~ r2_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_907,c_1471])).

tff(c_1475,plain,(
    ~ r2_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_1474])).

tff(c_80,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_68,plain,(
    g1_orders_2(u1_struct_0('#skF_2'),u1_orders_2('#skF_2')) = g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_182,plain,(
    ! [A_349,B_350] :
      ( u1_struct_0('#skF_2') = A_349
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(A_349,B_350)
      | ~ m1_subset_1(B_350,k1_zfmisc_1(k2_zfmisc_1(A_349,A_349))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_151])).

tff(c_186,plain,(
    ! [A_36] :
      ( u1_struct_0(A_36) = u1_struct_0('#skF_2')
      | g1_orders_2(u1_struct_0(A_36),u1_orders_2(A_36)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(A_36) ) ),
    inference(resolution,[status(thm)],[c_24,c_182])).

tff(c_189,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_186])).

tff(c_191,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_189])).

tff(c_226,plain,
    ( m1_subset_1(u1_orders_2('#skF_2'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ l1_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_24])).

tff(c_246,plain,(
    m1_subset_1(u1_orders_2('#skF_2'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_191,c_226])).

tff(c_214,plain,(
    g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_2')) = g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_68])).

tff(c_28,plain,(
    ! [D_43,B_39,C_42,A_38] :
      ( D_43 = B_39
      | g1_orders_2(C_42,D_43) != g1_orders_2(A_38,B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k2_zfmisc_1(A_38,A_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_283,plain,(
    ! [D_43,C_42] :
      ( u1_orders_2('#skF_2') = D_43
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(C_42,D_43)
      | ~ m1_subset_1(u1_orders_2('#skF_2'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_28])).

tff(c_291,plain,(
    ! [D_43,C_42] :
      ( u1_orders_2('#skF_2') = D_43
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(C_42,D_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_283])).

tff(c_320,plain,(
    u1_orders_2('#skF_2') = u1_orders_2('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_291])).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_238,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_26])).

tff(c_253,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_238])).

tff(c_255,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_253])).

tff(c_258,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_255])).

tff(c_262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_258])).

tff(c_263,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_253])).

tff(c_66,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_64,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_216,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_64])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_215,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_62])).

tff(c_54,plain,(
    r1_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_213,plain,(
    r1_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_54])).

tff(c_420,plain,(
    r1_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_213])).

tff(c_688,plain,(
    ! [E_402,C_405,D_404,F_403,A_400,B_401] :
      ( F_403 = E_402
      | ~ r1_funct_2(A_400,B_401,C_405,D_404,E_402,F_403)
      | ~ m1_subset_1(F_403,k1_zfmisc_1(k2_zfmisc_1(C_405,D_404)))
      | ~ v1_funct_2(F_403,C_405,D_404)
      | ~ v1_funct_1(F_403)
      | ~ m1_subset_1(E_402,k1_zfmisc_1(k2_zfmisc_1(A_400,B_401)))
      | ~ v1_funct_2(E_402,A_400,B_401)
      | ~ v1_funct_1(E_402)
      | v1_xboole_0(D_404)
      | v1_xboole_0(B_401) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_690,plain,
    ( '#skF_5' = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_420,c_688])).

tff(c_693,plain,
    ( '#skF_5' = '#skF_6'
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_216,c_215,c_60,c_425,c_424,c_690])).

tff(c_694,plain,(
    '#skF_5' = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_263,c_693])).

tff(c_94,plain,
    ( r4_waybel_0('#skF_1','#skF_2','#skF_5','#skF_7')
    | r3_waybel_0('#skF_1','#skF_2','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_96,plain,
    ( r4_waybel_0('#skF_1','#skF_2','#skF_5','#skF_8')
    | r3_waybel_0('#skF_1','#skF_2','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_94])).

tff(c_112,plain,(
    r3_waybel_0('#skF_1','#skF_2','#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_699,plain,(
    r3_waybel_0('#skF_1','#skF_2','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_694,c_112])).

tff(c_740,plain,(
    ! [A_411,D_412,B_413,C_414] :
      ( r2_yellow_0(A_411,D_412)
      | r3_waybel_0(A_411,B_413,C_414,D_412)
      | ~ m1_subset_1(D_412,k1_zfmisc_1(u1_struct_0(A_411)))
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_411),u1_struct_0(B_413))))
      | ~ v1_funct_2(C_414,u1_struct_0(A_411),u1_struct_0(B_413))
      | ~ v1_funct_1(C_414)
      | ~ l1_orders_2(B_413)
      | v2_struct_0(B_413)
      | ~ l1_orders_2(A_411)
      | v2_struct_0(A_411) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_746,plain,(
    ! [B_413,C_414] :
      ( r2_yellow_0('#skF_1','#skF_8')
      | r3_waybel_0('#skF_1',B_413,C_414,'#skF_8')
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_413))))
      | ~ v1_funct_2(C_414,u1_struct_0('#skF_1'),u1_struct_0(B_413))
      | ~ v1_funct_1(C_414)
      | ~ l1_orders_2(B_413)
      | v2_struct_0(B_413)
      | ~ l1_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_98,c_740])).

tff(c_755,plain,(
    ! [B_413,C_414] :
      ( r2_yellow_0('#skF_1','#skF_8')
      | r3_waybel_0('#skF_1',B_413,C_414,'#skF_8')
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_413))))
      | ~ v1_funct_2(C_414,u1_struct_0('#skF_1'),u1_struct_0(B_413))
      | ~ v1_funct_1(C_414)
      | ~ l1_orders_2(B_413)
      | v2_struct_0(B_413)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_746])).

tff(c_756,plain,(
    ! [B_413,C_414] :
      ( r2_yellow_0('#skF_1','#skF_8')
      | r3_waybel_0('#skF_1',B_413,C_414,'#skF_8')
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_413))))
      | ~ v1_funct_2(C_414,u1_struct_0('#skF_1'),u1_struct_0(B_413))
      | ~ v1_funct_1(C_414)
      | ~ l1_orders_2(B_413)
      | v2_struct_0(B_413) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_755])).

tff(c_990,plain,(
    r2_yellow_0('#skF_1','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_756])).

tff(c_856,plain,(
    ! [A_421,C_422,D_423] :
      ( r2_yellow_0('#skF_2',k7_relset_1(u1_struct_0(A_421),u1_struct_0('#skF_2'),C_422,D_423))
      | ~ r2_yellow_0(A_421,D_423)
      | ~ r3_waybel_0(A_421,'#skF_2',C_422,D_423)
      | ~ m1_subset_1(D_423,k1_zfmisc_1(u1_struct_0(A_421)))
      | ~ m1_subset_1(C_422,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_421),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_422,u1_struct_0(A_421),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_422)
      | ~ l1_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_orders_2(A_421)
      | v2_struct_0(A_421) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_842])).

tff(c_881,plain,(
    ! [A_421,C_422,D_423] :
      ( r2_yellow_0('#skF_2',k7_relset_1(u1_struct_0(A_421),u1_struct_0('#skF_4'),C_422,D_423))
      | ~ r2_yellow_0(A_421,D_423)
      | ~ r3_waybel_0(A_421,'#skF_2',C_422,D_423)
      | ~ m1_subset_1(D_423,k1_zfmisc_1(u1_struct_0(A_421)))
      | ~ m1_subset_1(C_422,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_421),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_422,u1_struct_0(A_421),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_422)
      | v2_struct_0('#skF_2')
      | ~ l1_orders_2(A_421)
      | v2_struct_0(A_421) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_191,c_191,c_856])).

tff(c_1937,plain,(
    ! [A_524,C_525,D_526] :
      ( r2_yellow_0('#skF_2',k7_relset_1(u1_struct_0(A_524),u1_struct_0('#skF_4'),C_525,D_526))
      | ~ r2_yellow_0(A_524,D_526)
      | ~ r3_waybel_0(A_524,'#skF_2',C_525,D_526)
      | ~ m1_subset_1(D_526,k1_zfmisc_1(u1_struct_0(A_524)))
      | ~ m1_subset_1(C_525,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_524),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_525,u1_struct_0(A_524),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_525)
      | ~ l1_orders_2(A_524)
      | v2_struct_0(A_524) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_881])).

tff(c_1939,plain,(
    ! [D_526] :
      ( r2_yellow_0('#skF_2',k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',D_526))
      | ~ r2_yellow_0('#skF_1',D_526)
      | ~ r3_waybel_0('#skF_1','#skF_2','#skF_6',D_526)
      | ~ m1_subset_1(D_526,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_424,c_1937])).

tff(c_1951,plain,(
    ! [D_526] :
      ( r2_yellow_0('#skF_2',k9_relat_1('#skF_6',D_526))
      | ~ r2_yellow_0('#skF_1',D_526)
      | ~ r3_waybel_0('#skF_1','#skF_2','#skF_6',D_526)
      | ~ m1_subset_1(D_526,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_60,c_425,c_422,c_1939])).

tff(c_2027,plain,(
    ! [D_529] :
      ( r2_yellow_0('#skF_2',k9_relat_1('#skF_6',D_529))
      | ~ r2_yellow_0('#skF_1',D_529)
      | ~ r3_waybel_0('#skF_1','#skF_2','#skF_6',D_529)
      | ~ m1_subset_1(D_529,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1951])).

tff(c_2030,plain,
    ( r2_yellow_0('#skF_2',k9_relat_1('#skF_6','#skF_8'))
    | ~ r2_yellow_0('#skF_1','#skF_8')
    | ~ r3_waybel_0('#skF_1','#skF_2','#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_98,c_2027])).

tff(c_2033,plain,(
    r2_yellow_0('#skF_2',k9_relat_1('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_990,c_2030])).

tff(c_42,plain,(
    ! [B_62,C_64,A_58] :
      ( r2_yellow_0(B_62,C_64)
      | ~ r2_yellow_0(A_58,C_64)
      | g1_orders_2(u1_struct_0(B_62),u1_orders_2(B_62)) != g1_orders_2(u1_struct_0(A_58),u1_orders_2(A_58))
      | ~ l1_orders_2(B_62)
      | ~ l1_orders_2(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_2037,plain,(
    ! [B_62] :
      ( r2_yellow_0(B_62,k9_relat_1('#skF_6','#skF_8'))
      | g1_orders_2(u1_struct_0(B_62),u1_orders_2(B_62)) != g1_orders_2(u1_struct_0('#skF_2'),u1_orders_2('#skF_2'))
      | ~ l1_orders_2(B_62)
      | ~ l1_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_2033,c_42])).

tff(c_2043,plain,(
    ! [B_62] :
      ( r2_yellow_0(B_62,k9_relat_1('#skF_6','#skF_8'))
      | g1_orders_2(u1_struct_0(B_62),u1_orders_2(B_62)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(B_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_191,c_320,c_2037])).

tff(c_2046,plain,
    ( r2_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8'))
    | ~ l1_orders_2('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2043])).

tff(c_2048,plain,(
    r2_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2046])).

tff(c_2050,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1475,c_2048])).

tff(c_2051,plain,(
    k2_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) != k1_funct_1('#skF_6',k2_yellow_0('#skF_1','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_1474])).

tff(c_2052,plain,(
    r2_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_1474])).

tff(c_46,plain,(
    ! [B_76,C_78,A_72] :
      ( k2_yellow_0(B_76,C_78) = k2_yellow_0(A_72,C_78)
      | ~ r2_yellow_0(A_72,C_78)
      | g1_orders_2(u1_struct_0(B_76),u1_orders_2(B_76)) != g1_orders_2(u1_struct_0(A_72),u1_orders_2(A_72))
      | ~ l1_orders_2(B_76)
      | ~ l1_orders_2(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_2059,plain,(
    ! [B_76] :
      ( k2_yellow_0(B_76,k9_relat_1('#skF_6','#skF_8')) = k2_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8'))
      | g1_orders_2(u1_struct_0(B_76),u1_orders_2(B_76)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(B_76)
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2052,c_46])).

tff(c_2159,plain,(
    ! [B_539] :
      ( k2_yellow_0(B_539,k9_relat_1('#skF_6','#skF_8')) = k2_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8'))
      | g1_orders_2(u1_struct_0(B_539),u1_orders_2(B_539)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(B_539) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2059])).

tff(c_2168,plain,
    ( k2_yellow_0('#skF_2',k9_relat_1('#skF_6','#skF_8')) = k2_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8'))
    | g1_orders_2(u1_struct_0('#skF_2'),u1_orders_2('#skF_4')) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
    | ~ l1_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_2159])).

tff(c_2177,plain,(
    k2_yellow_0('#skF_2',k9_relat_1('#skF_6','#skF_8')) = k2_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_191,c_2168])).

tff(c_1038,plain,(
    ! [A_435,B_436,C_437,D_438] :
      ( k3_funct_2(u1_struct_0(A_435),u1_struct_0(B_436),C_437,k2_yellow_0(A_435,D_438)) = k2_yellow_0(B_436,k7_relset_1(u1_struct_0(A_435),u1_struct_0(B_436),C_437,D_438))
      | ~ r2_yellow_0(A_435,D_438)
      | ~ r3_waybel_0(A_435,B_436,C_437,D_438)
      | ~ m1_subset_1(D_438,k1_zfmisc_1(u1_struct_0(A_435)))
      | ~ m1_subset_1(C_437,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_435),u1_struct_0(B_436))))
      | ~ v1_funct_2(C_437,u1_struct_0(A_435),u1_struct_0(B_436))
      | ~ v1_funct_1(C_437)
      | ~ l1_orders_2(B_436)
      | v2_struct_0(B_436)
      | ~ l1_orders_2(A_435)
      | v2_struct_0(A_435) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1052,plain,(
    ! [A_435,C_437,D_438] :
      ( k3_funct_2(u1_struct_0(A_435),u1_struct_0('#skF_2'),C_437,k2_yellow_0(A_435,D_438)) = k2_yellow_0('#skF_2',k7_relset_1(u1_struct_0(A_435),u1_struct_0('#skF_2'),C_437,D_438))
      | ~ r2_yellow_0(A_435,D_438)
      | ~ r3_waybel_0(A_435,'#skF_2',C_437,D_438)
      | ~ m1_subset_1(D_438,k1_zfmisc_1(u1_struct_0(A_435)))
      | ~ m1_subset_1(C_437,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_435),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_437,u1_struct_0(A_435),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_437)
      | ~ l1_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_orders_2(A_435)
      | v2_struct_0(A_435) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_1038])).

tff(c_1077,plain,(
    ! [A_435,C_437,D_438] :
      ( k3_funct_2(u1_struct_0(A_435),u1_struct_0('#skF_4'),C_437,k2_yellow_0(A_435,D_438)) = k2_yellow_0('#skF_2',k7_relset_1(u1_struct_0(A_435),u1_struct_0('#skF_4'),C_437,D_438))
      | ~ r2_yellow_0(A_435,D_438)
      | ~ r3_waybel_0(A_435,'#skF_2',C_437,D_438)
      | ~ m1_subset_1(D_438,k1_zfmisc_1(u1_struct_0(A_435)))
      | ~ m1_subset_1(C_437,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_435),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_437,u1_struct_0(A_435),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_437)
      | v2_struct_0('#skF_2')
      | ~ l1_orders_2(A_435)
      | v2_struct_0(A_435) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_191,c_191,c_191,c_1052])).

tff(c_3099,plain,(
    ! [A_634,C_635,D_636] :
      ( k3_funct_2(u1_struct_0(A_634),u1_struct_0('#skF_4'),C_635,k2_yellow_0(A_634,D_636)) = k2_yellow_0('#skF_2',k7_relset_1(u1_struct_0(A_634),u1_struct_0('#skF_4'),C_635,D_636))
      | ~ r2_yellow_0(A_634,D_636)
      | ~ r3_waybel_0(A_634,'#skF_2',C_635,D_636)
      | ~ m1_subset_1(D_636,k1_zfmisc_1(u1_struct_0(A_634)))
      | ~ m1_subset_1(C_635,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_634),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_635,u1_struct_0(A_634),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_635)
      | ~ l1_orders_2(A_634)
      | v2_struct_0(A_634) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1077])).

tff(c_3101,plain,(
    ! [D_636] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k2_yellow_0('#skF_1',D_636)) = k2_yellow_0('#skF_2',k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',D_636))
      | ~ r2_yellow_0('#skF_1',D_636)
      | ~ r3_waybel_0('#skF_1','#skF_2','#skF_6',D_636)
      | ~ m1_subset_1(D_636,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_424,c_3099])).

tff(c_3113,plain,(
    ! [D_636] :
      ( k2_yellow_0('#skF_2',k9_relat_1('#skF_6',D_636)) = k1_funct_1('#skF_6',k2_yellow_0('#skF_1',D_636))
      | ~ r2_yellow_0('#skF_1',D_636)
      | ~ r3_waybel_0('#skF_1','#skF_2','#skF_6',D_636)
      | ~ m1_subset_1(D_636,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_60,c_425,c_422,c_1344,c_3101])).

tff(c_3129,plain,(
    ! [D_637] :
      ( k2_yellow_0('#skF_2',k9_relat_1('#skF_6',D_637)) = k1_funct_1('#skF_6',k2_yellow_0('#skF_1',D_637))
      | ~ r2_yellow_0('#skF_1',D_637)
      | ~ r3_waybel_0('#skF_1','#skF_2','#skF_6',D_637)
      | ~ m1_subset_1(D_637,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_3113])).

tff(c_3132,plain,
    ( k2_yellow_0('#skF_2',k9_relat_1('#skF_6','#skF_8')) = k1_funct_1('#skF_6',k2_yellow_0('#skF_1','#skF_8'))
    | ~ r2_yellow_0('#skF_1','#skF_8')
    | ~ r3_waybel_0('#skF_1','#skF_2','#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_98,c_3129])).

tff(c_3135,plain,(
    k2_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) = k1_funct_1('#skF_6',k2_yellow_0('#skF_1','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_990,c_2177,c_3132])).

tff(c_3137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2051,c_3135])).

tff(c_3141,plain,(
    ! [B_638,C_639] :
      ( r3_waybel_0('#skF_1',B_638,C_639,'#skF_8')
      | ~ m1_subset_1(C_639,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_638))))
      | ~ v1_funct_2(C_639,u1_struct_0('#skF_1'),u1_struct_0(B_638))
      | ~ v1_funct_1(C_639)
      | ~ l1_orders_2(B_638)
      | v2_struct_0(B_638) ) ),
    inference(splitRight,[status(thm)],[c_756])).

tff(c_3147,plain,
    ( r3_waybel_0('#skF_1','#skF_4','#skF_6','#skF_8')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_424,c_3141])).

tff(c_3164,plain,
    ( r3_waybel_0('#skF_1','#skF_4','#skF_6','#skF_8')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_60,c_425,c_3147])).

tff(c_3166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_907,c_3164])).

tff(c_3167,plain,
    ( ~ r2_yellow_0('#skF_1','#skF_8')
    | r2_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_905])).

tff(c_3211,plain,(
    ~ r2_yellow_0('#skF_1','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_3167])).

tff(c_440,plain,
    ( m1_subset_1(u1_orders_2('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
    | ~ l1_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_24])).

tff(c_459,plain,(
    m1_subset_1(u1_orders_2('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_400,c_440])).

tff(c_423,plain,(
    g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_3')) = g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_70])).

tff(c_539,plain,(
    ! [D_43,C_42] :
      ( u1_orders_2('#skF_3') = D_43
      | g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) != g1_orders_2(C_42,D_43)
      | ~ m1_subset_1(u1_orders_2('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_28])).

tff(c_547,plain,(
    ! [D_43,C_42] :
      ( u1_orders_2('#skF_3') = D_43
      | g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) != g1_orders_2(C_42,D_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_539])).

tff(c_564,plain,(
    u1_orders_2('#skF_3') = u1_orders_2('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_547])).

tff(c_742,plain,(
    ! [D_412,B_413,C_414] :
      ( r2_yellow_0('#skF_3',D_412)
      | r3_waybel_0('#skF_3',B_413,C_414,D_412)
      | ~ m1_subset_1(D_412,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_413))))
      | ~ v1_funct_2(C_414,u1_struct_0('#skF_3'),u1_struct_0(B_413))
      | ~ v1_funct_1(C_414)
      | ~ l1_orders_2(B_413)
      | v2_struct_0(B_413)
      | ~ l1_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_740])).

tff(c_748,plain,(
    ! [D_412,B_413,C_414] :
      ( r2_yellow_0('#skF_3',D_412)
      | r3_waybel_0('#skF_3',B_413,C_414,D_412)
      | ~ m1_subset_1(D_412,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_413))))
      | ~ v1_funct_2(C_414,u1_struct_0('#skF_1'),u1_struct_0(B_413))
      | ~ v1_funct_1(C_414)
      | ~ l1_orders_2(B_413)
      | v2_struct_0(B_413)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_400,c_400,c_742])).

tff(c_3563,plain,(
    ! [D_680,B_681,C_682] :
      ( r2_yellow_0('#skF_3',D_680)
      | r3_waybel_0('#skF_3',B_681,C_682,D_680)
      | ~ m1_subset_1(D_680,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(C_682,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_681))))
      | ~ v1_funct_2(C_682,u1_struct_0('#skF_1'),u1_struct_0(B_681))
      | ~ v1_funct_1(C_682)
      | ~ l1_orders_2(B_681)
      | v2_struct_0(B_681) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_748])).

tff(c_3566,plain,(
    ! [B_681,C_682] :
      ( r2_yellow_0('#skF_3','#skF_8')
      | r3_waybel_0('#skF_3',B_681,C_682,'#skF_8')
      | ~ m1_subset_1(C_682,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_681))))
      | ~ v1_funct_2(C_682,u1_struct_0('#skF_1'),u1_struct_0(B_681))
      | ~ v1_funct_1(C_682)
      | ~ l1_orders_2(B_681)
      | v2_struct_0(B_681) ) ),
    inference(resolution,[status(thm)],[c_98,c_3563])).

tff(c_3567,plain,(
    r2_yellow_0('#skF_3','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_3566])).

tff(c_3571,plain,(
    ! [B_62] :
      ( r2_yellow_0(B_62,'#skF_8')
      | g1_orders_2(u1_struct_0(B_62),u1_orders_2(B_62)) != g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_3'))
      | ~ l1_orders_2(B_62)
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3567,c_42])).

tff(c_3577,plain,(
    ! [B_62] :
      ( r2_yellow_0(B_62,'#skF_8')
      | g1_orders_2(u1_struct_0(B_62),u1_orders_2(B_62)) != g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
      | ~ l1_orders_2(B_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_400,c_564,c_3571])).

tff(c_3580,plain,
    ( r2_yellow_0('#skF_1','#skF_8')
    | ~ l1_orders_2('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3577])).

tff(c_3582,plain,(
    r2_yellow_0('#skF_1','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_3580])).

tff(c_3584,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3211,c_3582])).

tff(c_3623,plain,(
    ! [B_687,C_688] :
      ( r3_waybel_0('#skF_3',B_687,C_688,'#skF_8')
      | ~ m1_subset_1(C_688,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_687))))
      | ~ v1_funct_2(C_688,u1_struct_0('#skF_1'),u1_struct_0(B_687))
      | ~ v1_funct_1(C_688)
      | ~ l1_orders_2(B_687)
      | v2_struct_0(B_687) ) ),
    inference(splitRight,[status(thm)],[c_3566])).

tff(c_3629,plain,
    ( r3_waybel_0('#skF_3','#skF_4','#skF_6','#skF_8')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_424,c_3623])).

tff(c_3646,plain,
    ( r3_waybel_0('#skF_3','#skF_4','#skF_6','#skF_8')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_60,c_425,c_3629])).

tff(c_3648,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_111,c_3646])).

tff(c_3649,plain,(
    r2_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_3167])).

tff(c_4297,plain,(
    ! [A_732,B_733,C_734,B_735] :
      ( k3_funct_2(u1_struct_0(A_732),B_733,C_734,k2_yellow_0(A_732,B_735)) = k1_funct_1(C_734,k2_yellow_0(A_732,B_735))
      | ~ m1_subset_1(C_734,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_732),B_733)))
      | ~ v1_funct_2(C_734,u1_struct_0(A_732),B_733)
      | ~ v1_funct_1(C_734)
      | v1_xboole_0(u1_struct_0(A_732))
      | ~ l1_orders_2(A_732) ) ),
    inference(resolution,[status(thm)],[c_20,c_477])).

tff(c_4301,plain,(
    ! [B_735] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k2_yellow_0('#skF_1',B_735)) = k1_funct_1('#skF_6',k2_yellow_0('#skF_1',B_735))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_424,c_4297])).

tff(c_4316,plain,(
    ! [B_735] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k2_yellow_0('#skF_1',B_735)) = k1_funct_1('#skF_6',k2_yellow_0('#skF_1',B_735))
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_60,c_425,c_4301])).

tff(c_4317,plain,(
    ! [B_735] : k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k2_yellow_0('#skF_1',B_735)) = k1_funct_1('#skF_6',k2_yellow_0('#skF_1',B_735)) ),
    inference(negUnitSimplification,[status(thm)],[c_474,c_4316])).

tff(c_3168,plain,(
    r3_waybel_0('#skF_1','#skF_4','#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_905])).

tff(c_3650,plain,(
    r2_yellow_0('#skF_1','#skF_8') ),
    inference(splitRight,[status(thm)],[c_3167])).

tff(c_3652,plain,(
    ! [B_76] :
      ( k2_yellow_0(B_76,'#skF_8') = k2_yellow_0('#skF_1','#skF_8')
      | g1_orders_2(u1_struct_0(B_76),u1_orders_2(B_76)) != g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
      | ~ l1_orders_2(B_76)
      | ~ l1_orders_2('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_3650,c_46])).

tff(c_3810,plain,(
    ! [B_697] :
      ( k2_yellow_0(B_697,'#skF_8') = k2_yellow_0('#skF_1','#skF_8')
      | g1_orders_2(u1_struct_0(B_697),u1_orders_2(B_697)) != g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
      | ~ l1_orders_2(B_697) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_3652])).

tff(c_3813,plain,
    ( k2_yellow_0('#skF_3','#skF_8') = k2_yellow_0('#skF_1','#skF_8')
    | g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_1')) != g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
    | ~ l1_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_564,c_3810])).

tff(c_3824,plain,(
    k2_yellow_0('#skF_3','#skF_8') = k2_yellow_0('#skF_1','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_400,c_3813])).

tff(c_443,plain,(
    ! [B_34] :
      ( m1_subset_1(k2_yellow_0('#skF_3',B_34),u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_20])).

tff(c_461,plain,(
    ! [B_34] : m1_subset_1(k2_yellow_0('#skF_3',B_34),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_443])).

tff(c_479,plain,(
    ! [B_379,C_380,B_34] :
      ( k3_funct_2(u1_struct_0('#skF_1'),B_379,C_380,k2_yellow_0('#skF_3',B_34)) = k1_funct_1(C_380,k2_yellow_0('#skF_3',B_34))
      | ~ m1_subset_1(C_380,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),B_379)))
      | ~ v1_funct_2(C_380,u1_struct_0('#skF_1'),B_379)
      | ~ v1_funct_1(C_380)
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_461,c_477])).

tff(c_3994,plain,(
    ! [B_708,C_709,B_710] :
      ( k3_funct_2(u1_struct_0('#skF_1'),B_708,C_709,k2_yellow_0('#skF_3',B_710)) = k1_funct_1(C_709,k2_yellow_0('#skF_3',B_710))
      | ~ m1_subset_1(C_709,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),B_708)))
      | ~ v1_funct_2(C_709,u1_struct_0('#skF_1'),B_708)
      | ~ v1_funct_1(C_709) ) ),
    inference(negUnitSimplification,[status(thm)],[c_474,c_479])).

tff(c_3998,plain,(
    ! [B_710] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k2_yellow_0('#skF_3',B_710)) = k1_funct_1('#skF_6',k2_yellow_0('#skF_3',B_710))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_424,c_3994])).

tff(c_4009,plain,(
    ! [B_711] : k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k2_yellow_0('#skF_3',B_711)) = k1_funct_1('#skF_6',k2_yellow_0('#skF_3',B_711)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_425,c_3998])).

tff(c_4018,plain,(
    k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k2_yellow_0('#skF_1','#skF_8')) = k1_funct_1('#skF_6',k2_yellow_0('#skF_3','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3824,c_4009])).

tff(c_4021,plain,(
    k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k2_yellow_0('#skF_1','#skF_8')) = k1_funct_1('#skF_6',k2_yellow_0('#skF_1','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3824,c_4018])).

tff(c_3716,plain,(
    ! [A_691,B_692,C_693,D_694] :
      ( k3_funct_2(u1_struct_0(A_691),u1_struct_0(B_692),C_693,k2_yellow_0(A_691,D_694)) = k2_yellow_0(B_692,k7_relset_1(u1_struct_0(A_691),u1_struct_0(B_692),C_693,D_694))
      | ~ r2_yellow_0(A_691,D_694)
      | ~ r3_waybel_0(A_691,B_692,C_693,D_694)
      | ~ m1_subset_1(D_694,k1_zfmisc_1(u1_struct_0(A_691)))
      | ~ m1_subset_1(C_693,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_691),u1_struct_0(B_692))))
      | ~ v1_funct_2(C_693,u1_struct_0(A_691),u1_struct_0(B_692))
      | ~ v1_funct_1(C_693)
      | ~ l1_orders_2(B_692)
      | v2_struct_0(B_692)
      | ~ l1_orders_2(A_691)
      | v2_struct_0(A_691) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3720,plain,(
    ! [D_694] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k2_yellow_0('#skF_1',D_694)) = k2_yellow_0('#skF_4',k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',D_694))
      | ~ r2_yellow_0('#skF_1',D_694)
      | ~ r3_waybel_0('#skF_1','#skF_4','#skF_6',D_694)
      | ~ m1_subset_1(D_694,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_424,c_3716])).

tff(c_3739,plain,(
    ! [D_694] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k2_yellow_0('#skF_1',D_694)) = k2_yellow_0('#skF_4',k9_relat_1('#skF_6',D_694))
      | ~ r2_yellow_0('#skF_1',D_694)
      | ~ r3_waybel_0('#skF_1','#skF_4','#skF_6',D_694)
      | ~ m1_subset_1(D_694,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_72,c_60,c_425,c_422,c_3720])).

tff(c_3740,plain,(
    ! [D_694] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k2_yellow_0('#skF_1',D_694)) = k2_yellow_0('#skF_4',k9_relat_1('#skF_6',D_694))
      | ~ r2_yellow_0('#skF_1',D_694)
      | ~ r3_waybel_0('#skF_1','#skF_4','#skF_6',D_694)
      | ~ m1_subset_1(D_694,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_74,c_3739])).

tff(c_4027,plain,
    ( k2_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) = k1_funct_1('#skF_6',k2_yellow_0('#skF_1','#skF_8'))
    | ~ r2_yellow_0('#skF_1','#skF_8')
    | ~ r3_waybel_0('#skF_1','#skF_4','#skF_6','#skF_8')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4021,c_3740])).

tff(c_4037,plain,(
    k2_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) = k1_funct_1('#skF_6',k2_yellow_0('#skF_1','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_3168,c_3650,c_4027])).

tff(c_3948,plain,(
    ! [A_704,B_705,C_706,D_707] :
      ( k3_funct_2(u1_struct_0(A_704),u1_struct_0(B_705),C_706,k2_yellow_0(A_704,D_707)) != k2_yellow_0(B_705,k7_relset_1(u1_struct_0(A_704),u1_struct_0(B_705),C_706,D_707))
      | ~ r2_yellow_0(B_705,k7_relset_1(u1_struct_0(A_704),u1_struct_0(B_705),C_706,D_707))
      | r3_waybel_0(A_704,B_705,C_706,D_707)
      | ~ m1_subset_1(D_707,k1_zfmisc_1(u1_struct_0(A_704)))
      | ~ m1_subset_1(C_706,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_704),u1_struct_0(B_705))))
      | ~ v1_funct_2(C_706,u1_struct_0(A_704),u1_struct_0(B_705))
      | ~ v1_funct_1(C_706)
      | ~ l1_orders_2(B_705)
      | v2_struct_0(B_705)
      | ~ l1_orders_2(A_704)
      | v2_struct_0(A_704) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3952,plain,(
    ! [B_705,C_706] :
      ( k3_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_705),C_706,k2_yellow_0('#skF_1','#skF_8')) != k2_yellow_0(B_705,k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0(B_705),C_706,'#skF_8'))
      | ~ r2_yellow_0(B_705,k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0(B_705),C_706,'#skF_8'))
      | r3_waybel_0('#skF_3',B_705,C_706,'#skF_8')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(C_706,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_705))))
      | ~ v1_funct_2(C_706,u1_struct_0('#skF_3'),u1_struct_0(B_705))
      | ~ v1_funct_1(C_706)
      | ~ l1_orders_2(B_705)
      | v2_struct_0(B_705)
      | ~ l1_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3824,c_3948])).

tff(c_3971,plain,(
    ! [B_705,C_706] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0(B_705),C_706,k2_yellow_0('#skF_1','#skF_8')) != k2_yellow_0(B_705,k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_705),C_706,'#skF_8'))
      | ~ r2_yellow_0(B_705,k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_705),C_706,'#skF_8'))
      | r3_waybel_0('#skF_3',B_705,C_706,'#skF_8')
      | ~ m1_subset_1(C_706,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_705))))
      | ~ v1_funct_2(C_706,u1_struct_0('#skF_1'),u1_struct_0(B_705))
      | ~ v1_funct_1(C_706)
      | ~ l1_orders_2(B_705)
      | v2_struct_0(B_705)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_400,c_400,c_98,c_400,c_400,c_400,c_400,c_3952])).

tff(c_6104,plain,(
    ! [B_901,C_902] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0(B_901),C_902,k2_yellow_0('#skF_1','#skF_8')) != k2_yellow_0(B_901,k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_901),C_902,'#skF_8'))
      | ~ r2_yellow_0(B_901,k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_901),C_902,'#skF_8'))
      | r3_waybel_0('#skF_3',B_901,C_902,'#skF_8')
      | ~ m1_subset_1(C_902,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_901))))
      | ~ v1_funct_2(C_902,u1_struct_0('#skF_1'),u1_struct_0(B_901))
      | ~ v1_funct_1(C_902)
      | ~ l1_orders_2(B_901)
      | v2_struct_0(B_901) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3971])).

tff(c_6113,plain,
    ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k2_yellow_0('#skF_1','#skF_8')) != k2_yellow_0('#skF_4',k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6','#skF_8'))
    | ~ r2_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8'))
    | r3_waybel_0('#skF_3','#skF_4','#skF_6','#skF_8')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_6104])).

tff(c_6129,plain,
    ( r3_waybel_0('#skF_3','#skF_4','#skF_6','#skF_8')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_60,c_425,c_424,c_3649,c_4317,c_4037,c_422,c_6113])).

tff(c_6131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_111,c_6129])).

tff(c_6133,plain,(
    ~ r3_waybel_0('#skF_1','#skF_2','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_92,plain,
    ( ~ r4_waybel_0('#skF_3','#skF_4','#skF_6','#skF_8')
    | r3_waybel_0('#skF_1','#skF_2','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_97,plain,
    ( ~ r4_waybel_0('#skF_3','#skF_4','#skF_6','#skF_8')
    | r3_waybel_0('#skF_1','#skF_2','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_92])).

tff(c_6138,plain,(
    ~ r4_waybel_0('#skF_3','#skF_4','#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_6133,c_97])).

tff(c_6172,plain,(
    ! [C_910,A_911,D_912,B_913] :
      ( C_910 = A_911
      | g1_orders_2(C_910,D_912) != g1_orders_2(A_911,B_913)
      | ~ m1_subset_1(B_913,k1_zfmisc_1(k2_zfmisc_1(A_911,A_911))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_6226,plain,(
    ! [A_923,B_924] :
      ( u1_struct_0('#skF_3') = A_923
      | g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) != g1_orders_2(A_923,B_924)
      | ~ m1_subset_1(B_924,k1_zfmisc_1(k2_zfmisc_1(A_923,A_923))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_6172])).

tff(c_6230,plain,(
    ! [A_36] :
      ( u1_struct_0(A_36) = u1_struct_0('#skF_3')
      | g1_orders_2(u1_struct_0(A_36),u1_orders_2(A_36)) != g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
      | ~ l1_orders_2(A_36) ) ),
    inference(resolution,[status(thm)],[c_24,c_6226])).

tff(c_6419,plain,
    ( u1_struct_0('#skF_3') = u1_struct_0('#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_6230])).

tff(c_6421,plain,(
    u1_struct_0('#skF_3') = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_6419])).

tff(c_6446,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6421,c_58])).

tff(c_6445,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6421,c_56])).

tff(c_6683,plain,(
    ! [A_967,D_968,B_969,C_970] :
      ( r1_yellow_0(A_967,D_968)
      | r4_waybel_0(A_967,B_969,C_970,D_968)
      | ~ m1_subset_1(D_968,k1_zfmisc_1(u1_struct_0(A_967)))
      | ~ m1_subset_1(C_970,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_967),u1_struct_0(B_969))))
      | ~ v1_funct_2(C_970,u1_struct_0(A_967),u1_struct_0(B_969))
      | ~ v1_funct_1(C_970)
      | ~ l1_orders_2(B_969)
      | v2_struct_0(B_969)
      | ~ l1_orders_2(A_967)
      | v2_struct_0(A_967) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6689,plain,(
    ! [B_969,C_970] :
      ( r1_yellow_0('#skF_1','#skF_8')
      | r4_waybel_0('#skF_1',B_969,C_970,'#skF_8')
      | ~ m1_subset_1(C_970,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_969))))
      | ~ v1_funct_2(C_970,u1_struct_0('#skF_1'),u1_struct_0(B_969))
      | ~ v1_funct_1(C_970)
      | ~ l1_orders_2(B_969)
      | v2_struct_0(B_969)
      | ~ l1_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_98,c_6683])).

tff(c_6698,plain,(
    ! [B_969,C_970] :
      ( r1_yellow_0('#skF_1','#skF_8')
      | r4_waybel_0('#skF_1',B_969,C_970,'#skF_8')
      | ~ m1_subset_1(C_970,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_969))))
      | ~ v1_funct_2(C_970,u1_struct_0('#skF_1'),u1_struct_0(B_969))
      | ~ v1_funct_1(C_970)
      | ~ l1_orders_2(B_969)
      | v2_struct_0(B_969)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_6689])).

tff(c_6699,plain,(
    ! [B_969,C_970] :
      ( r1_yellow_0('#skF_1','#skF_8')
      | r4_waybel_0('#skF_1',B_969,C_970,'#skF_8')
      | ~ m1_subset_1(C_970,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_969))))
      | ~ v1_funct_2(C_970,u1_struct_0('#skF_1'),u1_struct_0(B_969))
      | ~ v1_funct_1(C_970)
      | ~ l1_orders_2(B_969)
      | v2_struct_0(B_969) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_6698])).

tff(c_6779,plain,(
    r1_yellow_0('#skF_1','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_6699])).

tff(c_6140,plain,(
    ! [A_904,B_905,C_906,D_907] :
      ( k7_relset_1(A_904,B_905,C_906,D_907) = k9_relat_1(C_906,D_907)
      | ~ m1_subset_1(C_906,k1_zfmisc_1(k2_zfmisc_1(A_904,B_905))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_6148,plain,(
    ! [D_907] : k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_6',D_907) = k9_relat_1('#skF_6',D_907) ),
    inference(resolution,[status(thm)],[c_56,c_6140])).

tff(c_6443,plain,(
    ! [D_907] : k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',D_907) = k9_relat_1('#skF_6',D_907) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6421,c_6148])).

tff(c_6931,plain,(
    ! [B_996,A_997,C_998,D_999] :
      ( r1_yellow_0(B_996,k7_relset_1(u1_struct_0(A_997),u1_struct_0(B_996),C_998,D_999))
      | ~ r1_yellow_0(A_997,D_999)
      | ~ r4_waybel_0(A_997,B_996,C_998,D_999)
      | ~ m1_subset_1(D_999,k1_zfmisc_1(u1_struct_0(A_997)))
      | ~ m1_subset_1(C_998,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_997),u1_struct_0(B_996))))
      | ~ v1_funct_2(C_998,u1_struct_0(A_997),u1_struct_0(B_996))
      | ~ v1_funct_1(C_998)
      | ~ l1_orders_2(B_996)
      | v2_struct_0(B_996)
      | ~ l1_orders_2(A_997)
      | v2_struct_0(A_997) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6935,plain,(
    ! [D_999] :
      ( r1_yellow_0('#skF_4',k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',D_999))
      | ~ r1_yellow_0('#skF_1',D_999)
      | ~ r4_waybel_0('#skF_1','#skF_4','#skF_6',D_999)
      | ~ m1_subset_1(D_999,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6445,c_6931])).

tff(c_6954,plain,(
    ! [D_999] :
      ( r1_yellow_0('#skF_4',k9_relat_1('#skF_6',D_999))
      | ~ r1_yellow_0('#skF_1',D_999)
      | ~ r4_waybel_0('#skF_1','#skF_4','#skF_6',D_999)
      | ~ m1_subset_1(D_999,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_72,c_60,c_6446,c_6443,c_6935])).

tff(c_6973,plain,(
    ! [D_1000] :
      ( r1_yellow_0('#skF_4',k9_relat_1('#skF_6',D_1000))
      | ~ r1_yellow_0('#skF_1',D_1000)
      | ~ r4_waybel_0('#skF_1','#skF_4','#skF_6',D_1000)
      | ~ m1_subset_1(D_1000,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_74,c_6954])).

tff(c_6976,plain,
    ( r1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8'))
    | ~ r1_yellow_0('#skF_1','#skF_8')
    | ~ r4_waybel_0('#skF_1','#skF_4','#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_98,c_6973])).

tff(c_6979,plain,
    ( r1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8'))
    | ~ r4_waybel_0('#skF_1','#skF_4','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6779,c_6976])).

tff(c_6980,plain,(
    ~ r4_waybel_0('#skF_1','#skF_4','#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_6979])).

tff(c_6461,plain,
    ( m1_subset_1(u1_orders_2('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
    | ~ l1_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6421,c_24])).

tff(c_6480,plain,(
    m1_subset_1(u1_orders_2('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_6421,c_6461])).

tff(c_6444,plain,(
    g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_3')) = g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6421,c_70])).

tff(c_6560,plain,(
    ! [D_43,C_42] :
      ( u1_orders_2('#skF_3') = D_43
      | g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) != g1_orders_2(C_42,D_43)
      | ~ m1_subset_1(u1_orders_2('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6444,c_28])).

tff(c_6568,plain,(
    ! [D_43,C_42] :
      ( u1_orders_2('#skF_3') = D_43
      | g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) != g1_orders_2(C_42,D_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6480,c_6560])).

tff(c_6585,plain,(
    u1_orders_2('#skF_3') = u1_orders_2('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_6568])).

tff(c_44,plain,(
    ! [B_69,C_71,A_65] :
      ( k1_yellow_0(B_69,C_71) = k1_yellow_0(A_65,C_71)
      | ~ r1_yellow_0(A_65,C_71)
      | g1_orders_2(u1_struct_0(B_69),u1_orders_2(B_69)) != g1_orders_2(u1_struct_0(A_65),u1_orders_2(A_65))
      | ~ l1_orders_2(B_69)
      | ~ l1_orders_2(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_6781,plain,(
    ! [B_69] :
      ( k1_yellow_0(B_69,'#skF_8') = k1_yellow_0('#skF_1','#skF_8')
      | g1_orders_2(u1_struct_0(B_69),u1_orders_2(B_69)) != g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
      | ~ l1_orders_2(B_69)
      | ~ l1_orders_2('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6779,c_44])).

tff(c_6833,plain,(
    ! [B_987] :
      ( k1_yellow_0(B_987,'#skF_8') = k1_yellow_0('#skF_1','#skF_8')
      | g1_orders_2(u1_struct_0(B_987),u1_orders_2(B_987)) != g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
      | ~ l1_orders_2(B_987) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_6781])).

tff(c_6839,plain,
    ( k1_yellow_0('#skF_3','#skF_8') = k1_yellow_0('#skF_1','#skF_8')
    | g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_3')) != g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
    | ~ l1_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6421,c_6833])).

tff(c_6849,plain,(
    k1_yellow_0('#skF_3','#skF_8') = k1_yellow_0('#skF_1','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_6585,c_6839])).

tff(c_6470,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6421,c_26])).

tff(c_6485,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_6470])).

tff(c_6487,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_6485])).

tff(c_6490,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_6487])).

tff(c_6494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_6490])).

tff(c_6495,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_6485])).

tff(c_18,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1(k1_yellow_0(A_31,B_32),u1_struct_0(A_31))
      | ~ l1_orders_2(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6467,plain,(
    ! [B_32] :
      ( m1_subset_1(k1_yellow_0('#skF_3',B_32),u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6421,c_18])).

tff(c_6532,plain,(
    ! [B_953] : m1_subset_1(k1_yellow_0('#skF_3',B_953),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_6467])).

tff(c_32,plain,(
    ! [A_44,B_45,C_46,D_47] :
      ( k3_funct_2(A_44,B_45,C_46,D_47) = k1_funct_1(C_46,D_47)
      | ~ m1_subset_1(D_47,A_44)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45)))
      | ~ v1_funct_2(C_46,A_44,B_45)
      | ~ v1_funct_1(C_46)
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_6534,plain,(
    ! [B_45,C_46,B_953] :
      ( k3_funct_2(u1_struct_0('#skF_1'),B_45,C_46,k1_yellow_0('#skF_3',B_953)) = k1_funct_1(C_46,k1_yellow_0('#skF_3',B_953))
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),B_45)))
      | ~ v1_funct_2(C_46,u1_struct_0('#skF_1'),B_45)
      | ~ v1_funct_1(C_46)
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_6532,c_32])).

tff(c_7126,plain,(
    ! [B_1008,C_1009,B_1010] :
      ( k3_funct_2(u1_struct_0('#skF_1'),B_1008,C_1009,k1_yellow_0('#skF_3',B_1010)) = k1_funct_1(C_1009,k1_yellow_0('#skF_3',B_1010))
      | ~ m1_subset_1(C_1009,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),B_1008)))
      | ~ v1_funct_2(C_1009,u1_struct_0('#skF_1'),B_1008)
      | ~ v1_funct_1(C_1009) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6495,c_6534])).

tff(c_7130,plain,(
    ! [B_1010] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_3',B_1010)) = k1_funct_1('#skF_6',k1_yellow_0('#skF_3',B_1010))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_6445,c_7126])).

tff(c_7141,plain,(
    ! [B_1011] : k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_3',B_1011)) = k1_funct_1('#skF_6',k1_yellow_0('#skF_3',B_1011)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6446,c_7130])).

tff(c_7150,plain,(
    k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_1','#skF_8')) = k1_funct_1('#skF_6',k1_yellow_0('#skF_3','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6849,c_7141])).

tff(c_7153,plain,(
    k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_1','#skF_8')) = k1_funct_1('#skF_6',k1_yellow_0('#skF_1','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6849,c_7150])).

tff(c_7401,plain,(
    ! [A_1035,B_1036,C_1037,D_1038] :
      ( k3_funct_2(u1_struct_0(A_1035),u1_struct_0(B_1036),C_1037,k1_yellow_0(A_1035,D_1038)) != k1_yellow_0(B_1036,k7_relset_1(u1_struct_0(A_1035),u1_struct_0(B_1036),C_1037,D_1038))
      | ~ r1_yellow_0(B_1036,k7_relset_1(u1_struct_0(A_1035),u1_struct_0(B_1036),C_1037,D_1038))
      | r4_waybel_0(A_1035,B_1036,C_1037,D_1038)
      | ~ m1_subset_1(D_1038,k1_zfmisc_1(u1_struct_0(A_1035)))
      | ~ m1_subset_1(C_1037,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1035),u1_struct_0(B_1036))))
      | ~ v1_funct_2(C_1037,u1_struct_0(A_1035),u1_struct_0(B_1036))
      | ~ v1_funct_1(C_1037)
      | ~ l1_orders_2(B_1036)
      | v2_struct_0(B_1036)
      | ~ l1_orders_2(A_1035)
      | v2_struct_0(A_1035) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_7405,plain,
    ( k1_yellow_0('#skF_4',k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6','#skF_8')) != k1_funct_1('#skF_6',k1_yellow_0('#skF_1','#skF_8'))
    | ~ r1_yellow_0('#skF_4',k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6','#skF_8'))
    | r4_waybel_0('#skF_1','#skF_4','#skF_6','#skF_8')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_orders_2('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7153,c_7401])).

tff(c_7424,plain,
    ( k1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) != k1_funct_1('#skF_6',k1_yellow_0('#skF_1','#skF_8'))
    | ~ r1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8'))
    | r4_waybel_0('#skF_1','#skF_4','#skF_6','#skF_8')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_72,c_60,c_6446,c_6445,c_98,c_6443,c_6443,c_7405])).

tff(c_7425,plain,
    ( k1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) != k1_funct_1('#skF_6',k1_yellow_0('#skF_1','#skF_8'))
    | ~ r1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_74,c_6980,c_7424])).

tff(c_7447,plain,(
    ~ r1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_7425])).

tff(c_6203,plain,(
    ! [A_920,B_921] :
      ( u1_struct_0('#skF_2') = A_920
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(A_920,B_921)
      | ~ m1_subset_1(B_921,k1_zfmisc_1(k2_zfmisc_1(A_920,A_920))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_6172])).

tff(c_6207,plain,(
    ! [A_36] :
      ( u1_struct_0(A_36) = u1_struct_0('#skF_2')
      | g1_orders_2(u1_struct_0(A_36),u1_orders_2(A_36)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(A_36) ) ),
    inference(resolution,[status(thm)],[c_24,c_6203])).

tff(c_6210,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_6207])).

tff(c_6212,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_6210])).

tff(c_6247,plain,
    ( m1_subset_1(u1_orders_2('#skF_2'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ l1_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6212,c_24])).

tff(c_6267,plain,(
    m1_subset_1(u1_orders_2('#skF_2'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_6212,c_6247])).

tff(c_6235,plain,(
    g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_2')) = g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6212,c_68])).

tff(c_6304,plain,(
    ! [D_43,C_42] :
      ( u1_orders_2('#skF_2') = D_43
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(C_42,D_43)
      | ~ m1_subset_1(u1_orders_2('#skF_2'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6235,c_28])).

tff(c_6312,plain,(
    ! [D_43,C_42] :
      ( u1_orders_2('#skF_2') = D_43
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(C_42,D_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6267,c_6304])).

tff(c_6341,plain,(
    u1_orders_2('#skF_2') = u1_orders_2('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_6312])).

tff(c_6259,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6212,c_26])).

tff(c_6274,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_6259])).

tff(c_6276,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_6274])).

tff(c_6279,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_6276])).

tff(c_6283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_6279])).

tff(c_6284,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_6274])).

tff(c_6237,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6212,c_64])).

tff(c_6236,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6212,c_62])).

tff(c_6234,plain,(
    r1_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6212,c_54])).

tff(c_6441,plain,(
    r1_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6421,c_6234])).

tff(c_6709,plain,(
    ! [C_976,B_972,A_971,F_974,D_975,E_973] :
      ( F_974 = E_973
      | ~ r1_funct_2(A_971,B_972,C_976,D_975,E_973,F_974)
      | ~ m1_subset_1(F_974,k1_zfmisc_1(k2_zfmisc_1(C_976,D_975)))
      | ~ v1_funct_2(F_974,C_976,D_975)
      | ~ v1_funct_1(F_974)
      | ~ m1_subset_1(E_973,k1_zfmisc_1(k2_zfmisc_1(A_971,B_972)))
      | ~ v1_funct_2(E_973,A_971,B_972)
      | ~ v1_funct_1(E_973)
      | v1_xboole_0(D_975)
      | v1_xboole_0(B_972) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_6711,plain,
    ( '#skF_5' = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6441,c_6709])).

tff(c_6714,plain,
    ( '#skF_5' = '#skF_6'
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_6237,c_6236,c_60,c_6446,c_6445,c_6711])).

tff(c_6715,plain,(
    '#skF_5' = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_6284,c_6714])).

tff(c_6132,plain,(
    r4_waybel_0('#skF_1','#skF_2','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_6721,plain,(
    r4_waybel_0('#skF_1','#skF_2','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6715,c_6132])).

tff(c_6945,plain,(
    ! [A_997,C_998,D_999] :
      ( r1_yellow_0('#skF_2',k7_relset_1(u1_struct_0(A_997),u1_struct_0('#skF_2'),C_998,D_999))
      | ~ r1_yellow_0(A_997,D_999)
      | ~ r4_waybel_0(A_997,'#skF_2',C_998,D_999)
      | ~ m1_subset_1(D_999,k1_zfmisc_1(u1_struct_0(A_997)))
      | ~ m1_subset_1(C_998,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_997),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_998,u1_struct_0(A_997),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_998)
      | ~ l1_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_orders_2(A_997)
      | v2_struct_0(A_997) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6212,c_6931])).

tff(c_6970,plain,(
    ! [A_997,C_998,D_999] :
      ( r1_yellow_0('#skF_2',k7_relset_1(u1_struct_0(A_997),u1_struct_0('#skF_4'),C_998,D_999))
      | ~ r1_yellow_0(A_997,D_999)
      | ~ r4_waybel_0(A_997,'#skF_2',C_998,D_999)
      | ~ m1_subset_1(D_999,k1_zfmisc_1(u1_struct_0(A_997)))
      | ~ m1_subset_1(C_998,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_997),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_998,u1_struct_0(A_997),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_998)
      | v2_struct_0('#skF_2')
      | ~ l1_orders_2(A_997)
      | v2_struct_0(A_997) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_6212,c_6212,c_6945])).

tff(c_8247,plain,(
    ! [A_1123,C_1124,D_1125] :
      ( r1_yellow_0('#skF_2',k7_relset_1(u1_struct_0(A_1123),u1_struct_0('#skF_4'),C_1124,D_1125))
      | ~ r1_yellow_0(A_1123,D_1125)
      | ~ r4_waybel_0(A_1123,'#skF_2',C_1124,D_1125)
      | ~ m1_subset_1(D_1125,k1_zfmisc_1(u1_struct_0(A_1123)))
      | ~ m1_subset_1(C_1124,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1123),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_1124,u1_struct_0(A_1123),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_1124)
      | ~ l1_orders_2(A_1123)
      | v2_struct_0(A_1123) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_6970])).

tff(c_8249,plain,(
    ! [D_1125] :
      ( r1_yellow_0('#skF_2',k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',D_1125))
      | ~ r1_yellow_0('#skF_1',D_1125)
      | ~ r4_waybel_0('#skF_1','#skF_2','#skF_6',D_1125)
      | ~ m1_subset_1(D_1125,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6445,c_8247])).

tff(c_8261,plain,(
    ! [D_1125] :
      ( r1_yellow_0('#skF_2',k9_relat_1('#skF_6',D_1125))
      | ~ r1_yellow_0('#skF_1',D_1125)
      | ~ r4_waybel_0('#skF_1','#skF_2','#skF_6',D_1125)
      | ~ m1_subset_1(D_1125,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_60,c_6446,c_6443,c_8249])).

tff(c_8277,plain,(
    ! [D_1126] :
      ( r1_yellow_0('#skF_2',k9_relat_1('#skF_6',D_1126))
      | ~ r1_yellow_0('#skF_1',D_1126)
      | ~ r4_waybel_0('#skF_1','#skF_2','#skF_6',D_1126)
      | ~ m1_subset_1(D_1126,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_8261])).

tff(c_8280,plain,
    ( r1_yellow_0('#skF_2',k9_relat_1('#skF_6','#skF_8'))
    | ~ r1_yellow_0('#skF_1','#skF_8')
    | ~ r4_waybel_0('#skF_1','#skF_2','#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_98,c_8277])).

tff(c_8283,plain,(
    r1_yellow_0('#skF_2',k9_relat_1('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6721,c_6779,c_8280])).

tff(c_40,plain,(
    ! [B_62,C_64,A_58] :
      ( r1_yellow_0(B_62,C_64)
      | ~ r1_yellow_0(A_58,C_64)
      | g1_orders_2(u1_struct_0(B_62),u1_orders_2(B_62)) != g1_orders_2(u1_struct_0(A_58),u1_orders_2(A_58))
      | ~ l1_orders_2(B_62)
      | ~ l1_orders_2(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_8287,plain,(
    ! [B_62] :
      ( r1_yellow_0(B_62,k9_relat_1('#skF_6','#skF_8'))
      | g1_orders_2(u1_struct_0(B_62),u1_orders_2(B_62)) != g1_orders_2(u1_struct_0('#skF_2'),u1_orders_2('#skF_2'))
      | ~ l1_orders_2(B_62)
      | ~ l1_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8283,c_40])).

tff(c_8293,plain,(
    ! [B_62] :
      ( r1_yellow_0(B_62,k9_relat_1('#skF_6','#skF_8'))
      | g1_orders_2(u1_struct_0(B_62),u1_orders_2(B_62)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(B_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_6212,c_6341,c_8287])).

tff(c_8296,plain,
    ( r1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8'))
    | ~ l1_orders_2('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_8293])).

tff(c_8298,plain,(
    r1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_8296])).

tff(c_8300,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7447,c_8298])).

tff(c_8301,plain,(
    k1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) != k1_funct_1('#skF_6',k1_yellow_0('#skF_1','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_7425])).

tff(c_8302,plain,(
    r1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_7425])).

tff(c_8304,plain,(
    ! [B_69] :
      ( k1_yellow_0(B_69,k9_relat_1('#skF_6','#skF_8')) = k1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8'))
      | g1_orders_2(u1_struct_0(B_69),u1_orders_2(B_69)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(B_69)
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8302,c_44])).

tff(c_8410,plain,(
    ! [B_1134] :
      ( k1_yellow_0(B_1134,k9_relat_1('#skF_6','#skF_8')) = k1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8'))
      | g1_orders_2(u1_struct_0(B_1134),u1_orders_2(B_1134)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(B_1134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_8304])).

tff(c_8419,plain,
    ( k1_yellow_0('#skF_2',k9_relat_1('#skF_6','#skF_8')) = k1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8'))
    | g1_orders_2(u1_struct_0('#skF_2'),u1_orders_2('#skF_4')) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
    | ~ l1_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6341,c_8410])).

tff(c_8428,plain,(
    k1_yellow_0('#skF_2',k9_relat_1('#skF_6','#skF_8')) = k1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_6212,c_8419])).

tff(c_6498,plain,(
    ! [A_949,B_950,C_951,D_952] :
      ( k3_funct_2(A_949,B_950,C_951,D_952) = k1_funct_1(C_951,D_952)
      | ~ m1_subset_1(D_952,A_949)
      | ~ m1_subset_1(C_951,k1_zfmisc_1(k2_zfmisc_1(A_949,B_950)))
      | ~ v1_funct_2(C_951,A_949,B_950)
      | ~ v1_funct_1(C_951)
      | v1_xboole_0(A_949) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_8313,plain,(
    ! [A_1127,B_1128,C_1129,B_1130] :
      ( k3_funct_2(u1_struct_0(A_1127),B_1128,C_1129,k1_yellow_0(A_1127,B_1130)) = k1_funct_1(C_1129,k1_yellow_0(A_1127,B_1130))
      | ~ m1_subset_1(C_1129,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1127),B_1128)))
      | ~ v1_funct_2(C_1129,u1_struct_0(A_1127),B_1128)
      | ~ v1_funct_1(C_1129)
      | v1_xboole_0(u1_struct_0(A_1127))
      | ~ l1_orders_2(A_1127) ) ),
    inference(resolution,[status(thm)],[c_18,c_6498])).

tff(c_8317,plain,(
    ! [B_1130] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_1',B_1130)) = k1_funct_1('#skF_6',k1_yellow_0('#skF_1',B_1130))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6445,c_8313])).

tff(c_8332,plain,(
    ! [B_1130] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_1',B_1130)) = k1_funct_1('#skF_6',k1_yellow_0('#skF_1',B_1130))
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_60,c_6446,c_8317])).

tff(c_8333,plain,(
    ! [B_1130] : k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_1',B_1130)) = k1_funct_1('#skF_6',k1_yellow_0('#skF_1',B_1130)) ),
    inference(negUnitSimplification,[status(thm)],[c_6495,c_8332])).

tff(c_7158,plain,(
    ! [A_1012,B_1013,C_1014,D_1015] :
      ( k3_funct_2(u1_struct_0(A_1012),u1_struct_0(B_1013),C_1014,k1_yellow_0(A_1012,D_1015)) = k1_yellow_0(B_1013,k7_relset_1(u1_struct_0(A_1012),u1_struct_0(B_1013),C_1014,D_1015))
      | ~ r1_yellow_0(A_1012,D_1015)
      | ~ r4_waybel_0(A_1012,B_1013,C_1014,D_1015)
      | ~ m1_subset_1(D_1015,k1_zfmisc_1(u1_struct_0(A_1012)))
      | ~ m1_subset_1(C_1014,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1012),u1_struct_0(B_1013))))
      | ~ v1_funct_2(C_1014,u1_struct_0(A_1012),u1_struct_0(B_1013))
      | ~ v1_funct_1(C_1014)
      | ~ l1_orders_2(B_1013)
      | v2_struct_0(B_1013)
      | ~ l1_orders_2(A_1012)
      | v2_struct_0(A_1012) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_7172,plain,(
    ! [A_1012,C_1014,D_1015] :
      ( k3_funct_2(u1_struct_0(A_1012),u1_struct_0('#skF_2'),C_1014,k1_yellow_0(A_1012,D_1015)) = k1_yellow_0('#skF_2',k7_relset_1(u1_struct_0(A_1012),u1_struct_0('#skF_2'),C_1014,D_1015))
      | ~ r1_yellow_0(A_1012,D_1015)
      | ~ r4_waybel_0(A_1012,'#skF_2',C_1014,D_1015)
      | ~ m1_subset_1(D_1015,k1_zfmisc_1(u1_struct_0(A_1012)))
      | ~ m1_subset_1(C_1014,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1012),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_1014,u1_struct_0(A_1012),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_1014)
      | ~ l1_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_orders_2(A_1012)
      | v2_struct_0(A_1012) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6212,c_7158])).

tff(c_7197,plain,(
    ! [A_1012,C_1014,D_1015] :
      ( k3_funct_2(u1_struct_0(A_1012),u1_struct_0('#skF_4'),C_1014,k1_yellow_0(A_1012,D_1015)) = k1_yellow_0('#skF_2',k7_relset_1(u1_struct_0(A_1012),u1_struct_0('#skF_4'),C_1014,D_1015))
      | ~ r1_yellow_0(A_1012,D_1015)
      | ~ r4_waybel_0(A_1012,'#skF_2',C_1014,D_1015)
      | ~ m1_subset_1(D_1015,k1_zfmisc_1(u1_struct_0(A_1012)))
      | ~ m1_subset_1(C_1014,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1012),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_1014,u1_struct_0(A_1012),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_1014)
      | v2_struct_0('#skF_2')
      | ~ l1_orders_2(A_1012)
      | v2_struct_0(A_1012) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_6212,c_6212,c_6212,c_7172])).

tff(c_10083,plain,(
    ! [A_1288,C_1289,D_1290] :
      ( k3_funct_2(u1_struct_0(A_1288),u1_struct_0('#skF_4'),C_1289,k1_yellow_0(A_1288,D_1290)) = k1_yellow_0('#skF_2',k7_relset_1(u1_struct_0(A_1288),u1_struct_0('#skF_4'),C_1289,D_1290))
      | ~ r1_yellow_0(A_1288,D_1290)
      | ~ r4_waybel_0(A_1288,'#skF_2',C_1289,D_1290)
      | ~ m1_subset_1(D_1290,k1_zfmisc_1(u1_struct_0(A_1288)))
      | ~ m1_subset_1(C_1289,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1288),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_1289,u1_struct_0(A_1288),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_1289)
      | ~ l1_orders_2(A_1288)
      | v2_struct_0(A_1288) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_7197])).

tff(c_10085,plain,(
    ! [D_1290] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_1',D_1290)) = k1_yellow_0('#skF_2',k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',D_1290))
      | ~ r1_yellow_0('#skF_1',D_1290)
      | ~ r4_waybel_0('#skF_1','#skF_2','#skF_6',D_1290)
      | ~ m1_subset_1(D_1290,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6445,c_10083])).

tff(c_10097,plain,(
    ! [D_1290] :
      ( k1_yellow_0('#skF_2',k9_relat_1('#skF_6',D_1290)) = k1_funct_1('#skF_6',k1_yellow_0('#skF_1',D_1290))
      | ~ r1_yellow_0('#skF_1',D_1290)
      | ~ r4_waybel_0('#skF_1','#skF_2','#skF_6',D_1290)
      | ~ m1_subset_1(D_1290,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_60,c_6446,c_8333,c_6443,c_10085])).

tff(c_10113,plain,(
    ! [D_1291] :
      ( k1_yellow_0('#skF_2',k9_relat_1('#skF_6',D_1291)) = k1_funct_1('#skF_6',k1_yellow_0('#skF_1',D_1291))
      | ~ r1_yellow_0('#skF_1',D_1291)
      | ~ r4_waybel_0('#skF_1','#skF_2','#skF_6',D_1291)
      | ~ m1_subset_1(D_1291,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_10097])).

tff(c_10116,plain,
    ( k1_yellow_0('#skF_2',k9_relat_1('#skF_6','#skF_8')) = k1_funct_1('#skF_6',k1_yellow_0('#skF_1','#skF_8'))
    | ~ r1_yellow_0('#skF_1','#skF_8')
    | ~ r4_waybel_0('#skF_1','#skF_2','#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_98,c_10113])).

tff(c_10119,plain,(
    k1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) = k1_funct_1('#skF_6',k1_yellow_0('#skF_1','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6721,c_6779,c_8428,c_10116])).

tff(c_10121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8301,c_10119])).

tff(c_10122,plain,(
    r1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_6979])).

tff(c_10832,plain,(
    ! [A_1341,B_1342,C_1343,B_1344] :
      ( k3_funct_2(u1_struct_0(A_1341),B_1342,C_1343,k1_yellow_0(A_1341,B_1344)) = k1_funct_1(C_1343,k1_yellow_0(A_1341,B_1344))
      | ~ m1_subset_1(C_1343,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1341),B_1342)))
      | ~ v1_funct_2(C_1343,u1_struct_0(A_1341),B_1342)
      | ~ v1_funct_1(C_1343)
      | v1_xboole_0(u1_struct_0(A_1341))
      | ~ l1_orders_2(A_1341) ) ),
    inference(resolution,[status(thm)],[c_18,c_6498])).

tff(c_10836,plain,(
    ! [B_1344] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_1',B_1344)) = k1_funct_1('#skF_6',k1_yellow_0('#skF_1',B_1344))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6445,c_10832])).

tff(c_10851,plain,(
    ! [B_1344] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_1',B_1344)) = k1_funct_1('#skF_6',k1_yellow_0('#skF_1',B_1344))
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_60,c_6446,c_10836])).

tff(c_10852,plain,(
    ! [B_1344] : k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_1',B_1344)) = k1_funct_1('#skF_6',k1_yellow_0('#skF_1',B_1344)) ),
    inference(negUnitSimplification,[status(thm)],[c_6495,c_10851])).

tff(c_10123,plain,(
    r4_waybel_0('#skF_1','#skF_4','#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_6979])).

tff(c_10460,plain,(
    ! [B_1310,C_1311,B_1312] :
      ( k3_funct_2(u1_struct_0('#skF_1'),B_1310,C_1311,k1_yellow_0('#skF_3',B_1312)) = k1_funct_1(C_1311,k1_yellow_0('#skF_3',B_1312))
      | ~ m1_subset_1(C_1311,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),B_1310)))
      | ~ v1_funct_2(C_1311,u1_struct_0('#skF_1'),B_1310)
      | ~ v1_funct_1(C_1311) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6495,c_6534])).

tff(c_10464,plain,(
    ! [B_1312] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_3',B_1312)) = k1_funct_1('#skF_6',k1_yellow_0('#skF_3',B_1312))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_6445,c_10460])).

tff(c_10475,plain,(
    ! [B_1313] : k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_3',B_1313)) = k1_funct_1('#skF_6',k1_yellow_0('#skF_3',B_1313)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6446,c_10464])).

tff(c_10484,plain,(
    k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_1','#skF_8')) = k1_funct_1('#skF_6',k1_yellow_0('#skF_3','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6849,c_10475])).

tff(c_10487,plain,(
    k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_1','#skF_8')) = k1_funct_1('#skF_6',k1_yellow_0('#skF_1','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6849,c_10484])).

tff(c_10266,plain,(
    ! [A_1299,B_1300,C_1301,D_1302] :
      ( k3_funct_2(u1_struct_0(A_1299),u1_struct_0(B_1300),C_1301,k1_yellow_0(A_1299,D_1302)) = k1_yellow_0(B_1300,k7_relset_1(u1_struct_0(A_1299),u1_struct_0(B_1300),C_1301,D_1302))
      | ~ r1_yellow_0(A_1299,D_1302)
      | ~ r4_waybel_0(A_1299,B_1300,C_1301,D_1302)
      | ~ m1_subset_1(D_1302,k1_zfmisc_1(u1_struct_0(A_1299)))
      | ~ m1_subset_1(C_1301,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1299),u1_struct_0(B_1300))))
      | ~ v1_funct_2(C_1301,u1_struct_0(A_1299),u1_struct_0(B_1300))
      | ~ v1_funct_1(C_1301)
      | ~ l1_orders_2(B_1300)
      | v2_struct_0(B_1300)
      | ~ l1_orders_2(A_1299)
      | v2_struct_0(A_1299) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_10270,plain,(
    ! [D_1302] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_1',D_1302)) = k1_yellow_0('#skF_4',k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',D_1302))
      | ~ r1_yellow_0('#skF_1',D_1302)
      | ~ r4_waybel_0('#skF_1','#skF_4','#skF_6',D_1302)
      | ~ m1_subset_1(D_1302,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6445,c_10266])).

tff(c_10289,plain,(
    ! [D_1302] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_1',D_1302)) = k1_yellow_0('#skF_4',k9_relat_1('#skF_6',D_1302))
      | ~ r1_yellow_0('#skF_1',D_1302)
      | ~ r4_waybel_0('#skF_1','#skF_4','#skF_6',D_1302)
      | ~ m1_subset_1(D_1302,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_72,c_60,c_6446,c_6443,c_10270])).

tff(c_10290,plain,(
    ! [D_1302] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_1',D_1302)) = k1_yellow_0('#skF_4',k9_relat_1('#skF_6',D_1302))
      | ~ r1_yellow_0('#skF_1',D_1302)
      | ~ r4_waybel_0('#skF_1','#skF_4','#skF_6',D_1302)
      | ~ m1_subset_1(D_1302,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_74,c_10289])).

tff(c_10534,plain,
    ( k1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) = k1_funct_1('#skF_6',k1_yellow_0('#skF_1','#skF_8'))
    | ~ r1_yellow_0('#skF_1','#skF_8')
    | ~ r4_waybel_0('#skF_1','#skF_4','#skF_6','#skF_8')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_10487,c_10290])).

tff(c_10544,plain,(
    k1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) = k1_funct_1('#skF_6',k1_yellow_0('#skF_1','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_10123,c_6779,c_10534])).

tff(c_10394,plain,(
    ! [A_1306,B_1307,C_1308,D_1309] :
      ( k3_funct_2(u1_struct_0(A_1306),u1_struct_0(B_1307),C_1308,k1_yellow_0(A_1306,D_1309)) != k1_yellow_0(B_1307,k7_relset_1(u1_struct_0(A_1306),u1_struct_0(B_1307),C_1308,D_1309))
      | ~ r1_yellow_0(B_1307,k7_relset_1(u1_struct_0(A_1306),u1_struct_0(B_1307),C_1308,D_1309))
      | r4_waybel_0(A_1306,B_1307,C_1308,D_1309)
      | ~ m1_subset_1(D_1309,k1_zfmisc_1(u1_struct_0(A_1306)))
      | ~ m1_subset_1(C_1308,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1306),u1_struct_0(B_1307))))
      | ~ v1_funct_2(C_1308,u1_struct_0(A_1306),u1_struct_0(B_1307))
      | ~ v1_funct_1(C_1308)
      | ~ l1_orders_2(B_1307)
      | v2_struct_0(B_1307)
      | ~ l1_orders_2(A_1306)
      | v2_struct_0(A_1306) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_10400,plain,(
    ! [B_1307,C_1308] :
      ( k3_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_1307),C_1308,k1_yellow_0('#skF_1','#skF_8')) != k1_yellow_0(B_1307,k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0(B_1307),C_1308,'#skF_8'))
      | ~ r1_yellow_0(B_1307,k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0(B_1307),C_1308,'#skF_8'))
      | r4_waybel_0('#skF_3',B_1307,C_1308,'#skF_8')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(C_1308,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_1307))))
      | ~ v1_funct_2(C_1308,u1_struct_0('#skF_3'),u1_struct_0(B_1307))
      | ~ v1_funct_1(C_1308)
      | ~ l1_orders_2(B_1307)
      | v2_struct_0(B_1307)
      | ~ l1_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6849,c_10394])).

tff(c_10420,plain,(
    ! [B_1307,C_1308] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0(B_1307),C_1308,k1_yellow_0('#skF_1','#skF_8')) != k1_yellow_0(B_1307,k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_1307),C_1308,'#skF_8'))
      | ~ r1_yellow_0(B_1307,k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_1307),C_1308,'#skF_8'))
      | r4_waybel_0('#skF_3',B_1307,C_1308,'#skF_8')
      | ~ m1_subset_1(C_1308,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1307))))
      | ~ v1_funct_2(C_1308,u1_struct_0('#skF_1'),u1_struct_0(B_1307))
      | ~ v1_funct_1(C_1308)
      | ~ l1_orders_2(B_1307)
      | v2_struct_0(B_1307)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_6421,c_6421,c_98,c_6421,c_6421,c_6421,c_6421,c_10400])).

tff(c_12507,plain,(
    ! [B_1499,C_1500] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0(B_1499),C_1500,k1_yellow_0('#skF_1','#skF_8')) != k1_yellow_0(B_1499,k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_1499),C_1500,'#skF_8'))
      | ~ r1_yellow_0(B_1499,k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_1499),C_1500,'#skF_8'))
      | r4_waybel_0('#skF_3',B_1499,C_1500,'#skF_8')
      | ~ m1_subset_1(C_1500,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1499))))
      | ~ v1_funct_2(C_1500,u1_struct_0('#skF_1'),u1_struct_0(B_1499))
      | ~ v1_funct_1(C_1500)
      | ~ l1_orders_2(B_1499)
      | v2_struct_0(B_1499) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_10420])).

tff(c_12516,plain,
    ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_1','#skF_8')) != k1_yellow_0('#skF_4',k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6','#skF_8'))
    | ~ r1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8'))
    | r4_waybel_0('#skF_3','#skF_4','#skF_6','#skF_8')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6443,c_12507])).

tff(c_12532,plain,
    ( r4_waybel_0('#skF_3','#skF_4','#skF_6','#skF_8')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_60,c_6446,c_6445,c_10122,c_10852,c_10544,c_6443,c_12516])).

tff(c_12534,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_6138,c_12532])).

tff(c_12536,plain,(
    ~ r1_yellow_0('#skF_1','#skF_8') ),
    inference(splitRight,[status(thm)],[c_6699])).

tff(c_6685,plain,(
    ! [D_968,B_969,C_970] :
      ( r1_yellow_0('#skF_3',D_968)
      | r4_waybel_0('#skF_3',B_969,C_970,D_968)
      | ~ m1_subset_1(D_968,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(C_970,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_969))))
      | ~ v1_funct_2(C_970,u1_struct_0('#skF_3'),u1_struct_0(B_969))
      | ~ v1_funct_1(C_970)
      | ~ l1_orders_2(B_969)
      | v2_struct_0(B_969)
      | ~ l1_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6421,c_6683])).

tff(c_6691,plain,(
    ! [D_968,B_969,C_970] :
      ( r1_yellow_0('#skF_3',D_968)
      | r4_waybel_0('#skF_3',B_969,C_970,D_968)
      | ~ m1_subset_1(D_968,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(C_970,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_969))))
      | ~ v1_funct_2(C_970,u1_struct_0('#skF_1'),u1_struct_0(B_969))
      | ~ v1_funct_1(C_970)
      | ~ l1_orders_2(B_969)
      | v2_struct_0(B_969)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_6421,c_6421,c_6685])).

tff(c_13178,plain,(
    ! [D_1562,B_1563,C_1564] :
      ( r1_yellow_0('#skF_3',D_1562)
      | r4_waybel_0('#skF_3',B_1563,C_1564,D_1562)
      | ~ m1_subset_1(D_1562,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(C_1564,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1563))))
      | ~ v1_funct_2(C_1564,u1_struct_0('#skF_1'),u1_struct_0(B_1563))
      | ~ v1_funct_1(C_1564)
      | ~ l1_orders_2(B_1563)
      | v2_struct_0(B_1563) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_6691])).

tff(c_13181,plain,(
    ! [B_1563,C_1564] :
      ( r1_yellow_0('#skF_3','#skF_8')
      | r4_waybel_0('#skF_3',B_1563,C_1564,'#skF_8')
      | ~ m1_subset_1(C_1564,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1563))))
      | ~ v1_funct_2(C_1564,u1_struct_0('#skF_1'),u1_struct_0(B_1563))
      | ~ v1_funct_1(C_1564)
      | ~ l1_orders_2(B_1563)
      | v2_struct_0(B_1563) ) ),
    inference(resolution,[status(thm)],[c_98,c_13178])).

tff(c_13182,plain,(
    r1_yellow_0('#skF_3','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_13181])).

tff(c_13186,plain,(
    ! [B_62] :
      ( r1_yellow_0(B_62,'#skF_8')
      | g1_orders_2(u1_struct_0(B_62),u1_orders_2(B_62)) != g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_3'))
      | ~ l1_orders_2(B_62)
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_13182,c_40])).

tff(c_13192,plain,(
    ! [B_62] :
      ( r1_yellow_0(B_62,'#skF_8')
      | g1_orders_2(u1_struct_0(B_62),u1_orders_2(B_62)) != g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
      | ~ l1_orders_2(B_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_6421,c_6585,c_13186])).

tff(c_13195,plain,
    ( r1_yellow_0('#skF_1','#skF_8')
    | ~ l1_orders_2('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_13192])).

tff(c_13197,plain,(
    r1_yellow_0('#skF_1','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_13195])).

tff(c_13199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12536,c_13197])).

tff(c_13246,plain,(
    ! [B_1570,C_1571] :
      ( r4_waybel_0('#skF_3',B_1570,C_1571,'#skF_8')
      | ~ m1_subset_1(C_1571,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1570))))
      | ~ v1_funct_2(C_1571,u1_struct_0('#skF_1'),u1_struct_0(B_1570))
      | ~ v1_funct_1(C_1571)
      | ~ l1_orders_2(B_1570)
      | v2_struct_0(B_1570) ) ),
    inference(splitRight,[status(thm)],[c_13181])).

tff(c_13252,plain,
    ( r4_waybel_0('#skF_3','#skF_4','#skF_6','#skF_8')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_6445,c_13246])).

tff(c_13269,plain,
    ( r4_waybel_0('#skF_3','#skF_4','#skF_6','#skF_8')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_60,c_6446,c_13252])).

tff(c_13271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_6138,c_13269])).

tff(c_13273,plain,(
    r3_waybel_0('#skF_3','#skF_4','#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_88,plain,
    ( ~ r4_waybel_0('#skF_3','#skF_4','#skF_6','#skF_8')
    | ~ r3_waybel_0('#skF_3','#skF_4','#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_13274,plain,(
    ~ r3_waybel_0('#skF_3','#skF_4','#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_13276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13273,c_13274])).

tff(c_13277,plain,(
    ~ r4_waybel_0('#skF_3','#skF_4','#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_13318,plain,(
    ! [D_1579,B_1580,C_1581,A_1582] :
      ( D_1579 = B_1580
      | g1_orders_2(C_1581,D_1579) != g1_orders_2(A_1582,B_1580)
      | ~ m1_subset_1(B_1580,k1_zfmisc_1(k2_zfmisc_1(A_1582,A_1582))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_13350,plain,(
    ! [B_1592,A_1593] :
      ( u1_orders_2('#skF_3') = B_1592
      | g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) != g1_orders_2(A_1593,B_1592)
      | ~ m1_subset_1(B_1592,k1_zfmisc_1(k2_zfmisc_1(A_1593,A_1593))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_13318])).

tff(c_13354,plain,(
    ! [A_36] :
      ( u1_orders_2(A_36) = u1_orders_2('#skF_3')
      | g1_orders_2(u1_struct_0(A_36),u1_orders_2(A_36)) != g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
      | ~ l1_orders_2(A_36) ) ),
    inference(resolution,[status(thm)],[c_24,c_13350])).

tff(c_13357,plain,
    ( u1_orders_2('#skF_3') = u1_orders_2('#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_13354])).

tff(c_13359,plain,(
    u1_orders_2('#skF_3') = u1_orders_2('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_13357])).

tff(c_13387,plain,
    ( m1_subset_1(u1_orders_2('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))))
    | ~ l1_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13359,c_24])).

tff(c_13393,plain,(
    m1_subset_1(u1_orders_2('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_13387])).

tff(c_13380,plain,(
    g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_1')) = g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13359,c_70])).

tff(c_30,plain,(
    ! [C_42,A_38,D_43,B_39] :
      ( C_42 = A_38
      | g1_orders_2(C_42,D_43) != g1_orders_2(A_38,B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k2_zfmisc_1(A_38,A_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_13406,plain,(
    ! [C_42,D_43] :
      ( u1_struct_0('#skF_3') = C_42
      | g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) != g1_orders_2(C_42,D_43)
      | ~ m1_subset_1(u1_orders_2('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13380,c_30])).

tff(c_13414,plain,(
    ! [C_42,D_43] :
      ( u1_struct_0('#skF_3') = C_42
      | g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) != g1_orders_2(C_42,D_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13393,c_13406])).

tff(c_13420,plain,(
    u1_struct_0('#skF_3') = u1_struct_0('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_13414])).

tff(c_13436,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13420,c_58])).

tff(c_13435,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13420,c_56])).

tff(c_13870,plain,(
    ! [A_1642,D_1643,B_1644,C_1645] :
      ( r1_yellow_0(A_1642,D_1643)
      | r4_waybel_0(A_1642,B_1644,C_1645,D_1643)
      | ~ m1_subset_1(D_1643,k1_zfmisc_1(u1_struct_0(A_1642)))
      | ~ m1_subset_1(C_1645,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1642),u1_struct_0(B_1644))))
      | ~ v1_funct_2(C_1645,u1_struct_0(A_1642),u1_struct_0(B_1644))
      | ~ v1_funct_1(C_1645)
      | ~ l1_orders_2(B_1644)
      | v2_struct_0(B_1644)
      | ~ l1_orders_2(A_1642)
      | v2_struct_0(A_1642) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_13876,plain,(
    ! [B_1644,C_1645] :
      ( r1_yellow_0('#skF_1','#skF_8')
      | r4_waybel_0('#skF_1',B_1644,C_1645,'#skF_8')
      | ~ m1_subset_1(C_1645,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1644))))
      | ~ v1_funct_2(C_1645,u1_struct_0('#skF_1'),u1_struct_0(B_1644))
      | ~ v1_funct_1(C_1645)
      | ~ l1_orders_2(B_1644)
      | v2_struct_0(B_1644)
      | ~ l1_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_98,c_13870])).

tff(c_13885,plain,(
    ! [B_1644,C_1645] :
      ( r1_yellow_0('#skF_1','#skF_8')
      | r4_waybel_0('#skF_1',B_1644,C_1645,'#skF_8')
      | ~ m1_subset_1(C_1645,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1644))))
      | ~ v1_funct_2(C_1645,u1_struct_0('#skF_1'),u1_struct_0(B_1644))
      | ~ v1_funct_1(C_1645)
      | ~ l1_orders_2(B_1644)
      | v2_struct_0(B_1644)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_13876])).

tff(c_13886,plain,(
    ! [B_1644,C_1645] :
      ( r1_yellow_0('#skF_1','#skF_8')
      | r4_waybel_0('#skF_1',B_1644,C_1645,'#skF_8')
      | ~ m1_subset_1(C_1645,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1644))))
      | ~ v1_funct_2(C_1645,u1_struct_0('#skF_1'),u1_struct_0(B_1644))
      | ~ v1_funct_1(C_1645)
      | ~ l1_orders_2(B_1644)
      | v2_struct_0(B_1644) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_13885])).

tff(c_20963,plain,(
    r1_yellow_0('#skF_1','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_13886])).

tff(c_13286,plain,(
    ! [A_1573,B_1574,C_1575,D_1576] :
      ( k7_relset_1(A_1573,B_1574,C_1575,D_1576) = k9_relat_1(C_1575,D_1576)
      | ~ m1_subset_1(C_1575,k1_zfmisc_1(k2_zfmisc_1(A_1573,B_1574))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_13294,plain,(
    ! [D_1576] : k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_6',D_1576) = k9_relat_1('#skF_6',D_1576) ),
    inference(resolution,[status(thm)],[c_56,c_13286])).

tff(c_13433,plain,(
    ! [D_1576] : k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',D_1576) = k9_relat_1('#skF_6',D_1576) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13420,c_13294])).

tff(c_21001,plain,(
    ! [B_2284,A_2285,C_2286,D_2287] :
      ( r1_yellow_0(B_2284,k7_relset_1(u1_struct_0(A_2285),u1_struct_0(B_2284),C_2286,D_2287))
      | ~ r1_yellow_0(A_2285,D_2287)
      | ~ r4_waybel_0(A_2285,B_2284,C_2286,D_2287)
      | ~ m1_subset_1(D_2287,k1_zfmisc_1(u1_struct_0(A_2285)))
      | ~ m1_subset_1(C_2286,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2285),u1_struct_0(B_2284))))
      | ~ v1_funct_2(C_2286,u1_struct_0(A_2285),u1_struct_0(B_2284))
      | ~ v1_funct_1(C_2286)
      | ~ l1_orders_2(B_2284)
      | v2_struct_0(B_2284)
      | ~ l1_orders_2(A_2285)
      | v2_struct_0(A_2285) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_21011,plain,(
    ! [D_2287] :
      ( r1_yellow_0('#skF_4',k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',D_2287))
      | ~ r1_yellow_0('#skF_1',D_2287)
      | ~ r4_waybel_0('#skF_1','#skF_4','#skF_6',D_2287)
      | ~ m1_subset_1(D_2287,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_13435,c_21001])).

tff(c_21034,plain,(
    ! [D_2287] :
      ( r1_yellow_0('#skF_4',k9_relat_1('#skF_6',D_2287))
      | ~ r1_yellow_0('#skF_1',D_2287)
      | ~ r4_waybel_0('#skF_1','#skF_4','#skF_6',D_2287)
      | ~ m1_subset_1(D_2287,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_72,c_60,c_13436,c_13433,c_21011])).

tff(c_21081,plain,(
    ! [D_2289] :
      ( r1_yellow_0('#skF_4',k9_relat_1('#skF_6',D_2289))
      | ~ r1_yellow_0('#skF_1',D_2289)
      | ~ r4_waybel_0('#skF_1','#skF_4','#skF_6',D_2289)
      | ~ m1_subset_1(D_2289,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_74,c_21034])).

tff(c_21084,plain,
    ( r1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8'))
    | ~ r1_yellow_0('#skF_1','#skF_8')
    | ~ r4_waybel_0('#skF_1','#skF_4','#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_98,c_21081])).

tff(c_21087,plain,
    ( r1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8'))
    | ~ r4_waybel_0('#skF_1','#skF_4','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20963,c_21084])).

tff(c_21106,plain,(
    ~ r4_waybel_0('#skF_1','#skF_4','#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_21087])).

tff(c_20965,plain,(
    ! [B_69] :
      ( k1_yellow_0(B_69,'#skF_8') = k1_yellow_0('#skF_1','#skF_8')
      | g1_orders_2(u1_struct_0(B_69),u1_orders_2(B_69)) != g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
      | ~ l1_orders_2(B_69)
      | ~ l1_orders_2('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20963,c_44])).

tff(c_21060,plain,(
    ! [B_2288] :
      ( k1_yellow_0(B_2288,'#skF_8') = k1_yellow_0('#skF_1','#skF_8')
      | g1_orders_2(u1_struct_0(B_2288),u1_orders_2(B_2288)) != g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
      | ~ l1_orders_2(B_2288) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_20965])).

tff(c_21072,plain,
    ( k1_yellow_0('#skF_3','#skF_8') = k1_yellow_0('#skF_1','#skF_8')
    | g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_1')) != g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
    | ~ l1_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13359,c_21060])).

tff(c_21080,plain,(
    k1_yellow_0('#skF_3','#skF_8') = k1_yellow_0('#skF_1','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_13420,c_21072])).

tff(c_13460,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13420,c_26])).

tff(c_13475,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_13460])).

tff(c_13478,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_13475])).

tff(c_13481,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_13478])).

tff(c_13485,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_13481])).

tff(c_13486,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_13475])).

tff(c_13457,plain,(
    ! [B_32] :
      ( m1_subset_1(k1_yellow_0('#skF_3',B_32),u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13420,c_18])).

tff(c_13474,plain,(
    ! [B_32] : m1_subset_1(k1_yellow_0('#skF_3',B_32),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_13457])).

tff(c_13561,plain,(
    ! [A_1616,B_1617,C_1618,D_1619] :
      ( k3_funct_2(A_1616,B_1617,C_1618,D_1619) = k1_funct_1(C_1618,D_1619)
      | ~ m1_subset_1(D_1619,A_1616)
      | ~ m1_subset_1(C_1618,k1_zfmisc_1(k2_zfmisc_1(A_1616,B_1617)))
      | ~ v1_funct_2(C_1618,A_1616,B_1617)
      | ~ v1_funct_1(C_1618)
      | v1_xboole_0(A_1616) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_13567,plain,(
    ! [B_1617,C_1618,B_32] :
      ( k3_funct_2(u1_struct_0('#skF_1'),B_1617,C_1618,k1_yellow_0('#skF_3',B_32)) = k1_funct_1(C_1618,k1_yellow_0('#skF_3',B_32))
      | ~ m1_subset_1(C_1618,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),B_1617)))
      | ~ v1_funct_2(C_1618,u1_struct_0('#skF_1'),B_1617)
      | ~ v1_funct_1(C_1618)
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_13474,c_13561])).

tff(c_21234,plain,(
    ! [B_2306,C_2307,B_2308] :
      ( k3_funct_2(u1_struct_0('#skF_1'),B_2306,C_2307,k1_yellow_0('#skF_3',B_2308)) = k1_funct_1(C_2307,k1_yellow_0('#skF_3',B_2308))
      | ~ m1_subset_1(C_2307,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),B_2306)))
      | ~ v1_funct_2(C_2307,u1_struct_0('#skF_1'),B_2306)
      | ~ v1_funct_1(C_2307) ) ),
    inference(negUnitSimplification,[status(thm)],[c_13486,c_13567])).

tff(c_21238,plain,(
    ! [B_2308] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_3',B_2308)) = k1_funct_1('#skF_6',k1_yellow_0('#skF_3',B_2308))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_13435,c_21234])).

tff(c_21285,plain,(
    ! [B_2311] : k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_3',B_2311)) = k1_funct_1('#skF_6',k1_yellow_0('#skF_3',B_2311)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_13436,c_21238])).

tff(c_21294,plain,(
    k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_1','#skF_8')) = k1_funct_1('#skF_6',k1_yellow_0('#skF_3','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_21080,c_21285])).

tff(c_21297,plain,(
    k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_1','#skF_8')) = k1_funct_1('#skF_6',k1_yellow_0('#skF_1','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21080,c_21294])).

tff(c_21410,plain,(
    ! [A_2324,B_2325,C_2326,D_2327] :
      ( k3_funct_2(u1_struct_0(A_2324),u1_struct_0(B_2325),C_2326,k1_yellow_0(A_2324,D_2327)) != k1_yellow_0(B_2325,k7_relset_1(u1_struct_0(A_2324),u1_struct_0(B_2325),C_2326,D_2327))
      | ~ r1_yellow_0(B_2325,k7_relset_1(u1_struct_0(A_2324),u1_struct_0(B_2325),C_2326,D_2327))
      | r4_waybel_0(A_2324,B_2325,C_2326,D_2327)
      | ~ m1_subset_1(D_2327,k1_zfmisc_1(u1_struct_0(A_2324)))
      | ~ m1_subset_1(C_2326,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2324),u1_struct_0(B_2325))))
      | ~ v1_funct_2(C_2326,u1_struct_0(A_2324),u1_struct_0(B_2325))
      | ~ v1_funct_1(C_2326)
      | ~ l1_orders_2(B_2325)
      | v2_struct_0(B_2325)
      | ~ l1_orders_2(A_2324)
      | v2_struct_0(A_2324) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_21412,plain,
    ( k1_yellow_0('#skF_4',k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6','#skF_8')) != k1_funct_1('#skF_6',k1_yellow_0('#skF_1','#skF_8'))
    | ~ r1_yellow_0('#skF_4',k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6','#skF_8'))
    | r4_waybel_0('#skF_1','#skF_4','#skF_6','#skF_8')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_orders_2('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_21297,c_21410])).

tff(c_21430,plain,
    ( k1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) != k1_funct_1('#skF_6',k1_yellow_0('#skF_1','#skF_8'))
    | ~ r1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8'))
    | r4_waybel_0('#skF_1','#skF_4','#skF_6','#skF_8')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_72,c_60,c_13436,c_13435,c_98,c_13433,c_13433,c_21412])).

tff(c_21431,plain,
    ( k1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) != k1_funct_1('#skF_6',k1_yellow_0('#skF_1','#skF_8'))
    | ~ r1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_74,c_21106,c_21430])).

tff(c_21456,plain,(
    ~ r1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_21431])).

tff(c_13373,plain,(
    ! [B_1595,A_1596] :
      ( u1_orders_2('#skF_2') = B_1595
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(A_1596,B_1595)
      | ~ m1_subset_1(B_1595,k1_zfmisc_1(k2_zfmisc_1(A_1596,A_1596))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_13318])).

tff(c_13377,plain,(
    ! [A_36] :
      ( u1_orders_2(A_36) = u1_orders_2('#skF_2')
      | g1_orders_2(u1_struct_0(A_36),u1_orders_2(A_36)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(A_36) ) ),
    inference(resolution,[status(thm)],[c_24,c_13373])).

tff(c_13595,plain,
    ( u1_orders_2('#skF_2') = u1_orders_2('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_13377])).

tff(c_13597,plain,(
    u1_orders_2('#skF_2') = u1_orders_2('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_13595])).

tff(c_13331,plain,(
    ! [C_1583,A_1584,D_1585,B_1586] :
      ( C_1583 = A_1584
      | g1_orders_2(C_1583,D_1585) != g1_orders_2(A_1584,B_1586)
      | ~ m1_subset_1(B_1586,k1_zfmisc_1(k2_zfmisc_1(A_1584,A_1584))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_13712,plain,(
    ! [A_1628,B_1629] :
      ( u1_struct_0('#skF_2') = A_1628
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(A_1628,B_1629)
      | ~ m1_subset_1(B_1629,k1_zfmisc_1(k2_zfmisc_1(A_1628,A_1628))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_13331])).

tff(c_13727,plain,(
    ! [A_36] :
      ( u1_struct_0(A_36) = u1_struct_0('#skF_2')
      | g1_orders_2(u1_struct_0(A_36),u1_orders_2(A_36)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(A_36) ) ),
    inference(resolution,[status(thm)],[c_24,c_13712])).

tff(c_13730,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_13727])).

tff(c_13732,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_13730])).

tff(c_13793,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_13732,c_26])).

tff(c_13810,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_13793])).

tff(c_13813,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_13810])).

tff(c_13816,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_13813])).

tff(c_13820,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_13816])).

tff(c_13821,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_13810])).

tff(c_13768,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13732,c_64])).

tff(c_13767,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13732,c_62])).

tff(c_13434,plain,(
    r1_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13420,c_54])).

tff(c_13765,plain,(
    r1_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13732,c_13434])).

tff(c_38,plain,(
    ! [D_55,F_57,B_53,A_52,E_56,C_54] :
      ( F_57 = E_56
      | ~ r1_funct_2(A_52,B_53,C_54,D_55,E_56,F_57)
      | ~ m1_subset_1(F_57,k1_zfmisc_1(k2_zfmisc_1(C_54,D_55)))
      | ~ v1_funct_2(F_57,C_54,D_55)
      | ~ v1_funct_1(F_57)
      | ~ m1_subset_1(E_56,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | ~ v1_funct_2(E_56,A_52,B_53)
      | ~ v1_funct_1(E_56)
      | v1_xboole_0(D_55)
      | v1_xboole_0(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_13894,plain,
    ( '#skF_5' = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_13765,c_38])).

tff(c_13897,plain,
    ( '#skF_5' = '#skF_6'
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_13768,c_13767,c_60,c_13436,c_13435,c_13894])).

tff(c_13898,plain,(
    '#skF_5' = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_13821,c_13897])).

tff(c_13272,plain,(
    r4_waybel_0('#skF_1','#skF_2','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_13905,plain,(
    r4_waybel_0('#skF_1','#skF_2','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13898,c_13272])).

tff(c_21007,plain,(
    ! [A_2285,C_2286,D_2287] :
      ( r1_yellow_0('#skF_2',k7_relset_1(u1_struct_0(A_2285),u1_struct_0('#skF_2'),C_2286,D_2287))
      | ~ r1_yellow_0(A_2285,D_2287)
      | ~ r4_waybel_0(A_2285,'#skF_2',C_2286,D_2287)
      | ~ m1_subset_1(D_2287,k1_zfmisc_1(u1_struct_0(A_2285)))
      | ~ m1_subset_1(C_2286,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2285),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_2286,u1_struct_0(A_2285),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_2286)
      | ~ l1_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_orders_2(A_2285)
      | v2_struct_0(A_2285) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13732,c_21001])).

tff(c_21026,plain,(
    ! [A_2285,C_2286,D_2287] :
      ( r1_yellow_0('#skF_2',k7_relset_1(u1_struct_0(A_2285),u1_struct_0('#skF_4'),C_2286,D_2287))
      | ~ r1_yellow_0(A_2285,D_2287)
      | ~ r4_waybel_0(A_2285,'#skF_2',C_2286,D_2287)
      | ~ m1_subset_1(D_2287,k1_zfmisc_1(u1_struct_0(A_2285)))
      | ~ m1_subset_1(C_2286,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2285),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_2286,u1_struct_0(A_2285),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_2286)
      | v2_struct_0('#skF_2')
      | ~ l1_orders_2(A_2285)
      | v2_struct_0(A_2285) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_13732,c_13732,c_21007])).

tff(c_22000,plain,(
    ! [A_2383,C_2384,D_2385] :
      ( r1_yellow_0('#skF_2',k7_relset_1(u1_struct_0(A_2383),u1_struct_0('#skF_4'),C_2384,D_2385))
      | ~ r1_yellow_0(A_2383,D_2385)
      | ~ r4_waybel_0(A_2383,'#skF_2',C_2384,D_2385)
      | ~ m1_subset_1(D_2385,k1_zfmisc_1(u1_struct_0(A_2383)))
      | ~ m1_subset_1(C_2384,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2383),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_2384,u1_struct_0(A_2383),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_2384)
      | ~ l1_orders_2(A_2383)
      | v2_struct_0(A_2383) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_21026])).

tff(c_22006,plain,(
    ! [D_2385] :
      ( r1_yellow_0('#skF_2',k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',D_2385))
      | ~ r1_yellow_0('#skF_1',D_2385)
      | ~ r4_waybel_0('#skF_1','#skF_2','#skF_6',D_2385)
      | ~ m1_subset_1(D_2385,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_13435,c_22000])).

tff(c_22021,plain,(
    ! [D_2385] :
      ( r1_yellow_0('#skF_2',k9_relat_1('#skF_6',D_2385))
      | ~ r1_yellow_0('#skF_1',D_2385)
      | ~ r4_waybel_0('#skF_1','#skF_2','#skF_6',D_2385)
      | ~ m1_subset_1(D_2385,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_60,c_13436,c_13433,c_22006])).

tff(c_22030,plain,(
    ! [D_2386] :
      ( r1_yellow_0('#skF_2',k9_relat_1('#skF_6',D_2386))
      | ~ r1_yellow_0('#skF_1',D_2386)
      | ~ r4_waybel_0('#skF_1','#skF_2','#skF_6',D_2386)
      | ~ m1_subset_1(D_2386,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_22021])).

tff(c_22033,plain,
    ( r1_yellow_0('#skF_2',k9_relat_1('#skF_6','#skF_8'))
    | ~ r1_yellow_0('#skF_1','#skF_8')
    | ~ r4_waybel_0('#skF_1','#skF_2','#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_98,c_22030])).

tff(c_22036,plain,(
    r1_yellow_0('#skF_2',k9_relat_1('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13905,c_20963,c_22033])).

tff(c_22040,plain,(
    ! [B_62] :
      ( r1_yellow_0(B_62,k9_relat_1('#skF_6','#skF_8'))
      | g1_orders_2(u1_struct_0(B_62),u1_orders_2(B_62)) != g1_orders_2(u1_struct_0('#skF_2'),u1_orders_2('#skF_2'))
      | ~ l1_orders_2(B_62)
      | ~ l1_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22036,c_40])).

tff(c_22046,plain,(
    ! [B_62] :
      ( r1_yellow_0(B_62,k9_relat_1('#skF_6','#skF_8'))
      | g1_orders_2(u1_struct_0(B_62),u1_orders_2(B_62)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(B_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_13597,c_13732,c_22040])).

tff(c_22066,plain,
    ( r1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8'))
    | ~ l1_orders_2('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_22046])).

tff(c_22068,plain,(
    r1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_22066])).

tff(c_22070,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21456,c_22068])).

tff(c_22071,plain,(
    k1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) != k1_funct_1('#skF_6',k1_yellow_0('#skF_1','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_21431])).

tff(c_22072,plain,(
    r1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_21431])).

tff(c_22074,plain,(
    ! [B_69] :
      ( k1_yellow_0(B_69,k9_relat_1('#skF_6','#skF_8')) = k1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8'))
      | g1_orders_2(u1_struct_0(B_69),u1_orders_2(B_69)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(B_69)
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22072,c_44])).

tff(c_22126,plain,(
    ! [B_2391] :
      ( k1_yellow_0(B_2391,k9_relat_1('#skF_6','#skF_8')) = k1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8'))
      | g1_orders_2(u1_struct_0(B_2391),u1_orders_2(B_2391)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(B_2391) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_22074])).

tff(c_22129,plain,
    ( k1_yellow_0('#skF_2',k9_relat_1('#skF_6','#skF_8')) = k1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8'))
    | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_2')) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
    | ~ l1_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_13732,c_22126])).

tff(c_22140,plain,(
    k1_yellow_0('#skF_2',k9_relat_1('#skF_6','#skF_8')) = k1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_13597,c_22129])).

tff(c_22184,plain,(
    ! [A_2394,B_2395,C_2396,B_2397] :
      ( k3_funct_2(u1_struct_0(A_2394),B_2395,C_2396,k1_yellow_0(A_2394,B_2397)) = k1_funct_1(C_2396,k1_yellow_0(A_2394,B_2397))
      | ~ m1_subset_1(C_2396,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2394),B_2395)))
      | ~ v1_funct_2(C_2396,u1_struct_0(A_2394),B_2395)
      | ~ v1_funct_1(C_2396)
      | v1_xboole_0(u1_struct_0(A_2394))
      | ~ l1_orders_2(A_2394) ) ),
    inference(resolution,[status(thm)],[c_18,c_13561])).

tff(c_22192,plain,(
    ! [B_2397] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_1',B_2397)) = k1_funct_1('#skF_6',k1_yellow_0('#skF_1',B_2397))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_13435,c_22184])).

tff(c_22210,plain,(
    ! [B_2397] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_1',B_2397)) = k1_funct_1('#skF_6',k1_yellow_0('#skF_1',B_2397))
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_60,c_13436,c_22192])).

tff(c_22211,plain,(
    ! [B_2397] : k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_1',B_2397)) = k1_funct_1('#skF_6',k1_yellow_0('#skF_1',B_2397)) ),
    inference(negUnitSimplification,[status(thm)],[c_13486,c_22210])).

tff(c_21173,plain,(
    ! [A_2298,B_2299,C_2300,D_2301] :
      ( k3_funct_2(u1_struct_0(A_2298),u1_struct_0(B_2299),C_2300,k1_yellow_0(A_2298,D_2301)) = k1_yellow_0(B_2299,k7_relset_1(u1_struct_0(A_2298),u1_struct_0(B_2299),C_2300,D_2301))
      | ~ r1_yellow_0(A_2298,D_2301)
      | ~ r4_waybel_0(A_2298,B_2299,C_2300,D_2301)
      | ~ m1_subset_1(D_2301,k1_zfmisc_1(u1_struct_0(A_2298)))
      | ~ m1_subset_1(C_2300,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2298),u1_struct_0(B_2299))))
      | ~ v1_funct_2(C_2300,u1_struct_0(A_2298),u1_struct_0(B_2299))
      | ~ v1_funct_1(C_2300)
      | ~ l1_orders_2(B_2299)
      | v2_struct_0(B_2299)
      | ~ l1_orders_2(A_2298)
      | v2_struct_0(A_2298) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_21179,plain,(
    ! [A_2298,C_2300,D_2301] :
      ( k3_funct_2(u1_struct_0(A_2298),u1_struct_0('#skF_2'),C_2300,k1_yellow_0(A_2298,D_2301)) = k1_yellow_0('#skF_2',k7_relset_1(u1_struct_0(A_2298),u1_struct_0('#skF_2'),C_2300,D_2301))
      | ~ r1_yellow_0(A_2298,D_2301)
      | ~ r4_waybel_0(A_2298,'#skF_2',C_2300,D_2301)
      | ~ m1_subset_1(D_2301,k1_zfmisc_1(u1_struct_0(A_2298)))
      | ~ m1_subset_1(C_2300,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2298),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_2300,u1_struct_0(A_2298),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_2300)
      | ~ l1_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_orders_2(A_2298)
      | v2_struct_0(A_2298) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13732,c_21173])).

tff(c_21198,plain,(
    ! [A_2298,C_2300,D_2301] :
      ( k3_funct_2(u1_struct_0(A_2298),u1_struct_0('#skF_4'),C_2300,k1_yellow_0(A_2298,D_2301)) = k1_yellow_0('#skF_2',k7_relset_1(u1_struct_0(A_2298),u1_struct_0('#skF_4'),C_2300,D_2301))
      | ~ r1_yellow_0(A_2298,D_2301)
      | ~ r4_waybel_0(A_2298,'#skF_2',C_2300,D_2301)
      | ~ m1_subset_1(D_2301,k1_zfmisc_1(u1_struct_0(A_2298)))
      | ~ m1_subset_1(C_2300,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2298),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_2300,u1_struct_0(A_2298),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_2300)
      | v2_struct_0('#skF_2')
      | ~ l1_orders_2(A_2298)
      | v2_struct_0(A_2298) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_13732,c_13732,c_13732,c_21179])).

tff(c_23499,plain,(
    ! [A_2520,C_2521,D_2522] :
      ( k3_funct_2(u1_struct_0(A_2520),u1_struct_0('#skF_4'),C_2521,k1_yellow_0(A_2520,D_2522)) = k1_yellow_0('#skF_2',k7_relset_1(u1_struct_0(A_2520),u1_struct_0('#skF_4'),C_2521,D_2522))
      | ~ r1_yellow_0(A_2520,D_2522)
      | ~ r4_waybel_0(A_2520,'#skF_2',C_2521,D_2522)
      | ~ m1_subset_1(D_2522,k1_zfmisc_1(u1_struct_0(A_2520)))
      | ~ m1_subset_1(C_2521,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2520),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_2521,u1_struct_0(A_2520),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_2521)
      | ~ l1_orders_2(A_2520)
      | v2_struct_0(A_2520) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_21198])).

tff(c_23505,plain,(
    ! [D_2522] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_1',D_2522)) = k1_yellow_0('#skF_2',k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',D_2522))
      | ~ r1_yellow_0('#skF_1',D_2522)
      | ~ r4_waybel_0('#skF_1','#skF_2','#skF_6',D_2522)
      | ~ m1_subset_1(D_2522,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_13435,c_23499])).

tff(c_23520,plain,(
    ! [D_2522] :
      ( k1_yellow_0('#skF_2',k9_relat_1('#skF_6',D_2522)) = k1_funct_1('#skF_6',k1_yellow_0('#skF_1',D_2522))
      | ~ r1_yellow_0('#skF_1',D_2522)
      | ~ r4_waybel_0('#skF_1','#skF_2','#skF_6',D_2522)
      | ~ m1_subset_1(D_2522,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_60,c_13436,c_13433,c_22211,c_23505])).

tff(c_23529,plain,(
    ! [D_2523] :
      ( k1_yellow_0('#skF_2',k9_relat_1('#skF_6',D_2523)) = k1_funct_1('#skF_6',k1_yellow_0('#skF_1',D_2523))
      | ~ r1_yellow_0('#skF_1',D_2523)
      | ~ r4_waybel_0('#skF_1','#skF_2','#skF_6',D_2523)
      | ~ m1_subset_1(D_2523,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_23520])).

tff(c_23532,plain,
    ( k1_yellow_0('#skF_2',k9_relat_1('#skF_6','#skF_8')) = k1_funct_1('#skF_6',k1_yellow_0('#skF_1','#skF_8'))
    | ~ r1_yellow_0('#skF_1','#skF_8')
    | ~ r4_waybel_0('#skF_1','#skF_2','#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_98,c_23529])).

tff(c_23535,plain,(
    k1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) = k1_funct_1('#skF_6',k1_yellow_0('#skF_1','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13905,c_20963,c_22140,c_23532])).

tff(c_23537,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22071,c_23535])).

tff(c_23538,plain,(
    r1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_21087])).

tff(c_23539,plain,(
    r4_waybel_0('#skF_1','#skF_4','#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_21087])).

tff(c_23886,plain,(
    ! [B_2554,C_2555,B_2556] :
      ( k3_funct_2(u1_struct_0('#skF_1'),B_2554,C_2555,k1_yellow_0('#skF_3',B_2556)) = k1_funct_1(C_2555,k1_yellow_0('#skF_3',B_2556))
      | ~ m1_subset_1(C_2555,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),B_2554)))
      | ~ v1_funct_2(C_2555,u1_struct_0('#skF_1'),B_2554)
      | ~ v1_funct_1(C_2555) ) ),
    inference(negUnitSimplification,[status(thm)],[c_13486,c_13567])).

tff(c_23890,plain,(
    ! [B_2556] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_3',B_2556)) = k1_funct_1('#skF_6',k1_yellow_0('#skF_3',B_2556))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_13435,c_23886])).

tff(c_23937,plain,(
    ! [B_2561] : k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_3',B_2561)) = k1_funct_1('#skF_6',k1_yellow_0('#skF_3',B_2561)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_13436,c_23890])).

tff(c_23946,plain,(
    k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_1','#skF_8')) = k1_funct_1('#skF_6',k1_yellow_0('#skF_3','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_21080,c_23937])).

tff(c_23949,plain,(
    k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_1','#skF_8')) = k1_funct_1('#skF_6',k1_yellow_0('#skF_1','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21080,c_23946])).

tff(c_23685,plain,(
    ! [A_2531,B_2532,C_2533,D_2534] :
      ( k3_funct_2(u1_struct_0(A_2531),u1_struct_0(B_2532),C_2533,k1_yellow_0(A_2531,D_2534)) = k1_yellow_0(B_2532,k7_relset_1(u1_struct_0(A_2531),u1_struct_0(B_2532),C_2533,D_2534))
      | ~ r1_yellow_0(A_2531,D_2534)
      | ~ r4_waybel_0(A_2531,B_2532,C_2533,D_2534)
      | ~ m1_subset_1(D_2534,k1_zfmisc_1(u1_struct_0(A_2531)))
      | ~ m1_subset_1(C_2533,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2531),u1_struct_0(B_2532))))
      | ~ v1_funct_2(C_2533,u1_struct_0(A_2531),u1_struct_0(B_2532))
      | ~ v1_funct_1(C_2533)
      | ~ l1_orders_2(B_2532)
      | v2_struct_0(B_2532)
      | ~ l1_orders_2(A_2531)
      | v2_struct_0(A_2531) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_23695,plain,(
    ! [D_2534] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_1',D_2534)) = k1_yellow_0('#skF_4',k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',D_2534))
      | ~ r1_yellow_0('#skF_1',D_2534)
      | ~ r4_waybel_0('#skF_1','#skF_4','#skF_6',D_2534)
      | ~ m1_subset_1(D_2534,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_13435,c_23685])).

tff(c_23718,plain,(
    ! [D_2534] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_1',D_2534)) = k1_yellow_0('#skF_4',k9_relat_1('#skF_6',D_2534))
      | ~ r1_yellow_0('#skF_1',D_2534)
      | ~ r4_waybel_0('#skF_1','#skF_4','#skF_6',D_2534)
      | ~ m1_subset_1(D_2534,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_72,c_60,c_13436,c_13433,c_23695])).

tff(c_23719,plain,(
    ! [D_2534] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_1',D_2534)) = k1_yellow_0('#skF_4',k9_relat_1('#skF_6',D_2534))
      | ~ r1_yellow_0('#skF_1',D_2534)
      | ~ r4_waybel_0('#skF_1','#skF_4','#skF_6',D_2534)
      | ~ m1_subset_1(D_2534,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_74,c_23718])).

tff(c_23955,plain,
    ( k1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) = k1_funct_1('#skF_6',k1_yellow_0('#skF_1','#skF_8'))
    | ~ r1_yellow_0('#skF_1','#skF_8')
    | ~ r4_waybel_0('#skF_1','#skF_4','#skF_6','#skF_8')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_23949,c_23719])).

tff(c_23965,plain,(
    k1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8')) = k1_funct_1('#skF_6',k1_yellow_0('#skF_1','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_23539,c_20963,c_23955])).

tff(c_24115,plain,(
    ! [A_2572,B_2573,C_2574,B_2575] :
      ( k3_funct_2(u1_struct_0(A_2572),B_2573,C_2574,k1_yellow_0(A_2572,B_2575)) = k1_funct_1(C_2574,k1_yellow_0(A_2572,B_2575))
      | ~ m1_subset_1(C_2574,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2572),B_2573)))
      | ~ v1_funct_2(C_2574,u1_struct_0(A_2572),B_2573)
      | ~ v1_funct_1(C_2574)
      | v1_xboole_0(u1_struct_0(A_2572))
      | ~ l1_orders_2(A_2572) ) ),
    inference(resolution,[status(thm)],[c_18,c_13561])).

tff(c_24123,plain,(
    ! [B_2575] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_1',B_2575)) = k1_funct_1('#skF_6',k1_yellow_0('#skF_1',B_2575))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_13435,c_24115])).

tff(c_24141,plain,(
    ! [B_2575] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_1',B_2575)) = k1_funct_1('#skF_6',k1_yellow_0('#skF_1',B_2575))
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_60,c_13436,c_24123])).

tff(c_24142,plain,(
    ! [B_2575] : k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_1',B_2575)) = k1_funct_1('#skF_6',k1_yellow_0('#skF_1',B_2575)) ),
    inference(negUnitSimplification,[status(thm)],[c_13486,c_24141])).

tff(c_23775,plain,(
    ! [A_2545,B_2546,C_2547,D_2548] :
      ( k3_funct_2(u1_struct_0(A_2545),u1_struct_0(B_2546),C_2547,k1_yellow_0(A_2545,D_2548)) != k1_yellow_0(B_2546,k7_relset_1(u1_struct_0(A_2545),u1_struct_0(B_2546),C_2547,D_2548))
      | ~ r1_yellow_0(B_2546,k7_relset_1(u1_struct_0(A_2545),u1_struct_0(B_2546),C_2547,D_2548))
      | r4_waybel_0(A_2545,B_2546,C_2547,D_2548)
      | ~ m1_subset_1(D_2548,k1_zfmisc_1(u1_struct_0(A_2545)))
      | ~ m1_subset_1(C_2547,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2545),u1_struct_0(B_2546))))
      | ~ v1_funct_2(C_2547,u1_struct_0(A_2545),u1_struct_0(B_2546))
      | ~ v1_funct_1(C_2547)
      | ~ l1_orders_2(B_2546)
      | v2_struct_0(B_2546)
      | ~ l1_orders_2(A_2545)
      | v2_struct_0(A_2545) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_23781,plain,(
    ! [B_2546,C_2547] :
      ( k3_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_2546),C_2547,k1_yellow_0('#skF_1','#skF_8')) != k1_yellow_0(B_2546,k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0(B_2546),C_2547,'#skF_8'))
      | ~ r1_yellow_0(B_2546,k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0(B_2546),C_2547,'#skF_8'))
      | r4_waybel_0('#skF_3',B_2546,C_2547,'#skF_8')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(C_2547,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_2546))))
      | ~ v1_funct_2(C_2547,u1_struct_0('#skF_3'),u1_struct_0(B_2546))
      | ~ v1_funct_1(C_2547)
      | ~ l1_orders_2(B_2546)
      | v2_struct_0(B_2546)
      | ~ l1_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21080,c_23775])).

tff(c_23801,plain,(
    ! [B_2546,C_2547] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0(B_2546),C_2547,k1_yellow_0('#skF_1','#skF_8')) != k1_yellow_0(B_2546,k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_2546),C_2547,'#skF_8'))
      | ~ r1_yellow_0(B_2546,k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_2546),C_2547,'#skF_8'))
      | r4_waybel_0('#skF_3',B_2546,C_2547,'#skF_8')
      | ~ m1_subset_1(C_2547,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_2546))))
      | ~ v1_funct_2(C_2547,u1_struct_0('#skF_1'),u1_struct_0(B_2546))
      | ~ v1_funct_1(C_2547)
      | ~ l1_orders_2(B_2546)
      | v2_struct_0(B_2546)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_13420,c_13420,c_98,c_13420,c_13420,c_13420,c_13420,c_23781])).

tff(c_25829,plain,(
    ! [B_2742,C_2743] :
      ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0(B_2742),C_2743,k1_yellow_0('#skF_1','#skF_8')) != k1_yellow_0(B_2742,k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_2742),C_2743,'#skF_8'))
      | ~ r1_yellow_0(B_2742,k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_2742),C_2743,'#skF_8'))
      | r4_waybel_0('#skF_3',B_2742,C_2743,'#skF_8')
      | ~ m1_subset_1(C_2743,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_2742))))
      | ~ v1_funct_2(C_2743,u1_struct_0('#skF_1'),u1_struct_0(B_2742))
      | ~ v1_funct_1(C_2743)
      | ~ l1_orders_2(B_2742)
      | v2_struct_0(B_2742) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_23801])).

tff(c_25840,plain,
    ( k3_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6',k1_yellow_0('#skF_1','#skF_8')) != k1_yellow_0('#skF_4',k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'),'#skF_6','#skF_8'))
    | ~ r1_yellow_0('#skF_4',k9_relat_1('#skF_6','#skF_8'))
    | r4_waybel_0('#skF_3','#skF_4','#skF_6','#skF_8')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_13433,c_25829])).

tff(c_25857,plain,
    ( r4_waybel_0('#skF_3','#skF_4','#skF_6','#skF_8')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_60,c_13436,c_13435,c_23538,c_23965,c_13433,c_24142,c_25840])).

tff(c_25859,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_13277,c_25857])).

tff(c_25861,plain,(
    ~ r1_yellow_0('#skF_1','#skF_8') ),
    inference(splitRight,[status(thm)],[c_13886])).

tff(c_13874,plain,(
    ! [D_1643,B_1644,C_1645] :
      ( r1_yellow_0('#skF_3',D_1643)
      | r4_waybel_0('#skF_3',B_1644,C_1645,D_1643)
      | ~ m1_subset_1(D_1643,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(C_1645,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_1644))))
      | ~ v1_funct_2(C_1645,u1_struct_0('#skF_3'),u1_struct_0(B_1644))
      | ~ v1_funct_1(C_1645)
      | ~ l1_orders_2(B_1644)
      | v2_struct_0(B_1644)
      | ~ l1_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13420,c_13870])).

tff(c_13881,plain,(
    ! [D_1643,B_1644,C_1645] :
      ( r1_yellow_0('#skF_3',D_1643)
      | r4_waybel_0('#skF_3',B_1644,C_1645,D_1643)
      | ~ m1_subset_1(D_1643,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(C_1645,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1644))))
      | ~ v1_funct_2(C_1645,u1_struct_0('#skF_1'),u1_struct_0(B_1644))
      | ~ v1_funct_1(C_1645)
      | ~ l1_orders_2(B_1644)
      | v2_struct_0(B_1644)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_13420,c_13420,c_13874])).

tff(c_26545,plain,(
    ! [D_2818,B_2819,C_2820] :
      ( r1_yellow_0('#skF_3',D_2818)
      | r4_waybel_0('#skF_3',B_2819,C_2820,D_2818)
      | ~ m1_subset_1(D_2818,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(C_2820,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_2819))))
      | ~ v1_funct_2(C_2820,u1_struct_0('#skF_1'),u1_struct_0(B_2819))
      | ~ v1_funct_1(C_2820)
      | ~ l1_orders_2(B_2819)
      | v2_struct_0(B_2819) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_13881])).

tff(c_26548,plain,(
    ! [B_2819,C_2820] :
      ( r1_yellow_0('#skF_3','#skF_8')
      | r4_waybel_0('#skF_3',B_2819,C_2820,'#skF_8')
      | ~ m1_subset_1(C_2820,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_2819))))
      | ~ v1_funct_2(C_2820,u1_struct_0('#skF_1'),u1_struct_0(B_2819))
      | ~ v1_funct_1(C_2820)
      | ~ l1_orders_2(B_2819)
      | v2_struct_0(B_2819) ) ),
    inference(resolution,[status(thm)],[c_98,c_26545])).

tff(c_26681,plain,(
    r1_yellow_0('#skF_3','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_26548])).

tff(c_26685,plain,(
    ! [B_62] :
      ( r1_yellow_0(B_62,'#skF_8')
      | g1_orders_2(u1_struct_0(B_62),u1_orders_2(B_62)) != g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_3'))
      | ~ l1_orders_2(B_62)
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26681,c_40])).

tff(c_26691,plain,(
    ! [B_62] :
      ( r1_yellow_0(B_62,'#skF_8')
      | g1_orders_2(u1_struct_0(B_62),u1_orders_2(B_62)) != g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
      | ~ l1_orders_2(B_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_13359,c_13420,c_26685])).

tff(c_26694,plain,
    ( r1_yellow_0('#skF_1','#skF_8')
    | ~ l1_orders_2('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_26691])).

tff(c_26696,plain,(
    r1_yellow_0('#skF_1','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_26694])).

tff(c_26698,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25861,c_26696])).

tff(c_26701,plain,(
    ! [B_2827,C_2828] :
      ( r4_waybel_0('#skF_3',B_2827,C_2828,'#skF_8')
      | ~ m1_subset_1(C_2828,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_2827))))
      | ~ v1_funct_2(C_2828,u1_struct_0('#skF_1'),u1_struct_0(B_2827))
      | ~ v1_funct_1(C_2828)
      | ~ l1_orders_2(B_2827)
      | v2_struct_0(B_2827) ) ),
    inference(splitRight,[status(thm)],[c_26548])).

tff(c_26710,plain,
    ( r4_waybel_0('#skF_3','#skF_4','#skF_6','#skF_8')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_13435,c_26701])).

tff(c_26727,plain,
    ( r4_waybel_0('#skF_3','#skF_4','#skF_6','#skF_8')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_60,c_13436,c_26710])).

tff(c_26729,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_13277,c_26727])).

%------------------------------------------------------------------------------
