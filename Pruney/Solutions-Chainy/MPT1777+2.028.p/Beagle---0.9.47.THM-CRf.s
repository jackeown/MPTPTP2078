%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:36 EST 2020

% Result     : Theorem 22.51s
% Output     : CNFRefutation 22.64s
% Verified   : 
% Statistics : Number of formulae       :  242 (1670 expanded)
%              Number of leaves         :  129 ( 639 expanded)
%              Depth                    :   19
%              Number of atoms          :  320 (7091 expanded)
%              Number of equality atoms :   26 ( 812 expanded)
%              Maximal formula depth    :   30 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > r1_tmap_1 > v5_pre_topc > v1_funct_2 > m1_connsp_2 > v4_relat_1 > v4_pre_topc > v3_pre_topc > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_pre_topc > v3_ordinal1 > v3_lattices > v2_struct_0 > v2_pre_topc > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_pre_topc > v1_orders_2 > v1_funct_1 > v1_finset_1 > v10_lattices > l3_lattices > l1_struct_0 > l1_pre_topc > l1_orders_2 > k3_tmap_1 > k8_relset_1 > k2_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_xboole_0 > k1_tops_1 > k1_funct_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k6_relat_1 > k3_tarski > k3_relat_1 > k2_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_wellord2 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_25 > #skF_33 > #skF_7 > #skF_49 > #skF_5 > #skF_57 > #skF_52 > #skF_44 > #skF_18 > #skF_24 > #skF_35 > #skF_15 > #skF_19 > #skF_17 > #skF_31 > #skF_55 > #skF_22 > #skF_38 > #skF_36 > #skF_56 > #skF_54 > #skF_43 > #skF_40 > #skF_48 > #skF_37 > #skF_3 > #skF_10 > #skF_16 > #skF_47 > #skF_34 > #skF_32 > #skF_53 > #skF_51 > #skF_45 > #skF_28 > #skF_46 > #skF_41 > #skF_13 > #skF_2 > #skF_1 > #skF_9 > #skF_39 > #skF_26 > #skF_8 > #skF_23 > #skF_30 > #skF_14 > #skF_42 > #skF_11 > #skF_50 > #skF_29 > #skF_12 > #skF_27 > #skF_21 > #skF_6 > #skF_4 > #skF_20

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_25',type,(
    '#skF_25': $i > $i )).

tff('#skF_33',type,(
    '#skF_33': $i )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_49',type,(
    '#skF_49': ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_57',type,(
    '#skF_57': $i )).

tff('#skF_52',type,(
    '#skF_52': $i )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#skF_44',type,(
    '#skF_44': $i > $i )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#skF_18',type,(
    '#skF_18': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff('#skF_24',type,(
    '#skF_24': $i > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_35',type,(
    '#skF_35': $i > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff('#skF_19',type,(
    '#skF_19': $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_17',type,(
    '#skF_17': ( $i * $i ) > $i )).

tff('#skF_31',type,(
    '#skF_31': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_55',type,(
    '#skF_55': $i )).

tff('#skF_22',type,(
    '#skF_22': $i > $i )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff('#skF_38',type,(
    '#skF_38': $i )).

tff('#skF_36',type,(
    '#skF_36': $i )).

tff('#skF_56',type,(
    '#skF_56': $i )).

tff('#skF_54',type,(
    '#skF_54': $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_43',type,(
    '#skF_43': $i )).

tff('#skF_40',type,(
    '#skF_40': $i > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_48',type,(
    '#skF_48': $i )).

tff('#skF_37',type,(
    '#skF_37': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff('#skF_47',type,(
    '#skF_47': $i )).

tff('#skF_34',type,(
    '#skF_34': $i > $i )).

tff('#skF_32',type,(
    '#skF_32': $i > $i )).

tff('#skF_53',type,(
    '#skF_53': $i )).

tff('#skF_51',type,(
    '#skF_51': $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#skF_45',type,(
    '#skF_45': $i )).

tff('#skF_28',type,(
    '#skF_28': $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_46',type,(
    '#skF_46': $i )).

tff('#skF_41',type,(
    '#skF_41': $i > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_39',type,(
    '#skF_39': $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#skF_26',type,(
    '#skF_26': $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#skF_23',type,(
    '#skF_23': ( $i * $i ) > $i )).

tff('#skF_30',type,(
    '#skF_30': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_14',type,(
    '#skF_14': ( $i * $i * $i ) > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_42',type,(
    '#skF_42': $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': $i > $i )).

tff('#skF_50',type,(
    '#skF_50': ( $i * $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#skF_29',type,(
    '#skF_29': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(v3_lattices,type,(
    v3_lattices: $i > $o )).

tff('#skF_12',type,(
    '#skF_12': $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_27',type,(
    '#skF_27': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_21',type,(
    '#skF_21': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff('#skF_20',type,(
    '#skF_20': $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_1212,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).

tff(f_520,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_513,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_33,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_505,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_136,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_490,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_897,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_726,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_904,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_633,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_762,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_509,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_1106,axiom,(
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
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                     => ( m1_pre_topc(C,D)
                       => ! [F] :
                            ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(D)))
                           => ! [G] :
                                ( m1_subset_1(G,u1_struct_0(D))
                               => ! [H] :
                                    ( m1_subset_1(H,u1_struct_0(C))
                                   => ( ( v3_pre_topc(F,D)
                                        & r2_hidden(G,F)
                                        & r1_tarski(F,u1_struct_0(C))
                                        & G = H )
                                     => ( r1_tmap_1(D,B,E,G)
                                      <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tmap_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_547,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_622,plain,(
    l1_pre_topc('#skF_51') ),
    inference(cnfTransformation,[status(thm)],[f_1212])).

tff(c_612,plain,(
    m1_pre_topc('#skF_53','#skF_51') ),
    inference(cnfTransformation,[status(thm)],[f_1212])).

tff(c_32334,plain,(
    ! [B_109948,A_109949] :
      ( l1_pre_topc(B_109948)
      | ~ m1_pre_topc(B_109948,A_109949)
      | ~ l1_pre_topc(A_109949) ) ),
    inference(cnfTransformation,[status(thm)],[f_520])).

tff(c_32346,plain,
    ( l1_pre_topc('#skF_53')
    | ~ l1_pre_topc('#skF_51') ),
    inference(resolution,[status(thm)],[c_612,c_32334])).

tff(c_32354,plain,(
    l1_pre_topc('#skF_53') ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_32346])).

tff(c_382,plain,(
    ! [A_174] :
      ( l1_struct_0(A_174)
      | ~ l1_pre_topc(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_513])).

tff(c_614,plain,(
    ~ v2_struct_0('#skF_53') ),
    inference(cnfTransformation,[status(thm)],[f_1212])).

tff(c_6,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1861,plain,(
    ! [B_1334,A_1335] :
      ( l1_pre_topc(B_1334)
      | ~ m1_pre_topc(B_1334,A_1335)
      | ~ l1_pre_topc(A_1335) ) ),
    inference(cnfTransformation,[status(thm)],[f_520])).

tff(c_1873,plain,
    ( l1_pre_topc('#skF_53')
    | ~ l1_pre_topc('#skF_51') ),
    inference(resolution,[status(thm)],[c_612,c_1861])).

tff(c_1881,plain,(
    l1_pre_topc('#skF_53') ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_1873])).

tff(c_1019,plain,(
    ! [A_1291] :
      ( u1_struct_0(A_1291) = k2_struct_0(A_1291)
      | ~ l1_struct_0(A_1291) ) ),
    inference(cnfTransformation,[status(thm)],[f_505])).

tff(c_1030,plain,(
    ! [A_174] :
      ( u1_struct_0(A_174) = k2_struct_0(A_174)
      | ~ l1_pre_topc(A_174) ) ),
    inference(resolution,[status(thm)],[c_382,c_1019])).

tff(c_1896,plain,(
    u1_struct_0('#skF_53') = k2_struct_0('#skF_53') ),
    inference(resolution,[status(thm)],[c_1881,c_1030])).

tff(c_594,plain,(
    '#skF_57' = '#skF_56' ),
    inference(cnfTransformation,[status(thm)],[f_1212])).

tff(c_596,plain,(
    m1_subset_1('#skF_57',u1_struct_0('#skF_53')) ),
    inference(cnfTransformation,[status(thm)],[f_1212])).

tff(c_627,plain,(
    m1_subset_1('#skF_56',u1_struct_0('#skF_53')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_594,c_596])).

tff(c_1346,plain,(
    ! [B_1314,A_1315] :
      ( v1_xboole_0(B_1314)
      | ~ m1_subset_1(B_1314,A_1315)
      | ~ v1_xboole_0(A_1315) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1379,plain,
    ( v1_xboole_0('#skF_56')
    | ~ v1_xboole_0(u1_struct_0('#skF_53')) ),
    inference(resolution,[status(thm)],[c_627,c_1346])).

tff(c_1413,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_53')) ),
    inference(splitLeft,[status(thm)],[c_1379])).

tff(c_1966,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_53')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1896,c_1413])).

tff(c_1968,plain,(
    m1_subset_1('#skF_56',k2_struct_0('#skF_53')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1896,c_627])).

tff(c_76,plain,(
    ! [A_33,B_34] :
      ( r2_hidden(A_33,B_34)
      | v1_xboole_0(B_34)
      | ~ m1_subset_1(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_624,plain,(
    v2_pre_topc('#skF_51') ),
    inference(cnfTransformation,[status(thm)],[f_1212])).

tff(c_608,plain,(
    m1_pre_topc('#skF_54','#skF_51') ),
    inference(cnfTransformation,[status(thm)],[f_1212])).

tff(c_3588,plain,(
    ! [B_1407,A_1408] :
      ( v2_pre_topc(B_1407)
      | ~ m1_pre_topc(B_1407,A_1408)
      | ~ l1_pre_topc(A_1408)
      | ~ v2_pre_topc(A_1408) ) ),
    inference(cnfTransformation,[status(thm)],[f_490])).

tff(c_3597,plain,
    ( v2_pre_topc('#skF_54')
    | ~ l1_pre_topc('#skF_51')
    | ~ v2_pre_topc('#skF_51') ),
    inference(resolution,[status(thm)],[c_608,c_3588])).

tff(c_3605,plain,(
    v2_pre_topc('#skF_54') ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_622,c_3597])).

tff(c_1870,plain,
    ( l1_pre_topc('#skF_54')
    | ~ l1_pre_topc('#skF_51') ),
    inference(resolution,[status(thm)],[c_608,c_1861])).

tff(c_1878,plain,(
    l1_pre_topc('#skF_54') ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_1870])).

tff(c_544,plain,(
    ! [A_294] :
      ( m1_pre_topc(A_294,A_294)
      | ~ l1_pre_topc(A_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_897])).

tff(c_600,plain,(
    g1_pre_topc(u1_struct_0('#skF_53'),u1_pre_topc('#skF_53')) = '#skF_54' ),
    inference(cnfTransformation,[status(thm)],[f_1212])).

tff(c_1967,plain,(
    g1_pre_topc(k2_struct_0('#skF_53'),u1_pre_topc('#skF_53')) = '#skF_54' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1896,c_600])).

tff(c_14931,plain,(
    ! [A_74153,B_74154] :
      ( m1_pre_topc(A_74153,g1_pre_topc(u1_struct_0(B_74154),u1_pre_topc(B_74154)))
      | ~ m1_pre_topc(A_74153,B_74154)
      | ~ l1_pre_topc(B_74154)
      | ~ l1_pre_topc(A_74153) ) ),
    inference(cnfTransformation,[status(thm)],[f_726])).

tff(c_14957,plain,(
    ! [A_74153] :
      ( m1_pre_topc(A_74153,g1_pre_topc(k2_struct_0('#skF_53'),u1_pre_topc('#skF_53')))
      | ~ m1_pre_topc(A_74153,'#skF_53')
      | ~ l1_pre_topc('#skF_53')
      | ~ l1_pre_topc(A_74153) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1896,c_14931])).

tff(c_15010,plain,(
    ! [A_74232] :
      ( m1_pre_topc(A_74232,'#skF_54')
      | ~ m1_pre_topc(A_74232,'#skF_53')
      | ~ l1_pre_topc(A_74232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1881,c_1967,c_14957])).

tff(c_1888,plain,(
    u1_struct_0('#skF_54') = k2_struct_0('#skF_54') ),
    inference(resolution,[status(thm)],[c_1878,c_1030])).

tff(c_6639,plain,(
    ! [B_1488,A_1489] :
      ( r1_tarski(u1_struct_0(B_1488),u1_struct_0(A_1489))
      | ~ m1_pre_topc(B_1488,A_1489)
      | ~ l1_pre_topc(A_1489) ) ),
    inference(cnfTransformation,[status(thm)],[f_904])).

tff(c_6659,plain,(
    ! [B_1488] :
      ( r1_tarski(u1_struct_0(B_1488),k2_struct_0('#skF_54'))
      | ~ m1_pre_topc(B_1488,'#skF_54')
      | ~ l1_pre_topc('#skF_54') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1888,c_6639])).

tff(c_9718,plain,(
    ! [B_33364] :
      ( r1_tarski(u1_struct_0(B_33364),k2_struct_0('#skF_54'))
      | ~ m1_pre_topc(B_33364,'#skF_54') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1878,c_6659])).

tff(c_9735,plain,
    ( r1_tarski(k2_struct_0('#skF_53'),k2_struct_0('#skF_54'))
    | ~ m1_pre_topc('#skF_53','#skF_54') ),
    inference(superposition,[status(thm),theory(equality)],[c_1896,c_9718])).

tff(c_14726,plain,(
    ~ m1_pre_topc('#skF_53','#skF_54') ),
    inference(splitLeft,[status(thm)],[c_9735])).

tff(c_15013,plain,
    ( ~ m1_pre_topc('#skF_53','#skF_53')
    | ~ l1_pre_topc('#skF_53') ),
    inference(resolution,[status(thm)],[c_15010,c_14726])).

tff(c_15048,plain,(
    ~ m1_pre_topc('#skF_53','#skF_53') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1881,c_15013])).

tff(c_15077,plain,(
    ~ l1_pre_topc('#skF_53') ),
    inference(resolution,[status(thm)],[c_544,c_15048])).

tff(c_15084,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1881,c_15077])).

tff(c_15085,plain,(
    r1_tarski(k2_struct_0('#skF_53'),k2_struct_0('#skF_54')) ),
    inference(splitRight,[status(thm)],[c_9735])).

tff(c_12602,plain,(
    ! [B_67639,A_67640] :
      ( m1_pre_topc(B_67639,A_67640)
      | ~ m1_pre_topc(B_67639,g1_pre_topc(u1_struct_0(A_67640),u1_pre_topc(A_67640)))
      | ~ l1_pre_topc(A_67640) ) ),
    inference(cnfTransformation,[status(thm)],[f_633])).

tff(c_12614,plain,(
    ! [B_67639] :
      ( m1_pre_topc(B_67639,'#skF_53')
      | ~ m1_pre_topc(B_67639,g1_pre_topc(k2_struct_0('#skF_53'),u1_pre_topc('#skF_53')))
      | ~ l1_pre_topc('#skF_53') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1896,c_12602])).

tff(c_12671,plain,(
    ! [B_67718] :
      ( m1_pre_topc(B_67718,'#skF_53')
      | ~ m1_pre_topc(B_67718,'#skF_54') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1881,c_1967,c_12614])).

tff(c_12679,plain,
    ( m1_pre_topc('#skF_54','#skF_53')
    | ~ l1_pre_topc('#skF_54') ),
    inference(resolution,[status(thm)],[c_544,c_12671])).

tff(c_12685,plain,(
    m1_pre_topc('#skF_54','#skF_53') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1878,c_12679])).

tff(c_6665,plain,(
    ! [B_1488] :
      ( r1_tarski(u1_struct_0(B_1488),k2_struct_0('#skF_53'))
      | ~ m1_pre_topc(B_1488,'#skF_53')
      | ~ l1_pre_topc('#skF_53') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1896,c_6639])).

tff(c_7067,plain,(
    ! [B_1496] :
      ( r1_tarski(u1_struct_0(B_1496),k2_struct_0('#skF_53'))
      | ~ m1_pre_topc(B_1496,'#skF_53') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1881,c_6665])).

tff(c_7081,plain,
    ( r1_tarski(k2_struct_0('#skF_54'),k2_struct_0('#skF_53'))
    | ~ m1_pre_topc('#skF_54','#skF_53') ),
    inference(superposition,[status(thm),theory(equality)],[c_1888,c_7067])).

tff(c_17611,plain,(
    r1_tarski(k2_struct_0('#skF_54'),k2_struct_0('#skF_53')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12685,c_7081])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_17618,plain,
    ( k2_struct_0('#skF_54') = k2_struct_0('#skF_53')
    | ~ r1_tarski(k2_struct_0('#skF_53'),k2_struct_0('#skF_54')) ),
    inference(resolution,[status(thm)],[c_17611,c_10])).

tff(c_17630,plain,(
    k2_struct_0('#skF_54') = k2_struct_0('#skF_53') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15085,c_17618])).

tff(c_472,plain,(
    ! [A_260] :
      ( v3_pre_topc(k2_struct_0(A_260),A_260)
      | ~ l1_pre_topc(A_260)
      | ~ v2_pre_topc(A_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_762])).

tff(c_17686,plain,
    ( v3_pre_topc(k2_struct_0('#skF_53'),'#skF_54')
    | ~ l1_pre_topc('#skF_54')
    | ~ v2_pre_topc('#skF_54') ),
    inference(superposition,[status(thm),theory(equality)],[c_17630,c_472])).

tff(c_17701,plain,(
    v3_pre_topc(k2_struct_0('#skF_53'),'#skF_54') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3605,c_1878,c_17686])).

tff(c_14,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_3434,plain,(
    ! [A_1405] :
      ( m1_subset_1(k2_struct_0(A_1405),k1_zfmisc_1(u1_struct_0(A_1405)))
      | ~ l1_struct_0(A_1405) ) ),
    inference(cnfTransformation,[status(thm)],[f_509])).

tff(c_3449,plain,
    ( m1_subset_1(k2_struct_0('#skF_53'),k1_zfmisc_1(k2_struct_0('#skF_53')))
    | ~ l1_struct_0('#skF_53') ),
    inference(superposition,[status(thm),theory(equality)],[c_1896,c_3434])).

tff(c_3994,plain,(
    ~ l1_struct_0('#skF_53') ),
    inference(splitLeft,[status(thm)],[c_3449])).

tff(c_4000,plain,(
    ~ l1_pre_topc('#skF_53') ),
    inference(resolution,[status(thm)],[c_382,c_3994])).

tff(c_4005,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1881,c_4000])).

tff(c_4006,plain,(
    m1_subset_1(k2_struct_0('#skF_53'),k1_zfmisc_1(k2_struct_0('#skF_53'))) ),
    inference(splitRight,[status(thm)],[c_3449])).

tff(c_626,plain,(
    ~ v2_struct_0('#skF_51') ),
    inference(cnfTransformation,[status(thm)],[f_1212])).

tff(c_620,plain,(
    ~ v2_struct_0('#skF_52') ),
    inference(cnfTransformation,[status(thm)],[f_1212])).

tff(c_610,plain,(
    ~ v2_struct_0('#skF_54') ),
    inference(cnfTransformation,[status(thm)],[f_1212])).

tff(c_590,plain,(
    ~ r1_tmap_1('#skF_54','#skF_52','#skF_55','#skF_56') ),
    inference(cnfTransformation,[status(thm)],[f_1212])).

tff(c_618,plain,(
    v2_pre_topc('#skF_52') ),
    inference(cnfTransformation,[status(thm)],[f_1212])).

tff(c_616,plain,(
    l1_pre_topc('#skF_52') ),
    inference(cnfTransformation,[status(thm)],[f_1212])).

tff(c_606,plain,(
    v1_funct_1('#skF_55') ),
    inference(cnfTransformation,[status(thm)],[f_1212])).

tff(c_1305,plain,(
    ! [A_1313] :
      ( u1_struct_0(A_1313) = k2_struct_0(A_1313)
      | ~ l1_pre_topc(A_1313) ) ),
    inference(resolution,[status(thm)],[c_382,c_1019])).

tff(c_1328,plain,(
    u1_struct_0('#skF_52') = k2_struct_0('#skF_52') ),
    inference(resolution,[status(thm)],[c_616,c_1305])).

tff(c_604,plain,(
    v1_funct_2('#skF_55',u1_struct_0('#skF_54'),u1_struct_0('#skF_52')) ),
    inference(cnfTransformation,[status(thm)],[f_1212])).

tff(c_1382,plain,(
    v1_funct_2('#skF_55',u1_struct_0('#skF_54'),k2_struct_0('#skF_52')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1328,c_604])).

tff(c_1974,plain,(
    v1_funct_2('#skF_55',k2_struct_0('#skF_54'),k2_struct_0('#skF_52')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1888,c_1382])).

tff(c_17668,plain,(
    v1_funct_2('#skF_55',k2_struct_0('#skF_53'),k2_struct_0('#skF_52')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17630,c_1974])).

tff(c_17671,plain,(
    u1_struct_0('#skF_54') = k2_struct_0('#skF_53') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17630,c_1888])).

tff(c_602,plain,(
    m1_subset_1('#skF_55',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_54'),u1_struct_0('#skF_52')))) ),
    inference(cnfTransformation,[status(thm)],[f_1212])).

tff(c_1381,plain,(
    m1_subset_1('#skF_55',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_54'),k2_struct_0('#skF_52')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1328,c_602])).

tff(c_1973,plain,(
    m1_subset_1('#skF_55',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_54'),k2_struct_0('#skF_52')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1888,c_1381])).

tff(c_17667,plain,(
    m1_subset_1('#skF_55',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_53'),k2_struct_0('#skF_52')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17630,c_1973])).

tff(c_15086,plain,(
    m1_pre_topc('#skF_53','#skF_54') ),
    inference(splitRight,[status(thm)],[c_9735])).

tff(c_592,plain,(
    r1_tmap_1('#skF_53','#skF_52',k3_tmap_1('#skF_51','#skF_52','#skF_54','#skF_53','#skF_55'),'#skF_57') ),
    inference(cnfTransformation,[status(thm)],[f_1212])).

tff(c_628,plain,(
    r1_tmap_1('#skF_53','#skF_52',k3_tmap_1('#skF_51','#skF_52','#skF_54','#skF_53','#skF_55'),'#skF_56') ),
    inference(demodulation,[status(thm),theory(equality)],[c_594,c_592])).

tff(c_31919,plain,(
    ! [H_109471,A_109472,E_109467,F_109469,C_109466,B_109468,D_109470] :
      ( r1_tmap_1(D_109470,B_109468,E_109467,H_109471)
      | ~ r1_tmap_1(C_109466,B_109468,k3_tmap_1(A_109472,B_109468,D_109470,C_109466,E_109467),H_109471)
      | ~ r1_tarski(F_109469,u1_struct_0(C_109466))
      | ~ r2_hidden(H_109471,F_109469)
      | ~ v3_pre_topc(F_109469,D_109470)
      | ~ m1_subset_1(H_109471,u1_struct_0(C_109466))
      | ~ m1_subset_1(H_109471,u1_struct_0(D_109470))
      | ~ m1_subset_1(F_109469,k1_zfmisc_1(u1_struct_0(D_109470)))
      | ~ m1_pre_topc(C_109466,D_109470)
      | ~ m1_subset_1(E_109467,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_109470),u1_struct_0(B_109468))))
      | ~ v1_funct_2(E_109467,u1_struct_0(D_109470),u1_struct_0(B_109468))
      | ~ v1_funct_1(E_109467)
      | ~ m1_pre_topc(D_109470,A_109472)
      | v2_struct_0(D_109470)
      | ~ m1_pre_topc(C_109466,A_109472)
      | v2_struct_0(C_109466)
      | ~ l1_pre_topc(B_109468)
      | ~ v2_pre_topc(B_109468)
      | v2_struct_0(B_109468)
      | ~ l1_pre_topc(A_109472)
      | ~ v2_pre_topc(A_109472)
      | v2_struct_0(A_109472) ) ),
    inference(cnfTransformation,[status(thm)],[f_1106])).

tff(c_31922,plain,(
    ! [F_109469] :
      ( r1_tmap_1('#skF_54','#skF_52','#skF_55','#skF_56')
      | ~ r1_tarski(F_109469,u1_struct_0('#skF_53'))
      | ~ r2_hidden('#skF_56',F_109469)
      | ~ v3_pre_topc(F_109469,'#skF_54')
      | ~ m1_subset_1('#skF_56',u1_struct_0('#skF_53'))
      | ~ m1_subset_1('#skF_56',u1_struct_0('#skF_54'))
      | ~ m1_subset_1(F_109469,k1_zfmisc_1(u1_struct_0('#skF_54')))
      | ~ m1_pre_topc('#skF_53','#skF_54')
      | ~ m1_subset_1('#skF_55',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_54'),u1_struct_0('#skF_52'))))
      | ~ v1_funct_2('#skF_55',u1_struct_0('#skF_54'),u1_struct_0('#skF_52'))
      | ~ v1_funct_1('#skF_55')
      | ~ m1_pre_topc('#skF_54','#skF_51')
      | v2_struct_0('#skF_54')
      | ~ m1_pre_topc('#skF_53','#skF_51')
      | v2_struct_0('#skF_53')
      | ~ l1_pre_topc('#skF_52')
      | ~ v2_pre_topc('#skF_52')
      | v2_struct_0('#skF_52')
      | ~ l1_pre_topc('#skF_51')
      | ~ v2_pre_topc('#skF_51')
      | v2_struct_0('#skF_51') ) ),
    inference(resolution,[status(thm)],[c_628,c_31919])).

tff(c_31925,plain,(
    ! [F_109469] :
      ( r1_tmap_1('#skF_54','#skF_52','#skF_55','#skF_56')
      | ~ r1_tarski(F_109469,k2_struct_0('#skF_53'))
      | ~ r2_hidden('#skF_56',F_109469)
      | ~ v3_pre_topc(F_109469,'#skF_54')
      | ~ m1_subset_1(F_109469,k1_zfmisc_1(k2_struct_0('#skF_53')))
      | v2_struct_0('#skF_54')
      | v2_struct_0('#skF_53')
      | v2_struct_0('#skF_52')
      | v2_struct_0('#skF_51') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_622,c_618,c_616,c_612,c_608,c_606,c_17668,c_1328,c_17671,c_17667,c_1328,c_17671,c_15086,c_17671,c_1968,c_17671,c_1968,c_1896,c_1896,c_31922])).

tff(c_31937,plain,(
    ! [F_109781] :
      ( ~ r1_tarski(F_109781,k2_struct_0('#skF_53'))
      | ~ r2_hidden('#skF_56',F_109781)
      | ~ v3_pre_topc(F_109781,'#skF_54')
      | ~ m1_subset_1(F_109781,k1_zfmisc_1(k2_struct_0('#skF_53'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_626,c_620,c_614,c_610,c_590,c_31925])).

tff(c_32001,plain,
    ( ~ r1_tarski(k2_struct_0('#skF_53'),k2_struct_0('#skF_53'))
    | ~ r2_hidden('#skF_56',k2_struct_0('#skF_53'))
    | ~ v3_pre_topc(k2_struct_0('#skF_53'),'#skF_54') ),
    inference(resolution,[status(thm)],[c_4006,c_31937])).

tff(c_32073,plain,(
    ~ r2_hidden('#skF_56',k2_struct_0('#skF_53')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17701,c_14,c_32001])).

tff(c_32088,plain,
    ( v1_xboole_0(k2_struct_0('#skF_53'))
    | ~ m1_subset_1('#skF_56',k2_struct_0('#skF_53')) ),
    inference(resolution,[status(thm)],[c_76,c_32073])).

tff(c_32091,plain,(
    v1_xboole_0(k2_struct_0('#skF_53')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1968,c_32088])).

tff(c_32093,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1966,c_32091])).

tff(c_32095,plain,(
    v1_xboole_0(u1_struct_0('#skF_53')) ),
    inference(splitRight,[status(thm)],[c_1379])).

tff(c_740,plain,(
    ! [A_1262] :
      ( k1_xboole_0 = A_1262
      | ~ v1_xboole_0(A_1262) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_755,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_740])).

tff(c_24,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_758,plain,(
    ! [A_8] :
      ( A_8 = '#skF_1'
      | ~ v1_xboole_0(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_755,c_24])).

tff(c_32155,plain,(
    u1_struct_0('#skF_53') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32095,c_758])).

tff(c_32365,plain,(
    u1_struct_0('#skF_53') = k2_struct_0('#skF_53') ),
    inference(resolution,[status(thm)],[c_32354,c_1030])).

tff(c_32370,plain,(
    k2_struct_0('#skF_53') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32155,c_32365])).

tff(c_396,plain,(
    ! [A_182] :
      ( ~ v1_xboole_0(k2_struct_0(A_182))
      | ~ l1_struct_0(A_182)
      | v2_struct_0(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_547])).

tff(c_32375,plain,
    ( ~ v1_xboole_0('#skF_1')
    | ~ l1_struct_0('#skF_53')
    | v2_struct_0('#skF_53') ),
    inference(superposition,[status(thm),theory(equality)],[c_32370,c_396])).

tff(c_32379,plain,
    ( ~ l1_struct_0('#skF_53')
    | v2_struct_0('#skF_53') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_32375])).

tff(c_32380,plain,(
    ~ l1_struct_0('#skF_53') ),
    inference(negUnitSimplification,[status(thm)],[c_614,c_32379])).

tff(c_32387,plain,(
    ~ l1_pre_topc('#skF_53') ),
    inference(resolution,[status(thm)],[c_382,c_32380])).

tff(c_32392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32354,c_32387])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:13:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.51/10.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.51/10.64  
% 22.51/10.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.51/10.65  %$ r2_funct_2 > r1_tmap_1 > v5_pre_topc > v1_funct_2 > m1_connsp_2 > v4_relat_1 > v4_pre_topc > v3_pre_topc > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_pre_topc > v3_ordinal1 > v3_lattices > v2_struct_0 > v2_pre_topc > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_pre_topc > v1_orders_2 > v1_funct_1 > v1_finset_1 > v10_lattices > l3_lattices > l1_struct_0 > l1_pre_topc > l1_orders_2 > k3_tmap_1 > k8_relset_1 > k2_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_xboole_0 > k1_tops_1 > k1_funct_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k6_relat_1 > k3_tarski > k3_relat_1 > k2_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_wellord2 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_25 > #skF_33 > #skF_7 > #skF_49 > #skF_5 > #skF_57 > #skF_52 > #skF_44 > #skF_18 > #skF_24 > #skF_35 > #skF_15 > #skF_19 > #skF_17 > #skF_31 > #skF_55 > #skF_22 > #skF_38 > #skF_36 > #skF_56 > #skF_54 > #skF_43 > #skF_40 > #skF_48 > #skF_37 > #skF_3 > #skF_10 > #skF_16 > #skF_47 > #skF_34 > #skF_32 > #skF_53 > #skF_51 > #skF_45 > #skF_28 > #skF_46 > #skF_41 > #skF_13 > #skF_2 > #skF_1 > #skF_9 > #skF_39 > #skF_26 > #skF_8 > #skF_23 > #skF_30 > #skF_14 > #skF_42 > #skF_11 > #skF_50 > #skF_29 > #skF_12 > #skF_27 > #skF_21 > #skF_6 > #skF_4 > #skF_20
% 22.51/10.65  
% 22.51/10.65  %Foreground sorts:
% 22.51/10.65  
% 22.51/10.65  
% 22.51/10.65  %Background operators:
% 22.51/10.65  
% 22.51/10.65  
% 22.51/10.65  %Foreground operators:
% 22.51/10.65  tff(l3_lattices, type, l3_lattices: $i > $o).
% 22.51/10.65  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 22.51/10.65  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 22.51/10.65  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 22.51/10.65  tff('#skF_25', type, '#skF_25': $i > $i).
% 22.51/10.65  tff('#skF_33', type, '#skF_33': $i).
% 22.51/10.65  tff('#skF_7', type, '#skF_7': $i > $i).
% 22.51/10.65  tff('#skF_49', type, '#skF_49': ($i * $i * $i) > $i).
% 22.51/10.65  tff('#skF_5', type, '#skF_5': $i > $i).
% 22.51/10.65  tff('#skF_57', type, '#skF_57': $i).
% 22.51/10.65  tff('#skF_52', type, '#skF_52': $i).
% 22.51/10.65  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 22.51/10.65  tff('#skF_44', type, '#skF_44': $i > $i).
% 22.51/10.65  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 22.51/10.65  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 22.51/10.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 22.51/10.65  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 22.51/10.65  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 22.51/10.65  tff('#skF_18', type, '#skF_18': $i > $i).
% 22.51/10.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.51/10.65  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 22.51/10.65  tff('#skF_24', type, '#skF_24': $i > $i).
% 22.51/10.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 22.51/10.65  tff('#skF_35', type, '#skF_35': $i > $i).
% 22.51/10.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 22.51/10.65  tff('#skF_15', type, '#skF_15': $i).
% 22.51/10.65  tff('#skF_19', type, '#skF_19': $i > $i).
% 22.51/10.65  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 22.51/10.65  tff('#skF_17', type, '#skF_17': ($i * $i) > $i).
% 22.51/10.65  tff('#skF_31', type, '#skF_31': $i > $i).
% 22.51/10.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 22.51/10.65  tff('#skF_55', type, '#skF_55': $i).
% 22.51/10.65  tff('#skF_22', type, '#skF_22': $i > $i).
% 22.51/10.65  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 22.51/10.65  tff('#skF_38', type, '#skF_38': $i).
% 22.51/10.65  tff('#skF_36', type, '#skF_36': $i).
% 22.51/10.65  tff('#skF_56', type, '#skF_56': $i).
% 22.51/10.65  tff('#skF_54', type, '#skF_54': $i).
% 22.51/10.65  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 22.51/10.65  tff('#skF_43', type, '#skF_43': $i).
% 22.51/10.65  tff('#skF_40', type, '#skF_40': $i > $i).
% 22.51/10.65  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 22.51/10.65  tff('#skF_48', type, '#skF_48': $i).
% 22.51/10.65  tff('#skF_37', type, '#skF_37': $i).
% 22.51/10.65  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 22.51/10.65  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 22.51/10.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 22.51/10.65  tff('#skF_10', type, '#skF_10': $i).
% 22.51/10.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 22.51/10.65  tff('#skF_16', type, '#skF_16': $i).
% 22.51/10.65  tff('#skF_47', type, '#skF_47': $i).
% 22.51/10.65  tff('#skF_34', type, '#skF_34': $i > $i).
% 22.51/10.65  tff('#skF_32', type, '#skF_32': $i > $i).
% 22.51/10.65  tff('#skF_53', type, '#skF_53': $i).
% 22.51/10.65  tff('#skF_51', type, '#skF_51': $i).
% 22.51/10.65  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 22.51/10.65  tff('#skF_45', type, '#skF_45': $i).
% 22.51/10.65  tff('#skF_28', type, '#skF_28': $i > $i).
% 22.51/10.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 22.51/10.65  tff('#skF_46', type, '#skF_46': $i).
% 22.51/10.65  tff('#skF_41', type, '#skF_41': $i > $i).
% 22.51/10.65  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 22.51/10.65  tff('#skF_13', type, '#skF_13': $i).
% 22.51/10.65  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 22.51/10.65  tff('#skF_2', type, '#skF_2': $i).
% 22.51/10.65  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 22.51/10.65  tff('#skF_1', type, '#skF_1': $i).
% 22.51/10.65  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 22.51/10.65  tff(v10_lattices, type, v10_lattices: $i > $o).
% 22.51/10.65  tff('#skF_9', type, '#skF_9': $i).
% 22.51/10.65  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 22.51/10.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 22.51/10.65  tff('#skF_39', type, '#skF_39': $i > $i).
% 22.51/10.65  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 22.51/10.65  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 22.51/10.65  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 22.51/10.65  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 22.51/10.65  tff('#skF_26', type, '#skF_26': $i > $i).
% 22.51/10.65  tff('#skF_8', type, '#skF_8': $i).
% 22.51/10.65  tff('#skF_23', type, '#skF_23': ($i * $i) > $i).
% 22.51/10.65  tff('#skF_30', type, '#skF_30': $i).
% 22.51/10.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.51/10.65  tff('#skF_14', type, '#skF_14': ($i * $i * $i) > $i).
% 22.51/10.65  tff(k3_tarski, type, k3_tarski: $i > $i).
% 22.51/10.65  tff('#skF_42', type, '#skF_42': $i).
% 22.51/10.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 22.51/10.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 22.51/10.65  tff('#skF_11', type, '#skF_11': $i > $i).
% 22.51/10.65  tff('#skF_50', type, '#skF_50': ($i * $i * $i) > $i).
% 22.51/10.65  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 22.51/10.65  tff('#skF_29', type, '#skF_29': $i).
% 22.51/10.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.51/10.65  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 22.51/10.65  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 22.51/10.65  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 22.51/10.65  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 22.51/10.65  tff(v3_lattices, type, v3_lattices: $i > $o).
% 22.51/10.65  tff('#skF_12', type, '#skF_12': $i > $i).
% 22.51/10.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 22.51/10.65  tff('#skF_27', type, '#skF_27': ($i * $i) > $i).
% 22.51/10.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 22.51/10.65  tff('#skF_21', type, '#skF_21': ($i * $i) > $i).
% 22.51/10.65  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 22.51/10.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 22.51/10.65  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 22.51/10.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 22.51/10.65  tff('#skF_6', type, '#skF_6': $i > $i).
% 22.51/10.65  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 22.51/10.65  tff('#skF_20', type, '#skF_20': $i > $i).
% 22.51/10.65  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 22.51/10.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 22.51/10.65  
% 22.64/10.67  tff(f_1212, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 22.64/10.67  tff(f_520, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 22.64/10.67  tff(f_513, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 22.64/10.67  tff(f_33, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 22.64/10.67  tff(f_505, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 22.64/10.67  tff(f_101, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 22.64/10.67  tff(f_136, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 22.64/10.67  tff(f_490, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 22.64/10.67  tff(f_897, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 22.64/10.67  tff(f_726, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 22.64/10.67  tff(f_904, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_borsuk_1)).
% 22.64/10.67  tff(f_633, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 22.64/10.67  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 22.64/10.67  tff(f_762, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 22.64/10.67  tff(f_509, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 22.64/10.67  tff(f_1106, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tmap_1)).
% 22.64/10.67  tff(f_64, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_boole)).
% 22.64/10.67  tff(f_547, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 22.64/10.67  tff(c_622, plain, (l1_pre_topc('#skF_51')), inference(cnfTransformation, [status(thm)], [f_1212])).
% 22.64/10.67  tff(c_612, plain, (m1_pre_topc('#skF_53', '#skF_51')), inference(cnfTransformation, [status(thm)], [f_1212])).
% 22.64/10.67  tff(c_32334, plain, (![B_109948, A_109949]: (l1_pre_topc(B_109948) | ~m1_pre_topc(B_109948, A_109949) | ~l1_pre_topc(A_109949))), inference(cnfTransformation, [status(thm)], [f_520])).
% 22.64/10.67  tff(c_32346, plain, (l1_pre_topc('#skF_53') | ~l1_pre_topc('#skF_51')), inference(resolution, [status(thm)], [c_612, c_32334])).
% 22.64/10.67  tff(c_32354, plain, (l1_pre_topc('#skF_53')), inference(demodulation, [status(thm), theory('equality')], [c_622, c_32346])).
% 22.64/10.67  tff(c_382, plain, (![A_174]: (l1_struct_0(A_174) | ~l1_pre_topc(A_174))), inference(cnfTransformation, [status(thm)], [f_513])).
% 22.64/10.67  tff(c_614, plain, (~v2_struct_0('#skF_53')), inference(cnfTransformation, [status(thm)], [f_1212])).
% 22.64/10.67  tff(c_6, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_33])).
% 22.64/10.67  tff(c_1861, plain, (![B_1334, A_1335]: (l1_pre_topc(B_1334) | ~m1_pre_topc(B_1334, A_1335) | ~l1_pre_topc(A_1335))), inference(cnfTransformation, [status(thm)], [f_520])).
% 22.64/10.67  tff(c_1873, plain, (l1_pre_topc('#skF_53') | ~l1_pre_topc('#skF_51')), inference(resolution, [status(thm)], [c_612, c_1861])).
% 22.64/10.67  tff(c_1881, plain, (l1_pre_topc('#skF_53')), inference(demodulation, [status(thm), theory('equality')], [c_622, c_1873])).
% 22.64/10.67  tff(c_1019, plain, (![A_1291]: (u1_struct_0(A_1291)=k2_struct_0(A_1291) | ~l1_struct_0(A_1291))), inference(cnfTransformation, [status(thm)], [f_505])).
% 22.64/10.67  tff(c_1030, plain, (![A_174]: (u1_struct_0(A_174)=k2_struct_0(A_174) | ~l1_pre_topc(A_174))), inference(resolution, [status(thm)], [c_382, c_1019])).
% 22.64/10.67  tff(c_1896, plain, (u1_struct_0('#skF_53')=k2_struct_0('#skF_53')), inference(resolution, [status(thm)], [c_1881, c_1030])).
% 22.64/10.67  tff(c_594, plain, ('#skF_57'='#skF_56'), inference(cnfTransformation, [status(thm)], [f_1212])).
% 22.64/10.67  tff(c_596, plain, (m1_subset_1('#skF_57', u1_struct_0('#skF_53'))), inference(cnfTransformation, [status(thm)], [f_1212])).
% 22.64/10.67  tff(c_627, plain, (m1_subset_1('#skF_56', u1_struct_0('#skF_53'))), inference(demodulation, [status(thm), theory('equality')], [c_594, c_596])).
% 22.64/10.67  tff(c_1346, plain, (![B_1314, A_1315]: (v1_xboole_0(B_1314) | ~m1_subset_1(B_1314, A_1315) | ~v1_xboole_0(A_1315))), inference(cnfTransformation, [status(thm)], [f_101])).
% 22.64/10.67  tff(c_1379, plain, (v1_xboole_0('#skF_56') | ~v1_xboole_0(u1_struct_0('#skF_53'))), inference(resolution, [status(thm)], [c_627, c_1346])).
% 22.64/10.67  tff(c_1413, plain, (~v1_xboole_0(u1_struct_0('#skF_53'))), inference(splitLeft, [status(thm)], [c_1379])).
% 22.64/10.67  tff(c_1966, plain, (~v1_xboole_0(k2_struct_0('#skF_53'))), inference(demodulation, [status(thm), theory('equality')], [c_1896, c_1413])).
% 22.64/10.67  tff(c_1968, plain, (m1_subset_1('#skF_56', k2_struct_0('#skF_53'))), inference(demodulation, [status(thm), theory('equality')], [c_1896, c_627])).
% 22.64/10.67  tff(c_76, plain, (![A_33, B_34]: (r2_hidden(A_33, B_34) | v1_xboole_0(B_34) | ~m1_subset_1(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_136])).
% 22.64/10.67  tff(c_624, plain, (v2_pre_topc('#skF_51')), inference(cnfTransformation, [status(thm)], [f_1212])).
% 22.64/10.67  tff(c_608, plain, (m1_pre_topc('#skF_54', '#skF_51')), inference(cnfTransformation, [status(thm)], [f_1212])).
% 22.64/10.67  tff(c_3588, plain, (![B_1407, A_1408]: (v2_pre_topc(B_1407) | ~m1_pre_topc(B_1407, A_1408) | ~l1_pre_topc(A_1408) | ~v2_pre_topc(A_1408))), inference(cnfTransformation, [status(thm)], [f_490])).
% 22.64/10.67  tff(c_3597, plain, (v2_pre_topc('#skF_54') | ~l1_pre_topc('#skF_51') | ~v2_pre_topc('#skF_51')), inference(resolution, [status(thm)], [c_608, c_3588])).
% 22.64/10.67  tff(c_3605, plain, (v2_pre_topc('#skF_54')), inference(demodulation, [status(thm), theory('equality')], [c_624, c_622, c_3597])).
% 22.64/10.67  tff(c_1870, plain, (l1_pre_topc('#skF_54') | ~l1_pre_topc('#skF_51')), inference(resolution, [status(thm)], [c_608, c_1861])).
% 22.64/10.67  tff(c_1878, plain, (l1_pre_topc('#skF_54')), inference(demodulation, [status(thm), theory('equality')], [c_622, c_1870])).
% 22.64/10.67  tff(c_544, plain, (![A_294]: (m1_pre_topc(A_294, A_294) | ~l1_pre_topc(A_294))), inference(cnfTransformation, [status(thm)], [f_897])).
% 22.64/10.67  tff(c_600, plain, (g1_pre_topc(u1_struct_0('#skF_53'), u1_pre_topc('#skF_53'))='#skF_54'), inference(cnfTransformation, [status(thm)], [f_1212])).
% 22.64/10.67  tff(c_1967, plain, (g1_pre_topc(k2_struct_0('#skF_53'), u1_pre_topc('#skF_53'))='#skF_54'), inference(demodulation, [status(thm), theory('equality')], [c_1896, c_600])).
% 22.64/10.67  tff(c_14931, plain, (![A_74153, B_74154]: (m1_pre_topc(A_74153, g1_pre_topc(u1_struct_0(B_74154), u1_pre_topc(B_74154))) | ~m1_pre_topc(A_74153, B_74154) | ~l1_pre_topc(B_74154) | ~l1_pre_topc(A_74153))), inference(cnfTransformation, [status(thm)], [f_726])).
% 22.64/10.67  tff(c_14957, plain, (![A_74153]: (m1_pre_topc(A_74153, g1_pre_topc(k2_struct_0('#skF_53'), u1_pre_topc('#skF_53'))) | ~m1_pre_topc(A_74153, '#skF_53') | ~l1_pre_topc('#skF_53') | ~l1_pre_topc(A_74153))), inference(superposition, [status(thm), theory('equality')], [c_1896, c_14931])).
% 22.64/10.67  tff(c_15010, plain, (![A_74232]: (m1_pre_topc(A_74232, '#skF_54') | ~m1_pre_topc(A_74232, '#skF_53') | ~l1_pre_topc(A_74232))), inference(demodulation, [status(thm), theory('equality')], [c_1881, c_1967, c_14957])).
% 22.64/10.67  tff(c_1888, plain, (u1_struct_0('#skF_54')=k2_struct_0('#skF_54')), inference(resolution, [status(thm)], [c_1878, c_1030])).
% 22.64/10.67  tff(c_6639, plain, (![B_1488, A_1489]: (r1_tarski(u1_struct_0(B_1488), u1_struct_0(A_1489)) | ~m1_pre_topc(B_1488, A_1489) | ~l1_pre_topc(A_1489))), inference(cnfTransformation, [status(thm)], [f_904])).
% 22.64/10.67  tff(c_6659, plain, (![B_1488]: (r1_tarski(u1_struct_0(B_1488), k2_struct_0('#skF_54')) | ~m1_pre_topc(B_1488, '#skF_54') | ~l1_pre_topc('#skF_54'))), inference(superposition, [status(thm), theory('equality')], [c_1888, c_6639])).
% 22.64/10.67  tff(c_9718, plain, (![B_33364]: (r1_tarski(u1_struct_0(B_33364), k2_struct_0('#skF_54')) | ~m1_pre_topc(B_33364, '#skF_54'))), inference(demodulation, [status(thm), theory('equality')], [c_1878, c_6659])).
% 22.64/10.67  tff(c_9735, plain, (r1_tarski(k2_struct_0('#skF_53'), k2_struct_0('#skF_54')) | ~m1_pre_topc('#skF_53', '#skF_54')), inference(superposition, [status(thm), theory('equality')], [c_1896, c_9718])).
% 22.64/10.67  tff(c_14726, plain, (~m1_pre_topc('#skF_53', '#skF_54')), inference(splitLeft, [status(thm)], [c_9735])).
% 22.64/10.67  tff(c_15013, plain, (~m1_pre_topc('#skF_53', '#skF_53') | ~l1_pre_topc('#skF_53')), inference(resolution, [status(thm)], [c_15010, c_14726])).
% 22.64/10.67  tff(c_15048, plain, (~m1_pre_topc('#skF_53', '#skF_53')), inference(demodulation, [status(thm), theory('equality')], [c_1881, c_15013])).
% 22.64/10.67  tff(c_15077, plain, (~l1_pre_topc('#skF_53')), inference(resolution, [status(thm)], [c_544, c_15048])).
% 22.64/10.67  tff(c_15084, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1881, c_15077])).
% 22.64/10.67  tff(c_15085, plain, (r1_tarski(k2_struct_0('#skF_53'), k2_struct_0('#skF_54'))), inference(splitRight, [status(thm)], [c_9735])).
% 22.64/10.67  tff(c_12602, plain, (![B_67639, A_67640]: (m1_pre_topc(B_67639, A_67640) | ~m1_pre_topc(B_67639, g1_pre_topc(u1_struct_0(A_67640), u1_pre_topc(A_67640))) | ~l1_pre_topc(A_67640))), inference(cnfTransformation, [status(thm)], [f_633])).
% 22.64/10.67  tff(c_12614, plain, (![B_67639]: (m1_pre_topc(B_67639, '#skF_53') | ~m1_pre_topc(B_67639, g1_pre_topc(k2_struct_0('#skF_53'), u1_pre_topc('#skF_53'))) | ~l1_pre_topc('#skF_53'))), inference(superposition, [status(thm), theory('equality')], [c_1896, c_12602])).
% 22.64/10.67  tff(c_12671, plain, (![B_67718]: (m1_pre_topc(B_67718, '#skF_53') | ~m1_pre_topc(B_67718, '#skF_54'))), inference(demodulation, [status(thm), theory('equality')], [c_1881, c_1967, c_12614])).
% 22.64/10.67  tff(c_12679, plain, (m1_pre_topc('#skF_54', '#skF_53') | ~l1_pre_topc('#skF_54')), inference(resolution, [status(thm)], [c_544, c_12671])).
% 22.64/10.67  tff(c_12685, plain, (m1_pre_topc('#skF_54', '#skF_53')), inference(demodulation, [status(thm), theory('equality')], [c_1878, c_12679])).
% 22.64/10.67  tff(c_6665, plain, (![B_1488]: (r1_tarski(u1_struct_0(B_1488), k2_struct_0('#skF_53')) | ~m1_pre_topc(B_1488, '#skF_53') | ~l1_pre_topc('#skF_53'))), inference(superposition, [status(thm), theory('equality')], [c_1896, c_6639])).
% 22.64/10.67  tff(c_7067, plain, (![B_1496]: (r1_tarski(u1_struct_0(B_1496), k2_struct_0('#skF_53')) | ~m1_pre_topc(B_1496, '#skF_53'))), inference(demodulation, [status(thm), theory('equality')], [c_1881, c_6665])).
% 22.64/10.67  tff(c_7081, plain, (r1_tarski(k2_struct_0('#skF_54'), k2_struct_0('#skF_53')) | ~m1_pre_topc('#skF_54', '#skF_53')), inference(superposition, [status(thm), theory('equality')], [c_1888, c_7067])).
% 22.64/10.67  tff(c_17611, plain, (r1_tarski(k2_struct_0('#skF_54'), k2_struct_0('#skF_53'))), inference(demodulation, [status(thm), theory('equality')], [c_12685, c_7081])).
% 22.64/10.67  tff(c_10, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 22.64/10.67  tff(c_17618, plain, (k2_struct_0('#skF_54')=k2_struct_0('#skF_53') | ~r1_tarski(k2_struct_0('#skF_53'), k2_struct_0('#skF_54'))), inference(resolution, [status(thm)], [c_17611, c_10])).
% 22.64/10.67  tff(c_17630, plain, (k2_struct_0('#skF_54')=k2_struct_0('#skF_53')), inference(demodulation, [status(thm), theory('equality')], [c_15085, c_17618])).
% 22.64/10.67  tff(c_472, plain, (![A_260]: (v3_pre_topc(k2_struct_0(A_260), A_260) | ~l1_pre_topc(A_260) | ~v2_pre_topc(A_260))), inference(cnfTransformation, [status(thm)], [f_762])).
% 22.64/10.67  tff(c_17686, plain, (v3_pre_topc(k2_struct_0('#skF_53'), '#skF_54') | ~l1_pre_topc('#skF_54') | ~v2_pre_topc('#skF_54')), inference(superposition, [status(thm), theory('equality')], [c_17630, c_472])).
% 22.64/10.67  tff(c_17701, plain, (v3_pre_topc(k2_struct_0('#skF_53'), '#skF_54')), inference(demodulation, [status(thm), theory('equality')], [c_3605, c_1878, c_17686])).
% 22.64/10.67  tff(c_14, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 22.64/10.67  tff(c_3434, plain, (![A_1405]: (m1_subset_1(k2_struct_0(A_1405), k1_zfmisc_1(u1_struct_0(A_1405))) | ~l1_struct_0(A_1405))), inference(cnfTransformation, [status(thm)], [f_509])).
% 22.64/10.67  tff(c_3449, plain, (m1_subset_1(k2_struct_0('#skF_53'), k1_zfmisc_1(k2_struct_0('#skF_53'))) | ~l1_struct_0('#skF_53')), inference(superposition, [status(thm), theory('equality')], [c_1896, c_3434])).
% 22.64/10.67  tff(c_3994, plain, (~l1_struct_0('#skF_53')), inference(splitLeft, [status(thm)], [c_3449])).
% 22.64/10.67  tff(c_4000, plain, (~l1_pre_topc('#skF_53')), inference(resolution, [status(thm)], [c_382, c_3994])).
% 22.64/10.67  tff(c_4005, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1881, c_4000])).
% 22.64/10.67  tff(c_4006, plain, (m1_subset_1(k2_struct_0('#skF_53'), k1_zfmisc_1(k2_struct_0('#skF_53')))), inference(splitRight, [status(thm)], [c_3449])).
% 22.64/10.67  tff(c_626, plain, (~v2_struct_0('#skF_51')), inference(cnfTransformation, [status(thm)], [f_1212])).
% 22.64/10.67  tff(c_620, plain, (~v2_struct_0('#skF_52')), inference(cnfTransformation, [status(thm)], [f_1212])).
% 22.64/10.67  tff(c_610, plain, (~v2_struct_0('#skF_54')), inference(cnfTransformation, [status(thm)], [f_1212])).
% 22.64/10.67  tff(c_590, plain, (~r1_tmap_1('#skF_54', '#skF_52', '#skF_55', '#skF_56')), inference(cnfTransformation, [status(thm)], [f_1212])).
% 22.64/10.67  tff(c_618, plain, (v2_pre_topc('#skF_52')), inference(cnfTransformation, [status(thm)], [f_1212])).
% 22.64/10.67  tff(c_616, plain, (l1_pre_topc('#skF_52')), inference(cnfTransformation, [status(thm)], [f_1212])).
% 22.64/10.67  tff(c_606, plain, (v1_funct_1('#skF_55')), inference(cnfTransformation, [status(thm)], [f_1212])).
% 22.64/10.67  tff(c_1305, plain, (![A_1313]: (u1_struct_0(A_1313)=k2_struct_0(A_1313) | ~l1_pre_topc(A_1313))), inference(resolution, [status(thm)], [c_382, c_1019])).
% 22.64/10.67  tff(c_1328, plain, (u1_struct_0('#skF_52')=k2_struct_0('#skF_52')), inference(resolution, [status(thm)], [c_616, c_1305])).
% 22.64/10.67  tff(c_604, plain, (v1_funct_2('#skF_55', u1_struct_0('#skF_54'), u1_struct_0('#skF_52'))), inference(cnfTransformation, [status(thm)], [f_1212])).
% 22.64/10.67  tff(c_1382, plain, (v1_funct_2('#skF_55', u1_struct_0('#skF_54'), k2_struct_0('#skF_52'))), inference(demodulation, [status(thm), theory('equality')], [c_1328, c_604])).
% 22.64/10.67  tff(c_1974, plain, (v1_funct_2('#skF_55', k2_struct_0('#skF_54'), k2_struct_0('#skF_52'))), inference(demodulation, [status(thm), theory('equality')], [c_1888, c_1382])).
% 22.64/10.67  tff(c_17668, plain, (v1_funct_2('#skF_55', k2_struct_0('#skF_53'), k2_struct_0('#skF_52'))), inference(demodulation, [status(thm), theory('equality')], [c_17630, c_1974])).
% 22.64/10.67  tff(c_17671, plain, (u1_struct_0('#skF_54')=k2_struct_0('#skF_53')), inference(demodulation, [status(thm), theory('equality')], [c_17630, c_1888])).
% 22.64/10.67  tff(c_602, plain, (m1_subset_1('#skF_55', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_54'), u1_struct_0('#skF_52'))))), inference(cnfTransformation, [status(thm)], [f_1212])).
% 22.64/10.67  tff(c_1381, plain, (m1_subset_1('#skF_55', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_54'), k2_struct_0('#skF_52'))))), inference(demodulation, [status(thm), theory('equality')], [c_1328, c_602])).
% 22.64/10.67  tff(c_1973, plain, (m1_subset_1('#skF_55', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_54'), k2_struct_0('#skF_52'))))), inference(demodulation, [status(thm), theory('equality')], [c_1888, c_1381])).
% 22.64/10.67  tff(c_17667, plain, (m1_subset_1('#skF_55', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_53'), k2_struct_0('#skF_52'))))), inference(demodulation, [status(thm), theory('equality')], [c_17630, c_1973])).
% 22.64/10.67  tff(c_15086, plain, (m1_pre_topc('#skF_53', '#skF_54')), inference(splitRight, [status(thm)], [c_9735])).
% 22.64/10.67  tff(c_592, plain, (r1_tmap_1('#skF_53', '#skF_52', k3_tmap_1('#skF_51', '#skF_52', '#skF_54', '#skF_53', '#skF_55'), '#skF_57')), inference(cnfTransformation, [status(thm)], [f_1212])).
% 22.64/10.67  tff(c_628, plain, (r1_tmap_1('#skF_53', '#skF_52', k3_tmap_1('#skF_51', '#skF_52', '#skF_54', '#skF_53', '#skF_55'), '#skF_56')), inference(demodulation, [status(thm), theory('equality')], [c_594, c_592])).
% 22.64/10.67  tff(c_31919, plain, (![H_109471, A_109472, E_109467, F_109469, C_109466, B_109468, D_109470]: (r1_tmap_1(D_109470, B_109468, E_109467, H_109471) | ~r1_tmap_1(C_109466, B_109468, k3_tmap_1(A_109472, B_109468, D_109470, C_109466, E_109467), H_109471) | ~r1_tarski(F_109469, u1_struct_0(C_109466)) | ~r2_hidden(H_109471, F_109469) | ~v3_pre_topc(F_109469, D_109470) | ~m1_subset_1(H_109471, u1_struct_0(C_109466)) | ~m1_subset_1(H_109471, u1_struct_0(D_109470)) | ~m1_subset_1(F_109469, k1_zfmisc_1(u1_struct_0(D_109470))) | ~m1_pre_topc(C_109466, D_109470) | ~m1_subset_1(E_109467, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_109470), u1_struct_0(B_109468)))) | ~v1_funct_2(E_109467, u1_struct_0(D_109470), u1_struct_0(B_109468)) | ~v1_funct_1(E_109467) | ~m1_pre_topc(D_109470, A_109472) | v2_struct_0(D_109470) | ~m1_pre_topc(C_109466, A_109472) | v2_struct_0(C_109466) | ~l1_pre_topc(B_109468) | ~v2_pre_topc(B_109468) | v2_struct_0(B_109468) | ~l1_pre_topc(A_109472) | ~v2_pre_topc(A_109472) | v2_struct_0(A_109472))), inference(cnfTransformation, [status(thm)], [f_1106])).
% 22.64/10.67  tff(c_31922, plain, (![F_109469]: (r1_tmap_1('#skF_54', '#skF_52', '#skF_55', '#skF_56') | ~r1_tarski(F_109469, u1_struct_0('#skF_53')) | ~r2_hidden('#skF_56', F_109469) | ~v3_pre_topc(F_109469, '#skF_54') | ~m1_subset_1('#skF_56', u1_struct_0('#skF_53')) | ~m1_subset_1('#skF_56', u1_struct_0('#skF_54')) | ~m1_subset_1(F_109469, k1_zfmisc_1(u1_struct_0('#skF_54'))) | ~m1_pre_topc('#skF_53', '#skF_54') | ~m1_subset_1('#skF_55', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_54'), u1_struct_0('#skF_52')))) | ~v1_funct_2('#skF_55', u1_struct_0('#skF_54'), u1_struct_0('#skF_52')) | ~v1_funct_1('#skF_55') | ~m1_pre_topc('#skF_54', '#skF_51') | v2_struct_0('#skF_54') | ~m1_pre_topc('#skF_53', '#skF_51') | v2_struct_0('#skF_53') | ~l1_pre_topc('#skF_52') | ~v2_pre_topc('#skF_52') | v2_struct_0('#skF_52') | ~l1_pre_topc('#skF_51') | ~v2_pre_topc('#skF_51') | v2_struct_0('#skF_51'))), inference(resolution, [status(thm)], [c_628, c_31919])).
% 22.64/10.67  tff(c_31925, plain, (![F_109469]: (r1_tmap_1('#skF_54', '#skF_52', '#skF_55', '#skF_56') | ~r1_tarski(F_109469, k2_struct_0('#skF_53')) | ~r2_hidden('#skF_56', F_109469) | ~v3_pre_topc(F_109469, '#skF_54') | ~m1_subset_1(F_109469, k1_zfmisc_1(k2_struct_0('#skF_53'))) | v2_struct_0('#skF_54') | v2_struct_0('#skF_53') | v2_struct_0('#skF_52') | v2_struct_0('#skF_51'))), inference(demodulation, [status(thm), theory('equality')], [c_624, c_622, c_618, c_616, c_612, c_608, c_606, c_17668, c_1328, c_17671, c_17667, c_1328, c_17671, c_15086, c_17671, c_1968, c_17671, c_1968, c_1896, c_1896, c_31922])).
% 22.64/10.67  tff(c_31937, plain, (![F_109781]: (~r1_tarski(F_109781, k2_struct_0('#skF_53')) | ~r2_hidden('#skF_56', F_109781) | ~v3_pre_topc(F_109781, '#skF_54') | ~m1_subset_1(F_109781, k1_zfmisc_1(k2_struct_0('#skF_53'))))), inference(negUnitSimplification, [status(thm)], [c_626, c_620, c_614, c_610, c_590, c_31925])).
% 22.64/10.67  tff(c_32001, plain, (~r1_tarski(k2_struct_0('#skF_53'), k2_struct_0('#skF_53')) | ~r2_hidden('#skF_56', k2_struct_0('#skF_53')) | ~v3_pre_topc(k2_struct_0('#skF_53'), '#skF_54')), inference(resolution, [status(thm)], [c_4006, c_31937])).
% 22.64/10.67  tff(c_32073, plain, (~r2_hidden('#skF_56', k2_struct_0('#skF_53'))), inference(demodulation, [status(thm), theory('equality')], [c_17701, c_14, c_32001])).
% 22.64/10.67  tff(c_32088, plain, (v1_xboole_0(k2_struct_0('#skF_53')) | ~m1_subset_1('#skF_56', k2_struct_0('#skF_53'))), inference(resolution, [status(thm)], [c_76, c_32073])).
% 22.64/10.67  tff(c_32091, plain, (v1_xboole_0(k2_struct_0('#skF_53'))), inference(demodulation, [status(thm), theory('equality')], [c_1968, c_32088])).
% 22.64/10.67  tff(c_32093, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1966, c_32091])).
% 22.64/10.67  tff(c_32095, plain, (v1_xboole_0(u1_struct_0('#skF_53'))), inference(splitRight, [status(thm)], [c_1379])).
% 22.64/10.67  tff(c_740, plain, (![A_1262]: (k1_xboole_0=A_1262 | ~v1_xboole_0(A_1262))), inference(cnfTransformation, [status(thm)], [f_64])).
% 22.64/10.67  tff(c_755, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_6, c_740])).
% 22.64/10.67  tff(c_24, plain, (![A_8]: (k1_xboole_0=A_8 | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_64])).
% 22.64/10.67  tff(c_758, plain, (![A_8]: (A_8='#skF_1' | ~v1_xboole_0(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_755, c_24])).
% 22.64/10.67  tff(c_32155, plain, (u1_struct_0('#skF_53')='#skF_1'), inference(resolution, [status(thm)], [c_32095, c_758])).
% 22.64/10.67  tff(c_32365, plain, (u1_struct_0('#skF_53')=k2_struct_0('#skF_53')), inference(resolution, [status(thm)], [c_32354, c_1030])).
% 22.64/10.67  tff(c_32370, plain, (k2_struct_0('#skF_53')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32155, c_32365])).
% 22.64/10.67  tff(c_396, plain, (![A_182]: (~v1_xboole_0(k2_struct_0(A_182)) | ~l1_struct_0(A_182) | v2_struct_0(A_182))), inference(cnfTransformation, [status(thm)], [f_547])).
% 22.64/10.67  tff(c_32375, plain, (~v1_xboole_0('#skF_1') | ~l1_struct_0('#skF_53') | v2_struct_0('#skF_53')), inference(superposition, [status(thm), theory('equality')], [c_32370, c_396])).
% 22.64/10.67  tff(c_32379, plain, (~l1_struct_0('#skF_53') | v2_struct_0('#skF_53')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_32375])).
% 22.64/10.67  tff(c_32380, plain, (~l1_struct_0('#skF_53')), inference(negUnitSimplification, [status(thm)], [c_614, c_32379])).
% 22.64/10.67  tff(c_32387, plain, (~l1_pre_topc('#skF_53')), inference(resolution, [status(thm)], [c_382, c_32380])).
% 22.64/10.67  tff(c_32392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32354, c_32387])).
% 22.64/10.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.64/10.67  
% 22.64/10.67  Inference rules
% 22.64/10.67  ----------------------
% 22.64/10.67  #Ref     : 2
% 22.64/10.67  #Sup     : 6222
% 22.64/10.67  #Fact    : 0
% 22.64/10.67  #Define  : 0
% 22.64/10.67  #Split   : 206
% 22.64/10.67  #Chain   : 0
% 22.64/10.67  #Close   : 0
% 22.64/10.67  
% 22.64/10.67  Ordering : KBO
% 22.64/10.67  
% 22.64/10.67  Simplification rules
% 22.64/10.67  ----------------------
% 22.64/10.67  #Subsume      : 1739
% 22.64/10.67  #Demod        : 3955
% 22.64/10.67  #Tautology    : 1136
% 22.64/10.67  #SimpNegUnit  : 244
% 22.64/10.67  #BackRed      : 89
% 22.64/10.67  
% 22.64/10.67  #Partial instantiations: 109278
% 22.64/10.67  #Strategies tried      : 1
% 22.64/10.67  
% 22.64/10.67  Timing (in seconds)
% 22.64/10.67  ----------------------
% 22.64/10.67  Preprocessing        : 0.73
% 22.64/10.67  Parsing              : 0.33
% 22.64/10.67  CNF conversion       : 0.12
% 22.64/10.67  Main loop            : 9.14
% 22.64/10.67  Inferencing          : 2.32
% 22.64/10.67  Reduction            : 4.16
% 22.64/10.67  Demodulation         : 3.14
% 22.64/10.67  BG Simplification    : 0.15
% 22.64/10.67  Subsumption          : 1.95
% 22.64/10.67  Abstraction          : 0.13
% 22.64/10.67  MUC search           : 0.00
% 22.64/10.67  Cooper               : 0.00
% 22.64/10.67  Total                : 9.91
% 22.64/10.67  Index Insertion      : 0.00
% 22.64/10.67  Index Deletion       : 0.00
% 22.64/10.67  Index Matching       : 0.00
% 22.64/10.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
