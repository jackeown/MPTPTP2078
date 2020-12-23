%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:06 EST 2020

% Result     : Theorem 8.19s
% Output     : CNFRefutation 8.19s
% Verified   : 
% Statistics : Number of formulae       :  185 (7682 expanded)
%              Number of leaves         :   33 (2630 expanded)
%              Depth                    :   28
%              Number of atoms          :  582 (38924 expanded)
%              Number of equality atoms :   88 (10025 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_orders_3 > v1_funct_2 > r1_orders_2 > m1_subset_1 > v2_struct_0 > v1_funct_1 > l1_orders_2 > k2_zfmisc_1 > k1_funct_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k7_lattice3 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(v5_orders_3,type,(
    v5_orders_3: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff(k7_lattice3,type,(
    k7_lattice3: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_145,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( l1_orders_2(B)
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & l1_orders_2(C) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & l1_orders_2(D) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                       => ! [F] :
                            ( ( v1_funct_1(F)
                              & v1_funct_2(F,u1_struct_0(C),u1_struct_0(D))
                              & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(D)))) )
                           => ( ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(C),u1_orders_2(C))
                                & g1_orders_2(u1_struct_0(B),u1_orders_2(B)) = g1_orders_2(u1_struct_0(D),u1_orders_2(D))
                                & E = F
                                & v5_orders_3(E,A,B) )
                             => v5_orders_3(F,C,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_waybel_9)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k7_lattice3(k7_lattice3(A)) = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_lattice3)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v5_orders_3(C,A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ! [E] :
                        ( m1_subset_1(E,u1_struct_0(A))
                       => ( r1_orders_2(A,D,E)
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(B))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(B))
                                 => ( ( F = k1_funct_1(C,D)
                                      & G = k1_funct_1(C,E) )
                                   => r1_orders_2(B,F,G) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_orders_3)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(B))
                         => ( ( C = E
                              & D = F
                              & g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(B),u1_orders_2(B))
                              & r1_orders_2(A,C,D) )
                           => r1_orders_2(B,E,F) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l20_yellow_6)).

tff(c_34,plain,(
    '#skF_10' = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_30,plain,(
    ~ v5_orders_3('#skF_10','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_67,plain,(
    ~ v5_orders_3('#skF_9','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30])).

tff(c_56,plain,(
    l1_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_52,plain,(
    l1_orders_2('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_50,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_62,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_38,plain,(
    g1_orders_2(u1_struct_0('#skF_7'),u1_orders_2('#skF_7')) = g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_8,plain,(
    ! [A_8] :
      ( g1_orders_2(u1_struct_0(A_8),u1_orders_2(A_8)) = k7_lattice3(k7_lattice3(A_8))
      | ~ l1_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_119,plain,
    ( g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5')) = k7_lattice3(k7_lattice3('#skF_7'))
    | ~ l1_orders_2('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_8])).

tff(c_126,plain,(
    g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5')) = k7_lattice3(k7_lattice3('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_119])).

tff(c_166,plain,
    ( k7_lattice3(k7_lattice3('#skF_7')) = k7_lattice3(k7_lattice3('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_8])).

tff(c_173,plain,(
    k7_lattice3(k7_lattice3('#skF_7')) = k7_lattice3(k7_lattice3('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_166])).

tff(c_123,plain,
    ( g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5')) = k7_lattice3(k7_lattice3('#skF_7'))
    | ~ l1_orders_2('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_38])).

tff(c_129,plain,(
    g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5')) = k7_lattice3(k7_lattice3('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_123])).

tff(c_184,plain,(
    g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5')) = k7_lattice3(k7_lattice3('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_129])).

tff(c_2,plain,(
    ! [A_1] :
      ( m1_subset_1(u1_orders_2(A_1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1),u1_struct_0(A_1))))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_162,plain,(
    g1_orders_2(u1_struct_0('#skF_7'),u1_orders_2('#skF_7')) = k7_lattice3(k7_lattice3('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_38])).

tff(c_201,plain,(
    g1_orders_2(u1_struct_0('#skF_7'),u1_orders_2('#skF_7')) = k7_lattice3(k7_lattice3('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_162])).

tff(c_247,plain,(
    ! [C_378,A_379,D_380,B_381] :
      ( C_378 = A_379
      | g1_orders_2(C_378,D_380) != g1_orders_2(A_379,B_381)
      | ~ m1_subset_1(B_381,k1_zfmisc_1(k2_zfmisc_1(A_379,A_379))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_560,plain,(
    ! [A_401,B_402] :
      ( u1_struct_0('#skF_7') = A_401
      | k7_lattice3(k7_lattice3('#skF_5')) != g1_orders_2(A_401,B_402)
      | ~ m1_subset_1(B_402,k1_zfmisc_1(k2_zfmisc_1(A_401,A_401))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_247])).

tff(c_577,plain,(
    ! [A_403] :
      ( u1_struct_0(A_403) = u1_struct_0('#skF_7')
      | g1_orders_2(u1_struct_0(A_403),u1_orders_2(A_403)) != k7_lattice3(k7_lattice3('#skF_5'))
      | ~ l1_orders_2(A_403) ) ),
    inference(resolution,[status(thm)],[c_2,c_560])).

tff(c_586,plain,
    ( u1_struct_0('#skF_7') = u1_struct_0('#skF_5')
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_577])).

tff(c_600,plain,(
    u1_struct_0('#skF_7') = u1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_586])).

tff(c_42,plain,(
    v1_funct_2('#skF_10',u1_struct_0('#skF_7'),u1_struct_0('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_64,plain,(
    v1_funct_2('#skF_9',u1_struct_0('#skF_7'),u1_struct_0('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_42])).

tff(c_609,plain,(
    v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_64])).

tff(c_40,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_8')))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_65,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_8')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_40])).

tff(c_608,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_8')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_65])).

tff(c_18,plain,(
    ! [A_9,B_133,C_195] :
      ( m1_subset_1('#skF_4'(A_9,B_133,C_195),u1_struct_0(B_133))
      | v5_orders_3(C_195,A_9,B_133)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9),u1_struct_0(B_133))))
      | ~ v1_funct_2(C_195,u1_struct_0(A_9),u1_struct_0(B_133))
      | ~ v1_funct_1(C_195)
      | ~ l1_orders_2(B_133)
      | ~ l1_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_669,plain,
    ( m1_subset_1('#skF_4'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | v5_orders_3('#skF_9','#skF_5','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_608,c_18])).

tff(c_678,plain,
    ( m1_subset_1('#skF_4'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | v5_orders_3('#skF_9','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_50,c_609,c_669])).

tff(c_757,plain,(
    v5_orders_3('#skF_9','#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_678])).

tff(c_386,plain,(
    ! [A_389,B_390,C_391] :
      ( m1_subset_1('#skF_3'(A_389,B_390,C_391),u1_struct_0(B_390))
      | v5_orders_3(C_391,A_389,B_390)
      | ~ m1_subset_1(C_391,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_389),u1_struct_0(B_390))))
      | ~ v1_funct_2(C_391,u1_struct_0(A_389),u1_struct_0(B_390))
      | ~ v1_funct_1(C_391)
      | ~ l1_orders_2(B_390)
      | ~ l1_orders_2(A_389) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_392,plain,
    ( m1_subset_1('#skF_3'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | v5_orders_3('#skF_9','#skF_7','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_7'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_65,c_386])).

tff(c_401,plain,
    ( m1_subset_1('#skF_3'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | v5_orders_3('#skF_9','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_64,c_392])).

tff(c_402,plain,(
    m1_subset_1('#skF_3'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_401])).

tff(c_320,plain,(
    ! [A_385,B_386,C_387] :
      ( m1_subset_1('#skF_4'(A_385,B_386,C_387),u1_struct_0(B_386))
      | v5_orders_3(C_387,A_385,B_386)
      | ~ m1_subset_1(C_387,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_385),u1_struct_0(B_386))))
      | ~ v1_funct_2(C_387,u1_struct_0(A_385),u1_struct_0(B_386))
      | ~ v1_funct_1(C_387)
      | ~ l1_orders_2(B_386)
      | ~ l1_orders_2(A_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_324,plain,
    ( m1_subset_1('#skF_4'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | v5_orders_3('#skF_9','#skF_7','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_7'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_65,c_320])).

tff(c_330,plain,
    ( m1_subset_1('#skF_4'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | v5_orders_3('#skF_9','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_64,c_324])).

tff(c_331,plain,(
    m1_subset_1('#skF_4'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_330])).

tff(c_1224,plain,(
    ! [C_434,A_435,B_436] :
      ( k1_funct_1(C_434,'#skF_1'(A_435,B_436,C_434)) = '#skF_3'(A_435,B_436,C_434)
      | v5_orders_3(C_434,A_435,B_436)
      | ~ m1_subset_1(C_434,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_435),u1_struct_0(B_436))))
      | ~ v1_funct_2(C_434,u1_struct_0(A_435),u1_struct_0(B_436))
      | ~ v1_funct_1(C_434)
      | ~ l1_orders_2(B_436)
      | ~ l1_orders_2(A_435) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1236,plain,(
    ! [C_434,B_436] :
      ( k1_funct_1(C_434,'#skF_1'('#skF_7',B_436,C_434)) = '#skF_3'('#skF_7',B_436,C_434)
      | v5_orders_3(C_434,'#skF_7',B_436)
      | ~ m1_subset_1(C_434,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_436))))
      | ~ v1_funct_2(C_434,u1_struct_0('#skF_7'),u1_struct_0(B_436))
      | ~ v1_funct_1(C_434)
      | ~ l1_orders_2(B_436)
      | ~ l1_orders_2('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_600,c_1224])).

tff(c_3670,plain,(
    ! [C_634,B_635] :
      ( k1_funct_1(C_634,'#skF_1'('#skF_7',B_635,C_634)) = '#skF_3'('#skF_7',B_635,C_634)
      | v5_orders_3(C_634,'#skF_7',B_635)
      | ~ m1_subset_1(C_634,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_635))))
      | ~ v1_funct_2(C_634,u1_struct_0('#skF_5'),u1_struct_0(B_635))
      | ~ v1_funct_1(C_634)
      | ~ l1_orders_2(B_635) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_600,c_1236])).

tff(c_3676,plain,
    ( k1_funct_1('#skF_9','#skF_1'('#skF_7','#skF_8','#skF_9')) = '#skF_3'('#skF_7','#skF_8','#skF_9')
    | v5_orders_3('#skF_9','#skF_7','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_608,c_3670])).

tff(c_3689,plain,
    ( k1_funct_1('#skF_9','#skF_1'('#skF_7','#skF_8','#skF_9')) = '#skF_3'('#skF_7','#skF_8','#skF_9')
    | v5_orders_3('#skF_9','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_609,c_3676])).

tff(c_3690,plain,(
    k1_funct_1('#skF_9','#skF_1'('#skF_7','#skF_8','#skF_9')) = '#skF_3'('#skF_7','#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_3689])).

tff(c_761,plain,(
    ! [C_409,A_410,B_411] :
      ( k1_funct_1(C_409,'#skF_2'(A_410,B_411,C_409)) = '#skF_4'(A_410,B_411,C_409)
      | v5_orders_3(C_409,A_410,B_411)
      | ~ m1_subset_1(C_409,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_410),u1_struct_0(B_411))))
      | ~ v1_funct_2(C_409,u1_struct_0(A_410),u1_struct_0(B_411))
      | ~ v1_funct_1(C_409)
      | ~ l1_orders_2(B_411)
      | ~ l1_orders_2(A_410) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_767,plain,(
    ! [C_409,B_411] :
      ( k1_funct_1(C_409,'#skF_2'('#skF_7',B_411,C_409)) = '#skF_4'('#skF_7',B_411,C_409)
      | v5_orders_3(C_409,'#skF_7',B_411)
      | ~ m1_subset_1(C_409,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_411))))
      | ~ v1_funct_2(C_409,u1_struct_0('#skF_7'),u1_struct_0(B_411))
      | ~ v1_funct_1(C_409)
      | ~ l1_orders_2(B_411)
      | ~ l1_orders_2('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_600,c_761])).

tff(c_4022,plain,(
    ! [C_660,B_661] :
      ( k1_funct_1(C_660,'#skF_2'('#skF_7',B_661,C_660)) = '#skF_4'('#skF_7',B_661,C_660)
      | v5_orders_3(C_660,'#skF_7',B_661)
      | ~ m1_subset_1(C_660,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_661))))
      | ~ v1_funct_2(C_660,u1_struct_0('#skF_5'),u1_struct_0(B_661))
      | ~ v1_funct_1(C_660)
      | ~ l1_orders_2(B_661) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_600,c_767])).

tff(c_4028,plain,
    ( k1_funct_1('#skF_9','#skF_2'('#skF_7','#skF_8','#skF_9')) = '#skF_4'('#skF_7','#skF_8','#skF_9')
    | v5_orders_3('#skF_9','#skF_7','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_608,c_4022])).

tff(c_4041,plain,
    ( k1_funct_1('#skF_9','#skF_2'('#skF_7','#skF_8','#skF_9')) = '#skF_4'('#skF_7','#skF_8','#skF_9')
    | v5_orders_3('#skF_9','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_609,c_4028])).

tff(c_4042,plain,(
    k1_funct_1('#skF_9','#skF_2'('#skF_7','#skF_8','#skF_9')) = '#skF_4'('#skF_7','#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_4041])).

tff(c_679,plain,(
    ! [A_404,B_405,C_406] :
      ( m1_subset_1('#skF_1'(A_404,B_405,C_406),u1_struct_0(A_404))
      | v5_orders_3(C_406,A_404,B_405)
      | ~ m1_subset_1(C_406,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_404),u1_struct_0(B_405))))
      | ~ v1_funct_2(C_406,u1_struct_0(A_404),u1_struct_0(B_405))
      | ~ v1_funct_1(C_406)
      | ~ l1_orders_2(B_405)
      | ~ l1_orders_2(A_404) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_683,plain,(
    ! [B_405,C_406] :
      ( m1_subset_1('#skF_1'('#skF_7',B_405,C_406),u1_struct_0('#skF_7'))
      | v5_orders_3(C_406,'#skF_7',B_405)
      | ~ m1_subset_1(C_406,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_405))))
      | ~ v1_funct_2(C_406,u1_struct_0('#skF_7'),u1_struct_0(B_405))
      | ~ v1_funct_1(C_406)
      | ~ l1_orders_2(B_405)
      | ~ l1_orders_2('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_600,c_679])).

tff(c_3284,plain,(
    ! [B_602,C_603] :
      ( m1_subset_1('#skF_1'('#skF_7',B_602,C_603),u1_struct_0('#skF_5'))
      | v5_orders_3(C_603,'#skF_7',B_602)
      | ~ m1_subset_1(C_603,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_602))))
      | ~ v1_funct_2(C_603,u1_struct_0('#skF_5'),u1_struct_0(B_602))
      | ~ v1_funct_1(C_603)
      | ~ l1_orders_2(B_602) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_600,c_600,c_683])).

tff(c_3293,plain,
    ( m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
    | v5_orders_3('#skF_9','#skF_7','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_608,c_3284])).

tff(c_3308,plain,
    ( m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
    | v5_orders_3('#skF_9','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_609,c_3293])).

tff(c_3309,plain,(
    m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_3308])).

tff(c_515,plain,(
    ! [A_397,B_398,C_399] :
      ( m1_subset_1('#skF_2'(A_397,B_398,C_399),u1_struct_0(A_397))
      | v5_orders_3(C_399,A_397,B_398)
      | ~ m1_subset_1(C_399,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_397),u1_struct_0(B_398))))
      | ~ v1_funct_2(C_399,u1_struct_0(A_397),u1_struct_0(B_398))
      | ~ v1_funct_1(C_399)
      | ~ l1_orders_2(B_398)
      | ~ l1_orders_2(A_397) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_523,plain,
    ( m1_subset_1('#skF_2'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | v5_orders_3('#skF_9','#skF_7','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_7'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_65,c_515])).

tff(c_535,plain,
    ( m1_subset_1('#skF_2'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | v5_orders_3('#skF_9','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_64,c_523])).

tff(c_536,plain,(
    m1_subset_1('#skF_2'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_535])).

tff(c_605,plain,(
    m1_subset_1('#skF_2'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_536])).

tff(c_222,plain,(
    ! [D_374,B_375,C_376,A_377] :
      ( D_374 = B_375
      | g1_orders_2(C_376,D_374) != g1_orders_2(A_377,B_375)
      | ~ m1_subset_1(B_375,k1_zfmisc_1(k2_zfmisc_1(A_377,A_377))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_406,plain,(
    ! [B_392,A_393] :
      ( u1_orders_2('#skF_5') = B_392
      | k7_lattice3(k7_lattice3('#skF_5')) != g1_orders_2(A_393,B_392)
      | ~ m1_subset_1(B_392,k1_zfmisc_1(k2_zfmisc_1(A_393,A_393))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_222])).

tff(c_416,plain,(
    ! [A_394] :
      ( u1_orders_2(A_394) = u1_orders_2('#skF_5')
      | g1_orders_2(u1_struct_0(A_394),u1_orders_2(A_394)) != k7_lattice3(k7_lattice3('#skF_5'))
      | ~ l1_orders_2(A_394) ) ),
    inference(resolution,[status(thm)],[c_2,c_406])).

tff(c_422,plain,
    ( u1_orders_2('#skF_7') = u1_orders_2('#skF_5')
    | ~ l1_orders_2('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_416])).

tff(c_436,plain,(
    u1_orders_2('#skF_7') = u1_orders_2('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_422])).

tff(c_1051,plain,(
    ! [A_418,B_419,C_420] :
      ( r1_orders_2(A_418,'#skF_1'(A_418,B_419,C_420),'#skF_2'(A_418,B_419,C_420))
      | v5_orders_3(C_420,A_418,B_419)
      | ~ m1_subset_1(C_420,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_418),u1_struct_0(B_419))))
      | ~ v1_funct_2(C_420,u1_struct_0(A_418),u1_struct_0(B_419))
      | ~ v1_funct_1(C_420)
      | ~ l1_orders_2(B_419)
      | ~ l1_orders_2(A_418) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1063,plain,(
    ! [B_419,C_420] :
      ( r1_orders_2('#skF_7','#skF_1'('#skF_7',B_419,C_420),'#skF_2'('#skF_7',B_419,C_420))
      | v5_orders_3(C_420,'#skF_7',B_419)
      | ~ m1_subset_1(C_420,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_419))))
      | ~ v1_funct_2(C_420,u1_struct_0('#skF_7'),u1_struct_0(B_419))
      | ~ v1_funct_1(C_420)
      | ~ l1_orders_2(B_419)
      | ~ l1_orders_2('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_600,c_1051])).

tff(c_3711,plain,(
    ! [B_637,C_638] :
      ( r1_orders_2('#skF_7','#skF_1'('#skF_7',B_637,C_638),'#skF_2'('#skF_7',B_637,C_638))
      | v5_orders_3(C_638,'#skF_7',B_637)
      | ~ m1_subset_1(C_638,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_637))))
      | ~ v1_funct_2(C_638,u1_struct_0('#skF_5'),u1_struct_0(B_637))
      | ~ v1_funct_1(C_638)
      | ~ l1_orders_2(B_637) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_600,c_1063])).

tff(c_3717,plain,
    ( r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_2'('#skF_7','#skF_8','#skF_9'))
    | v5_orders_3('#skF_9','#skF_7','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_608,c_3711])).

tff(c_3730,plain,
    ( r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_2'('#skF_7','#skF_8','#skF_9'))
    | v5_orders_3('#skF_9','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_609,c_3717])).

tff(c_3731,plain,(
    r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_2'('#skF_7','#skF_8','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_3730])).

tff(c_28,plain,(
    ! [B_284,E_312,F_314,A_252] :
      ( r1_orders_2(B_284,E_312,F_314)
      | ~ r1_orders_2(A_252,E_312,F_314)
      | g1_orders_2(u1_struct_0(B_284),u1_orders_2(B_284)) != g1_orders_2(u1_struct_0(A_252),u1_orders_2(A_252))
      | ~ m1_subset_1(F_314,u1_struct_0(B_284))
      | ~ m1_subset_1(E_312,u1_struct_0(B_284))
      | ~ m1_subset_1(F_314,u1_struct_0(A_252))
      | ~ m1_subset_1(E_312,u1_struct_0(A_252))
      | ~ l1_orders_2(B_284)
      | ~ l1_orders_2(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3740,plain,(
    ! [B_284] :
      ( r1_orders_2(B_284,'#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_2'('#skF_7','#skF_8','#skF_9'))
      | g1_orders_2(u1_struct_0(B_284),u1_orders_2(B_284)) != g1_orders_2(u1_struct_0('#skF_7'),u1_orders_2('#skF_7'))
      | ~ m1_subset_1('#skF_2'('#skF_7','#skF_8','#skF_9'),u1_struct_0(B_284))
      | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0(B_284))
      | ~ m1_subset_1('#skF_2'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
      | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
      | ~ l1_orders_2(B_284)
      | ~ l1_orders_2('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_3731,c_28])).

tff(c_3856,plain,(
    ! [B_648] :
      ( r1_orders_2(B_648,'#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_2'('#skF_7','#skF_8','#skF_9'))
      | g1_orders_2(u1_struct_0(B_648),u1_orders_2(B_648)) != k7_lattice3(k7_lattice3('#skF_5'))
      | ~ m1_subset_1('#skF_2'('#skF_7','#skF_8','#skF_9'),u1_struct_0(B_648))
      | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0(B_648))
      | ~ l1_orders_2(B_648) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3309,c_600,c_605,c_600,c_184,c_436,c_600,c_3740])).

tff(c_3866,plain,
    ( r1_orders_2('#skF_5','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_2'('#skF_7','#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_2'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_3856])).

tff(c_3881,plain,(
    r1_orders_2('#skF_5','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_2'('#skF_7','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3309,c_605,c_3866])).

tff(c_10,plain,(
    ! [B_133,E_234,D_226,C_195,A_9] :
      ( r1_orders_2(B_133,k1_funct_1(C_195,D_226),k1_funct_1(C_195,E_234))
      | ~ m1_subset_1(k1_funct_1(C_195,E_234),u1_struct_0(B_133))
      | ~ m1_subset_1(k1_funct_1(C_195,D_226),u1_struct_0(B_133))
      | ~ r1_orders_2(A_9,D_226,E_234)
      | ~ m1_subset_1(E_234,u1_struct_0(A_9))
      | ~ m1_subset_1(D_226,u1_struct_0(A_9))
      | ~ v5_orders_3(C_195,A_9,B_133)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9),u1_struct_0(B_133))))
      | ~ v1_funct_2(C_195,u1_struct_0(A_9),u1_struct_0(B_133))
      | ~ v1_funct_1(C_195)
      | ~ l1_orders_2(B_133)
      | ~ l1_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3885,plain,(
    ! [B_133,C_195] :
      ( r1_orders_2(B_133,k1_funct_1(C_195,'#skF_1'('#skF_7','#skF_8','#skF_9')),k1_funct_1(C_195,'#skF_2'('#skF_7','#skF_8','#skF_9')))
      | ~ m1_subset_1(k1_funct_1(C_195,'#skF_2'('#skF_7','#skF_8','#skF_9')),u1_struct_0(B_133))
      | ~ m1_subset_1(k1_funct_1(C_195,'#skF_1'('#skF_7','#skF_8','#skF_9')),u1_struct_0(B_133))
      | ~ m1_subset_1('#skF_2'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
      | ~ v5_orders_3(C_195,'#skF_5',B_133)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_133))))
      | ~ v1_funct_2(C_195,u1_struct_0('#skF_5'),u1_struct_0(B_133))
      | ~ v1_funct_1(C_195)
      | ~ l1_orders_2(B_133)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3881,c_10])).

tff(c_4309,plain,(
    ! [B_684,C_685] :
      ( r1_orders_2(B_684,k1_funct_1(C_685,'#skF_1'('#skF_7','#skF_8','#skF_9')),k1_funct_1(C_685,'#skF_2'('#skF_7','#skF_8','#skF_9')))
      | ~ m1_subset_1(k1_funct_1(C_685,'#skF_2'('#skF_7','#skF_8','#skF_9')),u1_struct_0(B_684))
      | ~ m1_subset_1(k1_funct_1(C_685,'#skF_1'('#skF_7','#skF_8','#skF_9')),u1_struct_0(B_684))
      | ~ v5_orders_3(C_685,'#skF_5',B_684)
      | ~ m1_subset_1(C_685,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_684))))
      | ~ v1_funct_2(C_685,u1_struct_0('#skF_5'),u1_struct_0(B_684))
      | ~ v1_funct_1(C_685)
      | ~ l1_orders_2(B_684) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3309,c_605,c_3885])).

tff(c_4316,plain,(
    ! [B_684] :
      ( r1_orders_2(B_684,k1_funct_1('#skF_9','#skF_1'('#skF_7','#skF_8','#skF_9')),'#skF_4'('#skF_7','#skF_8','#skF_9'))
      | ~ m1_subset_1(k1_funct_1('#skF_9','#skF_2'('#skF_7','#skF_8','#skF_9')),u1_struct_0(B_684))
      | ~ m1_subset_1(k1_funct_1('#skF_9','#skF_1'('#skF_7','#skF_8','#skF_9')),u1_struct_0(B_684))
      | ~ v5_orders_3('#skF_9','#skF_5',B_684)
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_684))))
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0(B_684))
      | ~ v1_funct_1('#skF_9')
      | ~ l1_orders_2(B_684) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4042,c_4309])).

tff(c_4326,plain,(
    ! [B_686] :
      ( r1_orders_2(B_686,'#skF_3'('#skF_7','#skF_8','#skF_9'),'#skF_4'('#skF_7','#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_4'('#skF_7','#skF_8','#skF_9'),u1_struct_0(B_686))
      | ~ m1_subset_1('#skF_3'('#skF_7','#skF_8','#skF_9'),u1_struct_0(B_686))
      | ~ v5_orders_3('#skF_9','#skF_5',B_686)
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_686))))
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0(B_686))
      | ~ l1_orders_2(B_686) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_3690,c_4042,c_3690,c_4316])).

tff(c_4332,plain,
    ( r1_orders_2('#skF_8','#skF_3'('#skF_7','#skF_8','#skF_9'),'#skF_4'('#skF_7','#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_4'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ v5_orders_3('#skF_9','#skF_5','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_608,c_4326])).

tff(c_4340,plain,(
    r1_orders_2('#skF_8','#skF_3'('#skF_7','#skF_8','#skF_9'),'#skF_4'('#skF_7','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_609,c_757,c_402,c_331,c_4332])).

tff(c_12,plain,(
    ! [B_133,A_9,C_195] :
      ( ~ r1_orders_2(B_133,'#skF_3'(A_9,B_133,C_195),'#skF_4'(A_9,B_133,C_195))
      | v5_orders_3(C_195,A_9,B_133)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9),u1_struct_0(B_133))))
      | ~ v1_funct_2(C_195,u1_struct_0(A_9),u1_struct_0(B_133))
      | ~ v1_funct_1(C_195)
      | ~ l1_orders_2(B_133)
      | ~ l1_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4358,plain,
    ( v5_orders_3('#skF_9','#skF_7','#skF_8')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_8'))))
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_7'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_4340,c_12])).

tff(c_4367,plain,(
    v5_orders_3('#skF_9','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_609,c_600,c_608,c_600,c_4358])).

tff(c_4369,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_4367])).

tff(c_4371,plain,(
    ~ v5_orders_3('#skF_9','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_678])).

tff(c_20,plain,(
    ! [A_9,B_133,C_195] :
      ( m1_subset_1('#skF_3'(A_9,B_133,C_195),u1_struct_0(B_133))
      | v5_orders_3(C_195,A_9,B_133)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9),u1_struct_0(B_133))))
      | ~ v1_funct_2(C_195,u1_struct_0(A_9),u1_struct_0(B_133))
      | ~ v1_funct_1(C_195)
      | ~ l1_orders_2(B_133)
      | ~ l1_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_667,plain,
    ( m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | v5_orders_3('#skF_9','#skF_5','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_608,c_20])).

tff(c_675,plain,
    ( m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | v5_orders_3('#skF_9','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_50,c_609,c_667])).

tff(c_4411,plain,(
    m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_4371,c_675])).

tff(c_4370,plain,(
    m1_subset_1('#skF_4'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_678])).

tff(c_60,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_76,plain,(
    ! [A_372] :
      ( g1_orders_2(u1_struct_0(A_372),u1_orders_2(A_372)) = k7_lattice3(k7_lattice3(A_372))
      | ~ l1_orders_2(A_372) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_36,plain,(
    g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) = g1_orders_2(u1_struct_0('#skF_8'),u1_orders_2('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_82,plain,
    ( g1_orders_2(u1_struct_0('#skF_8'),u1_orders_2('#skF_8')) = k7_lattice3(k7_lattice3('#skF_6'))
    | ~ l1_orders_2('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_36])).

tff(c_91,plain,(
    g1_orders_2(u1_struct_0('#skF_8'),u1_orders_2('#skF_8')) = k7_lattice3(k7_lattice3('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_82])).

tff(c_99,plain,
    ( k7_lattice3(k7_lattice3('#skF_6')) = k7_lattice3(k7_lattice3('#skF_8'))
    | ~ l1_orders_2('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_8])).

tff(c_106,plain,(
    k7_lattice3(k7_lattice3('#skF_6')) = k7_lattice3(k7_lattice3('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_99])).

tff(c_88,plain,
    ( g1_orders_2(u1_struct_0('#skF_8'),u1_orders_2('#skF_8')) = k7_lattice3(k7_lattice3('#skF_6'))
    | ~ l1_orders_2('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_76])).

tff(c_94,plain,(
    g1_orders_2(u1_struct_0('#skF_8'),u1_orders_2('#skF_8')) = k7_lattice3(k7_lattice3('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_88])).

tff(c_145,plain,(
    g1_orders_2(u1_struct_0('#skF_8'),u1_orders_2('#skF_8')) = k7_lattice3(k7_lattice3('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_94])).

tff(c_95,plain,(
    g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) = k7_lattice3(k7_lattice3('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_36])).

tff(c_130,plain,(
    g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) = k7_lattice3(k7_lattice3('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_95])).

tff(c_740,plain,(
    ! [A_407,B_408] :
      ( u1_struct_0('#skF_6') = A_407
      | k7_lattice3(k7_lattice3('#skF_8')) != g1_orders_2(A_407,B_408)
      | ~ m1_subset_1(B_408,k1_zfmisc_1(k2_zfmisc_1(A_407,A_407))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_247])).

tff(c_4455,plain,(
    ! [A_693] :
      ( u1_struct_0(A_693) = u1_struct_0('#skF_6')
      | g1_orders_2(u1_struct_0(A_693),u1_orders_2(A_693)) != k7_lattice3(k7_lattice3('#skF_8'))
      | ~ l1_orders_2(A_693) ) ),
    inference(resolution,[status(thm)],[c_2,c_740])).

tff(c_4470,plain,
    ( u1_struct_0('#skF_6') = u1_struct_0('#skF_8')
    | ~ l1_orders_2('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_4455])).

tff(c_4485,plain,(
    u1_struct_0('#skF_6') = u1_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4470])).

tff(c_268,plain,(
    ! [B_382,A_383] :
      ( u1_orders_2('#skF_8') = B_382
      | k7_lattice3(k7_lattice3('#skF_8')) != g1_orders_2(A_383,B_382)
      | ~ m1_subset_1(B_382,k1_zfmisc_1(k2_zfmisc_1(A_383,A_383))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_222])).

tff(c_273,plain,(
    ! [A_384] :
      ( u1_orders_2(A_384) = u1_orders_2('#skF_8')
      | g1_orders_2(u1_struct_0(A_384),u1_orders_2(A_384)) != k7_lattice3(k7_lattice3('#skF_8'))
      | ~ l1_orders_2(A_384) ) ),
    inference(resolution,[status(thm)],[c_2,c_268])).

tff(c_285,plain,
    ( u1_orders_2('#skF_6') = u1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_273])).

tff(c_299,plain,(
    u1_orders_2('#skF_6') = u1_orders_2('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_285])).

tff(c_32,plain,(
    v5_orders_3('#skF_9','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_4853,plain,(
    ! [C_714,A_715,B_716] :
      ( k1_funct_1(C_714,'#skF_1'(A_715,B_716,C_714)) = '#skF_3'(A_715,B_716,C_714)
      | v5_orders_3(C_714,A_715,B_716)
      | ~ m1_subset_1(C_714,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_715),u1_struct_0(B_716))))
      | ~ v1_funct_2(C_714,u1_struct_0(A_715),u1_struct_0(B_716))
      | ~ v1_funct_1(C_714)
      | ~ l1_orders_2(B_716)
      | ~ l1_orders_2(A_715) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4863,plain,
    ( k1_funct_1('#skF_9','#skF_1'('#skF_5','#skF_8','#skF_9')) = '#skF_3'('#skF_5','#skF_8','#skF_9')
    | v5_orders_3('#skF_9','#skF_5','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_608,c_4853])).

tff(c_4882,plain,
    ( k1_funct_1('#skF_9','#skF_1'('#skF_5','#skF_8','#skF_9')) = '#skF_3'('#skF_5','#skF_8','#skF_9')
    | v5_orders_3('#skF_9','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_50,c_609,c_4863])).

tff(c_4883,plain,(
    k1_funct_1('#skF_9','#skF_1'('#skF_5','#skF_8','#skF_9')) = '#skF_3'('#skF_5','#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_4371,c_4882])).

tff(c_4373,plain,(
    ! [C_687,A_688,B_689] :
      ( k1_funct_1(C_687,'#skF_2'(A_688,B_689,C_687)) = '#skF_4'(A_688,B_689,C_687)
      | v5_orders_3(C_687,A_688,B_689)
      | ~ m1_subset_1(C_687,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_688),u1_struct_0(B_689))))
      | ~ v1_funct_2(C_687,u1_struct_0(A_688),u1_struct_0(B_689))
      | ~ v1_funct_1(C_687)
      | ~ l1_orders_2(B_689)
      | ~ l1_orders_2(A_688) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4377,plain,
    ( k1_funct_1('#skF_9','#skF_2'('#skF_5','#skF_8','#skF_9')) = '#skF_4'('#skF_5','#skF_8','#skF_9')
    | v5_orders_3('#skF_9','#skF_5','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_608,c_4373])).

tff(c_4393,plain,
    ( k1_funct_1('#skF_9','#skF_2'('#skF_5','#skF_8','#skF_9')) = '#skF_4'('#skF_5','#skF_8','#skF_9')
    | v5_orders_3('#skF_9','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_50,c_609,c_4377])).

tff(c_4394,plain,(
    k1_funct_1('#skF_9','#skF_2'('#skF_5','#skF_8','#skF_9')) = '#skF_4'('#skF_5','#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_4371,c_4393])).

tff(c_681,plain,
    ( m1_subset_1('#skF_1'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
    | v5_orders_3('#skF_9','#skF_5','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_608,c_679])).

tff(c_694,plain,
    ( m1_subset_1('#skF_1'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
    | v5_orders_3('#skF_9','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_50,c_609,c_681])).

tff(c_4372,plain,(
    m1_subset_1('#skF_1'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_4371,c_694])).

tff(c_24,plain,(
    ! [A_9,B_133,C_195] :
      ( m1_subset_1('#skF_2'(A_9,B_133,C_195),u1_struct_0(A_9))
      | v5_orders_3(C_195,A_9,B_133)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9),u1_struct_0(B_133))))
      | ~ v1_funct_2(C_195,u1_struct_0(A_9),u1_struct_0(B_133))
      | ~ v1_funct_1(C_195)
      | ~ l1_orders_2(B_133)
      | ~ l1_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_665,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
    | v5_orders_3('#skF_9','#skF_5','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_608,c_24])).

tff(c_672,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
    | v5_orders_3('#skF_9','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_50,c_609,c_665])).

tff(c_4410,plain,(
    m1_subset_1('#skF_2'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_4371,c_672])).

tff(c_4759,plain,(
    ! [A_706,B_707,C_708] :
      ( r1_orders_2(A_706,'#skF_1'(A_706,B_707,C_708),'#skF_2'(A_706,B_707,C_708))
      | v5_orders_3(C_708,A_706,B_707)
      | ~ m1_subset_1(C_708,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_706),u1_struct_0(B_707))))
      | ~ v1_funct_2(C_708,u1_struct_0(A_706),u1_struct_0(B_707))
      | ~ v1_funct_1(C_708)
      | ~ l1_orders_2(B_707)
      | ~ l1_orders_2(A_706) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4769,plain,
    ( r1_orders_2('#skF_5','#skF_1'('#skF_5','#skF_8','#skF_9'),'#skF_2'('#skF_5','#skF_8','#skF_9'))
    | v5_orders_3('#skF_9','#skF_5','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_608,c_4759])).

tff(c_4788,plain,
    ( r1_orders_2('#skF_5','#skF_1'('#skF_5','#skF_8','#skF_9'),'#skF_2'('#skF_5','#skF_8','#skF_9'))
    | v5_orders_3('#skF_9','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_50,c_609,c_4769])).

tff(c_4789,plain,(
    r1_orders_2('#skF_5','#skF_1'('#skF_5','#skF_8','#skF_9'),'#skF_2'('#skF_5','#skF_8','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_4371,c_4788])).

tff(c_4989,plain,(
    ! [B_732,D_730,A_734,C_733,E_731] :
      ( r1_orders_2(B_732,k1_funct_1(C_733,D_730),k1_funct_1(C_733,E_731))
      | ~ m1_subset_1(k1_funct_1(C_733,E_731),u1_struct_0(B_732))
      | ~ m1_subset_1(k1_funct_1(C_733,D_730),u1_struct_0(B_732))
      | ~ r1_orders_2(A_734,D_730,E_731)
      | ~ m1_subset_1(E_731,u1_struct_0(A_734))
      | ~ m1_subset_1(D_730,u1_struct_0(A_734))
      | ~ v5_orders_3(C_733,A_734,B_732)
      | ~ m1_subset_1(C_733,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_734),u1_struct_0(B_732))))
      | ~ v1_funct_2(C_733,u1_struct_0(A_734),u1_struct_0(B_732))
      | ~ v1_funct_1(C_733)
      | ~ l1_orders_2(B_732)
      | ~ l1_orders_2(A_734) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4991,plain,(
    ! [B_732,C_733] :
      ( r1_orders_2(B_732,k1_funct_1(C_733,'#skF_1'('#skF_5','#skF_8','#skF_9')),k1_funct_1(C_733,'#skF_2'('#skF_5','#skF_8','#skF_9')))
      | ~ m1_subset_1(k1_funct_1(C_733,'#skF_2'('#skF_5','#skF_8','#skF_9')),u1_struct_0(B_732))
      | ~ m1_subset_1(k1_funct_1(C_733,'#skF_1'('#skF_5','#skF_8','#skF_9')),u1_struct_0(B_732))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_1'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
      | ~ v5_orders_3(C_733,'#skF_5',B_732)
      | ~ m1_subset_1(C_733,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_732))))
      | ~ v1_funct_2(C_733,u1_struct_0('#skF_5'),u1_struct_0(B_732))
      | ~ v1_funct_1(C_733)
      | ~ l1_orders_2(B_732)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4789,c_4989])).

tff(c_6506,plain,(
    ! [B_852,C_853] :
      ( r1_orders_2(B_852,k1_funct_1(C_853,'#skF_1'('#skF_5','#skF_8','#skF_9')),k1_funct_1(C_853,'#skF_2'('#skF_5','#skF_8','#skF_9')))
      | ~ m1_subset_1(k1_funct_1(C_853,'#skF_2'('#skF_5','#skF_8','#skF_9')),u1_struct_0(B_852))
      | ~ m1_subset_1(k1_funct_1(C_853,'#skF_1'('#skF_5','#skF_8','#skF_9')),u1_struct_0(B_852))
      | ~ v5_orders_3(C_853,'#skF_5',B_852)
      | ~ m1_subset_1(C_853,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_852))))
      | ~ v1_funct_2(C_853,u1_struct_0('#skF_5'),u1_struct_0(B_852))
      | ~ v1_funct_1(C_853)
      | ~ l1_orders_2(B_852) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4372,c_4410,c_4991])).

tff(c_6513,plain,(
    ! [B_852] :
      ( r1_orders_2(B_852,'#skF_3'('#skF_5','#skF_8','#skF_9'),k1_funct_1('#skF_9','#skF_2'('#skF_5','#skF_8','#skF_9')))
      | ~ m1_subset_1(k1_funct_1('#skF_9','#skF_2'('#skF_5','#skF_8','#skF_9')),u1_struct_0(B_852))
      | ~ m1_subset_1(k1_funct_1('#skF_9','#skF_1'('#skF_5','#skF_8','#skF_9')),u1_struct_0(B_852))
      | ~ v5_orders_3('#skF_9','#skF_5',B_852)
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_852))))
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0(B_852))
      | ~ v1_funct_1('#skF_9')
      | ~ l1_orders_2(B_852) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4883,c_6506])).

tff(c_6579,plain,(
    ! [B_858] :
      ( r1_orders_2(B_858,'#skF_3'('#skF_5','#skF_8','#skF_9'),'#skF_4'('#skF_5','#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_8','#skF_9'),u1_struct_0(B_858))
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_9'),u1_struct_0(B_858))
      | ~ v5_orders_3('#skF_9','#skF_5',B_858)
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_858))))
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0(B_858))
      | ~ l1_orders_2(B_858) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_4883,c_4394,c_4394,c_6513])).

tff(c_6582,plain,
    ( r1_orders_2('#skF_6','#skF_3'('#skF_5','#skF_8','#skF_9'),'#skF_4'('#skF_5','#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_4'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_6'))
    | ~ v5_orders_3('#skF_9','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))))
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4485,c_6579])).

tff(c_6590,plain,(
    r1_orders_2('#skF_6','#skF_3'('#skF_5','#skF_8','#skF_9'),'#skF_4'('#skF_5','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_609,c_4485,c_608,c_32,c_4411,c_4485,c_4370,c_4485,c_6582])).

tff(c_6599,plain,(
    ! [B_284] :
      ( r1_orders_2(B_284,'#skF_3'('#skF_5','#skF_8','#skF_9'),'#skF_4'('#skF_5','#skF_8','#skF_9'))
      | g1_orders_2(u1_struct_0(B_284),u1_orders_2(B_284)) != g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6'))
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_8','#skF_9'),u1_struct_0(B_284))
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_9'),u1_struct_0(B_284))
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_6'))
      | ~ l1_orders_2(B_284)
      | ~ l1_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_6590,c_28])).

tff(c_6606,plain,(
    ! [B_859] :
      ( r1_orders_2(B_859,'#skF_3'('#skF_5','#skF_8','#skF_9'),'#skF_4'('#skF_5','#skF_8','#skF_9'))
      | g1_orders_2(u1_struct_0(B_859),u1_orders_2(B_859)) != k7_lattice3(k7_lattice3('#skF_8'))
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_8','#skF_9'),u1_struct_0(B_859))
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_9'),u1_struct_0(B_859))
      | ~ l1_orders_2(B_859) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_4411,c_4485,c_4370,c_4485,c_145,c_4485,c_299,c_6599])).

tff(c_6618,plain,
    ( r1_orders_2('#skF_8','#skF_3'('#skF_5','#skF_8','#skF_9'),'#skF_4'('#skF_5','#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_4'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ l1_orders_2('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_6606])).

tff(c_6633,plain,(
    r1_orders_2('#skF_8','#skF_3'('#skF_5','#skF_8','#skF_9'),'#skF_4'('#skF_5','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4411,c_4370,c_6618])).

tff(c_6656,plain,
    ( v5_orders_3('#skF_9','#skF_5','#skF_8')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))))
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_6633,c_12])).

tff(c_6665,plain,(
    v5_orders_3('#skF_9','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_50,c_609,c_608,c_6656])).

tff(c_6667,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4371,c_6665])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:43:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.19/2.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.19/2.78  
% 8.19/2.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.19/2.78  %$ v5_orders_3 > v1_funct_2 > r1_orders_2 > m1_subset_1 > v2_struct_0 > v1_funct_1 > l1_orders_2 > k2_zfmisc_1 > k1_funct_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k7_lattice3 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3
% 8.19/2.78  
% 8.19/2.78  %Foreground sorts:
% 8.19/2.78  
% 8.19/2.78  
% 8.19/2.78  %Background operators:
% 8.19/2.78  
% 8.19/2.78  
% 8.19/2.78  %Foreground operators:
% 8.19/2.78  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.19/2.78  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.19/2.78  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.19/2.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.19/2.78  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 8.19/2.78  tff(v5_orders_3, type, v5_orders_3: ($i * $i * $i) > $o).
% 8.19/2.78  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.19/2.78  tff('#skF_7', type, '#skF_7': $i).
% 8.19/2.78  tff('#skF_10', type, '#skF_10': $i).
% 8.19/2.78  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 8.19/2.78  tff(k7_lattice3, type, k7_lattice3: $i > $i).
% 8.19/2.78  tff('#skF_5', type, '#skF_5': $i).
% 8.19/2.78  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.19/2.78  tff('#skF_6', type, '#skF_6': $i).
% 8.19/2.78  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.19/2.78  tff('#skF_9', type, '#skF_9': $i).
% 8.19/2.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.19/2.78  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.19/2.78  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 8.19/2.78  tff('#skF_8', type, '#skF_8': $i).
% 8.19/2.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.19/2.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.19/2.78  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.19/2.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.19/2.78  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 8.19/2.78  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.19/2.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.19/2.78  
% 8.19/2.81  tff(f_145, negated_conjecture, ~(![A]: (l1_orders_2(A) => (![B]: (l1_orders_2(B) => (![C]: ((~v2_struct_0(C) & l1_orders_2(C)) => (![D]: ((~v2_struct_0(D) & l1_orders_2(D)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(D))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(D))))) => (((((g1_orders_2(u1_struct_0(A), u1_orders_2(A)) = g1_orders_2(u1_struct_0(C), u1_orders_2(C))) & (g1_orders_2(u1_struct_0(B), u1_orders_2(B)) = g1_orders_2(u1_struct_0(D), u1_orders_2(D)))) & (E = F)) & v5_orders_3(E, A, B)) => v5_orders_3(F, C, D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_waybel_9)).
% 8.19/2.81  tff(f_42, axiom, (![A]: (l1_orders_2(A) => (k7_lattice3(k7_lattice3(A)) = g1_orders_2(u1_struct_0(A), u1_orders_2(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_lattice3)).
% 8.19/2.81  tff(f_29, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 8.19/2.81  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C, D]: ((g1_orders_2(A, B) = g1_orders_2(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_orders_2)).
% 8.19/2.81  tff(f_76, axiom, (![A]: (l1_orders_2(A) => (![B]: (l1_orders_2(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v5_orders_3(C, A, B) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => (r1_orders_2(A, D, E) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(B)) => (((F = k1_funct_1(C, D)) & (G = k1_funct_1(C, E))) => r1_orders_2(B, F, G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_orders_3)).
% 8.19/2.81  tff(f_103, axiom, (![A]: (l1_orders_2(A) => (![B]: (l1_orders_2(B) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (((((C = E) & (D = F)) & (g1_orders_2(u1_struct_0(A), u1_orders_2(A)) = g1_orders_2(u1_struct_0(B), u1_orders_2(B)))) & r1_orders_2(A, C, D)) => r1_orders_2(B, E, F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l20_yellow_6)).
% 8.19/2.81  tff(c_34, plain, ('#skF_10'='#skF_9'), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.19/2.81  tff(c_30, plain, (~v5_orders_3('#skF_10', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.19/2.81  tff(c_67, plain, (~v5_orders_3('#skF_9', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30])).
% 8.19/2.81  tff(c_56, plain, (l1_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.19/2.81  tff(c_52, plain, (l1_orders_2('#skF_8')), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.19/2.81  tff(c_50, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.19/2.81  tff(c_62, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.19/2.81  tff(c_38, plain, (g1_orders_2(u1_struct_0('#skF_7'), u1_orders_2('#skF_7'))=g1_orders_2(u1_struct_0('#skF_5'), u1_orders_2('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.19/2.81  tff(c_8, plain, (![A_8]: (g1_orders_2(u1_struct_0(A_8), u1_orders_2(A_8))=k7_lattice3(k7_lattice3(A_8)) | ~l1_orders_2(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.19/2.81  tff(c_119, plain, (g1_orders_2(u1_struct_0('#skF_5'), u1_orders_2('#skF_5'))=k7_lattice3(k7_lattice3('#skF_7')) | ~l1_orders_2('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_38, c_8])).
% 8.19/2.81  tff(c_126, plain, (g1_orders_2(u1_struct_0('#skF_5'), u1_orders_2('#skF_5'))=k7_lattice3(k7_lattice3('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_119])).
% 8.19/2.81  tff(c_166, plain, (k7_lattice3(k7_lattice3('#skF_7'))=k7_lattice3(k7_lattice3('#skF_5')) | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_126, c_8])).
% 8.19/2.81  tff(c_173, plain, (k7_lattice3(k7_lattice3('#skF_7'))=k7_lattice3(k7_lattice3('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_166])).
% 8.19/2.81  tff(c_123, plain, (g1_orders_2(u1_struct_0('#skF_5'), u1_orders_2('#skF_5'))=k7_lattice3(k7_lattice3('#skF_7')) | ~l1_orders_2('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_8, c_38])).
% 8.19/2.81  tff(c_129, plain, (g1_orders_2(u1_struct_0('#skF_5'), u1_orders_2('#skF_5'))=k7_lattice3(k7_lattice3('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_123])).
% 8.19/2.81  tff(c_184, plain, (g1_orders_2(u1_struct_0('#skF_5'), u1_orders_2('#skF_5'))=k7_lattice3(k7_lattice3('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_129])).
% 8.19/2.81  tff(c_2, plain, (![A_1]: (m1_subset_1(u1_orders_2(A_1), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1), u1_struct_0(A_1)))) | ~l1_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.19/2.81  tff(c_162, plain, (g1_orders_2(u1_struct_0('#skF_7'), u1_orders_2('#skF_7'))=k7_lattice3(k7_lattice3('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_38])).
% 8.19/2.81  tff(c_201, plain, (g1_orders_2(u1_struct_0('#skF_7'), u1_orders_2('#skF_7'))=k7_lattice3(k7_lattice3('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_162])).
% 8.19/2.81  tff(c_247, plain, (![C_378, A_379, D_380, B_381]: (C_378=A_379 | g1_orders_2(C_378, D_380)!=g1_orders_2(A_379, B_381) | ~m1_subset_1(B_381, k1_zfmisc_1(k2_zfmisc_1(A_379, A_379))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.19/2.81  tff(c_560, plain, (![A_401, B_402]: (u1_struct_0('#skF_7')=A_401 | k7_lattice3(k7_lattice3('#skF_5'))!=g1_orders_2(A_401, B_402) | ~m1_subset_1(B_402, k1_zfmisc_1(k2_zfmisc_1(A_401, A_401))))), inference(superposition, [status(thm), theory('equality')], [c_201, c_247])).
% 8.19/2.81  tff(c_577, plain, (![A_403]: (u1_struct_0(A_403)=u1_struct_0('#skF_7') | g1_orders_2(u1_struct_0(A_403), u1_orders_2(A_403))!=k7_lattice3(k7_lattice3('#skF_5')) | ~l1_orders_2(A_403))), inference(resolution, [status(thm)], [c_2, c_560])).
% 8.19/2.81  tff(c_586, plain, (u1_struct_0('#skF_7')=u1_struct_0('#skF_5') | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_184, c_577])).
% 8.19/2.81  tff(c_600, plain, (u1_struct_0('#skF_7')=u1_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_586])).
% 8.19/2.81  tff(c_42, plain, (v1_funct_2('#skF_10', u1_struct_0('#skF_7'), u1_struct_0('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.19/2.81  tff(c_64, plain, (v1_funct_2('#skF_9', u1_struct_0('#skF_7'), u1_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_42])).
% 8.19/2.81  tff(c_609, plain, (v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_600, c_64])).
% 8.19/2.81  tff(c_40, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_8'))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.19/2.81  tff(c_65, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_8'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_40])).
% 8.19/2.81  tff(c_608, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_8'))))), inference(demodulation, [status(thm), theory('equality')], [c_600, c_65])).
% 8.19/2.81  tff(c_18, plain, (![A_9, B_133, C_195]: (m1_subset_1('#skF_4'(A_9, B_133, C_195), u1_struct_0(B_133)) | v5_orders_3(C_195, A_9, B_133) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9), u1_struct_0(B_133)))) | ~v1_funct_2(C_195, u1_struct_0(A_9), u1_struct_0(B_133)) | ~v1_funct_1(C_195) | ~l1_orders_2(B_133) | ~l1_orders_2(A_9))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.19/2.81  tff(c_669, plain, (m1_subset_1('#skF_4'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | v5_orders_3('#skF_9', '#skF_5', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8') | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_608, c_18])).
% 8.19/2.81  tff(c_678, plain, (m1_subset_1('#skF_4'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | v5_orders_3('#skF_9', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_50, c_609, c_669])).
% 8.19/2.81  tff(c_757, plain, (v5_orders_3('#skF_9', '#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_678])).
% 8.19/2.81  tff(c_386, plain, (![A_389, B_390, C_391]: (m1_subset_1('#skF_3'(A_389, B_390, C_391), u1_struct_0(B_390)) | v5_orders_3(C_391, A_389, B_390) | ~m1_subset_1(C_391, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_389), u1_struct_0(B_390)))) | ~v1_funct_2(C_391, u1_struct_0(A_389), u1_struct_0(B_390)) | ~v1_funct_1(C_391) | ~l1_orders_2(B_390) | ~l1_orders_2(A_389))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.19/2.81  tff(c_392, plain, (m1_subset_1('#skF_3'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | v5_orders_3('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_7'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8') | ~l1_orders_2('#skF_7')), inference(resolution, [status(thm)], [c_65, c_386])).
% 8.19/2.81  tff(c_401, plain, (m1_subset_1('#skF_3'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | v5_orders_3('#skF_9', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_64, c_392])).
% 8.19/2.81  tff(c_402, plain, (m1_subset_1('#skF_3'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_67, c_401])).
% 8.19/2.81  tff(c_320, plain, (![A_385, B_386, C_387]: (m1_subset_1('#skF_4'(A_385, B_386, C_387), u1_struct_0(B_386)) | v5_orders_3(C_387, A_385, B_386) | ~m1_subset_1(C_387, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_385), u1_struct_0(B_386)))) | ~v1_funct_2(C_387, u1_struct_0(A_385), u1_struct_0(B_386)) | ~v1_funct_1(C_387) | ~l1_orders_2(B_386) | ~l1_orders_2(A_385))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.19/2.81  tff(c_324, plain, (m1_subset_1('#skF_4'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | v5_orders_3('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_7'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8') | ~l1_orders_2('#skF_7')), inference(resolution, [status(thm)], [c_65, c_320])).
% 8.19/2.81  tff(c_330, plain, (m1_subset_1('#skF_4'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | v5_orders_3('#skF_9', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_64, c_324])).
% 8.19/2.81  tff(c_331, plain, (m1_subset_1('#skF_4'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_67, c_330])).
% 8.19/2.81  tff(c_1224, plain, (![C_434, A_435, B_436]: (k1_funct_1(C_434, '#skF_1'(A_435, B_436, C_434))='#skF_3'(A_435, B_436, C_434) | v5_orders_3(C_434, A_435, B_436) | ~m1_subset_1(C_434, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_435), u1_struct_0(B_436)))) | ~v1_funct_2(C_434, u1_struct_0(A_435), u1_struct_0(B_436)) | ~v1_funct_1(C_434) | ~l1_orders_2(B_436) | ~l1_orders_2(A_435))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.19/2.81  tff(c_1236, plain, (![C_434, B_436]: (k1_funct_1(C_434, '#skF_1'('#skF_7', B_436, C_434))='#skF_3'('#skF_7', B_436, C_434) | v5_orders_3(C_434, '#skF_7', B_436) | ~m1_subset_1(C_434, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_436)))) | ~v1_funct_2(C_434, u1_struct_0('#skF_7'), u1_struct_0(B_436)) | ~v1_funct_1(C_434) | ~l1_orders_2(B_436) | ~l1_orders_2('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_600, c_1224])).
% 8.19/2.81  tff(c_3670, plain, (![C_634, B_635]: (k1_funct_1(C_634, '#skF_1'('#skF_7', B_635, C_634))='#skF_3'('#skF_7', B_635, C_634) | v5_orders_3(C_634, '#skF_7', B_635) | ~m1_subset_1(C_634, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_635)))) | ~v1_funct_2(C_634, u1_struct_0('#skF_5'), u1_struct_0(B_635)) | ~v1_funct_1(C_634) | ~l1_orders_2(B_635))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_600, c_1236])).
% 8.19/2.81  tff(c_3676, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_7', '#skF_8', '#skF_9'))='#skF_3'('#skF_7', '#skF_8', '#skF_9') | v5_orders_3('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_608, c_3670])).
% 8.19/2.81  tff(c_3689, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_7', '#skF_8', '#skF_9'))='#skF_3'('#skF_7', '#skF_8', '#skF_9') | v5_orders_3('#skF_9', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_609, c_3676])).
% 8.19/2.81  tff(c_3690, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_7', '#skF_8', '#skF_9'))='#skF_3'('#skF_7', '#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_67, c_3689])).
% 8.19/2.81  tff(c_761, plain, (![C_409, A_410, B_411]: (k1_funct_1(C_409, '#skF_2'(A_410, B_411, C_409))='#skF_4'(A_410, B_411, C_409) | v5_orders_3(C_409, A_410, B_411) | ~m1_subset_1(C_409, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_410), u1_struct_0(B_411)))) | ~v1_funct_2(C_409, u1_struct_0(A_410), u1_struct_0(B_411)) | ~v1_funct_1(C_409) | ~l1_orders_2(B_411) | ~l1_orders_2(A_410))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.19/2.81  tff(c_767, plain, (![C_409, B_411]: (k1_funct_1(C_409, '#skF_2'('#skF_7', B_411, C_409))='#skF_4'('#skF_7', B_411, C_409) | v5_orders_3(C_409, '#skF_7', B_411) | ~m1_subset_1(C_409, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_411)))) | ~v1_funct_2(C_409, u1_struct_0('#skF_7'), u1_struct_0(B_411)) | ~v1_funct_1(C_409) | ~l1_orders_2(B_411) | ~l1_orders_2('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_600, c_761])).
% 8.19/2.81  tff(c_4022, plain, (![C_660, B_661]: (k1_funct_1(C_660, '#skF_2'('#skF_7', B_661, C_660))='#skF_4'('#skF_7', B_661, C_660) | v5_orders_3(C_660, '#skF_7', B_661) | ~m1_subset_1(C_660, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_661)))) | ~v1_funct_2(C_660, u1_struct_0('#skF_5'), u1_struct_0(B_661)) | ~v1_funct_1(C_660) | ~l1_orders_2(B_661))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_600, c_767])).
% 8.19/2.81  tff(c_4028, plain, (k1_funct_1('#skF_9', '#skF_2'('#skF_7', '#skF_8', '#skF_9'))='#skF_4'('#skF_7', '#skF_8', '#skF_9') | v5_orders_3('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_608, c_4022])).
% 8.19/2.81  tff(c_4041, plain, (k1_funct_1('#skF_9', '#skF_2'('#skF_7', '#skF_8', '#skF_9'))='#skF_4'('#skF_7', '#skF_8', '#skF_9') | v5_orders_3('#skF_9', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_609, c_4028])).
% 8.19/2.81  tff(c_4042, plain, (k1_funct_1('#skF_9', '#skF_2'('#skF_7', '#skF_8', '#skF_9'))='#skF_4'('#skF_7', '#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_67, c_4041])).
% 8.19/2.81  tff(c_679, plain, (![A_404, B_405, C_406]: (m1_subset_1('#skF_1'(A_404, B_405, C_406), u1_struct_0(A_404)) | v5_orders_3(C_406, A_404, B_405) | ~m1_subset_1(C_406, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_404), u1_struct_0(B_405)))) | ~v1_funct_2(C_406, u1_struct_0(A_404), u1_struct_0(B_405)) | ~v1_funct_1(C_406) | ~l1_orders_2(B_405) | ~l1_orders_2(A_404))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.19/2.81  tff(c_683, plain, (![B_405, C_406]: (m1_subset_1('#skF_1'('#skF_7', B_405, C_406), u1_struct_0('#skF_7')) | v5_orders_3(C_406, '#skF_7', B_405) | ~m1_subset_1(C_406, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_405)))) | ~v1_funct_2(C_406, u1_struct_0('#skF_7'), u1_struct_0(B_405)) | ~v1_funct_1(C_406) | ~l1_orders_2(B_405) | ~l1_orders_2('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_600, c_679])).
% 8.19/2.81  tff(c_3284, plain, (![B_602, C_603]: (m1_subset_1('#skF_1'('#skF_7', B_602, C_603), u1_struct_0('#skF_5')) | v5_orders_3(C_603, '#skF_7', B_602) | ~m1_subset_1(C_603, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_602)))) | ~v1_funct_2(C_603, u1_struct_0('#skF_5'), u1_struct_0(B_602)) | ~v1_funct_1(C_603) | ~l1_orders_2(B_602))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_600, c_600, c_683])).
% 8.19/2.81  tff(c_3293, plain, (m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | v5_orders_3('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_608, c_3284])).
% 8.19/2.81  tff(c_3308, plain, (m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | v5_orders_3('#skF_9', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_609, c_3293])).
% 8.19/2.81  tff(c_3309, plain, (m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_67, c_3308])).
% 8.19/2.81  tff(c_515, plain, (![A_397, B_398, C_399]: (m1_subset_1('#skF_2'(A_397, B_398, C_399), u1_struct_0(A_397)) | v5_orders_3(C_399, A_397, B_398) | ~m1_subset_1(C_399, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_397), u1_struct_0(B_398)))) | ~v1_funct_2(C_399, u1_struct_0(A_397), u1_struct_0(B_398)) | ~v1_funct_1(C_399) | ~l1_orders_2(B_398) | ~l1_orders_2(A_397))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.19/2.81  tff(c_523, plain, (m1_subset_1('#skF_2'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | v5_orders_3('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_7'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8') | ~l1_orders_2('#skF_7')), inference(resolution, [status(thm)], [c_65, c_515])).
% 8.19/2.81  tff(c_535, plain, (m1_subset_1('#skF_2'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | v5_orders_3('#skF_9', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_64, c_523])).
% 8.19/2.81  tff(c_536, plain, (m1_subset_1('#skF_2'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_67, c_535])).
% 8.19/2.81  tff(c_605, plain, (m1_subset_1('#skF_2'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_600, c_536])).
% 8.19/2.81  tff(c_222, plain, (![D_374, B_375, C_376, A_377]: (D_374=B_375 | g1_orders_2(C_376, D_374)!=g1_orders_2(A_377, B_375) | ~m1_subset_1(B_375, k1_zfmisc_1(k2_zfmisc_1(A_377, A_377))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.19/2.81  tff(c_406, plain, (![B_392, A_393]: (u1_orders_2('#skF_5')=B_392 | k7_lattice3(k7_lattice3('#skF_5'))!=g1_orders_2(A_393, B_392) | ~m1_subset_1(B_392, k1_zfmisc_1(k2_zfmisc_1(A_393, A_393))))), inference(superposition, [status(thm), theory('equality')], [c_184, c_222])).
% 8.19/2.81  tff(c_416, plain, (![A_394]: (u1_orders_2(A_394)=u1_orders_2('#skF_5') | g1_orders_2(u1_struct_0(A_394), u1_orders_2(A_394))!=k7_lattice3(k7_lattice3('#skF_5')) | ~l1_orders_2(A_394))), inference(resolution, [status(thm)], [c_2, c_406])).
% 8.19/2.81  tff(c_422, plain, (u1_orders_2('#skF_7')=u1_orders_2('#skF_5') | ~l1_orders_2('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_201, c_416])).
% 8.19/2.81  tff(c_436, plain, (u1_orders_2('#skF_7')=u1_orders_2('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_422])).
% 8.19/2.81  tff(c_1051, plain, (![A_418, B_419, C_420]: (r1_orders_2(A_418, '#skF_1'(A_418, B_419, C_420), '#skF_2'(A_418, B_419, C_420)) | v5_orders_3(C_420, A_418, B_419) | ~m1_subset_1(C_420, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_418), u1_struct_0(B_419)))) | ~v1_funct_2(C_420, u1_struct_0(A_418), u1_struct_0(B_419)) | ~v1_funct_1(C_420) | ~l1_orders_2(B_419) | ~l1_orders_2(A_418))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.19/2.81  tff(c_1063, plain, (![B_419, C_420]: (r1_orders_2('#skF_7', '#skF_1'('#skF_7', B_419, C_420), '#skF_2'('#skF_7', B_419, C_420)) | v5_orders_3(C_420, '#skF_7', B_419) | ~m1_subset_1(C_420, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_419)))) | ~v1_funct_2(C_420, u1_struct_0('#skF_7'), u1_struct_0(B_419)) | ~v1_funct_1(C_420) | ~l1_orders_2(B_419) | ~l1_orders_2('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_600, c_1051])).
% 8.19/2.81  tff(c_3711, plain, (![B_637, C_638]: (r1_orders_2('#skF_7', '#skF_1'('#skF_7', B_637, C_638), '#skF_2'('#skF_7', B_637, C_638)) | v5_orders_3(C_638, '#skF_7', B_637) | ~m1_subset_1(C_638, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_637)))) | ~v1_funct_2(C_638, u1_struct_0('#skF_5'), u1_struct_0(B_637)) | ~v1_funct_1(C_638) | ~l1_orders_2(B_637))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_600, c_1063])).
% 8.19/2.81  tff(c_3717, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_2'('#skF_7', '#skF_8', '#skF_9')) | v5_orders_3('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_608, c_3711])).
% 8.19/2.81  tff(c_3730, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_2'('#skF_7', '#skF_8', '#skF_9')) | v5_orders_3('#skF_9', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_609, c_3717])).
% 8.19/2.81  tff(c_3731, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_2'('#skF_7', '#skF_8', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_67, c_3730])).
% 8.19/2.81  tff(c_28, plain, (![B_284, E_312, F_314, A_252]: (r1_orders_2(B_284, E_312, F_314) | ~r1_orders_2(A_252, E_312, F_314) | g1_orders_2(u1_struct_0(B_284), u1_orders_2(B_284))!=g1_orders_2(u1_struct_0(A_252), u1_orders_2(A_252)) | ~m1_subset_1(F_314, u1_struct_0(B_284)) | ~m1_subset_1(E_312, u1_struct_0(B_284)) | ~m1_subset_1(F_314, u1_struct_0(A_252)) | ~m1_subset_1(E_312, u1_struct_0(A_252)) | ~l1_orders_2(B_284) | ~l1_orders_2(A_252))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.19/2.81  tff(c_3740, plain, (![B_284]: (r1_orders_2(B_284, '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_2'('#skF_7', '#skF_8', '#skF_9')) | g1_orders_2(u1_struct_0(B_284), u1_orders_2(B_284))!=g1_orders_2(u1_struct_0('#skF_7'), u1_orders_2('#skF_7')) | ~m1_subset_1('#skF_2'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0(B_284)) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0(B_284)) | ~m1_subset_1('#skF_2'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | ~l1_orders_2(B_284) | ~l1_orders_2('#skF_7'))), inference(resolution, [status(thm)], [c_3731, c_28])).
% 8.19/2.81  tff(c_3856, plain, (![B_648]: (r1_orders_2(B_648, '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_2'('#skF_7', '#skF_8', '#skF_9')) | g1_orders_2(u1_struct_0(B_648), u1_orders_2(B_648))!=k7_lattice3(k7_lattice3('#skF_5')) | ~m1_subset_1('#skF_2'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0(B_648)) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0(B_648)) | ~l1_orders_2(B_648))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3309, c_600, c_605, c_600, c_184, c_436, c_600, c_3740])).
% 8.19/2.81  tff(c_3866, plain, (r1_orders_2('#skF_5', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_2'('#skF_7', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_2'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_184, c_3856])).
% 8.19/2.81  tff(c_3881, plain, (r1_orders_2('#skF_5', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_2'('#skF_7', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_3309, c_605, c_3866])).
% 8.19/2.81  tff(c_10, plain, (![B_133, E_234, D_226, C_195, A_9]: (r1_orders_2(B_133, k1_funct_1(C_195, D_226), k1_funct_1(C_195, E_234)) | ~m1_subset_1(k1_funct_1(C_195, E_234), u1_struct_0(B_133)) | ~m1_subset_1(k1_funct_1(C_195, D_226), u1_struct_0(B_133)) | ~r1_orders_2(A_9, D_226, E_234) | ~m1_subset_1(E_234, u1_struct_0(A_9)) | ~m1_subset_1(D_226, u1_struct_0(A_9)) | ~v5_orders_3(C_195, A_9, B_133) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9), u1_struct_0(B_133)))) | ~v1_funct_2(C_195, u1_struct_0(A_9), u1_struct_0(B_133)) | ~v1_funct_1(C_195) | ~l1_orders_2(B_133) | ~l1_orders_2(A_9))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.19/2.81  tff(c_3885, plain, (![B_133, C_195]: (r1_orders_2(B_133, k1_funct_1(C_195, '#skF_1'('#skF_7', '#skF_8', '#skF_9')), k1_funct_1(C_195, '#skF_2'('#skF_7', '#skF_8', '#skF_9'))) | ~m1_subset_1(k1_funct_1(C_195, '#skF_2'('#skF_7', '#skF_8', '#skF_9')), u1_struct_0(B_133)) | ~m1_subset_1(k1_funct_1(C_195, '#skF_1'('#skF_7', '#skF_8', '#skF_9')), u1_struct_0(B_133)) | ~m1_subset_1('#skF_2'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | ~v5_orders_3(C_195, '#skF_5', B_133) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_133)))) | ~v1_funct_2(C_195, u1_struct_0('#skF_5'), u1_struct_0(B_133)) | ~v1_funct_1(C_195) | ~l1_orders_2(B_133) | ~l1_orders_2('#skF_5'))), inference(resolution, [status(thm)], [c_3881, c_10])).
% 8.19/2.81  tff(c_4309, plain, (![B_684, C_685]: (r1_orders_2(B_684, k1_funct_1(C_685, '#skF_1'('#skF_7', '#skF_8', '#skF_9')), k1_funct_1(C_685, '#skF_2'('#skF_7', '#skF_8', '#skF_9'))) | ~m1_subset_1(k1_funct_1(C_685, '#skF_2'('#skF_7', '#skF_8', '#skF_9')), u1_struct_0(B_684)) | ~m1_subset_1(k1_funct_1(C_685, '#skF_1'('#skF_7', '#skF_8', '#skF_9')), u1_struct_0(B_684)) | ~v5_orders_3(C_685, '#skF_5', B_684) | ~m1_subset_1(C_685, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_684)))) | ~v1_funct_2(C_685, u1_struct_0('#skF_5'), u1_struct_0(B_684)) | ~v1_funct_1(C_685) | ~l1_orders_2(B_684))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_3309, c_605, c_3885])).
% 8.19/2.81  tff(c_4316, plain, (![B_684]: (r1_orders_2(B_684, k1_funct_1('#skF_9', '#skF_1'('#skF_7', '#skF_8', '#skF_9')), '#skF_4'('#skF_7', '#skF_8', '#skF_9')) | ~m1_subset_1(k1_funct_1('#skF_9', '#skF_2'('#skF_7', '#skF_8', '#skF_9')), u1_struct_0(B_684)) | ~m1_subset_1(k1_funct_1('#skF_9', '#skF_1'('#skF_7', '#skF_8', '#skF_9')), u1_struct_0(B_684)) | ~v5_orders_3('#skF_9', '#skF_5', B_684) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_684)))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0(B_684)) | ~v1_funct_1('#skF_9') | ~l1_orders_2(B_684))), inference(superposition, [status(thm), theory('equality')], [c_4042, c_4309])).
% 8.19/2.81  tff(c_4326, plain, (![B_686]: (r1_orders_2(B_686, '#skF_3'('#skF_7', '#skF_8', '#skF_9'), '#skF_4'('#skF_7', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_4'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0(B_686)) | ~m1_subset_1('#skF_3'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0(B_686)) | ~v5_orders_3('#skF_9', '#skF_5', B_686) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_686)))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0(B_686)) | ~l1_orders_2(B_686))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_3690, c_4042, c_3690, c_4316])).
% 8.19/2.81  tff(c_4332, plain, (r1_orders_2('#skF_8', '#skF_3'('#skF_7', '#skF_8', '#skF_9'), '#skF_4'('#skF_7', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_4'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_3'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | ~v5_orders_3('#skF_9', '#skF_5', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_608, c_4326])).
% 8.19/2.81  tff(c_4340, plain, (r1_orders_2('#skF_8', '#skF_3'('#skF_7', '#skF_8', '#skF_9'), '#skF_4'('#skF_7', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_609, c_757, c_402, c_331, c_4332])).
% 8.19/2.81  tff(c_12, plain, (![B_133, A_9, C_195]: (~r1_orders_2(B_133, '#skF_3'(A_9, B_133, C_195), '#skF_4'(A_9, B_133, C_195)) | v5_orders_3(C_195, A_9, B_133) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9), u1_struct_0(B_133)))) | ~v1_funct_2(C_195, u1_struct_0(A_9), u1_struct_0(B_133)) | ~v1_funct_1(C_195) | ~l1_orders_2(B_133) | ~l1_orders_2(A_9))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.19/2.81  tff(c_4358, plain, (v5_orders_3('#skF_9', '#skF_7', '#skF_8') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_8')))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_7'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8') | ~l1_orders_2('#skF_7')), inference(resolution, [status(thm)], [c_4340, c_12])).
% 8.19/2.81  tff(c_4367, plain, (v5_orders_3('#skF_9', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_609, c_600, c_608, c_600, c_4358])).
% 8.19/2.81  tff(c_4369, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_4367])).
% 8.19/2.81  tff(c_4371, plain, (~v5_orders_3('#skF_9', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_678])).
% 8.19/2.81  tff(c_20, plain, (![A_9, B_133, C_195]: (m1_subset_1('#skF_3'(A_9, B_133, C_195), u1_struct_0(B_133)) | v5_orders_3(C_195, A_9, B_133) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9), u1_struct_0(B_133)))) | ~v1_funct_2(C_195, u1_struct_0(A_9), u1_struct_0(B_133)) | ~v1_funct_1(C_195) | ~l1_orders_2(B_133) | ~l1_orders_2(A_9))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.19/2.81  tff(c_667, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | v5_orders_3('#skF_9', '#skF_5', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8') | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_608, c_20])).
% 8.19/2.81  tff(c_675, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | v5_orders_3('#skF_9', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_50, c_609, c_667])).
% 8.19/2.81  tff(c_4411, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_4371, c_675])).
% 8.19/2.81  tff(c_4370, plain, (m1_subset_1('#skF_4'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_8'))), inference(splitRight, [status(thm)], [c_678])).
% 8.19/2.81  tff(c_60, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.19/2.81  tff(c_76, plain, (![A_372]: (g1_orders_2(u1_struct_0(A_372), u1_orders_2(A_372))=k7_lattice3(k7_lattice3(A_372)) | ~l1_orders_2(A_372))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.19/2.81  tff(c_36, plain, (g1_orders_2(u1_struct_0('#skF_6'), u1_orders_2('#skF_6'))=g1_orders_2(u1_struct_0('#skF_8'), u1_orders_2('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.19/2.81  tff(c_82, plain, (g1_orders_2(u1_struct_0('#skF_8'), u1_orders_2('#skF_8'))=k7_lattice3(k7_lattice3('#skF_6')) | ~l1_orders_2('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_76, c_36])).
% 8.19/2.81  tff(c_91, plain, (g1_orders_2(u1_struct_0('#skF_8'), u1_orders_2('#skF_8'))=k7_lattice3(k7_lattice3('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_82])).
% 8.19/2.81  tff(c_99, plain, (k7_lattice3(k7_lattice3('#skF_6'))=k7_lattice3(k7_lattice3('#skF_8')) | ~l1_orders_2('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_91, c_8])).
% 8.19/2.81  tff(c_106, plain, (k7_lattice3(k7_lattice3('#skF_6'))=k7_lattice3(k7_lattice3('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_99])).
% 8.19/2.81  tff(c_88, plain, (g1_orders_2(u1_struct_0('#skF_8'), u1_orders_2('#skF_8'))=k7_lattice3(k7_lattice3('#skF_6')) | ~l1_orders_2('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_36, c_76])).
% 8.19/2.81  tff(c_94, plain, (g1_orders_2(u1_struct_0('#skF_8'), u1_orders_2('#skF_8'))=k7_lattice3(k7_lattice3('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_88])).
% 8.19/2.81  tff(c_145, plain, (g1_orders_2(u1_struct_0('#skF_8'), u1_orders_2('#skF_8'))=k7_lattice3(k7_lattice3('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_94])).
% 8.19/2.81  tff(c_95, plain, (g1_orders_2(u1_struct_0('#skF_6'), u1_orders_2('#skF_6'))=k7_lattice3(k7_lattice3('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_36])).
% 8.19/2.81  tff(c_130, plain, (g1_orders_2(u1_struct_0('#skF_6'), u1_orders_2('#skF_6'))=k7_lattice3(k7_lattice3('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_95])).
% 8.19/2.81  tff(c_740, plain, (![A_407, B_408]: (u1_struct_0('#skF_6')=A_407 | k7_lattice3(k7_lattice3('#skF_8'))!=g1_orders_2(A_407, B_408) | ~m1_subset_1(B_408, k1_zfmisc_1(k2_zfmisc_1(A_407, A_407))))), inference(superposition, [status(thm), theory('equality')], [c_130, c_247])).
% 8.19/2.81  tff(c_4455, plain, (![A_693]: (u1_struct_0(A_693)=u1_struct_0('#skF_6') | g1_orders_2(u1_struct_0(A_693), u1_orders_2(A_693))!=k7_lattice3(k7_lattice3('#skF_8')) | ~l1_orders_2(A_693))), inference(resolution, [status(thm)], [c_2, c_740])).
% 8.19/2.81  tff(c_4470, plain, (u1_struct_0('#skF_6')=u1_struct_0('#skF_8') | ~l1_orders_2('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_145, c_4455])).
% 8.19/2.81  tff(c_4485, plain, (u1_struct_0('#skF_6')=u1_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_4470])).
% 8.19/2.81  tff(c_268, plain, (![B_382, A_383]: (u1_orders_2('#skF_8')=B_382 | k7_lattice3(k7_lattice3('#skF_8'))!=g1_orders_2(A_383, B_382) | ~m1_subset_1(B_382, k1_zfmisc_1(k2_zfmisc_1(A_383, A_383))))), inference(superposition, [status(thm), theory('equality')], [c_145, c_222])).
% 8.19/2.81  tff(c_273, plain, (![A_384]: (u1_orders_2(A_384)=u1_orders_2('#skF_8') | g1_orders_2(u1_struct_0(A_384), u1_orders_2(A_384))!=k7_lattice3(k7_lattice3('#skF_8')) | ~l1_orders_2(A_384))), inference(resolution, [status(thm)], [c_2, c_268])).
% 8.19/2.81  tff(c_285, plain, (u1_orders_2('#skF_6')=u1_orders_2('#skF_8') | ~l1_orders_2('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_130, c_273])).
% 8.19/2.81  tff(c_299, plain, (u1_orders_2('#skF_6')=u1_orders_2('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_285])).
% 8.19/2.81  tff(c_32, plain, (v5_orders_3('#skF_9', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.19/2.81  tff(c_4853, plain, (![C_714, A_715, B_716]: (k1_funct_1(C_714, '#skF_1'(A_715, B_716, C_714))='#skF_3'(A_715, B_716, C_714) | v5_orders_3(C_714, A_715, B_716) | ~m1_subset_1(C_714, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_715), u1_struct_0(B_716)))) | ~v1_funct_2(C_714, u1_struct_0(A_715), u1_struct_0(B_716)) | ~v1_funct_1(C_714) | ~l1_orders_2(B_716) | ~l1_orders_2(A_715))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.19/2.81  tff(c_4863, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_5', '#skF_8', '#skF_9'))='#skF_3'('#skF_5', '#skF_8', '#skF_9') | v5_orders_3('#skF_9', '#skF_5', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8') | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_608, c_4853])).
% 8.19/2.81  tff(c_4882, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_5', '#skF_8', '#skF_9'))='#skF_3'('#skF_5', '#skF_8', '#skF_9') | v5_orders_3('#skF_9', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_50, c_609, c_4863])).
% 8.19/2.81  tff(c_4883, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_5', '#skF_8', '#skF_9'))='#skF_3'('#skF_5', '#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_4371, c_4882])).
% 8.19/2.81  tff(c_4373, plain, (![C_687, A_688, B_689]: (k1_funct_1(C_687, '#skF_2'(A_688, B_689, C_687))='#skF_4'(A_688, B_689, C_687) | v5_orders_3(C_687, A_688, B_689) | ~m1_subset_1(C_687, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_688), u1_struct_0(B_689)))) | ~v1_funct_2(C_687, u1_struct_0(A_688), u1_struct_0(B_689)) | ~v1_funct_1(C_687) | ~l1_orders_2(B_689) | ~l1_orders_2(A_688))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.19/2.81  tff(c_4377, plain, (k1_funct_1('#skF_9', '#skF_2'('#skF_5', '#skF_8', '#skF_9'))='#skF_4'('#skF_5', '#skF_8', '#skF_9') | v5_orders_3('#skF_9', '#skF_5', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8') | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_608, c_4373])).
% 8.19/2.81  tff(c_4393, plain, (k1_funct_1('#skF_9', '#skF_2'('#skF_5', '#skF_8', '#skF_9'))='#skF_4'('#skF_5', '#skF_8', '#skF_9') | v5_orders_3('#skF_9', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_50, c_609, c_4377])).
% 8.19/2.81  tff(c_4394, plain, (k1_funct_1('#skF_9', '#skF_2'('#skF_5', '#skF_8', '#skF_9'))='#skF_4'('#skF_5', '#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_4371, c_4393])).
% 8.19/2.81  tff(c_681, plain, (m1_subset_1('#skF_1'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | v5_orders_3('#skF_9', '#skF_5', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8') | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_608, c_679])).
% 8.19/2.81  tff(c_694, plain, (m1_subset_1('#skF_1'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | v5_orders_3('#skF_9', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_50, c_609, c_681])).
% 8.19/2.81  tff(c_4372, plain, (m1_subset_1('#skF_1'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_4371, c_694])).
% 8.19/2.81  tff(c_24, plain, (![A_9, B_133, C_195]: (m1_subset_1('#skF_2'(A_9, B_133, C_195), u1_struct_0(A_9)) | v5_orders_3(C_195, A_9, B_133) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9), u1_struct_0(B_133)))) | ~v1_funct_2(C_195, u1_struct_0(A_9), u1_struct_0(B_133)) | ~v1_funct_1(C_195) | ~l1_orders_2(B_133) | ~l1_orders_2(A_9))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.19/2.81  tff(c_665, plain, (m1_subset_1('#skF_2'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | v5_orders_3('#skF_9', '#skF_5', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8') | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_608, c_24])).
% 8.19/2.81  tff(c_672, plain, (m1_subset_1('#skF_2'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | v5_orders_3('#skF_9', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_50, c_609, c_665])).
% 8.19/2.81  tff(c_4410, plain, (m1_subset_1('#skF_2'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_4371, c_672])).
% 8.19/2.81  tff(c_4759, plain, (![A_706, B_707, C_708]: (r1_orders_2(A_706, '#skF_1'(A_706, B_707, C_708), '#skF_2'(A_706, B_707, C_708)) | v5_orders_3(C_708, A_706, B_707) | ~m1_subset_1(C_708, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_706), u1_struct_0(B_707)))) | ~v1_funct_2(C_708, u1_struct_0(A_706), u1_struct_0(B_707)) | ~v1_funct_1(C_708) | ~l1_orders_2(B_707) | ~l1_orders_2(A_706))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.19/2.81  tff(c_4769, plain, (r1_orders_2('#skF_5', '#skF_1'('#skF_5', '#skF_8', '#skF_9'), '#skF_2'('#skF_5', '#skF_8', '#skF_9')) | v5_orders_3('#skF_9', '#skF_5', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8') | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_608, c_4759])).
% 8.19/2.81  tff(c_4788, plain, (r1_orders_2('#skF_5', '#skF_1'('#skF_5', '#skF_8', '#skF_9'), '#skF_2'('#skF_5', '#skF_8', '#skF_9')) | v5_orders_3('#skF_9', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_50, c_609, c_4769])).
% 8.19/2.81  tff(c_4789, plain, (r1_orders_2('#skF_5', '#skF_1'('#skF_5', '#skF_8', '#skF_9'), '#skF_2'('#skF_5', '#skF_8', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_4371, c_4788])).
% 8.19/2.81  tff(c_4989, plain, (![B_732, D_730, A_734, C_733, E_731]: (r1_orders_2(B_732, k1_funct_1(C_733, D_730), k1_funct_1(C_733, E_731)) | ~m1_subset_1(k1_funct_1(C_733, E_731), u1_struct_0(B_732)) | ~m1_subset_1(k1_funct_1(C_733, D_730), u1_struct_0(B_732)) | ~r1_orders_2(A_734, D_730, E_731) | ~m1_subset_1(E_731, u1_struct_0(A_734)) | ~m1_subset_1(D_730, u1_struct_0(A_734)) | ~v5_orders_3(C_733, A_734, B_732) | ~m1_subset_1(C_733, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_734), u1_struct_0(B_732)))) | ~v1_funct_2(C_733, u1_struct_0(A_734), u1_struct_0(B_732)) | ~v1_funct_1(C_733) | ~l1_orders_2(B_732) | ~l1_orders_2(A_734))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.19/2.81  tff(c_4991, plain, (![B_732, C_733]: (r1_orders_2(B_732, k1_funct_1(C_733, '#skF_1'('#skF_5', '#skF_8', '#skF_9')), k1_funct_1(C_733, '#skF_2'('#skF_5', '#skF_8', '#skF_9'))) | ~m1_subset_1(k1_funct_1(C_733, '#skF_2'('#skF_5', '#skF_8', '#skF_9')), u1_struct_0(B_732)) | ~m1_subset_1(k1_funct_1(C_733, '#skF_1'('#skF_5', '#skF_8', '#skF_9')), u1_struct_0(B_732)) | ~m1_subset_1('#skF_2'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_1'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | ~v5_orders_3(C_733, '#skF_5', B_732) | ~m1_subset_1(C_733, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_732)))) | ~v1_funct_2(C_733, u1_struct_0('#skF_5'), u1_struct_0(B_732)) | ~v1_funct_1(C_733) | ~l1_orders_2(B_732) | ~l1_orders_2('#skF_5'))), inference(resolution, [status(thm)], [c_4789, c_4989])).
% 8.19/2.81  tff(c_6506, plain, (![B_852, C_853]: (r1_orders_2(B_852, k1_funct_1(C_853, '#skF_1'('#skF_5', '#skF_8', '#skF_9')), k1_funct_1(C_853, '#skF_2'('#skF_5', '#skF_8', '#skF_9'))) | ~m1_subset_1(k1_funct_1(C_853, '#skF_2'('#skF_5', '#skF_8', '#skF_9')), u1_struct_0(B_852)) | ~m1_subset_1(k1_funct_1(C_853, '#skF_1'('#skF_5', '#skF_8', '#skF_9')), u1_struct_0(B_852)) | ~v5_orders_3(C_853, '#skF_5', B_852) | ~m1_subset_1(C_853, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_852)))) | ~v1_funct_2(C_853, u1_struct_0('#skF_5'), u1_struct_0(B_852)) | ~v1_funct_1(C_853) | ~l1_orders_2(B_852))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4372, c_4410, c_4991])).
% 8.19/2.81  tff(c_6513, plain, (![B_852]: (r1_orders_2(B_852, '#skF_3'('#skF_5', '#skF_8', '#skF_9'), k1_funct_1('#skF_9', '#skF_2'('#skF_5', '#skF_8', '#skF_9'))) | ~m1_subset_1(k1_funct_1('#skF_9', '#skF_2'('#skF_5', '#skF_8', '#skF_9')), u1_struct_0(B_852)) | ~m1_subset_1(k1_funct_1('#skF_9', '#skF_1'('#skF_5', '#skF_8', '#skF_9')), u1_struct_0(B_852)) | ~v5_orders_3('#skF_9', '#skF_5', B_852) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_852)))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0(B_852)) | ~v1_funct_1('#skF_9') | ~l1_orders_2(B_852))), inference(superposition, [status(thm), theory('equality')], [c_4883, c_6506])).
% 8.19/2.81  tff(c_6579, plain, (![B_858]: (r1_orders_2(B_858, '#skF_3'('#skF_5', '#skF_8', '#skF_9'), '#skF_4'('#skF_5', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0(B_858)) | ~m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0(B_858)) | ~v5_orders_3('#skF_9', '#skF_5', B_858) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_858)))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0(B_858)) | ~l1_orders_2(B_858))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_4883, c_4394, c_4394, c_6513])).
% 8.19/2.81  tff(c_6582, plain, (r1_orders_2('#skF_6', '#skF_3'('#skF_5', '#skF_8', '#skF_9'), '#skF_4'('#skF_5', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_6')) | ~v5_orders_3('#skF_9', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_8')))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4485, c_6579])).
% 8.19/2.81  tff(c_6590, plain, (r1_orders_2('#skF_6', '#skF_3'('#skF_5', '#skF_8', '#skF_9'), '#skF_4'('#skF_5', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_609, c_4485, c_608, c_32, c_4411, c_4485, c_4370, c_4485, c_6582])).
% 8.19/2.81  tff(c_6599, plain, (![B_284]: (r1_orders_2(B_284, '#skF_3'('#skF_5', '#skF_8', '#skF_9'), '#skF_4'('#skF_5', '#skF_8', '#skF_9')) | g1_orders_2(u1_struct_0(B_284), u1_orders_2(B_284))!=g1_orders_2(u1_struct_0('#skF_6'), u1_orders_2('#skF_6')) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0(B_284)) | ~m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0(B_284)) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_6')) | ~l1_orders_2(B_284) | ~l1_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_6590, c_28])).
% 8.19/2.81  tff(c_6606, plain, (![B_859]: (r1_orders_2(B_859, '#skF_3'('#skF_5', '#skF_8', '#skF_9'), '#skF_4'('#skF_5', '#skF_8', '#skF_9')) | g1_orders_2(u1_struct_0(B_859), u1_orders_2(B_859))!=k7_lattice3(k7_lattice3('#skF_8')) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0(B_859)) | ~m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0(B_859)) | ~l1_orders_2(B_859))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_4411, c_4485, c_4370, c_4485, c_145, c_4485, c_299, c_6599])).
% 8.19/2.81  tff(c_6618, plain, (r1_orders_2('#skF_8', '#skF_3'('#skF_5', '#skF_8', '#skF_9'), '#skF_4'('#skF_5', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | ~l1_orders_2('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_145, c_6606])).
% 8.19/2.81  tff(c_6633, plain, (r1_orders_2('#skF_8', '#skF_3'('#skF_5', '#skF_8', '#skF_9'), '#skF_4'('#skF_5', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_4411, c_4370, c_6618])).
% 8.19/2.81  tff(c_6656, plain, (v5_orders_3('#skF_9', '#skF_5', '#skF_8') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_8')))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8') | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_6633, c_12])).
% 8.19/2.81  tff(c_6665, plain, (v5_orders_3('#skF_9', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_50, c_609, c_608, c_6656])).
% 8.19/2.81  tff(c_6667, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4371, c_6665])).
% 8.19/2.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.19/2.81  
% 8.19/2.81  Inference rules
% 8.19/2.81  ----------------------
% 8.19/2.81  #Ref     : 26
% 8.19/2.81  #Sup     : 1375
% 8.19/2.81  #Fact    : 0
% 8.19/2.81  #Define  : 0
% 8.19/2.81  #Split   : 13
% 8.19/2.81  #Chain   : 0
% 8.19/2.81  #Close   : 0
% 8.19/2.81  
% 8.19/2.81  Ordering : KBO
% 8.19/2.81  
% 8.19/2.81  Simplification rules
% 8.19/2.81  ----------------------
% 8.19/2.81  #Subsume      : 806
% 8.19/2.81  #Demod        : 4320
% 8.19/2.81  #Tautology    : 229
% 8.19/2.81  #SimpNegUnit  : 38
% 8.19/2.81  #BackRed      : 26
% 8.19/2.81  
% 8.19/2.81  #Partial instantiations: 0
% 8.19/2.81  #Strategies tried      : 1
% 8.19/2.81  
% 8.19/2.81  Timing (in seconds)
% 8.19/2.81  ----------------------
% 8.19/2.81  Preprocessing        : 0.34
% 8.19/2.81  Parsing              : 0.17
% 8.19/2.81  CNF conversion       : 0.04
% 8.19/2.81  Main loop            : 1.66
% 8.19/2.81  Inferencing          : 0.49
% 8.19/2.81  Reduction            : 0.74
% 8.19/2.81  Demodulation         : 0.56
% 8.19/2.81  BG Simplification    : 0.05
% 8.19/2.81  Subsumption          : 0.29
% 8.19/2.81  Abstraction          : 0.08
% 8.19/2.81  MUC search           : 0.00
% 8.19/2.81  Cooper               : 0.00
% 8.19/2.81  Total                : 2.07
% 8.19/2.81  Index Insertion      : 0.00
% 8.19/2.81  Index Deletion       : 0.00
% 8.19/2.81  Index Matching       : 0.00
% 8.19/2.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
