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
% DateTime   : Thu Dec  3 10:31:06 EST 2020

% Result     : Theorem 8.08s
% Output     : CNFRefutation 8.27s
% Verified   : 
% Statistics : Number of formulae       :  172 (4342 expanded)
%              Number of leaves         :   32 (1424 expanded)
%              Depth                    :   27
%              Number of atoms          :  564 (21646 expanded)
%              Number of equality atoms :   71 (5869 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_orders_3 > v1_funct_2 > r2_orders_2 > r1_orders_2 > m1_subset_1 > v2_struct_0 > v1_funct_1 > l1_orders_2 > k2_zfmisc_1 > k1_funct_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3

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

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

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

tff(f_103,axiom,(
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

tff(f_69,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(B),u1_orders_2(B))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ! [E] :
                        ( m1_subset_1(E,u1_struct_0(B))
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(B))
                           => ( ( C = E
                                & D = F )
                             => ( ( r1_orders_2(A,C,D)
                                 => r1_orders_2(B,E,F) )
                                & ( r2_orders_2(A,C,D)
                                 => r2_orders_2(B,E,F) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_0)).

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

tff(c_60,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2,plain,(
    ! [A_1] :
      ( m1_subset_1(u1_orders_2(A_1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1),u1_struct_0(A_1))))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_36,plain,(
    g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) = g1_orders_2(u1_struct_0('#skF_8'),u1_orders_2('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_85,plain,(
    ! [D_372,B_373,C_374,A_375] :
      ( D_372 = B_373
      | g1_orders_2(C_374,D_372) != g1_orders_2(A_375,B_373)
      | ~ m1_subset_1(B_373,k1_zfmisc_1(k2_zfmisc_1(A_375,A_375))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_107,plain,(
    ! [B_380,A_381] :
      ( u1_orders_2('#skF_6') = B_380
      | g1_orders_2(u1_struct_0('#skF_8'),u1_orders_2('#skF_8')) != g1_orders_2(A_381,B_380)
      | ~ m1_subset_1(B_380,k1_zfmisc_1(k2_zfmisc_1(A_381,A_381))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_85])).

tff(c_111,plain,(
    ! [A_1] :
      ( u1_orders_2(A_1) = u1_orders_2('#skF_6')
      | g1_orders_2(u1_struct_0(A_1),u1_orders_2(A_1)) != g1_orders_2(u1_struct_0('#skF_8'),u1_orders_2('#skF_8'))
      | ~ l1_orders_2(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_107])).

tff(c_114,plain,
    ( u1_orders_2('#skF_6') = u1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_8') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_111])).

tff(c_116,plain,(
    u1_orders_2('#skF_6') = u1_orders_2('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_114])).

tff(c_136,plain,
    ( m1_subset_1(u1_orders_2('#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_6'))))
    | ~ l1_orders_2('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_2])).

tff(c_140,plain,(
    m1_subset_1(u1_orders_2('#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_136])).

tff(c_132,plain,(
    g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_8')) = g1_orders_2(u1_struct_0('#skF_8'),u1_orders_2('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_36])).

tff(c_6,plain,(
    ! [C_6,A_2,D_7,B_3] :
      ( C_6 = A_2
      | g1_orders_2(C_6,D_7) != g1_orders_2(A_2,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(k2_zfmisc_1(A_2,A_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_146,plain,(
    ! [C_6,D_7] :
      ( u1_struct_0('#skF_6') = C_6
      | g1_orders_2(u1_struct_0('#skF_8'),u1_orders_2('#skF_8')) != g1_orders_2(C_6,D_7)
      | ~ m1_subset_1(u1_orders_2('#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_6')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_6])).

tff(c_154,plain,(
    ! [C_6,D_7] :
      ( u1_struct_0('#skF_6') = C_6
      | g1_orders_2(u1_struct_0('#skF_8'),u1_orders_2('#skF_8')) != g1_orders_2(C_6,D_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_146])).

tff(c_160,plain,(
    u1_struct_0('#skF_6') = u1_struct_0('#skF_8') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_154])).

tff(c_48,plain,(
    v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_194,plain,(
    v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_48])).

tff(c_62,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_38,plain,(
    g1_orders_2(u1_struct_0('#skF_7'),u1_orders_2('#skF_7')) = g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_98,plain,(
    ! [C_376,A_377,D_378,B_379] :
      ( C_376 = A_377
      | g1_orders_2(C_376,D_378) != g1_orders_2(A_377,B_379)
      | ~ m1_subset_1(B_379,k1_zfmisc_1(k2_zfmisc_1(A_377,A_377))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_306,plain,(
    ! [A_398,B_399] :
      ( u1_struct_0('#skF_7') = A_398
      | g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5')) != g1_orders_2(A_398,B_399)
      | ~ m1_subset_1(B_399,k1_zfmisc_1(k2_zfmisc_1(A_398,A_398))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_98])).

tff(c_314,plain,(
    ! [A_1] :
      ( u1_struct_0(A_1) = u1_struct_0('#skF_7')
      | g1_orders_2(u1_struct_0(A_1),u1_orders_2(A_1)) != g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5'))
      | ~ l1_orders_2(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_306])).

tff(c_318,plain,
    ( u1_struct_0('#skF_7') = u1_struct_0('#skF_5')
    | ~ l1_orders_2('#skF_5') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_314])).

tff(c_320,plain,(
    u1_struct_0('#skF_7') = u1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_318])).

tff(c_46,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_193,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_8')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_46])).

tff(c_20,plain,(
    ! [A_71,B_195,C_257] :
      ( m1_subset_1('#skF_4'(A_71,B_195,C_257),u1_struct_0(B_195))
      | v5_orders_3(C_257,A_71,B_195)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_71),u1_struct_0(B_195))))
      | ~ v1_funct_2(C_257,u1_struct_0(A_71),u1_struct_0(B_195))
      | ~ v1_funct_1(C_257)
      | ~ l1_orders_2(B_195)
      | ~ l1_orders_2(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_218,plain,
    ( m1_subset_1('#skF_4'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | v5_orders_3('#skF_9','#skF_5','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_193,c_20])).

tff(c_221,plain,
    ( m1_subset_1('#skF_4'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | v5_orders_3('#skF_9','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_50,c_194,c_218])).

tff(c_273,plain,(
    v5_orders_3('#skF_9','#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_42,plain,(
    v1_funct_2('#skF_10',u1_struct_0('#skF_7'),u1_struct_0('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_64,plain,(
    v1_funct_2('#skF_9',u1_struct_0('#skF_7'),u1_struct_0('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_42])).

tff(c_40,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_8')))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_65,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_8')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_40])).

tff(c_278,plain,(
    ! [A_395,B_396,C_397] :
      ( m1_subset_1('#skF_3'(A_395,B_396,C_397),u1_struct_0(B_396))
      | v5_orders_3(C_397,A_395,B_396)
      | ~ m1_subset_1(C_397,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_395),u1_struct_0(B_396))))
      | ~ v1_funct_2(C_397,u1_struct_0(A_395),u1_struct_0(B_396))
      | ~ v1_funct_1(C_397)
      | ~ l1_orders_2(B_396)
      | ~ l1_orders_2(A_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_290,plain,
    ( m1_subset_1('#skF_3'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | v5_orders_3('#skF_9','#skF_7','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_7'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_65,c_278])).

tff(c_304,plain,
    ( m1_subset_1('#skF_3'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | v5_orders_3('#skF_9','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_64,c_290])).

tff(c_305,plain,(
    m1_subset_1('#skF_3'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_304])).

tff(c_170,plain,(
    ! [A_385,B_386,C_387] :
      ( m1_subset_1('#skF_4'(A_385,B_386,C_387),u1_struct_0(B_386))
      | v5_orders_3(C_387,A_385,B_386)
      | ~ m1_subset_1(C_387,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_385),u1_struct_0(B_386))))
      | ~ v1_funct_2(C_387,u1_struct_0(A_385),u1_struct_0(B_386))
      | ~ v1_funct_1(C_387)
      | ~ l1_orders_2(B_386)
      | ~ l1_orders_2(A_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_176,plain,
    ( m1_subset_1('#skF_4'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | v5_orders_3('#skF_9','#skF_7','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_7'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_65,c_170])).

tff(c_185,plain,
    ( m1_subset_1('#skF_4'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | v5_orders_3('#skF_9','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_64,c_176])).

tff(c_186,plain,(
    m1_subset_1('#skF_4'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_185])).

tff(c_728,plain,(
    ! [C_426,A_427,B_428] :
      ( k1_funct_1(C_426,'#skF_1'(A_427,B_428,C_426)) = '#skF_3'(A_427,B_428,C_426)
      | v5_orders_3(C_426,A_427,B_428)
      | ~ m1_subset_1(C_426,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_427),u1_struct_0(B_428))))
      | ~ v1_funct_2(C_426,u1_struct_0(A_427),u1_struct_0(B_428))
      | ~ v1_funct_1(C_426)
      | ~ l1_orders_2(B_428)
      | ~ l1_orders_2(A_427) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_732,plain,(
    ! [C_426,B_428] :
      ( k1_funct_1(C_426,'#skF_1'('#skF_7',B_428,C_426)) = '#skF_3'('#skF_7',B_428,C_426)
      | v5_orders_3(C_426,'#skF_7',B_428)
      | ~ m1_subset_1(C_426,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_428))))
      | ~ v1_funct_2(C_426,u1_struct_0('#skF_7'),u1_struct_0(B_428))
      | ~ v1_funct_1(C_426)
      | ~ l1_orders_2(B_428)
      | ~ l1_orders_2('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_728])).

tff(c_2544,plain,(
    ! [C_602,B_603] :
      ( k1_funct_1(C_602,'#skF_1'('#skF_7',B_603,C_602)) = '#skF_3'('#skF_7',B_603,C_602)
      | v5_orders_3(C_602,'#skF_7',B_603)
      | ~ m1_subset_1(C_602,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_603))))
      | ~ v1_funct_2(C_602,u1_struct_0('#skF_5'),u1_struct_0(B_603))
      | ~ v1_funct_1(C_602)
      | ~ l1_orders_2(B_603) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_320,c_732])).

tff(c_2550,plain,
    ( k1_funct_1('#skF_9','#skF_1'('#skF_7','#skF_8','#skF_9')) = '#skF_3'('#skF_7','#skF_8','#skF_9')
    | v5_orders_3('#skF_9','#skF_7','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_193,c_2544])).

tff(c_2563,plain,
    ( k1_funct_1('#skF_9','#skF_1'('#skF_7','#skF_8','#skF_9')) = '#skF_3'('#skF_7','#skF_8','#skF_9')
    | v5_orders_3('#skF_9','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_194,c_2550])).

tff(c_2564,plain,(
    k1_funct_1('#skF_9','#skF_1'('#skF_7','#skF_8','#skF_9')) = '#skF_3'('#skF_7','#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_2563])).

tff(c_504,plain,(
    ! [C_410,A_411,B_412] :
      ( k1_funct_1(C_410,'#skF_2'(A_411,B_412,C_410)) = '#skF_4'(A_411,B_412,C_410)
      | v5_orders_3(C_410,A_411,B_412)
      | ~ m1_subset_1(C_410,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_411),u1_struct_0(B_412))))
      | ~ v1_funct_2(C_410,u1_struct_0(A_411),u1_struct_0(B_412))
      | ~ v1_funct_1(C_410)
      | ~ l1_orders_2(B_412)
      | ~ l1_orders_2(A_411) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_508,plain,(
    ! [C_410,B_412] :
      ( k1_funct_1(C_410,'#skF_2'('#skF_7',B_412,C_410)) = '#skF_4'('#skF_7',B_412,C_410)
      | v5_orders_3(C_410,'#skF_7',B_412)
      | ~ m1_subset_1(C_410,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_412))))
      | ~ v1_funct_2(C_410,u1_struct_0('#skF_7'),u1_struct_0(B_412))
      | ~ v1_funct_1(C_410)
      | ~ l1_orders_2(B_412)
      | ~ l1_orders_2('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_504])).

tff(c_2698,plain,(
    ! [C_617,B_618] :
      ( k1_funct_1(C_617,'#skF_2'('#skF_7',B_618,C_617)) = '#skF_4'('#skF_7',B_618,C_617)
      | v5_orders_3(C_617,'#skF_7',B_618)
      | ~ m1_subset_1(C_617,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_618))))
      | ~ v1_funct_2(C_617,u1_struct_0('#skF_5'),u1_struct_0(B_618))
      | ~ v1_funct_1(C_617)
      | ~ l1_orders_2(B_618) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_320,c_508])).

tff(c_2704,plain,
    ( k1_funct_1('#skF_9','#skF_2'('#skF_7','#skF_8','#skF_9')) = '#skF_4'('#skF_7','#skF_8','#skF_9')
    | v5_orders_3('#skF_9','#skF_7','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_193,c_2698])).

tff(c_2717,plain,
    ( k1_funct_1('#skF_9','#skF_2'('#skF_7','#skF_8','#skF_9')) = '#skF_4'('#skF_7','#skF_8','#skF_9')
    | v5_orders_3('#skF_9','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_194,c_2704])).

tff(c_2718,plain,(
    k1_funct_1('#skF_9','#skF_2'('#skF_7','#skF_8','#skF_9')) = '#skF_4'('#skF_7','#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_2717])).

tff(c_245,plain,(
    ! [A_392,B_393,C_394] :
      ( m1_subset_1('#skF_1'(A_392,B_393,C_394),u1_struct_0(A_392))
      | v5_orders_3(C_394,A_392,B_393)
      | ~ m1_subset_1(C_394,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_392),u1_struct_0(B_393))))
      | ~ v1_funct_2(C_394,u1_struct_0(A_392),u1_struct_0(B_393))
      | ~ v1_funct_1(C_394)
      | ~ l1_orders_2(B_393)
      | ~ l1_orders_2(A_392) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_257,plain,
    ( m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | v5_orders_3('#skF_9','#skF_7','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_7'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_65,c_245])).

tff(c_271,plain,
    ( m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
    | v5_orders_3('#skF_9','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_64,c_257])).

tff(c_272,plain,(
    m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_271])).

tff(c_331,plain,(
    m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_272])).

tff(c_391,plain,(
    ! [A_401,B_402,C_403] :
      ( m1_subset_1('#skF_2'(A_401,B_402,C_403),u1_struct_0(A_401))
      | v5_orders_3(C_403,A_401,B_402)
      | ~ m1_subset_1(C_403,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_401),u1_struct_0(B_402))))
      | ~ v1_funct_2(C_403,u1_struct_0(A_401),u1_struct_0(B_402))
      | ~ v1_funct_1(C_403)
      | ~ l1_orders_2(B_402)
      | ~ l1_orders_2(A_401) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_395,plain,(
    ! [B_402,C_403] :
      ( m1_subset_1('#skF_2'('#skF_7',B_402,C_403),u1_struct_0('#skF_7'))
      | v5_orders_3(C_403,'#skF_7',B_402)
      | ~ m1_subset_1(C_403,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_402))))
      | ~ v1_funct_2(C_403,u1_struct_0('#skF_7'),u1_struct_0(B_402))
      | ~ v1_funct_1(C_403)
      | ~ l1_orders_2(B_402)
      | ~ l1_orders_2('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_391])).

tff(c_2008,plain,(
    ! [B_552,C_553] :
      ( m1_subset_1('#skF_2'('#skF_7',B_552,C_553),u1_struct_0('#skF_5'))
      | v5_orders_3(C_553,'#skF_7',B_552)
      | ~ m1_subset_1(C_553,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_552))))
      | ~ v1_funct_2(C_553,u1_struct_0('#skF_5'),u1_struct_0(B_552))
      | ~ v1_funct_1(C_553)
      | ~ l1_orders_2(B_552) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_320,c_320,c_395])).

tff(c_2017,plain,
    ( m1_subset_1('#skF_2'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
    | v5_orders_3('#skF_9','#skF_7','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_193,c_2008])).

tff(c_2032,plain,
    ( m1_subset_1('#skF_2'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
    | v5_orders_3('#skF_9','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_194,c_2017])).

tff(c_2033,plain,(
    m1_subset_1('#skF_2'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_2032])).

tff(c_352,plain,
    ( m1_subset_1(u1_orders_2('#skF_7'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_7'))))
    | ~ l1_orders_2('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_2])).

tff(c_371,plain,(
    m1_subset_1(u1_orders_2('#skF_7'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_320,c_352])).

tff(c_332,plain,(
    g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_7')) = g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_38])).

tff(c_4,plain,(
    ! [D_7,B_3,C_6,A_2] :
      ( D_7 = B_3
      | g1_orders_2(C_6,D_7) != g1_orders_2(A_2,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(k2_zfmisc_1(A_2,A_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_440,plain,(
    ! [D_7,C_6] :
      ( u1_orders_2('#skF_7') = D_7
      | g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5')) != g1_orders_2(C_6,D_7)
      | ~ m1_subset_1(u1_orders_2('#skF_7'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_4])).

tff(c_446,plain,(
    ! [D_7,C_6] :
      ( u1_orders_2('#skF_7') = D_7
      | g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5')) != g1_orders_2(C_6,D_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_440])).

tff(c_459,plain,(
    u1_orders_2('#skF_7') = u1_orders_2('#skF_5') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_446])).

tff(c_581,plain,(
    ! [A_418,B_419,C_420] :
      ( r1_orders_2(A_418,'#skF_1'(A_418,B_419,C_420),'#skF_2'(A_418,B_419,C_420))
      | v5_orders_3(C_420,A_418,B_419)
      | ~ m1_subset_1(C_420,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_418),u1_struct_0(B_419))))
      | ~ v1_funct_2(C_420,u1_struct_0(A_418),u1_struct_0(B_419))
      | ~ v1_funct_1(C_420)
      | ~ l1_orders_2(B_419)
      | ~ l1_orders_2(A_418) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_585,plain,(
    ! [B_419,C_420] :
      ( r1_orders_2('#skF_7','#skF_1'('#skF_7',B_419,C_420),'#skF_2'('#skF_7',B_419,C_420))
      | v5_orders_3(C_420,'#skF_7',B_419)
      | ~ m1_subset_1(C_420,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_419))))
      | ~ v1_funct_2(C_420,u1_struct_0('#skF_7'),u1_struct_0(B_419))
      | ~ v1_funct_1(C_420)
      | ~ l1_orders_2(B_419)
      | ~ l1_orders_2('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_581])).

tff(c_2445,plain,(
    ! [B_596,C_597] :
      ( r1_orders_2('#skF_7','#skF_1'('#skF_7',B_596,C_597),'#skF_2'('#skF_7',B_596,C_597))
      | v5_orders_3(C_597,'#skF_7',B_596)
      | ~ m1_subset_1(C_597,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_596))))
      | ~ v1_funct_2(C_597,u1_struct_0('#skF_5'),u1_struct_0(B_596))
      | ~ v1_funct_1(C_597)
      | ~ l1_orders_2(B_596) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_320,c_585])).

tff(c_2451,plain,
    ( r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_2'('#skF_7','#skF_8','#skF_9'))
    | v5_orders_3('#skF_9','#skF_7','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_193,c_2445])).

tff(c_2464,plain,
    ( r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_2'('#skF_7','#skF_8','#skF_9'))
    | v5_orders_3('#skF_9','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_194,c_2451])).

tff(c_2465,plain,(
    r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_2'('#skF_7','#skF_8','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_2464])).

tff(c_10,plain,(
    ! [B_40,E_68,F_70,A_8] :
      ( r1_orders_2(B_40,E_68,F_70)
      | ~ r1_orders_2(A_8,E_68,F_70)
      | ~ m1_subset_1(F_70,u1_struct_0(B_40))
      | ~ m1_subset_1(E_68,u1_struct_0(B_40))
      | ~ m1_subset_1(F_70,u1_struct_0(A_8))
      | ~ m1_subset_1(E_68,u1_struct_0(A_8))
      | g1_orders_2(u1_struct_0(B_40),u1_orders_2(B_40)) != g1_orders_2(u1_struct_0(A_8),u1_orders_2(A_8))
      | ~ l1_orders_2(B_40)
      | ~ l1_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2474,plain,(
    ! [B_40] :
      ( r1_orders_2(B_40,'#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_2'('#skF_7','#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_2'('#skF_7','#skF_8','#skF_9'),u1_struct_0(B_40))
      | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0(B_40))
      | ~ m1_subset_1('#skF_2'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
      | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_7'))
      | g1_orders_2(u1_struct_0(B_40),u1_orders_2(B_40)) != g1_orders_2(u1_struct_0('#skF_7'),u1_orders_2('#skF_7'))
      | ~ l1_orders_2(B_40)
      | ~ l1_orders_2('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_2465,c_10])).

tff(c_2480,plain,(
    ! [B_40] :
      ( r1_orders_2(B_40,'#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_2'('#skF_7','#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_2'('#skF_7','#skF_8','#skF_9'),u1_struct_0(B_40))
      | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0(B_40))
      | g1_orders_2(u1_struct_0(B_40),u1_orders_2(B_40)) != g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5'))
      | ~ l1_orders_2(B_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_320,c_459,c_331,c_320,c_2033,c_320,c_2474])).

tff(c_2676,plain,
    ( r1_orders_2('#skF_5','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_2'('#skF_7','#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_2'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2480])).

tff(c_2678,plain,(
    r1_orders_2('#skF_5','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_2'('#skF_7','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_331,c_2033,c_2676])).

tff(c_12,plain,(
    ! [E_296,D_288,C_257,A_71,B_195] :
      ( r1_orders_2(B_195,k1_funct_1(C_257,D_288),k1_funct_1(C_257,E_296))
      | ~ m1_subset_1(k1_funct_1(C_257,E_296),u1_struct_0(B_195))
      | ~ m1_subset_1(k1_funct_1(C_257,D_288),u1_struct_0(B_195))
      | ~ r1_orders_2(A_71,D_288,E_296)
      | ~ m1_subset_1(E_296,u1_struct_0(A_71))
      | ~ m1_subset_1(D_288,u1_struct_0(A_71))
      | ~ v5_orders_3(C_257,A_71,B_195)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_71),u1_struct_0(B_195))))
      | ~ v1_funct_2(C_257,u1_struct_0(A_71),u1_struct_0(B_195))
      | ~ v1_funct_1(C_257)
      | ~ l1_orders_2(B_195)
      | ~ l1_orders_2(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2689,plain,(
    ! [B_195,C_257] :
      ( r1_orders_2(B_195,k1_funct_1(C_257,'#skF_1'('#skF_7','#skF_8','#skF_9')),k1_funct_1(C_257,'#skF_2'('#skF_7','#skF_8','#skF_9')))
      | ~ m1_subset_1(k1_funct_1(C_257,'#skF_2'('#skF_7','#skF_8','#skF_9')),u1_struct_0(B_195))
      | ~ m1_subset_1(k1_funct_1(C_257,'#skF_1'('#skF_7','#skF_8','#skF_9')),u1_struct_0(B_195))
      | ~ m1_subset_1('#skF_2'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
      | ~ v5_orders_3(C_257,'#skF_5',B_195)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_195))))
      | ~ v1_funct_2(C_257,u1_struct_0('#skF_5'),u1_struct_0(B_195))
      | ~ v1_funct_1(C_257)
      | ~ l1_orders_2(B_195)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2678,c_12])).

tff(c_3203,plain,(
    ! [B_662,C_663] :
      ( r1_orders_2(B_662,k1_funct_1(C_663,'#skF_1'('#skF_7','#skF_8','#skF_9')),k1_funct_1(C_663,'#skF_2'('#skF_7','#skF_8','#skF_9')))
      | ~ m1_subset_1(k1_funct_1(C_663,'#skF_2'('#skF_7','#skF_8','#skF_9')),u1_struct_0(B_662))
      | ~ m1_subset_1(k1_funct_1(C_663,'#skF_1'('#skF_7','#skF_8','#skF_9')),u1_struct_0(B_662))
      | ~ v5_orders_3(C_663,'#skF_5',B_662)
      | ~ m1_subset_1(C_663,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_662))))
      | ~ v1_funct_2(C_663,u1_struct_0('#skF_5'),u1_struct_0(B_662))
      | ~ v1_funct_1(C_663)
      | ~ l1_orders_2(B_662) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_331,c_2033,c_2689])).

tff(c_3210,plain,(
    ! [B_662] :
      ( r1_orders_2(B_662,k1_funct_1('#skF_9','#skF_1'('#skF_7','#skF_8','#skF_9')),'#skF_4'('#skF_7','#skF_8','#skF_9'))
      | ~ m1_subset_1(k1_funct_1('#skF_9','#skF_2'('#skF_7','#skF_8','#skF_9')),u1_struct_0(B_662))
      | ~ m1_subset_1(k1_funct_1('#skF_9','#skF_1'('#skF_7','#skF_8','#skF_9')),u1_struct_0(B_662))
      | ~ v5_orders_3('#skF_9','#skF_5',B_662)
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_662))))
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0(B_662))
      | ~ v1_funct_1('#skF_9')
      | ~ l1_orders_2(B_662) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2718,c_3203])).

tff(c_3220,plain,(
    ! [B_664] :
      ( r1_orders_2(B_664,'#skF_3'('#skF_7','#skF_8','#skF_9'),'#skF_4'('#skF_7','#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_4'('#skF_7','#skF_8','#skF_9'),u1_struct_0(B_664))
      | ~ m1_subset_1('#skF_3'('#skF_7','#skF_8','#skF_9'),u1_struct_0(B_664))
      | ~ v5_orders_3('#skF_9','#skF_5',B_664)
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_664))))
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0(B_664))
      | ~ l1_orders_2(B_664) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2564,c_2718,c_2564,c_3210])).

tff(c_3226,plain,
    ( r1_orders_2('#skF_8','#skF_3'('#skF_7','#skF_8','#skF_9'),'#skF_4'('#skF_7','#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_4'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ v5_orders_3('#skF_9','#skF_5','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_193,c_3220])).

tff(c_3234,plain,(
    r1_orders_2('#skF_8','#skF_3'('#skF_7','#skF_8','#skF_9'),'#skF_4'('#skF_7','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_194,c_273,c_305,c_186,c_3226])).

tff(c_14,plain,(
    ! [B_195,A_71,C_257] :
      ( ~ r1_orders_2(B_195,'#skF_3'(A_71,B_195,C_257),'#skF_4'(A_71,B_195,C_257))
      | v5_orders_3(C_257,A_71,B_195)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_71),u1_struct_0(B_195))))
      | ~ v1_funct_2(C_257,u1_struct_0(A_71),u1_struct_0(B_195))
      | ~ v1_funct_1(C_257)
      | ~ l1_orders_2(B_195)
      | ~ l1_orders_2(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3252,plain,
    ( v5_orders_3('#skF_9','#skF_7','#skF_8')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_8'))))
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_7'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_3234,c_14])).

tff(c_3261,plain,(
    v5_orders_3('#skF_9','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_194,c_320,c_193,c_320,c_3252])).

tff(c_3263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_3261])).

tff(c_3265,plain,(
    ~ v5_orders_3('#skF_9','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_3299,plain,(
    ! [A_668,B_669,C_670] :
      ( m1_subset_1('#skF_3'(A_668,B_669,C_670),u1_struct_0(B_669))
      | v5_orders_3(C_670,A_668,B_669)
      | ~ m1_subset_1(C_670,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_668),u1_struct_0(B_669))))
      | ~ v1_funct_2(C_670,u1_struct_0(A_668),u1_struct_0(B_669))
      | ~ v1_funct_1(C_670)
      | ~ l1_orders_2(B_669)
      | ~ l1_orders_2(A_668) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3303,plain,
    ( m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | v5_orders_3('#skF_9','#skF_5','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_193,c_3299])).

tff(c_3317,plain,
    ( m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | v5_orders_3('#skF_9','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_50,c_194,c_3303])).

tff(c_3318,plain,(
    m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_3265,c_3317])).

tff(c_3264,plain,(
    m1_subset_1('#skF_4'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_32,plain,(
    v5_orders_3('#skF_9','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_3628,plain,(
    ! [C_691,A_692,B_693] :
      ( k1_funct_1(C_691,'#skF_1'(A_692,B_693,C_691)) = '#skF_3'(A_692,B_693,C_691)
      | v5_orders_3(C_691,A_692,B_693)
      | ~ m1_subset_1(C_691,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_692),u1_struct_0(B_693))))
      | ~ v1_funct_2(C_691,u1_struct_0(A_692),u1_struct_0(B_693))
      | ~ v1_funct_1(C_691)
      | ~ l1_orders_2(B_693)
      | ~ l1_orders_2(A_692) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3638,plain,
    ( k1_funct_1('#skF_9','#skF_1'('#skF_5','#skF_8','#skF_9')) = '#skF_3'('#skF_5','#skF_8','#skF_9')
    | v5_orders_3('#skF_9','#skF_5','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_193,c_3628])).

tff(c_3657,plain,
    ( k1_funct_1('#skF_9','#skF_1'('#skF_5','#skF_8','#skF_9')) = '#skF_3'('#skF_5','#skF_8','#skF_9')
    | v5_orders_3('#skF_9','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_50,c_194,c_3638])).

tff(c_3658,plain,(
    k1_funct_1('#skF_9','#skF_1'('#skF_5','#skF_8','#skF_9')) = '#skF_3'('#skF_5','#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_3265,c_3657])).

tff(c_3540,plain,(
    ! [C_681,A_682,B_683] :
      ( k1_funct_1(C_681,'#skF_2'(A_682,B_683,C_681)) = '#skF_4'(A_682,B_683,C_681)
      | v5_orders_3(C_681,A_682,B_683)
      | ~ m1_subset_1(C_681,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_682),u1_struct_0(B_683))))
      | ~ v1_funct_2(C_681,u1_struct_0(A_682),u1_struct_0(B_683))
      | ~ v1_funct_1(C_681)
      | ~ l1_orders_2(B_683)
      | ~ l1_orders_2(A_682) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3550,plain,
    ( k1_funct_1('#skF_9','#skF_2'('#skF_5','#skF_8','#skF_9')) = '#skF_4'('#skF_5','#skF_8','#skF_9')
    | v5_orders_3('#skF_9','#skF_5','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_193,c_3540])).

tff(c_3569,plain,
    ( k1_funct_1('#skF_9','#skF_2'('#skF_5','#skF_8','#skF_9')) = '#skF_4'('#skF_5','#skF_8','#skF_9')
    | v5_orders_3('#skF_9','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_50,c_194,c_3550])).

tff(c_3570,plain,(
    k1_funct_1('#skF_9','#skF_2'('#skF_5','#skF_8','#skF_9')) = '#skF_4'('#skF_5','#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_3265,c_3569])).

tff(c_249,plain,
    ( m1_subset_1('#skF_1'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
    | v5_orders_3('#skF_9','#skF_5','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_193,c_245])).

tff(c_263,plain,
    ( m1_subset_1('#skF_1'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
    | v5_orders_3('#skF_9','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_50,c_194,c_249])).

tff(c_3296,plain,(
    m1_subset_1('#skF_1'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_3265,c_263])).

tff(c_3266,plain,(
    ! [A_665,B_666,C_667] :
      ( m1_subset_1('#skF_2'(A_665,B_666,C_667),u1_struct_0(A_665))
      | v5_orders_3(C_667,A_665,B_666)
      | ~ m1_subset_1(C_667,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_665),u1_struct_0(B_666))))
      | ~ v1_funct_2(C_667,u1_struct_0(A_665),u1_struct_0(B_666))
      | ~ v1_funct_1(C_667)
      | ~ l1_orders_2(B_666)
      | ~ l1_orders_2(A_665) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3270,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
    | v5_orders_3('#skF_9','#skF_5','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_193,c_3266])).

tff(c_3284,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
    | v5_orders_3('#skF_9','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_50,c_194,c_3270])).

tff(c_3295,plain,(
    m1_subset_1('#skF_2'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_3265,c_3284])).

tff(c_3406,plain,(
    ! [A_674,B_675,C_676] :
      ( r1_orders_2(A_674,'#skF_1'(A_674,B_675,C_676),'#skF_2'(A_674,B_675,C_676))
      | v5_orders_3(C_676,A_674,B_675)
      | ~ m1_subset_1(C_676,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_674),u1_struct_0(B_675))))
      | ~ v1_funct_2(C_676,u1_struct_0(A_674),u1_struct_0(B_675))
      | ~ v1_funct_1(C_676)
      | ~ l1_orders_2(B_675)
      | ~ l1_orders_2(A_674) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3414,plain,
    ( r1_orders_2('#skF_5','#skF_1'('#skF_5','#skF_8','#skF_9'),'#skF_2'('#skF_5','#skF_8','#skF_9'))
    | v5_orders_3('#skF_9','#skF_5','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_193,c_3406])).

tff(c_3430,plain,
    ( r1_orders_2('#skF_5','#skF_1'('#skF_5','#skF_8','#skF_9'),'#skF_2'('#skF_5','#skF_8','#skF_9'))
    | v5_orders_3('#skF_9','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_50,c_194,c_3414])).

tff(c_3431,plain,(
    r1_orders_2('#skF_5','#skF_1'('#skF_5','#skF_8','#skF_9'),'#skF_2'('#skF_5','#skF_8','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_3265,c_3430])).

tff(c_3851,plain,(
    ! [C_713,A_717,B_716,D_714,E_715] :
      ( r1_orders_2(B_716,k1_funct_1(C_713,D_714),k1_funct_1(C_713,E_715))
      | ~ m1_subset_1(k1_funct_1(C_713,E_715),u1_struct_0(B_716))
      | ~ m1_subset_1(k1_funct_1(C_713,D_714),u1_struct_0(B_716))
      | ~ r1_orders_2(A_717,D_714,E_715)
      | ~ m1_subset_1(E_715,u1_struct_0(A_717))
      | ~ m1_subset_1(D_714,u1_struct_0(A_717))
      | ~ v5_orders_3(C_713,A_717,B_716)
      | ~ m1_subset_1(C_713,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_717),u1_struct_0(B_716))))
      | ~ v1_funct_2(C_713,u1_struct_0(A_717),u1_struct_0(B_716))
      | ~ v1_funct_1(C_713)
      | ~ l1_orders_2(B_716)
      | ~ l1_orders_2(A_717) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3855,plain,(
    ! [B_716,C_713] :
      ( r1_orders_2(B_716,k1_funct_1(C_713,'#skF_1'('#skF_5','#skF_8','#skF_9')),k1_funct_1(C_713,'#skF_2'('#skF_5','#skF_8','#skF_9')))
      | ~ m1_subset_1(k1_funct_1(C_713,'#skF_2'('#skF_5','#skF_8','#skF_9')),u1_struct_0(B_716))
      | ~ m1_subset_1(k1_funct_1(C_713,'#skF_1'('#skF_5','#skF_8','#skF_9')),u1_struct_0(B_716))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_1'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
      | ~ v5_orders_3(C_713,'#skF_5',B_716)
      | ~ m1_subset_1(C_713,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_716))))
      | ~ v1_funct_2(C_713,u1_struct_0('#skF_5'),u1_struct_0(B_716))
      | ~ v1_funct_1(C_713)
      | ~ l1_orders_2(B_716)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3431,c_3851])).

tff(c_6218,plain,(
    ! [B_920,C_921] :
      ( r1_orders_2(B_920,k1_funct_1(C_921,'#skF_1'('#skF_5','#skF_8','#skF_9')),k1_funct_1(C_921,'#skF_2'('#skF_5','#skF_8','#skF_9')))
      | ~ m1_subset_1(k1_funct_1(C_921,'#skF_2'('#skF_5','#skF_8','#skF_9')),u1_struct_0(B_920))
      | ~ m1_subset_1(k1_funct_1(C_921,'#skF_1'('#skF_5','#skF_8','#skF_9')),u1_struct_0(B_920))
      | ~ v5_orders_3(C_921,'#skF_5',B_920)
      | ~ m1_subset_1(C_921,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_920))))
      | ~ v1_funct_2(C_921,u1_struct_0('#skF_5'),u1_struct_0(B_920))
      | ~ v1_funct_1(C_921)
      | ~ l1_orders_2(B_920) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3296,c_3295,c_3855])).

tff(c_6225,plain,(
    ! [B_920] :
      ( r1_orders_2(B_920,'#skF_3'('#skF_5','#skF_8','#skF_9'),k1_funct_1('#skF_9','#skF_2'('#skF_5','#skF_8','#skF_9')))
      | ~ m1_subset_1(k1_funct_1('#skF_9','#skF_2'('#skF_5','#skF_8','#skF_9')),u1_struct_0(B_920))
      | ~ m1_subset_1(k1_funct_1('#skF_9','#skF_1'('#skF_5','#skF_8','#skF_9')),u1_struct_0(B_920))
      | ~ v5_orders_3('#skF_9','#skF_5',B_920)
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_920))))
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0(B_920))
      | ~ v1_funct_1('#skF_9')
      | ~ l1_orders_2(B_920) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3658,c_6218])).

tff(c_6235,plain,(
    ! [B_922] :
      ( r1_orders_2(B_922,'#skF_3'('#skF_5','#skF_8','#skF_9'),'#skF_4'('#skF_5','#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_8','#skF_9'),u1_struct_0(B_922))
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_9'),u1_struct_0(B_922))
      | ~ v5_orders_3('#skF_9','#skF_5',B_922)
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_922))))
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0(B_922))
      | ~ l1_orders_2(B_922) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_3658,c_3570,c_3570,c_6225])).

tff(c_6244,plain,
    ( r1_orders_2('#skF_6','#skF_3'('#skF_5','#skF_8','#skF_9'),'#skF_4'('#skF_5','#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_4'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_6'))
    | ~ v5_orders_3('#skF_9','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))))
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_6235])).

tff(c_6251,plain,(
    r1_orders_2('#skF_6','#skF_3'('#skF_5','#skF_8','#skF_9'),'#skF_4'('#skF_5','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_194,c_160,c_193,c_32,c_3318,c_160,c_3264,c_160,c_6244])).

tff(c_6255,plain,(
    ! [B_40] :
      ( r1_orders_2(B_40,'#skF_3'('#skF_5','#skF_8','#skF_9'),'#skF_4'('#skF_5','#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_8','#skF_9'),u1_struct_0(B_40))
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_9'),u1_struct_0(B_40))
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_6'))
      | g1_orders_2(u1_struct_0(B_40),u1_orders_2(B_40)) != g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6'))
      | ~ l1_orders_2(B_40)
      | ~ l1_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_6251,c_10])).

tff(c_6261,plain,(
    ! [B_40] :
      ( r1_orders_2(B_40,'#skF_3'('#skF_5','#skF_8','#skF_9'),'#skF_4'('#skF_5','#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_8','#skF_9'),u1_struct_0(B_40))
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_9'),u1_struct_0(B_40))
      | g1_orders_2(u1_struct_0(B_40),u1_orders_2(B_40)) != g1_orders_2(u1_struct_0('#skF_8'),u1_orders_2('#skF_8'))
      | ~ l1_orders_2(B_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_116,c_160,c_3318,c_160,c_3264,c_160,c_6255])).

tff(c_6300,plain,
    ( r1_orders_2('#skF_8','#skF_3'('#skF_5','#skF_8','#skF_9'),'#skF_4'('#skF_5','#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_4'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ l1_orders_2('#skF_8') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_6261])).

tff(c_6302,plain,(
    r1_orders_2('#skF_8','#skF_3'('#skF_5','#skF_8','#skF_9'),'#skF_4'('#skF_5','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3318,c_3264,c_6300])).

tff(c_6325,plain,
    ( v5_orders_3('#skF_9','#skF_5','#skF_8')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))))
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_6302,c_14])).

tff(c_6334,plain,(
    v5_orders_3('#skF_9','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_50,c_194,c_193,c_6325])).

tff(c_6336,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3265,c_6334])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:18:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.08/2.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.20/2.75  
% 8.20/2.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.27/2.75  %$ v5_orders_3 > v1_funct_2 > r2_orders_2 > r1_orders_2 > m1_subset_1 > v2_struct_0 > v1_funct_1 > l1_orders_2 > k2_zfmisc_1 > k1_funct_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3
% 8.27/2.75  
% 8.27/2.75  %Foreground sorts:
% 8.27/2.75  
% 8.27/2.75  
% 8.27/2.75  %Background operators:
% 8.27/2.75  
% 8.27/2.75  
% 8.27/2.75  %Foreground operators:
% 8.27/2.75  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.27/2.75  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.27/2.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.27/2.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.27/2.75  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 8.27/2.75  tff(v5_orders_3, type, v5_orders_3: ($i * $i * $i) > $o).
% 8.27/2.75  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.27/2.75  tff('#skF_7', type, '#skF_7': $i).
% 8.27/2.75  tff('#skF_10', type, '#skF_10': $i).
% 8.27/2.75  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 8.27/2.75  tff('#skF_5', type, '#skF_5': $i).
% 8.27/2.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.27/2.75  tff('#skF_6', type, '#skF_6': $i).
% 8.27/2.75  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.27/2.75  tff('#skF_9', type, '#skF_9': $i).
% 8.27/2.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.27/2.75  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.27/2.75  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 8.27/2.75  tff('#skF_8', type, '#skF_8': $i).
% 8.27/2.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.27/2.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.27/2.75  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.27/2.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.27/2.75  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 8.27/2.75  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 8.27/2.75  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.27/2.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.27/2.75  
% 8.27/2.78  tff(f_145, negated_conjecture, ~(![A]: (l1_orders_2(A) => (![B]: (l1_orders_2(B) => (![C]: ((~v2_struct_0(C) & l1_orders_2(C)) => (![D]: ((~v2_struct_0(D) & l1_orders_2(D)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(D))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(D))))) => (((((g1_orders_2(u1_struct_0(A), u1_orders_2(A)) = g1_orders_2(u1_struct_0(C), u1_orders_2(C))) & (g1_orders_2(u1_struct_0(B), u1_orders_2(B)) = g1_orders_2(u1_struct_0(D), u1_orders_2(D)))) & (E = F)) & v5_orders_3(E, A, B)) => v5_orders_3(F, C, D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_waybel_9)).
% 8.27/2.78  tff(f_29, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 8.27/2.78  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C, D]: ((g1_orders_2(A, B) = g1_orders_2(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_orders_2)).
% 8.27/2.78  tff(f_103, axiom, (![A]: (l1_orders_2(A) => (![B]: (l1_orders_2(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v5_orders_3(C, A, B) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => (r1_orders_2(A, D, E) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(B)) => (((F = k1_funct_1(C, D)) & (G = k1_funct_1(C, E))) => r1_orders_2(B, F, G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_orders_3)).
% 8.27/2.78  tff(f_69, axiom, (![A]: (l1_orders_2(A) => (![B]: (l1_orders_2(B) => ((g1_orders_2(u1_struct_0(A), u1_orders_2(A)) = g1_orders_2(u1_struct_0(B), u1_orders_2(B))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (((C = E) & (D = F)) => ((r1_orders_2(A, C, D) => r1_orders_2(B, E, F)) & (r2_orders_2(A, C, D) => r2_orders_2(B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_0)).
% 8.27/2.78  tff(c_34, plain, ('#skF_10'='#skF_9'), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.27/2.78  tff(c_30, plain, (~v5_orders_3('#skF_10', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.27/2.78  tff(c_67, plain, (~v5_orders_3('#skF_9', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30])).
% 8.27/2.78  tff(c_56, plain, (l1_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.27/2.78  tff(c_52, plain, (l1_orders_2('#skF_8')), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.27/2.78  tff(c_50, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.27/2.78  tff(c_60, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.27/2.78  tff(c_2, plain, (![A_1]: (m1_subset_1(u1_orders_2(A_1), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1), u1_struct_0(A_1)))) | ~l1_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.27/2.78  tff(c_36, plain, (g1_orders_2(u1_struct_0('#skF_6'), u1_orders_2('#skF_6'))=g1_orders_2(u1_struct_0('#skF_8'), u1_orders_2('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.27/2.78  tff(c_85, plain, (![D_372, B_373, C_374, A_375]: (D_372=B_373 | g1_orders_2(C_374, D_372)!=g1_orders_2(A_375, B_373) | ~m1_subset_1(B_373, k1_zfmisc_1(k2_zfmisc_1(A_375, A_375))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.27/2.78  tff(c_107, plain, (![B_380, A_381]: (u1_orders_2('#skF_6')=B_380 | g1_orders_2(u1_struct_0('#skF_8'), u1_orders_2('#skF_8'))!=g1_orders_2(A_381, B_380) | ~m1_subset_1(B_380, k1_zfmisc_1(k2_zfmisc_1(A_381, A_381))))), inference(superposition, [status(thm), theory('equality')], [c_36, c_85])).
% 8.27/2.78  tff(c_111, plain, (![A_1]: (u1_orders_2(A_1)=u1_orders_2('#skF_6') | g1_orders_2(u1_struct_0(A_1), u1_orders_2(A_1))!=g1_orders_2(u1_struct_0('#skF_8'), u1_orders_2('#skF_8')) | ~l1_orders_2(A_1))), inference(resolution, [status(thm)], [c_2, c_107])).
% 8.27/2.78  tff(c_114, plain, (u1_orders_2('#skF_6')=u1_orders_2('#skF_8') | ~l1_orders_2('#skF_8')), inference(reflexivity, [status(thm), theory('equality')], [c_111])).
% 8.27/2.78  tff(c_116, plain, (u1_orders_2('#skF_6')=u1_orders_2('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_114])).
% 8.27/2.78  tff(c_136, plain, (m1_subset_1(u1_orders_2('#skF_8'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_6')))) | ~l1_orders_2('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_116, c_2])).
% 8.27/2.78  tff(c_140, plain, (m1_subset_1(u1_orders_2('#skF_8'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_136])).
% 8.27/2.78  tff(c_132, plain, (g1_orders_2(u1_struct_0('#skF_6'), u1_orders_2('#skF_8'))=g1_orders_2(u1_struct_0('#skF_8'), u1_orders_2('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_36])).
% 8.27/2.78  tff(c_6, plain, (![C_6, A_2, D_7, B_3]: (C_6=A_2 | g1_orders_2(C_6, D_7)!=g1_orders_2(A_2, B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(k2_zfmisc_1(A_2, A_2))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.27/2.78  tff(c_146, plain, (![C_6, D_7]: (u1_struct_0('#skF_6')=C_6 | g1_orders_2(u1_struct_0('#skF_8'), u1_orders_2('#skF_8'))!=g1_orders_2(C_6, D_7) | ~m1_subset_1(u1_orders_2('#skF_8'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_6')))))), inference(superposition, [status(thm), theory('equality')], [c_132, c_6])).
% 8.27/2.78  tff(c_154, plain, (![C_6, D_7]: (u1_struct_0('#skF_6')=C_6 | g1_orders_2(u1_struct_0('#skF_8'), u1_orders_2('#skF_8'))!=g1_orders_2(C_6, D_7))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_146])).
% 8.27/2.78  tff(c_160, plain, (u1_struct_0('#skF_6')=u1_struct_0('#skF_8')), inference(reflexivity, [status(thm), theory('equality')], [c_154])).
% 8.27/2.78  tff(c_48, plain, (v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.27/2.78  tff(c_194, plain, (v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_48])).
% 8.27/2.78  tff(c_62, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.27/2.78  tff(c_38, plain, (g1_orders_2(u1_struct_0('#skF_7'), u1_orders_2('#skF_7'))=g1_orders_2(u1_struct_0('#skF_5'), u1_orders_2('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.27/2.78  tff(c_98, plain, (![C_376, A_377, D_378, B_379]: (C_376=A_377 | g1_orders_2(C_376, D_378)!=g1_orders_2(A_377, B_379) | ~m1_subset_1(B_379, k1_zfmisc_1(k2_zfmisc_1(A_377, A_377))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.27/2.78  tff(c_306, plain, (![A_398, B_399]: (u1_struct_0('#skF_7')=A_398 | g1_orders_2(u1_struct_0('#skF_5'), u1_orders_2('#skF_5'))!=g1_orders_2(A_398, B_399) | ~m1_subset_1(B_399, k1_zfmisc_1(k2_zfmisc_1(A_398, A_398))))), inference(superposition, [status(thm), theory('equality')], [c_38, c_98])).
% 8.27/2.78  tff(c_314, plain, (![A_1]: (u1_struct_0(A_1)=u1_struct_0('#skF_7') | g1_orders_2(u1_struct_0(A_1), u1_orders_2(A_1))!=g1_orders_2(u1_struct_0('#skF_5'), u1_orders_2('#skF_5')) | ~l1_orders_2(A_1))), inference(resolution, [status(thm)], [c_2, c_306])).
% 8.27/2.78  tff(c_318, plain, (u1_struct_0('#skF_7')=u1_struct_0('#skF_5') | ~l1_orders_2('#skF_5')), inference(reflexivity, [status(thm), theory('equality')], [c_314])).
% 8.27/2.78  tff(c_320, plain, (u1_struct_0('#skF_7')=u1_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_318])).
% 8.27/2.78  tff(c_46, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.27/2.78  tff(c_193, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_8'))))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_46])).
% 8.27/2.78  tff(c_20, plain, (![A_71, B_195, C_257]: (m1_subset_1('#skF_4'(A_71, B_195, C_257), u1_struct_0(B_195)) | v5_orders_3(C_257, A_71, B_195) | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_71), u1_struct_0(B_195)))) | ~v1_funct_2(C_257, u1_struct_0(A_71), u1_struct_0(B_195)) | ~v1_funct_1(C_257) | ~l1_orders_2(B_195) | ~l1_orders_2(A_71))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.27/2.78  tff(c_218, plain, (m1_subset_1('#skF_4'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | v5_orders_3('#skF_9', '#skF_5', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8') | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_193, c_20])).
% 8.27/2.78  tff(c_221, plain, (m1_subset_1('#skF_4'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | v5_orders_3('#skF_9', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_50, c_194, c_218])).
% 8.27/2.78  tff(c_273, plain, (v5_orders_3('#skF_9', '#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_221])).
% 8.27/2.78  tff(c_42, plain, (v1_funct_2('#skF_10', u1_struct_0('#skF_7'), u1_struct_0('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.27/2.78  tff(c_64, plain, (v1_funct_2('#skF_9', u1_struct_0('#skF_7'), u1_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_42])).
% 8.27/2.78  tff(c_40, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_8'))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.27/2.78  tff(c_65, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_8'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_40])).
% 8.27/2.78  tff(c_278, plain, (![A_395, B_396, C_397]: (m1_subset_1('#skF_3'(A_395, B_396, C_397), u1_struct_0(B_396)) | v5_orders_3(C_397, A_395, B_396) | ~m1_subset_1(C_397, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_395), u1_struct_0(B_396)))) | ~v1_funct_2(C_397, u1_struct_0(A_395), u1_struct_0(B_396)) | ~v1_funct_1(C_397) | ~l1_orders_2(B_396) | ~l1_orders_2(A_395))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.27/2.78  tff(c_290, plain, (m1_subset_1('#skF_3'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | v5_orders_3('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_7'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8') | ~l1_orders_2('#skF_7')), inference(resolution, [status(thm)], [c_65, c_278])).
% 8.27/2.78  tff(c_304, plain, (m1_subset_1('#skF_3'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | v5_orders_3('#skF_9', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_64, c_290])).
% 8.27/2.78  tff(c_305, plain, (m1_subset_1('#skF_3'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_67, c_304])).
% 8.27/2.78  tff(c_170, plain, (![A_385, B_386, C_387]: (m1_subset_1('#skF_4'(A_385, B_386, C_387), u1_struct_0(B_386)) | v5_orders_3(C_387, A_385, B_386) | ~m1_subset_1(C_387, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_385), u1_struct_0(B_386)))) | ~v1_funct_2(C_387, u1_struct_0(A_385), u1_struct_0(B_386)) | ~v1_funct_1(C_387) | ~l1_orders_2(B_386) | ~l1_orders_2(A_385))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.27/2.78  tff(c_176, plain, (m1_subset_1('#skF_4'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | v5_orders_3('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_7'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8') | ~l1_orders_2('#skF_7')), inference(resolution, [status(thm)], [c_65, c_170])).
% 8.27/2.78  tff(c_185, plain, (m1_subset_1('#skF_4'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | v5_orders_3('#skF_9', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_64, c_176])).
% 8.27/2.78  tff(c_186, plain, (m1_subset_1('#skF_4'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_67, c_185])).
% 8.27/2.78  tff(c_728, plain, (![C_426, A_427, B_428]: (k1_funct_1(C_426, '#skF_1'(A_427, B_428, C_426))='#skF_3'(A_427, B_428, C_426) | v5_orders_3(C_426, A_427, B_428) | ~m1_subset_1(C_426, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_427), u1_struct_0(B_428)))) | ~v1_funct_2(C_426, u1_struct_0(A_427), u1_struct_0(B_428)) | ~v1_funct_1(C_426) | ~l1_orders_2(B_428) | ~l1_orders_2(A_427))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.27/2.78  tff(c_732, plain, (![C_426, B_428]: (k1_funct_1(C_426, '#skF_1'('#skF_7', B_428, C_426))='#skF_3'('#skF_7', B_428, C_426) | v5_orders_3(C_426, '#skF_7', B_428) | ~m1_subset_1(C_426, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_428)))) | ~v1_funct_2(C_426, u1_struct_0('#skF_7'), u1_struct_0(B_428)) | ~v1_funct_1(C_426) | ~l1_orders_2(B_428) | ~l1_orders_2('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_320, c_728])).
% 8.27/2.78  tff(c_2544, plain, (![C_602, B_603]: (k1_funct_1(C_602, '#skF_1'('#skF_7', B_603, C_602))='#skF_3'('#skF_7', B_603, C_602) | v5_orders_3(C_602, '#skF_7', B_603) | ~m1_subset_1(C_602, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_603)))) | ~v1_funct_2(C_602, u1_struct_0('#skF_5'), u1_struct_0(B_603)) | ~v1_funct_1(C_602) | ~l1_orders_2(B_603))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_320, c_732])).
% 8.27/2.78  tff(c_2550, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_7', '#skF_8', '#skF_9'))='#skF_3'('#skF_7', '#skF_8', '#skF_9') | v5_orders_3('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_193, c_2544])).
% 8.27/2.78  tff(c_2563, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_7', '#skF_8', '#skF_9'))='#skF_3'('#skF_7', '#skF_8', '#skF_9') | v5_orders_3('#skF_9', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_194, c_2550])).
% 8.27/2.78  tff(c_2564, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_7', '#skF_8', '#skF_9'))='#skF_3'('#skF_7', '#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_67, c_2563])).
% 8.27/2.78  tff(c_504, plain, (![C_410, A_411, B_412]: (k1_funct_1(C_410, '#skF_2'(A_411, B_412, C_410))='#skF_4'(A_411, B_412, C_410) | v5_orders_3(C_410, A_411, B_412) | ~m1_subset_1(C_410, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_411), u1_struct_0(B_412)))) | ~v1_funct_2(C_410, u1_struct_0(A_411), u1_struct_0(B_412)) | ~v1_funct_1(C_410) | ~l1_orders_2(B_412) | ~l1_orders_2(A_411))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.27/2.78  tff(c_508, plain, (![C_410, B_412]: (k1_funct_1(C_410, '#skF_2'('#skF_7', B_412, C_410))='#skF_4'('#skF_7', B_412, C_410) | v5_orders_3(C_410, '#skF_7', B_412) | ~m1_subset_1(C_410, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_412)))) | ~v1_funct_2(C_410, u1_struct_0('#skF_7'), u1_struct_0(B_412)) | ~v1_funct_1(C_410) | ~l1_orders_2(B_412) | ~l1_orders_2('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_320, c_504])).
% 8.27/2.78  tff(c_2698, plain, (![C_617, B_618]: (k1_funct_1(C_617, '#skF_2'('#skF_7', B_618, C_617))='#skF_4'('#skF_7', B_618, C_617) | v5_orders_3(C_617, '#skF_7', B_618) | ~m1_subset_1(C_617, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_618)))) | ~v1_funct_2(C_617, u1_struct_0('#skF_5'), u1_struct_0(B_618)) | ~v1_funct_1(C_617) | ~l1_orders_2(B_618))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_320, c_508])).
% 8.27/2.78  tff(c_2704, plain, (k1_funct_1('#skF_9', '#skF_2'('#skF_7', '#skF_8', '#skF_9'))='#skF_4'('#skF_7', '#skF_8', '#skF_9') | v5_orders_3('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_193, c_2698])).
% 8.27/2.78  tff(c_2717, plain, (k1_funct_1('#skF_9', '#skF_2'('#skF_7', '#skF_8', '#skF_9'))='#skF_4'('#skF_7', '#skF_8', '#skF_9') | v5_orders_3('#skF_9', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_194, c_2704])).
% 8.27/2.78  tff(c_2718, plain, (k1_funct_1('#skF_9', '#skF_2'('#skF_7', '#skF_8', '#skF_9'))='#skF_4'('#skF_7', '#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_67, c_2717])).
% 8.27/2.78  tff(c_245, plain, (![A_392, B_393, C_394]: (m1_subset_1('#skF_1'(A_392, B_393, C_394), u1_struct_0(A_392)) | v5_orders_3(C_394, A_392, B_393) | ~m1_subset_1(C_394, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_392), u1_struct_0(B_393)))) | ~v1_funct_2(C_394, u1_struct_0(A_392), u1_struct_0(B_393)) | ~v1_funct_1(C_394) | ~l1_orders_2(B_393) | ~l1_orders_2(A_392))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.27/2.78  tff(c_257, plain, (m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | v5_orders_3('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_7'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8') | ~l1_orders_2('#skF_7')), inference(resolution, [status(thm)], [c_65, c_245])).
% 8.27/2.78  tff(c_271, plain, (m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | v5_orders_3('#skF_9', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_64, c_257])).
% 8.27/2.78  tff(c_272, plain, (m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_67, c_271])).
% 8.27/2.78  tff(c_331, plain, (m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_320, c_272])).
% 8.27/2.78  tff(c_391, plain, (![A_401, B_402, C_403]: (m1_subset_1('#skF_2'(A_401, B_402, C_403), u1_struct_0(A_401)) | v5_orders_3(C_403, A_401, B_402) | ~m1_subset_1(C_403, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_401), u1_struct_0(B_402)))) | ~v1_funct_2(C_403, u1_struct_0(A_401), u1_struct_0(B_402)) | ~v1_funct_1(C_403) | ~l1_orders_2(B_402) | ~l1_orders_2(A_401))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.27/2.78  tff(c_395, plain, (![B_402, C_403]: (m1_subset_1('#skF_2'('#skF_7', B_402, C_403), u1_struct_0('#skF_7')) | v5_orders_3(C_403, '#skF_7', B_402) | ~m1_subset_1(C_403, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_402)))) | ~v1_funct_2(C_403, u1_struct_0('#skF_7'), u1_struct_0(B_402)) | ~v1_funct_1(C_403) | ~l1_orders_2(B_402) | ~l1_orders_2('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_320, c_391])).
% 8.27/2.78  tff(c_2008, plain, (![B_552, C_553]: (m1_subset_1('#skF_2'('#skF_7', B_552, C_553), u1_struct_0('#skF_5')) | v5_orders_3(C_553, '#skF_7', B_552) | ~m1_subset_1(C_553, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_552)))) | ~v1_funct_2(C_553, u1_struct_0('#skF_5'), u1_struct_0(B_552)) | ~v1_funct_1(C_553) | ~l1_orders_2(B_552))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_320, c_320, c_395])).
% 8.27/2.78  tff(c_2017, plain, (m1_subset_1('#skF_2'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | v5_orders_3('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_193, c_2008])).
% 8.27/2.78  tff(c_2032, plain, (m1_subset_1('#skF_2'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | v5_orders_3('#skF_9', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_194, c_2017])).
% 8.27/2.78  tff(c_2033, plain, (m1_subset_1('#skF_2'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_67, c_2032])).
% 8.27/2.78  tff(c_352, plain, (m1_subset_1(u1_orders_2('#skF_7'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_7')))) | ~l1_orders_2('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_320, c_2])).
% 8.27/2.78  tff(c_371, plain, (m1_subset_1(u1_orders_2('#skF_7'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_320, c_352])).
% 8.27/2.78  tff(c_332, plain, (g1_orders_2(u1_struct_0('#skF_5'), u1_orders_2('#skF_7'))=g1_orders_2(u1_struct_0('#skF_5'), u1_orders_2('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_320, c_38])).
% 8.27/2.78  tff(c_4, plain, (![D_7, B_3, C_6, A_2]: (D_7=B_3 | g1_orders_2(C_6, D_7)!=g1_orders_2(A_2, B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(k2_zfmisc_1(A_2, A_2))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.27/2.78  tff(c_440, plain, (![D_7, C_6]: (u1_orders_2('#skF_7')=D_7 | g1_orders_2(u1_struct_0('#skF_5'), u1_orders_2('#skF_5'))!=g1_orders_2(C_6, D_7) | ~m1_subset_1(u1_orders_2('#skF_7'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_5')))))), inference(superposition, [status(thm), theory('equality')], [c_332, c_4])).
% 8.27/2.78  tff(c_446, plain, (![D_7, C_6]: (u1_orders_2('#skF_7')=D_7 | g1_orders_2(u1_struct_0('#skF_5'), u1_orders_2('#skF_5'))!=g1_orders_2(C_6, D_7))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_440])).
% 8.27/2.78  tff(c_459, plain, (u1_orders_2('#skF_7')=u1_orders_2('#skF_5')), inference(reflexivity, [status(thm), theory('equality')], [c_446])).
% 8.27/2.78  tff(c_581, plain, (![A_418, B_419, C_420]: (r1_orders_2(A_418, '#skF_1'(A_418, B_419, C_420), '#skF_2'(A_418, B_419, C_420)) | v5_orders_3(C_420, A_418, B_419) | ~m1_subset_1(C_420, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_418), u1_struct_0(B_419)))) | ~v1_funct_2(C_420, u1_struct_0(A_418), u1_struct_0(B_419)) | ~v1_funct_1(C_420) | ~l1_orders_2(B_419) | ~l1_orders_2(A_418))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.27/2.78  tff(c_585, plain, (![B_419, C_420]: (r1_orders_2('#skF_7', '#skF_1'('#skF_7', B_419, C_420), '#skF_2'('#skF_7', B_419, C_420)) | v5_orders_3(C_420, '#skF_7', B_419) | ~m1_subset_1(C_420, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_419)))) | ~v1_funct_2(C_420, u1_struct_0('#skF_7'), u1_struct_0(B_419)) | ~v1_funct_1(C_420) | ~l1_orders_2(B_419) | ~l1_orders_2('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_320, c_581])).
% 8.27/2.78  tff(c_2445, plain, (![B_596, C_597]: (r1_orders_2('#skF_7', '#skF_1'('#skF_7', B_596, C_597), '#skF_2'('#skF_7', B_596, C_597)) | v5_orders_3(C_597, '#skF_7', B_596) | ~m1_subset_1(C_597, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_596)))) | ~v1_funct_2(C_597, u1_struct_0('#skF_5'), u1_struct_0(B_596)) | ~v1_funct_1(C_597) | ~l1_orders_2(B_596))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_320, c_585])).
% 8.27/2.78  tff(c_2451, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_2'('#skF_7', '#skF_8', '#skF_9')) | v5_orders_3('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_193, c_2445])).
% 8.27/2.78  tff(c_2464, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_2'('#skF_7', '#skF_8', '#skF_9')) | v5_orders_3('#skF_9', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_194, c_2451])).
% 8.27/2.78  tff(c_2465, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_2'('#skF_7', '#skF_8', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_67, c_2464])).
% 8.27/2.78  tff(c_10, plain, (![B_40, E_68, F_70, A_8]: (r1_orders_2(B_40, E_68, F_70) | ~r1_orders_2(A_8, E_68, F_70) | ~m1_subset_1(F_70, u1_struct_0(B_40)) | ~m1_subset_1(E_68, u1_struct_0(B_40)) | ~m1_subset_1(F_70, u1_struct_0(A_8)) | ~m1_subset_1(E_68, u1_struct_0(A_8)) | g1_orders_2(u1_struct_0(B_40), u1_orders_2(B_40))!=g1_orders_2(u1_struct_0(A_8), u1_orders_2(A_8)) | ~l1_orders_2(B_40) | ~l1_orders_2(A_8))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.27/2.78  tff(c_2474, plain, (![B_40]: (r1_orders_2(B_40, '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_2'('#skF_7', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_2'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0(B_40)) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0(B_40)) | ~m1_subset_1('#skF_2'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_7')) | g1_orders_2(u1_struct_0(B_40), u1_orders_2(B_40))!=g1_orders_2(u1_struct_0('#skF_7'), u1_orders_2('#skF_7')) | ~l1_orders_2(B_40) | ~l1_orders_2('#skF_7'))), inference(resolution, [status(thm)], [c_2465, c_10])).
% 8.27/2.78  tff(c_2480, plain, (![B_40]: (r1_orders_2(B_40, '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_2'('#skF_7', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_2'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0(B_40)) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0(B_40)) | g1_orders_2(u1_struct_0(B_40), u1_orders_2(B_40))!=g1_orders_2(u1_struct_0('#skF_5'), u1_orders_2('#skF_5')) | ~l1_orders_2(B_40))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_320, c_459, c_331, c_320, c_2033, c_320, c_2474])).
% 8.27/2.78  tff(c_2676, plain, (r1_orders_2('#skF_5', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_2'('#skF_7', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_2'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(reflexivity, [status(thm), theory('equality')], [c_2480])).
% 8.27/2.78  tff(c_2678, plain, (r1_orders_2('#skF_5', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_2'('#skF_7', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_331, c_2033, c_2676])).
% 8.27/2.78  tff(c_12, plain, (![E_296, D_288, C_257, A_71, B_195]: (r1_orders_2(B_195, k1_funct_1(C_257, D_288), k1_funct_1(C_257, E_296)) | ~m1_subset_1(k1_funct_1(C_257, E_296), u1_struct_0(B_195)) | ~m1_subset_1(k1_funct_1(C_257, D_288), u1_struct_0(B_195)) | ~r1_orders_2(A_71, D_288, E_296) | ~m1_subset_1(E_296, u1_struct_0(A_71)) | ~m1_subset_1(D_288, u1_struct_0(A_71)) | ~v5_orders_3(C_257, A_71, B_195) | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_71), u1_struct_0(B_195)))) | ~v1_funct_2(C_257, u1_struct_0(A_71), u1_struct_0(B_195)) | ~v1_funct_1(C_257) | ~l1_orders_2(B_195) | ~l1_orders_2(A_71))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.27/2.78  tff(c_2689, plain, (![B_195, C_257]: (r1_orders_2(B_195, k1_funct_1(C_257, '#skF_1'('#skF_7', '#skF_8', '#skF_9')), k1_funct_1(C_257, '#skF_2'('#skF_7', '#skF_8', '#skF_9'))) | ~m1_subset_1(k1_funct_1(C_257, '#skF_2'('#skF_7', '#skF_8', '#skF_9')), u1_struct_0(B_195)) | ~m1_subset_1(k1_funct_1(C_257, '#skF_1'('#skF_7', '#skF_8', '#skF_9')), u1_struct_0(B_195)) | ~m1_subset_1('#skF_2'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | ~v5_orders_3(C_257, '#skF_5', B_195) | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_195)))) | ~v1_funct_2(C_257, u1_struct_0('#skF_5'), u1_struct_0(B_195)) | ~v1_funct_1(C_257) | ~l1_orders_2(B_195) | ~l1_orders_2('#skF_5'))), inference(resolution, [status(thm)], [c_2678, c_12])).
% 8.27/2.78  tff(c_3203, plain, (![B_662, C_663]: (r1_orders_2(B_662, k1_funct_1(C_663, '#skF_1'('#skF_7', '#skF_8', '#skF_9')), k1_funct_1(C_663, '#skF_2'('#skF_7', '#skF_8', '#skF_9'))) | ~m1_subset_1(k1_funct_1(C_663, '#skF_2'('#skF_7', '#skF_8', '#skF_9')), u1_struct_0(B_662)) | ~m1_subset_1(k1_funct_1(C_663, '#skF_1'('#skF_7', '#skF_8', '#skF_9')), u1_struct_0(B_662)) | ~v5_orders_3(C_663, '#skF_5', B_662) | ~m1_subset_1(C_663, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_662)))) | ~v1_funct_2(C_663, u1_struct_0('#skF_5'), u1_struct_0(B_662)) | ~v1_funct_1(C_663) | ~l1_orders_2(B_662))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_331, c_2033, c_2689])).
% 8.27/2.78  tff(c_3210, plain, (![B_662]: (r1_orders_2(B_662, k1_funct_1('#skF_9', '#skF_1'('#skF_7', '#skF_8', '#skF_9')), '#skF_4'('#skF_7', '#skF_8', '#skF_9')) | ~m1_subset_1(k1_funct_1('#skF_9', '#skF_2'('#skF_7', '#skF_8', '#skF_9')), u1_struct_0(B_662)) | ~m1_subset_1(k1_funct_1('#skF_9', '#skF_1'('#skF_7', '#skF_8', '#skF_9')), u1_struct_0(B_662)) | ~v5_orders_3('#skF_9', '#skF_5', B_662) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_662)))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0(B_662)) | ~v1_funct_1('#skF_9') | ~l1_orders_2(B_662))), inference(superposition, [status(thm), theory('equality')], [c_2718, c_3203])).
% 8.27/2.78  tff(c_3220, plain, (![B_664]: (r1_orders_2(B_664, '#skF_3'('#skF_7', '#skF_8', '#skF_9'), '#skF_4'('#skF_7', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_4'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0(B_664)) | ~m1_subset_1('#skF_3'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0(B_664)) | ~v5_orders_3('#skF_9', '#skF_5', B_664) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_664)))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0(B_664)) | ~l1_orders_2(B_664))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2564, c_2718, c_2564, c_3210])).
% 8.27/2.78  tff(c_3226, plain, (r1_orders_2('#skF_8', '#skF_3'('#skF_7', '#skF_8', '#skF_9'), '#skF_4'('#skF_7', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_4'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_3'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | ~v5_orders_3('#skF_9', '#skF_5', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_193, c_3220])).
% 8.27/2.78  tff(c_3234, plain, (r1_orders_2('#skF_8', '#skF_3'('#skF_7', '#skF_8', '#skF_9'), '#skF_4'('#skF_7', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_194, c_273, c_305, c_186, c_3226])).
% 8.27/2.78  tff(c_14, plain, (![B_195, A_71, C_257]: (~r1_orders_2(B_195, '#skF_3'(A_71, B_195, C_257), '#skF_4'(A_71, B_195, C_257)) | v5_orders_3(C_257, A_71, B_195) | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_71), u1_struct_0(B_195)))) | ~v1_funct_2(C_257, u1_struct_0(A_71), u1_struct_0(B_195)) | ~v1_funct_1(C_257) | ~l1_orders_2(B_195) | ~l1_orders_2(A_71))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.27/2.78  tff(c_3252, plain, (v5_orders_3('#skF_9', '#skF_7', '#skF_8') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_8')))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_7'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8') | ~l1_orders_2('#skF_7')), inference(resolution, [status(thm)], [c_3234, c_14])).
% 8.27/2.78  tff(c_3261, plain, (v5_orders_3('#skF_9', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_194, c_320, c_193, c_320, c_3252])).
% 8.27/2.78  tff(c_3263, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_3261])).
% 8.27/2.78  tff(c_3265, plain, (~v5_orders_3('#skF_9', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_221])).
% 8.27/2.78  tff(c_3299, plain, (![A_668, B_669, C_670]: (m1_subset_1('#skF_3'(A_668, B_669, C_670), u1_struct_0(B_669)) | v5_orders_3(C_670, A_668, B_669) | ~m1_subset_1(C_670, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_668), u1_struct_0(B_669)))) | ~v1_funct_2(C_670, u1_struct_0(A_668), u1_struct_0(B_669)) | ~v1_funct_1(C_670) | ~l1_orders_2(B_669) | ~l1_orders_2(A_668))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.27/2.78  tff(c_3303, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | v5_orders_3('#skF_9', '#skF_5', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8') | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_193, c_3299])).
% 8.27/2.78  tff(c_3317, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | v5_orders_3('#skF_9', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_50, c_194, c_3303])).
% 8.27/2.78  tff(c_3318, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_3265, c_3317])).
% 8.27/2.78  tff(c_3264, plain, (m1_subset_1('#skF_4'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_8'))), inference(splitRight, [status(thm)], [c_221])).
% 8.27/2.78  tff(c_32, plain, (v5_orders_3('#skF_9', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.27/2.78  tff(c_3628, plain, (![C_691, A_692, B_693]: (k1_funct_1(C_691, '#skF_1'(A_692, B_693, C_691))='#skF_3'(A_692, B_693, C_691) | v5_orders_3(C_691, A_692, B_693) | ~m1_subset_1(C_691, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_692), u1_struct_0(B_693)))) | ~v1_funct_2(C_691, u1_struct_0(A_692), u1_struct_0(B_693)) | ~v1_funct_1(C_691) | ~l1_orders_2(B_693) | ~l1_orders_2(A_692))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.27/2.78  tff(c_3638, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_5', '#skF_8', '#skF_9'))='#skF_3'('#skF_5', '#skF_8', '#skF_9') | v5_orders_3('#skF_9', '#skF_5', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8') | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_193, c_3628])).
% 8.27/2.78  tff(c_3657, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_5', '#skF_8', '#skF_9'))='#skF_3'('#skF_5', '#skF_8', '#skF_9') | v5_orders_3('#skF_9', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_50, c_194, c_3638])).
% 8.27/2.78  tff(c_3658, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_5', '#skF_8', '#skF_9'))='#skF_3'('#skF_5', '#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_3265, c_3657])).
% 8.27/2.78  tff(c_3540, plain, (![C_681, A_682, B_683]: (k1_funct_1(C_681, '#skF_2'(A_682, B_683, C_681))='#skF_4'(A_682, B_683, C_681) | v5_orders_3(C_681, A_682, B_683) | ~m1_subset_1(C_681, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_682), u1_struct_0(B_683)))) | ~v1_funct_2(C_681, u1_struct_0(A_682), u1_struct_0(B_683)) | ~v1_funct_1(C_681) | ~l1_orders_2(B_683) | ~l1_orders_2(A_682))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.27/2.78  tff(c_3550, plain, (k1_funct_1('#skF_9', '#skF_2'('#skF_5', '#skF_8', '#skF_9'))='#skF_4'('#skF_5', '#skF_8', '#skF_9') | v5_orders_3('#skF_9', '#skF_5', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8') | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_193, c_3540])).
% 8.27/2.78  tff(c_3569, plain, (k1_funct_1('#skF_9', '#skF_2'('#skF_5', '#skF_8', '#skF_9'))='#skF_4'('#skF_5', '#skF_8', '#skF_9') | v5_orders_3('#skF_9', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_50, c_194, c_3550])).
% 8.27/2.78  tff(c_3570, plain, (k1_funct_1('#skF_9', '#skF_2'('#skF_5', '#skF_8', '#skF_9'))='#skF_4'('#skF_5', '#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_3265, c_3569])).
% 8.27/2.78  tff(c_249, plain, (m1_subset_1('#skF_1'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | v5_orders_3('#skF_9', '#skF_5', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8') | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_193, c_245])).
% 8.27/2.78  tff(c_263, plain, (m1_subset_1('#skF_1'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | v5_orders_3('#skF_9', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_50, c_194, c_249])).
% 8.27/2.78  tff(c_3296, plain, (m1_subset_1('#skF_1'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_3265, c_263])).
% 8.27/2.78  tff(c_3266, plain, (![A_665, B_666, C_667]: (m1_subset_1('#skF_2'(A_665, B_666, C_667), u1_struct_0(A_665)) | v5_orders_3(C_667, A_665, B_666) | ~m1_subset_1(C_667, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_665), u1_struct_0(B_666)))) | ~v1_funct_2(C_667, u1_struct_0(A_665), u1_struct_0(B_666)) | ~v1_funct_1(C_667) | ~l1_orders_2(B_666) | ~l1_orders_2(A_665))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.27/2.78  tff(c_3270, plain, (m1_subset_1('#skF_2'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | v5_orders_3('#skF_9', '#skF_5', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8') | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_193, c_3266])).
% 8.27/2.78  tff(c_3284, plain, (m1_subset_1('#skF_2'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | v5_orders_3('#skF_9', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_50, c_194, c_3270])).
% 8.27/2.78  tff(c_3295, plain, (m1_subset_1('#skF_2'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_3265, c_3284])).
% 8.27/2.78  tff(c_3406, plain, (![A_674, B_675, C_676]: (r1_orders_2(A_674, '#skF_1'(A_674, B_675, C_676), '#skF_2'(A_674, B_675, C_676)) | v5_orders_3(C_676, A_674, B_675) | ~m1_subset_1(C_676, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_674), u1_struct_0(B_675)))) | ~v1_funct_2(C_676, u1_struct_0(A_674), u1_struct_0(B_675)) | ~v1_funct_1(C_676) | ~l1_orders_2(B_675) | ~l1_orders_2(A_674))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.27/2.78  tff(c_3414, plain, (r1_orders_2('#skF_5', '#skF_1'('#skF_5', '#skF_8', '#skF_9'), '#skF_2'('#skF_5', '#skF_8', '#skF_9')) | v5_orders_3('#skF_9', '#skF_5', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8') | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_193, c_3406])).
% 8.27/2.78  tff(c_3430, plain, (r1_orders_2('#skF_5', '#skF_1'('#skF_5', '#skF_8', '#skF_9'), '#skF_2'('#skF_5', '#skF_8', '#skF_9')) | v5_orders_3('#skF_9', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_50, c_194, c_3414])).
% 8.27/2.78  tff(c_3431, plain, (r1_orders_2('#skF_5', '#skF_1'('#skF_5', '#skF_8', '#skF_9'), '#skF_2'('#skF_5', '#skF_8', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_3265, c_3430])).
% 8.27/2.78  tff(c_3851, plain, (![C_713, A_717, B_716, D_714, E_715]: (r1_orders_2(B_716, k1_funct_1(C_713, D_714), k1_funct_1(C_713, E_715)) | ~m1_subset_1(k1_funct_1(C_713, E_715), u1_struct_0(B_716)) | ~m1_subset_1(k1_funct_1(C_713, D_714), u1_struct_0(B_716)) | ~r1_orders_2(A_717, D_714, E_715) | ~m1_subset_1(E_715, u1_struct_0(A_717)) | ~m1_subset_1(D_714, u1_struct_0(A_717)) | ~v5_orders_3(C_713, A_717, B_716) | ~m1_subset_1(C_713, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_717), u1_struct_0(B_716)))) | ~v1_funct_2(C_713, u1_struct_0(A_717), u1_struct_0(B_716)) | ~v1_funct_1(C_713) | ~l1_orders_2(B_716) | ~l1_orders_2(A_717))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.27/2.78  tff(c_3855, plain, (![B_716, C_713]: (r1_orders_2(B_716, k1_funct_1(C_713, '#skF_1'('#skF_5', '#skF_8', '#skF_9')), k1_funct_1(C_713, '#skF_2'('#skF_5', '#skF_8', '#skF_9'))) | ~m1_subset_1(k1_funct_1(C_713, '#skF_2'('#skF_5', '#skF_8', '#skF_9')), u1_struct_0(B_716)) | ~m1_subset_1(k1_funct_1(C_713, '#skF_1'('#skF_5', '#skF_8', '#skF_9')), u1_struct_0(B_716)) | ~m1_subset_1('#skF_2'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_1'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | ~v5_orders_3(C_713, '#skF_5', B_716) | ~m1_subset_1(C_713, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_716)))) | ~v1_funct_2(C_713, u1_struct_0('#skF_5'), u1_struct_0(B_716)) | ~v1_funct_1(C_713) | ~l1_orders_2(B_716) | ~l1_orders_2('#skF_5'))), inference(resolution, [status(thm)], [c_3431, c_3851])).
% 8.27/2.78  tff(c_6218, plain, (![B_920, C_921]: (r1_orders_2(B_920, k1_funct_1(C_921, '#skF_1'('#skF_5', '#skF_8', '#skF_9')), k1_funct_1(C_921, '#skF_2'('#skF_5', '#skF_8', '#skF_9'))) | ~m1_subset_1(k1_funct_1(C_921, '#skF_2'('#skF_5', '#skF_8', '#skF_9')), u1_struct_0(B_920)) | ~m1_subset_1(k1_funct_1(C_921, '#skF_1'('#skF_5', '#skF_8', '#skF_9')), u1_struct_0(B_920)) | ~v5_orders_3(C_921, '#skF_5', B_920) | ~m1_subset_1(C_921, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_920)))) | ~v1_funct_2(C_921, u1_struct_0('#skF_5'), u1_struct_0(B_920)) | ~v1_funct_1(C_921) | ~l1_orders_2(B_920))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_3296, c_3295, c_3855])).
% 8.27/2.78  tff(c_6225, plain, (![B_920]: (r1_orders_2(B_920, '#skF_3'('#skF_5', '#skF_8', '#skF_9'), k1_funct_1('#skF_9', '#skF_2'('#skF_5', '#skF_8', '#skF_9'))) | ~m1_subset_1(k1_funct_1('#skF_9', '#skF_2'('#skF_5', '#skF_8', '#skF_9')), u1_struct_0(B_920)) | ~m1_subset_1(k1_funct_1('#skF_9', '#skF_1'('#skF_5', '#skF_8', '#skF_9')), u1_struct_0(B_920)) | ~v5_orders_3('#skF_9', '#skF_5', B_920) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_920)))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0(B_920)) | ~v1_funct_1('#skF_9') | ~l1_orders_2(B_920))), inference(superposition, [status(thm), theory('equality')], [c_3658, c_6218])).
% 8.27/2.78  tff(c_6235, plain, (![B_922]: (r1_orders_2(B_922, '#skF_3'('#skF_5', '#skF_8', '#skF_9'), '#skF_4'('#skF_5', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0(B_922)) | ~m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0(B_922)) | ~v5_orders_3('#skF_9', '#skF_5', B_922) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_922)))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0(B_922)) | ~l1_orders_2(B_922))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_3658, c_3570, c_3570, c_6225])).
% 8.27/2.78  tff(c_6244, plain, (r1_orders_2('#skF_6', '#skF_3'('#skF_5', '#skF_8', '#skF_9'), '#skF_4'('#skF_5', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_6')) | ~v5_orders_3('#skF_9', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_8')))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_160, c_6235])).
% 8.27/2.78  tff(c_6251, plain, (r1_orders_2('#skF_6', '#skF_3'('#skF_5', '#skF_8', '#skF_9'), '#skF_4'('#skF_5', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_194, c_160, c_193, c_32, c_3318, c_160, c_3264, c_160, c_6244])).
% 8.27/2.78  tff(c_6255, plain, (![B_40]: (r1_orders_2(B_40, '#skF_3'('#skF_5', '#skF_8', '#skF_9'), '#skF_4'('#skF_5', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0(B_40)) | ~m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0(B_40)) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_6')) | g1_orders_2(u1_struct_0(B_40), u1_orders_2(B_40))!=g1_orders_2(u1_struct_0('#skF_6'), u1_orders_2('#skF_6')) | ~l1_orders_2(B_40) | ~l1_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_6251, c_10])).
% 8.27/2.78  tff(c_6261, plain, (![B_40]: (r1_orders_2(B_40, '#skF_3'('#skF_5', '#skF_8', '#skF_9'), '#skF_4'('#skF_5', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0(B_40)) | ~m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0(B_40)) | g1_orders_2(u1_struct_0(B_40), u1_orders_2(B_40))!=g1_orders_2(u1_struct_0('#skF_8'), u1_orders_2('#skF_8')) | ~l1_orders_2(B_40))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_116, c_160, c_3318, c_160, c_3264, c_160, c_6255])).
% 8.27/2.78  tff(c_6300, plain, (r1_orders_2('#skF_8', '#skF_3'('#skF_5', '#skF_8', '#skF_9'), '#skF_4'('#skF_5', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | ~l1_orders_2('#skF_8')), inference(reflexivity, [status(thm), theory('equality')], [c_6261])).
% 8.27/2.78  tff(c_6302, plain, (r1_orders_2('#skF_8', '#skF_3'('#skF_5', '#skF_8', '#skF_9'), '#skF_4'('#skF_5', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3318, c_3264, c_6300])).
% 8.27/2.78  tff(c_6325, plain, (v5_orders_3('#skF_9', '#skF_5', '#skF_8') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_8')))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8') | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_6302, c_14])).
% 8.27/2.78  tff(c_6334, plain, (v5_orders_3('#skF_9', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_50, c_194, c_193, c_6325])).
% 8.27/2.78  tff(c_6336, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3265, c_6334])).
% 8.27/2.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.27/2.78  
% 8.27/2.78  Inference rules
% 8.27/2.78  ----------------------
% 8.27/2.78  #Ref     : 35
% 8.27/2.78  #Sup     : 1241
% 8.27/2.78  #Fact    : 0
% 8.27/2.78  #Define  : 0
% 8.27/2.78  #Split   : 11
% 8.27/2.78  #Chain   : 0
% 8.27/2.78  #Close   : 0
% 8.27/2.78  
% 8.27/2.78  Ordering : KBO
% 8.27/2.78  
% 8.27/2.78  Simplification rules
% 8.27/2.78  ----------------------
% 8.27/2.78  #Subsume      : 725
% 8.27/2.78  #Demod        : 4258
% 8.27/2.78  #Tautology    : 161
% 8.27/2.78  #SimpNegUnit  : 53
% 8.27/2.78  #BackRed      : 24
% 8.27/2.78  
% 8.27/2.78  #Partial instantiations: 0
% 8.27/2.78  #Strategies tried      : 1
% 8.27/2.78  
% 8.27/2.78  Timing (in seconds)
% 8.27/2.78  ----------------------
% 8.27/2.78  Preprocessing        : 0.36
% 8.27/2.78  Parsing              : 0.18
% 8.27/2.78  CNF conversion       : 0.05
% 8.27/2.78  Main loop            : 1.61
% 8.27/2.78  Inferencing          : 0.50
% 8.27/2.78  Reduction            : 0.71
% 8.27/2.78  Demodulation         : 0.53
% 8.27/2.78  BG Simplification    : 0.05
% 8.27/2.78  Subsumption          : 0.29
% 8.27/2.78  Abstraction          : 0.08
% 8.27/2.78  MUC search           : 0.00
% 8.27/2.78  Cooper               : 0.00
% 8.27/2.78  Total                : 2.04
% 8.27/2.78  Index Insertion      : 0.00
% 8.27/2.78  Index Deletion       : 0.00
% 8.27/2.78  Index Matching       : 0.00
% 8.27/2.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
