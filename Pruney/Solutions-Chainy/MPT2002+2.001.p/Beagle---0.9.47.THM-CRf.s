%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:06 EST 2020

% Result     : Theorem 7.64s
% Output     : CNFRefutation 7.64s
% Verified   : 
% Statistics : Number of formulae       :  177 (2195 expanded)
%              Number of leaves         :   33 ( 755 expanded)
%              Depth                    :   24
%              Number of atoms          :  590 (11947 expanded)
%              Number of equality atoms :   59 (2892 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_orders_3 > v1_funct_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v1_funct_1 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_waybel_9)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(f_84,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_orders_3)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

tff(c_34,plain,(
    '#skF_10' = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_30,plain,(
    ~ v5_orders_3('#skF_10','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_67,plain,(
    ~ v5_orders_3('#skF_9','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30])).

tff(c_56,plain,(
    l1_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_52,plain,(
    l1_orders_2('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_50,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_6,plain,(
    ! [A_8] :
      ( m1_subset_1(u1_orders_2(A_8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8),u1_struct_0(A_8))))
      | ~ l1_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_36,plain,(
    g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) = g1_orders_2(u1_struct_0('#skF_8'),u1_orders_2('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_85,plain,(
    ! [C_316,A_317,D_318,B_319] :
      ( C_316 = A_317
      | g1_orders_2(C_316,D_318) != g1_orders_2(A_317,B_319)
      | ~ m1_subset_1(B_319,k1_zfmisc_1(k2_zfmisc_1(A_317,A_317))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_107,plain,(
    ! [A_324,B_325] :
      ( u1_struct_0('#skF_6') = A_324
      | g1_orders_2(u1_struct_0('#skF_8'),u1_orders_2('#skF_8')) != g1_orders_2(A_324,B_325)
      | ~ m1_subset_1(B_325,k1_zfmisc_1(k2_zfmisc_1(A_324,A_324))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_85])).

tff(c_111,plain,(
    ! [A_8] :
      ( u1_struct_0(A_8) = u1_struct_0('#skF_6')
      | g1_orders_2(u1_struct_0(A_8),u1_orders_2(A_8)) != g1_orders_2(u1_struct_0('#skF_8'),u1_orders_2('#skF_8'))
      | ~ l1_orders_2(A_8) ) ),
    inference(resolution,[status(thm)],[c_6,c_107])).

tff(c_114,plain,
    ( u1_struct_0('#skF_6') = u1_struct_0('#skF_8')
    | ~ l1_orders_2('#skF_8') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_111])).

tff(c_116,plain,(
    u1_struct_0('#skF_6') = u1_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_114])).

tff(c_48,plain,(
    v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_134,plain,(
    v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_48])).

tff(c_62,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_38,plain,(
    g1_orders_2(u1_struct_0('#skF_7'),u1_orders_2('#skF_7')) = g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_225,plain,(
    ! [A_339,B_340] :
      ( u1_struct_0('#skF_7') = A_339
      | g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5')) != g1_orders_2(A_339,B_340)
      | ~ m1_subset_1(B_340,k1_zfmisc_1(k2_zfmisc_1(A_339,A_339))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_85])).

tff(c_233,plain,(
    ! [A_8] :
      ( u1_struct_0(A_8) = u1_struct_0('#skF_7')
      | g1_orders_2(u1_struct_0(A_8),u1_orders_2(A_8)) != g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5'))
      | ~ l1_orders_2(A_8) ) ),
    inference(resolution,[status(thm)],[c_6,c_225])).

tff(c_236,plain,
    ( u1_struct_0('#skF_7') = u1_struct_0('#skF_5')
    | ~ l1_orders_2('#skF_5') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_233])).

tff(c_238,plain,(
    u1_struct_0('#skF_7') = u1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_236])).

tff(c_46,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_133,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_8')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_46])).

tff(c_291,plain,(
    ! [A_342,B_343,C_344] :
      ( m1_subset_1('#skF_4'(A_342,B_343,C_344),u1_struct_0(B_343))
      | v5_orders_3(C_344,A_342,B_343)
      | ~ m1_subset_1(C_344,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_342),u1_struct_0(B_343))))
      | ~ v1_funct_2(C_344,u1_struct_0(A_342),u1_struct_0(B_343))
      | ~ v1_funct_1(C_344)
      | ~ l1_orders_2(B_343)
      | ~ l1_orders_2(A_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_301,plain,
    ( m1_subset_1('#skF_4'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | v5_orders_3('#skF_9','#skF_5','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_133,c_291])).

tff(c_320,plain,
    ( m1_subset_1('#skF_4'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | v5_orders_3('#skF_9','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_50,c_134,c_301])).

tff(c_369,plain,(
    v5_orders_3('#skF_9','#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_320])).

tff(c_375,plain,(
    ! [A_351,B_352,C_353] :
      ( m1_subset_1('#skF_3'(A_351,B_352,C_353),u1_struct_0(B_352))
      | v5_orders_3(C_353,A_351,B_352)
      | ~ m1_subset_1(C_353,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_351),u1_struct_0(B_352))))
      | ~ v1_funct_2(C_353,u1_struct_0(A_351),u1_struct_0(B_352))
      | ~ v1_funct_1(C_353)
      | ~ l1_orders_2(B_352)
      | ~ l1_orders_2(A_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_379,plain,(
    ! [B_352,C_353] :
      ( m1_subset_1('#skF_3'('#skF_7',B_352,C_353),u1_struct_0(B_352))
      | v5_orders_3(C_353,'#skF_7',B_352)
      | ~ m1_subset_1(C_353,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_352))))
      | ~ v1_funct_2(C_353,u1_struct_0('#skF_7'),u1_struct_0(B_352))
      | ~ v1_funct_1(C_353)
      | ~ l1_orders_2(B_352)
      | ~ l1_orders_2('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_375])).

tff(c_3009,plain,(
    ! [B_603,C_604] :
      ( m1_subset_1('#skF_3'('#skF_7',B_603,C_604),u1_struct_0(B_603))
      | v5_orders_3(C_604,'#skF_7',B_603)
      | ~ m1_subset_1(C_604,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_603))))
      | ~ v1_funct_2(C_604,u1_struct_0('#skF_5'),u1_struct_0(B_603))
      | ~ v1_funct_1(C_604)
      | ~ l1_orders_2(B_603) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_238,c_379])).

tff(c_3015,plain,
    ( m1_subset_1('#skF_3'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | v5_orders_3('#skF_9','#skF_7','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_133,c_3009])).

tff(c_3028,plain,
    ( m1_subset_1('#skF_3'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | v5_orders_3('#skF_9','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_134,c_3015])).

tff(c_3029,plain,(
    m1_subset_1('#skF_3'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_3028])).

tff(c_295,plain,(
    ! [B_343,C_344] :
      ( m1_subset_1('#skF_4'('#skF_7',B_343,C_344),u1_struct_0(B_343))
      | v5_orders_3(C_344,'#skF_7',B_343)
      | ~ m1_subset_1(C_344,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_343))))
      | ~ v1_funct_2(C_344,u1_struct_0('#skF_7'),u1_struct_0(B_343))
      | ~ v1_funct_1(C_344)
      | ~ l1_orders_2(B_343)
      | ~ l1_orders_2('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_291])).

tff(c_2944,plain,(
    ! [B_599,C_600] :
      ( m1_subset_1('#skF_4'('#skF_7',B_599,C_600),u1_struct_0(B_599))
      | v5_orders_3(C_600,'#skF_7',B_599)
      | ~ m1_subset_1(C_600,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_599))))
      | ~ v1_funct_2(C_600,u1_struct_0('#skF_5'),u1_struct_0(B_599))
      | ~ v1_funct_1(C_600)
      | ~ l1_orders_2(B_599) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_238,c_295])).

tff(c_2950,plain,
    ( m1_subset_1('#skF_4'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | v5_orders_3('#skF_9','#skF_7','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_133,c_2944])).

tff(c_2963,plain,
    ( m1_subset_1('#skF_4'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | v5_orders_3('#skF_9','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_134,c_2950])).

tff(c_2964,plain,(
    m1_subset_1('#skF_4'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_2963])).

tff(c_576,plain,(
    ! [C_379,A_380,B_381] :
      ( k1_funct_1(C_379,'#skF_1'(A_380,B_381,C_379)) = '#skF_3'(A_380,B_381,C_379)
      | v5_orders_3(C_379,A_380,B_381)
      | ~ m1_subset_1(C_379,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_380),u1_struct_0(B_381))))
      | ~ v1_funct_2(C_379,u1_struct_0(A_380),u1_struct_0(B_381))
      | ~ v1_funct_1(C_379)
      | ~ l1_orders_2(B_381)
      | ~ l1_orders_2(A_380) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_580,plain,(
    ! [C_379,B_381] :
      ( k1_funct_1(C_379,'#skF_1'('#skF_7',B_381,C_379)) = '#skF_3'('#skF_7',B_381,C_379)
      | v5_orders_3(C_379,'#skF_7',B_381)
      | ~ m1_subset_1(C_379,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_381))))
      | ~ v1_funct_2(C_379,u1_struct_0('#skF_7'),u1_struct_0(B_381))
      | ~ v1_funct_1(C_379)
      | ~ l1_orders_2(B_381)
      | ~ l1_orders_2('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_576])).

tff(c_3124,plain,(
    ! [C_615,B_616] :
      ( k1_funct_1(C_615,'#skF_1'('#skF_7',B_616,C_615)) = '#skF_3'('#skF_7',B_616,C_615)
      | v5_orders_3(C_615,'#skF_7',B_616)
      | ~ m1_subset_1(C_615,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_616))))
      | ~ v1_funct_2(C_615,u1_struct_0('#skF_5'),u1_struct_0(B_616))
      | ~ v1_funct_1(C_615)
      | ~ l1_orders_2(B_616) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_238,c_580])).

tff(c_3130,plain,
    ( k1_funct_1('#skF_9','#skF_1'('#skF_7','#skF_8','#skF_9')) = '#skF_3'('#skF_7','#skF_8','#skF_9')
    | v5_orders_3('#skF_9','#skF_7','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_133,c_3124])).

tff(c_3143,plain,
    ( k1_funct_1('#skF_9','#skF_1'('#skF_7','#skF_8','#skF_9')) = '#skF_3'('#skF_7','#skF_8','#skF_9')
    | v5_orders_3('#skF_9','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_134,c_3130])).

tff(c_3144,plain,(
    k1_funct_1('#skF_9','#skF_1'('#skF_7','#skF_8','#skF_9')) = '#skF_3'('#skF_7','#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_3143])).

tff(c_2497,plain,(
    ! [C_555,A_556,B_557] :
      ( k1_funct_1(C_555,'#skF_2'(A_556,B_557,C_555)) = '#skF_4'(A_556,B_557,C_555)
      | v5_orders_3(C_555,A_556,B_557)
      | ~ m1_subset_1(C_555,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_556),u1_struct_0(B_557))))
      | ~ v1_funct_2(C_555,u1_struct_0(A_556),u1_struct_0(B_557))
      | ~ v1_funct_1(C_555)
      | ~ l1_orders_2(B_557)
      | ~ l1_orders_2(A_556) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2501,plain,(
    ! [C_555,B_557] :
      ( k1_funct_1(C_555,'#skF_2'('#skF_7',B_557,C_555)) = '#skF_4'('#skF_7',B_557,C_555)
      | v5_orders_3(C_555,'#skF_7',B_557)
      | ~ m1_subset_1(C_555,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_557))))
      | ~ v1_funct_2(C_555,u1_struct_0('#skF_7'),u1_struct_0(B_557))
      | ~ v1_funct_1(C_555)
      | ~ l1_orders_2(B_557)
      | ~ l1_orders_2('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_2497])).

tff(c_3548,plain,(
    ! [C_657,B_658] :
      ( k1_funct_1(C_657,'#skF_2'('#skF_7',B_658,C_657)) = '#skF_4'('#skF_7',B_658,C_657)
      | v5_orders_3(C_657,'#skF_7',B_658)
      | ~ m1_subset_1(C_657,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_658))))
      | ~ v1_funct_2(C_657,u1_struct_0('#skF_5'),u1_struct_0(B_658))
      | ~ v1_funct_1(C_657)
      | ~ l1_orders_2(B_658) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_238,c_2501])).

tff(c_3554,plain,
    ( k1_funct_1('#skF_9','#skF_2'('#skF_7','#skF_8','#skF_9')) = '#skF_4'('#skF_7','#skF_8','#skF_9')
    | v5_orders_3('#skF_9','#skF_7','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_133,c_3548])).

tff(c_3567,plain,
    ( k1_funct_1('#skF_9','#skF_2'('#skF_7','#skF_8','#skF_9')) = '#skF_4'('#skF_7','#skF_8','#skF_9')
    | v5_orders_3('#skF_9','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_134,c_3554])).

tff(c_3568,plain,(
    k1_funct_1('#skF_9','#skF_2'('#skF_7','#skF_8','#skF_9')) = '#skF_4'('#skF_7','#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_3567])).

tff(c_500,plain,(
    ! [A_373,B_374,C_375] :
      ( m1_subset_1('#skF_1'(A_373,B_374,C_375),u1_struct_0(A_373))
      | v5_orders_3(C_375,A_373,B_374)
      | ~ m1_subset_1(C_375,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_373),u1_struct_0(B_374))))
      | ~ v1_funct_2(C_375,u1_struct_0(A_373),u1_struct_0(B_374))
      | ~ v1_funct_1(C_375)
      | ~ l1_orders_2(B_374)
      | ~ l1_orders_2(A_373) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_504,plain,(
    ! [B_374,C_375] :
      ( m1_subset_1('#skF_1'('#skF_7',B_374,C_375),u1_struct_0('#skF_7'))
      | v5_orders_3(C_375,'#skF_7',B_374)
      | ~ m1_subset_1(C_375,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_374))))
      | ~ v1_funct_2(C_375,u1_struct_0('#skF_7'),u1_struct_0(B_374))
      | ~ v1_funct_1(C_375)
      | ~ l1_orders_2(B_374)
      | ~ l1_orders_2('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_500])).

tff(c_2553,plain,(
    ! [B_560,C_561] :
      ( m1_subset_1('#skF_1'('#skF_7',B_560,C_561),u1_struct_0('#skF_5'))
      | v5_orders_3(C_561,'#skF_7',B_560)
      | ~ m1_subset_1(C_561,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_560))))
      | ~ v1_funct_2(C_561,u1_struct_0('#skF_5'),u1_struct_0(B_560))
      | ~ v1_funct_1(C_561)
      | ~ l1_orders_2(B_560) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_238,c_238,c_504])).

tff(c_2562,plain,
    ( m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
    | v5_orders_3('#skF_9','#skF_7','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_133,c_2553])).

tff(c_2577,plain,
    ( m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
    | v5_orders_3('#skF_9','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_134,c_2562])).

tff(c_2578,plain,(
    m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_2577])).

tff(c_436,plain,(
    ! [A_362,B_363,C_364] :
      ( m1_subset_1('#skF_2'(A_362,B_363,C_364),u1_struct_0(A_362))
      | v5_orders_3(C_364,A_362,B_363)
      | ~ m1_subset_1(C_364,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_362),u1_struct_0(B_363))))
      | ~ v1_funct_2(C_364,u1_struct_0(A_362),u1_struct_0(B_363))
      | ~ v1_funct_1(C_364)
      | ~ l1_orders_2(B_363)
      | ~ l1_orders_2(A_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_440,plain,(
    ! [B_363,C_364] :
      ( m1_subset_1('#skF_2'('#skF_7',B_363,C_364),u1_struct_0('#skF_7'))
      | v5_orders_3(C_364,'#skF_7',B_363)
      | ~ m1_subset_1(C_364,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_363))))
      | ~ v1_funct_2(C_364,u1_struct_0('#skF_7'),u1_struct_0(B_363))
      | ~ v1_funct_1(C_364)
      | ~ l1_orders_2(B_363)
      | ~ l1_orders_2('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_436])).

tff(c_536,plain,(
    ! [B_376,C_377] :
      ( m1_subset_1('#skF_2'('#skF_7',B_376,C_377),u1_struct_0('#skF_5'))
      | v5_orders_3(C_377,'#skF_7',B_376)
      | ~ m1_subset_1(C_377,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_376))))
      | ~ v1_funct_2(C_377,u1_struct_0('#skF_5'),u1_struct_0(B_376))
      | ~ v1_funct_1(C_377)
      | ~ l1_orders_2(B_376) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_238,c_238,c_440])).

tff(c_545,plain,
    ( m1_subset_1('#skF_2'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
    | v5_orders_3('#skF_9','#skF_7','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_133,c_536])).

tff(c_560,plain,
    ( m1_subset_1('#skF_2'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
    | v5_orders_3('#skF_9','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_134,c_545])).

tff(c_561,plain,(
    m1_subset_1('#skF_2'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_560])).

tff(c_2000,plain,(
    ! [A_507,B_508,C_509] :
      ( r1_orders_2(A_507,'#skF_1'(A_507,B_508,C_509),'#skF_2'(A_507,B_508,C_509))
      | v5_orders_3(C_509,A_507,B_508)
      | ~ m1_subset_1(C_509,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_507),u1_struct_0(B_508))))
      | ~ v1_funct_2(C_509,u1_struct_0(A_507),u1_struct_0(B_508))
      | ~ v1_funct_1(C_509)
      | ~ l1_orders_2(B_508)
      | ~ l1_orders_2(A_507) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2004,plain,(
    ! [B_508,C_509] :
      ( r1_orders_2('#skF_7','#skF_1'('#skF_7',B_508,C_509),'#skF_2'('#skF_7',B_508,C_509))
      | v5_orders_3(C_509,'#skF_7',B_508)
      | ~ m1_subset_1(C_509,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_508))))
      | ~ v1_funct_2(C_509,u1_struct_0('#skF_7'),u1_struct_0(B_508))
      | ~ v1_funct_1(C_509)
      | ~ l1_orders_2(B_508)
      | ~ l1_orders_2('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_2000])).

tff(c_3588,plain,(
    ! [B_660,C_661] :
      ( r1_orders_2('#skF_7','#skF_1'('#skF_7',B_660,C_661),'#skF_2'('#skF_7',B_660,C_661))
      | v5_orders_3(C_661,'#skF_7',B_660)
      | ~ m1_subset_1(C_661,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_660))))
      | ~ v1_funct_2(C_661,u1_struct_0('#skF_5'),u1_struct_0(B_660))
      | ~ v1_funct_1(C_661)
      | ~ l1_orders_2(B_660) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_238,c_2004])).

tff(c_3594,plain,
    ( r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_2'('#skF_7','#skF_8','#skF_9'))
    | v5_orders_3('#skF_9','#skF_7','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_133,c_3588])).

tff(c_3607,plain,
    ( r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_2'('#skF_7','#skF_8','#skF_9'))
    | v5_orders_3('#skF_9','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_134,c_3594])).

tff(c_3608,plain,(
    r1_orders_2('#skF_7','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_2'('#skF_7','#skF_8','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_3607])).

tff(c_257,plain,
    ( m1_subset_1(u1_orders_2('#skF_7'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_7'))))
    | ~ l1_orders_2('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_6])).

tff(c_264,plain,(
    m1_subset_1(u1_orders_2('#skF_7'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_238,c_257])).

tff(c_249,plain,(
    g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_7')) = g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_38])).

tff(c_8,plain,(
    ! [D_14,B_10,C_13,A_9] :
      ( D_14 = B_10
      | g1_orders_2(C_13,D_14) != g1_orders_2(A_9,B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(k2_zfmisc_1(A_9,A_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_279,plain,(
    ! [D_14,C_13] :
      ( u1_orders_2('#skF_7') = D_14
      | g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5')) != g1_orders_2(C_13,D_14)
      | ~ m1_subset_1(u1_orders_2('#skF_7'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_8])).

tff(c_287,plain,(
    ! [D_14,C_13] :
      ( u1_orders_2('#skF_7') = D_14
      | g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5')) != g1_orders_2(C_13,D_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_279])).

tff(c_328,plain,(
    u1_orders_2('#skF_7') = u1_orders_2('#skF_5') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_287])).

tff(c_4,plain,(
    ! [B_5,C_7,A_1] :
      ( r2_hidden(k4_tarski(B_5,C_7),u1_orders_2(A_1))
      | ~ r1_orders_2(A_1,B_5,C_7)
      | ~ m1_subset_1(C_7,u1_struct_0(A_1))
      | ~ m1_subset_1(B_5,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_344,plain,(
    ! [B_5,C_7] :
      ( r2_hidden(k4_tarski(B_5,C_7),u1_orders_2('#skF_5'))
      | ~ r1_orders_2('#skF_7',B_5,C_7)
      | ~ m1_subset_1(C_7,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(B_5,u1_struct_0('#skF_7'))
      | ~ l1_orders_2('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_328,c_4])).

tff(c_480,plain,(
    ! [B_369,C_370] :
      ( r2_hidden(k4_tarski(B_369,C_370),u1_orders_2('#skF_5'))
      | ~ r1_orders_2('#skF_7',B_369,C_370)
      | ~ m1_subset_1(C_370,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_369,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_238,c_238,c_344])).

tff(c_2,plain,(
    ! [A_1,B_5,C_7] :
      ( r1_orders_2(A_1,B_5,C_7)
      | ~ r2_hidden(k4_tarski(B_5,C_7),u1_orders_2(A_1))
      | ~ m1_subset_1(C_7,u1_struct_0(A_1))
      | ~ m1_subset_1(B_5,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_486,plain,(
    ! [B_369,C_370] :
      ( r1_orders_2('#skF_5',B_369,C_370)
      | ~ l1_orders_2('#skF_5')
      | ~ r1_orders_2('#skF_7',B_369,C_370)
      | ~ m1_subset_1(C_370,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_369,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_480,c_2])).

tff(c_490,plain,(
    ! [B_369,C_370] :
      ( r1_orders_2('#skF_5',B_369,C_370)
      | ~ r1_orders_2('#skF_7',B_369,C_370)
      | ~ m1_subset_1(C_370,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_369,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_486])).

tff(c_3637,plain,
    ( r1_orders_2('#skF_5','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_2'('#skF_7','#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_2'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_3608,c_490])).

tff(c_3643,plain,(
    r1_orders_2('#skF_5','#skF_1'('#skF_7','#skF_8','#skF_9'),'#skF_2'('#skF_7','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2578,c_561,c_3637])).

tff(c_12,plain,(
    ! [A_15,D_232,C_201,E_240,B_139] :
      ( r1_orders_2(B_139,k1_funct_1(C_201,D_232),k1_funct_1(C_201,E_240))
      | ~ m1_subset_1(k1_funct_1(C_201,E_240),u1_struct_0(B_139))
      | ~ m1_subset_1(k1_funct_1(C_201,D_232),u1_struct_0(B_139))
      | ~ r1_orders_2(A_15,D_232,E_240)
      | ~ m1_subset_1(E_240,u1_struct_0(A_15))
      | ~ m1_subset_1(D_232,u1_struct_0(A_15))
      | ~ v5_orders_3(C_201,A_15,B_139)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_15),u1_struct_0(B_139))))
      | ~ v1_funct_2(C_201,u1_struct_0(A_15),u1_struct_0(B_139))
      | ~ v1_funct_1(C_201)
      | ~ l1_orders_2(B_139)
      | ~ l1_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3645,plain,(
    ! [B_139,C_201] :
      ( r1_orders_2(B_139,k1_funct_1(C_201,'#skF_1'('#skF_7','#skF_8','#skF_9')),k1_funct_1(C_201,'#skF_2'('#skF_7','#skF_8','#skF_9')))
      | ~ m1_subset_1(k1_funct_1(C_201,'#skF_2'('#skF_7','#skF_8','#skF_9')),u1_struct_0(B_139))
      | ~ m1_subset_1(k1_funct_1(C_201,'#skF_1'('#skF_7','#skF_8','#skF_9')),u1_struct_0(B_139))
      | ~ m1_subset_1('#skF_2'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_1'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
      | ~ v5_orders_3(C_201,'#skF_5',B_139)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_139))))
      | ~ v1_funct_2(C_201,u1_struct_0('#skF_5'),u1_struct_0(B_139))
      | ~ v1_funct_1(C_201)
      | ~ l1_orders_2(B_139)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3643,c_12])).

tff(c_3894,plain,(
    ! [B_681,C_682] :
      ( r1_orders_2(B_681,k1_funct_1(C_682,'#skF_1'('#skF_7','#skF_8','#skF_9')),k1_funct_1(C_682,'#skF_2'('#skF_7','#skF_8','#skF_9')))
      | ~ m1_subset_1(k1_funct_1(C_682,'#skF_2'('#skF_7','#skF_8','#skF_9')),u1_struct_0(B_681))
      | ~ m1_subset_1(k1_funct_1(C_682,'#skF_1'('#skF_7','#skF_8','#skF_9')),u1_struct_0(B_681))
      | ~ v5_orders_3(C_682,'#skF_5',B_681)
      | ~ m1_subset_1(C_682,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_681))))
      | ~ v1_funct_2(C_682,u1_struct_0('#skF_5'),u1_struct_0(B_681))
      | ~ v1_funct_1(C_682)
      | ~ l1_orders_2(B_681) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2578,c_561,c_3645])).

tff(c_3905,plain,(
    ! [B_681] :
      ( r1_orders_2(B_681,k1_funct_1('#skF_9','#skF_1'('#skF_7','#skF_8','#skF_9')),'#skF_4'('#skF_7','#skF_8','#skF_9'))
      | ~ m1_subset_1(k1_funct_1('#skF_9','#skF_2'('#skF_7','#skF_8','#skF_9')),u1_struct_0(B_681))
      | ~ m1_subset_1(k1_funct_1('#skF_9','#skF_1'('#skF_7','#skF_8','#skF_9')),u1_struct_0(B_681))
      | ~ v5_orders_3('#skF_9','#skF_5',B_681)
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_681))))
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0(B_681))
      | ~ v1_funct_1('#skF_9')
      | ~ l1_orders_2(B_681) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3568,c_3894])).

tff(c_3920,plain,(
    ! [B_683] :
      ( r1_orders_2(B_683,'#skF_3'('#skF_7','#skF_8','#skF_9'),'#skF_4'('#skF_7','#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_4'('#skF_7','#skF_8','#skF_9'),u1_struct_0(B_683))
      | ~ m1_subset_1('#skF_3'('#skF_7','#skF_8','#skF_9'),u1_struct_0(B_683))
      | ~ v5_orders_3('#skF_9','#skF_5',B_683)
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_683))))
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0(B_683))
      | ~ l1_orders_2(B_683) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_3144,c_3568,c_3144,c_3905])).

tff(c_3926,plain,
    ( r1_orders_2('#skF_8','#skF_3'('#skF_7','#skF_8','#skF_9'),'#skF_4'('#skF_7','#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_4'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_7','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ v5_orders_3('#skF_9','#skF_5','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_133,c_3920])).

tff(c_3934,plain,(
    r1_orders_2('#skF_8','#skF_3'('#skF_7','#skF_8','#skF_9'),'#skF_4'('#skF_7','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_134,c_369,c_3029,c_2964,c_3926])).

tff(c_14,plain,(
    ! [B_139,A_15,C_201] :
      ( ~ r1_orders_2(B_139,'#skF_3'(A_15,B_139,C_201),'#skF_4'(A_15,B_139,C_201))
      | v5_orders_3(C_201,A_15,B_139)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_15),u1_struct_0(B_139))))
      | ~ v1_funct_2(C_201,u1_struct_0(A_15),u1_struct_0(B_139))
      | ~ v1_funct_1(C_201)
      | ~ l1_orders_2(B_139)
      | ~ l1_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3986,plain,
    ( v5_orders_3('#skF_9','#skF_7','#skF_8')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_8'))))
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_7'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_3934,c_14])).

tff(c_3992,plain,(
    v5_orders_3('#skF_9','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_134,c_238,c_133,c_238,c_3986])).

tff(c_3994,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_3992])).

tff(c_3996,plain,(
    ~ v5_orders_3('#skF_9','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_320])).

tff(c_4013,plain,(
    ! [A_692,B_693,C_694] :
      ( m1_subset_1('#skF_3'(A_692,B_693,C_694),u1_struct_0(B_693))
      | v5_orders_3(C_694,A_692,B_693)
      | ~ m1_subset_1(C_694,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_692),u1_struct_0(B_693))))
      | ~ v1_funct_2(C_694,u1_struct_0(A_692),u1_struct_0(B_693))
      | ~ v1_funct_1(C_694)
      | ~ l1_orders_2(B_693)
      | ~ l1_orders_2(A_692) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4023,plain,
    ( m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | v5_orders_3('#skF_9','#skF_5','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_133,c_4013])).

tff(c_4042,plain,
    ( m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | v5_orders_3('#skF_9','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_50,c_134,c_4023])).

tff(c_4043,plain,(
    m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_3996,c_4042])).

tff(c_3995,plain,(
    m1_subset_1('#skF_4'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_320])).

tff(c_60,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_32,plain,(
    v5_orders_3('#skF_9','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_4614,plain,(
    ! [C_753,A_754,B_755] :
      ( k1_funct_1(C_753,'#skF_1'(A_754,B_755,C_753)) = '#skF_3'(A_754,B_755,C_753)
      | v5_orders_3(C_753,A_754,B_755)
      | ~ m1_subset_1(C_753,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_754),u1_struct_0(B_755))))
      | ~ v1_funct_2(C_753,u1_struct_0(A_754),u1_struct_0(B_755))
      | ~ v1_funct_1(C_753)
      | ~ l1_orders_2(B_755)
      | ~ l1_orders_2(A_754) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4624,plain,
    ( k1_funct_1('#skF_9','#skF_1'('#skF_5','#skF_8','#skF_9')) = '#skF_3'('#skF_5','#skF_8','#skF_9')
    | v5_orders_3('#skF_9','#skF_5','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_133,c_4614])).

tff(c_4643,plain,
    ( k1_funct_1('#skF_9','#skF_1'('#skF_5','#skF_8','#skF_9')) = '#skF_3'('#skF_5','#skF_8','#skF_9')
    | v5_orders_3('#skF_9','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_50,c_134,c_4624])).

tff(c_4644,plain,(
    k1_funct_1('#skF_9','#skF_1'('#skF_5','#skF_8','#skF_9')) = '#skF_3'('#skF_5','#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_3996,c_4643])).

tff(c_4242,plain,(
    ! [C_722,A_723,B_724] :
      ( k1_funct_1(C_722,'#skF_2'(A_723,B_724,C_722)) = '#skF_4'(A_723,B_724,C_722)
      | v5_orders_3(C_722,A_723,B_724)
      | ~ m1_subset_1(C_722,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_723),u1_struct_0(B_724))))
      | ~ v1_funct_2(C_722,u1_struct_0(A_723),u1_struct_0(B_724))
      | ~ v1_funct_1(C_722)
      | ~ l1_orders_2(B_724)
      | ~ l1_orders_2(A_723) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4252,plain,
    ( k1_funct_1('#skF_9','#skF_2'('#skF_5','#skF_8','#skF_9')) = '#skF_4'('#skF_5','#skF_8','#skF_9')
    | v5_orders_3('#skF_9','#skF_5','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_133,c_4242])).

tff(c_4271,plain,
    ( k1_funct_1('#skF_9','#skF_2'('#skF_5','#skF_8','#skF_9')) = '#skF_4'('#skF_5','#skF_8','#skF_9')
    | v5_orders_3('#skF_9','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_50,c_134,c_4252])).

tff(c_4272,plain,(
    k1_funct_1('#skF_9','#skF_2'('#skF_5','#skF_8','#skF_9')) = '#skF_4'('#skF_5','#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_3996,c_4271])).

tff(c_4156,plain,(
    ! [A_715,B_716,C_717] :
      ( m1_subset_1('#skF_1'(A_715,B_716,C_717),u1_struct_0(A_715))
      | v5_orders_3(C_717,A_715,B_716)
      | ~ m1_subset_1(C_717,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_715),u1_struct_0(B_716))))
      | ~ v1_funct_2(C_717,u1_struct_0(A_715),u1_struct_0(B_716))
      | ~ v1_funct_1(C_717)
      | ~ l1_orders_2(B_716)
      | ~ l1_orders_2(A_715) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4166,plain,
    ( m1_subset_1('#skF_1'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
    | v5_orders_3('#skF_9','#skF_5','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_133,c_4156])).

tff(c_4185,plain,
    ( m1_subset_1('#skF_1'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
    | v5_orders_3('#skF_9','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_50,c_134,c_4166])).

tff(c_4186,plain,(
    m1_subset_1('#skF_1'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_3996,c_4185])).

tff(c_4091,plain,(
    ! [A_709,B_710,C_711] :
      ( m1_subset_1('#skF_2'(A_709,B_710,C_711),u1_struct_0(A_709))
      | v5_orders_3(C_711,A_709,B_710)
      | ~ m1_subset_1(C_711,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_709),u1_struct_0(B_710))))
      | ~ v1_funct_2(C_711,u1_struct_0(A_709),u1_struct_0(B_710))
      | ~ v1_funct_1(C_711)
      | ~ l1_orders_2(B_710)
      | ~ l1_orders_2(A_709) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4101,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
    | v5_orders_3('#skF_9','#skF_5','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_133,c_4091])).

tff(c_4120,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
    | v5_orders_3('#skF_9','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_50,c_134,c_4101])).

tff(c_4121,plain,(
    m1_subset_1('#skF_2'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_3996,c_4120])).

tff(c_4315,plain,(
    ! [A_727,B_728,C_729] :
      ( r1_orders_2(A_727,'#skF_1'(A_727,B_728,C_729),'#skF_2'(A_727,B_728,C_729))
      | v5_orders_3(C_729,A_727,B_728)
      | ~ m1_subset_1(C_729,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_727),u1_struct_0(B_728))))
      | ~ v1_funct_2(C_729,u1_struct_0(A_727),u1_struct_0(B_728))
      | ~ v1_funct_1(C_729)
      | ~ l1_orders_2(B_728)
      | ~ l1_orders_2(A_727) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4325,plain,
    ( r1_orders_2('#skF_5','#skF_1'('#skF_5','#skF_8','#skF_9'),'#skF_2'('#skF_5','#skF_8','#skF_9'))
    | v5_orders_3('#skF_9','#skF_5','#skF_8')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_133,c_4315])).

tff(c_4344,plain,
    ( r1_orders_2('#skF_5','#skF_1'('#skF_5','#skF_8','#skF_9'),'#skF_2'('#skF_5','#skF_8','#skF_9'))
    | v5_orders_3('#skF_9','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_50,c_134,c_4325])).

tff(c_4345,plain,(
    r1_orders_2('#skF_5','#skF_1'('#skF_5','#skF_8','#skF_9'),'#skF_2'('#skF_5','#skF_8','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_3996,c_4344])).

tff(c_4798,plain,(
    ! [B_772,E_768,C_771,D_769,A_770] :
      ( r1_orders_2(B_772,k1_funct_1(C_771,D_769),k1_funct_1(C_771,E_768))
      | ~ m1_subset_1(k1_funct_1(C_771,E_768),u1_struct_0(B_772))
      | ~ m1_subset_1(k1_funct_1(C_771,D_769),u1_struct_0(B_772))
      | ~ r1_orders_2(A_770,D_769,E_768)
      | ~ m1_subset_1(E_768,u1_struct_0(A_770))
      | ~ m1_subset_1(D_769,u1_struct_0(A_770))
      | ~ v5_orders_3(C_771,A_770,B_772)
      | ~ m1_subset_1(C_771,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_770),u1_struct_0(B_772))))
      | ~ v1_funct_2(C_771,u1_struct_0(A_770),u1_struct_0(B_772))
      | ~ v1_funct_1(C_771)
      | ~ l1_orders_2(B_772)
      | ~ l1_orders_2(A_770) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4804,plain,(
    ! [B_772,C_771] :
      ( r1_orders_2(B_772,k1_funct_1(C_771,'#skF_1'('#skF_5','#skF_8','#skF_9')),k1_funct_1(C_771,'#skF_2'('#skF_5','#skF_8','#skF_9')))
      | ~ m1_subset_1(k1_funct_1(C_771,'#skF_2'('#skF_5','#skF_8','#skF_9')),u1_struct_0(B_772))
      | ~ m1_subset_1(k1_funct_1(C_771,'#skF_1'('#skF_5','#skF_8','#skF_9')),u1_struct_0(B_772))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_1'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_5'))
      | ~ v5_orders_3(C_771,'#skF_5',B_772)
      | ~ m1_subset_1(C_771,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_772))))
      | ~ v1_funct_2(C_771,u1_struct_0('#skF_5'),u1_struct_0(B_772))
      | ~ v1_funct_1(C_771)
      | ~ l1_orders_2(B_772)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4345,c_4798])).

tff(c_5654,plain,(
    ! [B_851,C_852] :
      ( r1_orders_2(B_851,k1_funct_1(C_852,'#skF_1'('#skF_5','#skF_8','#skF_9')),k1_funct_1(C_852,'#skF_2'('#skF_5','#skF_8','#skF_9')))
      | ~ m1_subset_1(k1_funct_1(C_852,'#skF_2'('#skF_5','#skF_8','#skF_9')),u1_struct_0(B_851))
      | ~ m1_subset_1(k1_funct_1(C_852,'#skF_1'('#skF_5','#skF_8','#skF_9')),u1_struct_0(B_851))
      | ~ v5_orders_3(C_852,'#skF_5',B_851)
      | ~ m1_subset_1(C_852,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_851))))
      | ~ v1_funct_2(C_852,u1_struct_0('#skF_5'),u1_struct_0(B_851))
      | ~ v1_funct_1(C_852)
      | ~ l1_orders_2(B_851) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4186,c_4121,c_4804])).

tff(c_5665,plain,(
    ! [B_851] :
      ( r1_orders_2(B_851,'#skF_3'('#skF_5','#skF_8','#skF_9'),k1_funct_1('#skF_9','#skF_2'('#skF_5','#skF_8','#skF_9')))
      | ~ m1_subset_1(k1_funct_1('#skF_9','#skF_2'('#skF_5','#skF_8','#skF_9')),u1_struct_0(B_851))
      | ~ m1_subset_1(k1_funct_1('#skF_9','#skF_1'('#skF_5','#skF_8','#skF_9')),u1_struct_0(B_851))
      | ~ v5_orders_3('#skF_9','#skF_5',B_851)
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_851))))
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0(B_851))
      | ~ v1_funct_1('#skF_9')
      | ~ l1_orders_2(B_851) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4644,c_5654])).

tff(c_5680,plain,(
    ! [B_853] :
      ( r1_orders_2(B_853,'#skF_3'('#skF_5','#skF_8','#skF_9'),'#skF_4'('#skF_5','#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_8','#skF_9'),u1_struct_0(B_853))
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_9'),u1_struct_0(B_853))
      | ~ v5_orders_3('#skF_9','#skF_5',B_853)
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_853))))
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0(B_853))
      | ~ l1_orders_2(B_853) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_4644,c_4272,c_4272,c_5665])).

tff(c_5689,plain,
    ( r1_orders_2('#skF_6','#skF_3'('#skF_5','#skF_8','#skF_9'),'#skF_4'('#skF_5','#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_4'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_6'))
    | ~ v5_orders_3('#skF_9','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))))
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_5680])).

tff(c_5696,plain,(
    r1_orders_2('#skF_6','#skF_3'('#skF_5','#skF_8','#skF_9'),'#skF_4'('#skF_5','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_134,c_116,c_133,c_32,c_4043,c_116,c_3995,c_116,c_5689])).

tff(c_138,plain,
    ( m1_subset_1(u1_orders_2('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_6'))))
    | ~ l1_orders_2('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_6])).

tff(c_145,plain,(
    m1_subset_1(u1_orders_2('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_8')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_116,c_138])).

tff(c_132,plain,(
    g1_orders_2(u1_struct_0('#skF_8'),u1_orders_2('#skF_6')) = g1_orders_2(u1_struct_0('#skF_8'),u1_orders_2('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_36])).

tff(c_155,plain,(
    ! [D_14,C_13] :
      ( u1_orders_2('#skF_6') = D_14
      | g1_orders_2(u1_struct_0('#skF_8'),u1_orders_2('#skF_8')) != g1_orders_2(C_13,D_14)
      | ~ m1_subset_1(u1_orders_2('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_8')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_8])).

tff(c_163,plain,(
    ! [D_14,C_13] :
      ( u1_orders_2('#skF_6') = D_14
      | g1_orders_2(u1_struct_0('#skF_8'),u1_orders_2('#skF_8')) != g1_orders_2(C_13,D_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_155])).

tff(c_169,plain,(
    u1_orders_2('#skF_6') = u1_orders_2('#skF_8') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_163])).

tff(c_186,plain,(
    ! [B_5,C_7] :
      ( r2_hidden(k4_tarski(B_5,C_7),u1_orders_2('#skF_8'))
      | ~ r1_orders_2('#skF_6',B_5,C_7)
      | ~ m1_subset_1(C_7,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_5,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_4])).

tff(c_4079,plain,(
    ! [B_705,C_706] :
      ( r2_hidden(k4_tarski(B_705,C_706),u1_orders_2('#skF_8'))
      | ~ r1_orders_2('#skF_6',B_705,C_706)
      | ~ m1_subset_1(C_706,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(B_705,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_116,c_116,c_186])).

tff(c_4085,plain,(
    ! [B_705,C_706] :
      ( r1_orders_2('#skF_8',B_705,C_706)
      | ~ l1_orders_2('#skF_8')
      | ~ r1_orders_2('#skF_6',B_705,C_706)
      | ~ m1_subset_1(C_706,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(B_705,u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_4079,c_2])).

tff(c_4089,plain,(
    ! [B_705,C_706] :
      ( r1_orders_2('#skF_8',B_705,C_706)
      | ~ r1_orders_2('#skF_6',B_705,C_706)
      | ~ m1_subset_1(C_706,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(B_705,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4085])).

tff(c_5726,plain,
    ( r1_orders_2('#skF_8','#skF_3'('#skF_5','#skF_8','#skF_9'),'#skF_4'('#skF_5','#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_4'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(resolution,[status(thm)],[c_5696,c_4089])).

tff(c_5732,plain,(
    r1_orders_2('#skF_8','#skF_3'('#skF_5','#skF_8','#skF_9'),'#skF_4'('#skF_5','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4043,c_3995,c_5726])).

tff(c_5736,plain,
    ( v5_orders_3('#skF_9','#skF_5','#skF_8')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))))
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_5'),u1_struct_0('#skF_8'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_orders_2('#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_5732,c_14])).

tff(c_5742,plain,(
    v5_orders_3('#skF_9','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_50,c_134,c_133,c_5736])).

tff(c_5744,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3996,c_5742])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:51:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.64/2.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.64/2.53  
% 7.64/2.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.64/2.53  %$ v5_orders_3 > v1_funct_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v1_funct_1 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3
% 7.64/2.53  
% 7.64/2.53  %Foreground sorts:
% 7.64/2.53  
% 7.64/2.53  
% 7.64/2.53  %Background operators:
% 7.64/2.53  
% 7.64/2.53  
% 7.64/2.53  %Foreground operators:
% 7.64/2.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.64/2.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.64/2.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.64/2.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.64/2.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.64/2.53  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.64/2.53  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 7.64/2.53  tff(v5_orders_3, type, v5_orders_3: ($i * $i * $i) > $o).
% 7.64/2.53  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.64/2.53  tff('#skF_7', type, '#skF_7': $i).
% 7.64/2.53  tff('#skF_10', type, '#skF_10': $i).
% 7.64/2.53  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 7.64/2.53  tff('#skF_5', type, '#skF_5': $i).
% 7.64/2.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.64/2.53  tff('#skF_6', type, '#skF_6': $i).
% 7.64/2.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.64/2.53  tff('#skF_9', type, '#skF_9': $i).
% 7.64/2.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.64/2.53  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.64/2.53  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 7.64/2.53  tff('#skF_8', type, '#skF_8': $i).
% 7.64/2.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.64/2.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.64/2.53  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.64/2.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.64/2.53  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 7.64/2.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.64/2.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.64/2.53  
% 7.64/2.56  tff(f_126, negated_conjecture, ~(![A]: (l1_orders_2(A) => (![B]: (l1_orders_2(B) => (![C]: ((~v2_struct_0(C) & l1_orders_2(C)) => (![D]: ((~v2_struct_0(D) & l1_orders_2(D)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(D))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(D))))) => (((((g1_orders_2(u1_struct_0(A), u1_orders_2(A)) = g1_orders_2(u1_struct_0(C), u1_orders_2(C))) & (g1_orders_2(u1_struct_0(B), u1_orders_2(B)) = g1_orders_2(u1_struct_0(D), u1_orders_2(D)))) & (E = F)) & v5_orders_3(E, A, B)) => v5_orders_3(F, C, D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_waybel_9)).
% 7.64/2.56  tff(f_41, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 7.64/2.56  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C, D]: ((g1_orders_2(A, B) = g1_orders_2(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_orders_2)).
% 7.64/2.56  tff(f_84, axiom, (![A]: (l1_orders_2(A) => (![B]: (l1_orders_2(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v5_orders_3(C, A, B) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => (r1_orders_2(A, D, E) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(B)) => (((F = k1_funct_1(C, D)) & (G = k1_funct_1(C, E))) => r1_orders_2(B, F, G)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_orders_3)).
% 7.64/2.56  tff(f_37, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_orders_2)).
% 7.64/2.56  tff(c_34, plain, ('#skF_10'='#skF_9'), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.64/2.56  tff(c_30, plain, (~v5_orders_3('#skF_10', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.64/2.56  tff(c_67, plain, (~v5_orders_3('#skF_9', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30])).
% 7.64/2.56  tff(c_56, plain, (l1_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.64/2.56  tff(c_52, plain, (l1_orders_2('#skF_8')), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.64/2.56  tff(c_50, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.64/2.56  tff(c_6, plain, (![A_8]: (m1_subset_1(u1_orders_2(A_8), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8), u1_struct_0(A_8)))) | ~l1_orders_2(A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.64/2.56  tff(c_36, plain, (g1_orders_2(u1_struct_0('#skF_6'), u1_orders_2('#skF_6'))=g1_orders_2(u1_struct_0('#skF_8'), u1_orders_2('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.64/2.56  tff(c_85, plain, (![C_316, A_317, D_318, B_319]: (C_316=A_317 | g1_orders_2(C_316, D_318)!=g1_orders_2(A_317, B_319) | ~m1_subset_1(B_319, k1_zfmisc_1(k2_zfmisc_1(A_317, A_317))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.64/2.56  tff(c_107, plain, (![A_324, B_325]: (u1_struct_0('#skF_6')=A_324 | g1_orders_2(u1_struct_0('#skF_8'), u1_orders_2('#skF_8'))!=g1_orders_2(A_324, B_325) | ~m1_subset_1(B_325, k1_zfmisc_1(k2_zfmisc_1(A_324, A_324))))), inference(superposition, [status(thm), theory('equality')], [c_36, c_85])).
% 7.64/2.56  tff(c_111, plain, (![A_8]: (u1_struct_0(A_8)=u1_struct_0('#skF_6') | g1_orders_2(u1_struct_0(A_8), u1_orders_2(A_8))!=g1_orders_2(u1_struct_0('#skF_8'), u1_orders_2('#skF_8')) | ~l1_orders_2(A_8))), inference(resolution, [status(thm)], [c_6, c_107])).
% 7.64/2.56  tff(c_114, plain, (u1_struct_0('#skF_6')=u1_struct_0('#skF_8') | ~l1_orders_2('#skF_8')), inference(reflexivity, [status(thm), theory('equality')], [c_111])).
% 7.64/2.56  tff(c_116, plain, (u1_struct_0('#skF_6')=u1_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_114])).
% 7.64/2.56  tff(c_48, plain, (v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.64/2.56  tff(c_134, plain, (v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_48])).
% 7.64/2.56  tff(c_62, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.64/2.56  tff(c_38, plain, (g1_orders_2(u1_struct_0('#skF_7'), u1_orders_2('#skF_7'))=g1_orders_2(u1_struct_0('#skF_5'), u1_orders_2('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.64/2.56  tff(c_225, plain, (![A_339, B_340]: (u1_struct_0('#skF_7')=A_339 | g1_orders_2(u1_struct_0('#skF_5'), u1_orders_2('#skF_5'))!=g1_orders_2(A_339, B_340) | ~m1_subset_1(B_340, k1_zfmisc_1(k2_zfmisc_1(A_339, A_339))))), inference(superposition, [status(thm), theory('equality')], [c_38, c_85])).
% 7.64/2.56  tff(c_233, plain, (![A_8]: (u1_struct_0(A_8)=u1_struct_0('#skF_7') | g1_orders_2(u1_struct_0(A_8), u1_orders_2(A_8))!=g1_orders_2(u1_struct_0('#skF_5'), u1_orders_2('#skF_5')) | ~l1_orders_2(A_8))), inference(resolution, [status(thm)], [c_6, c_225])).
% 7.64/2.56  tff(c_236, plain, (u1_struct_0('#skF_7')=u1_struct_0('#skF_5') | ~l1_orders_2('#skF_5')), inference(reflexivity, [status(thm), theory('equality')], [c_233])).
% 7.64/2.56  tff(c_238, plain, (u1_struct_0('#skF_7')=u1_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_236])).
% 7.64/2.56  tff(c_46, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.64/2.56  tff(c_133, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_8'))))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_46])).
% 7.64/2.56  tff(c_291, plain, (![A_342, B_343, C_344]: (m1_subset_1('#skF_4'(A_342, B_343, C_344), u1_struct_0(B_343)) | v5_orders_3(C_344, A_342, B_343) | ~m1_subset_1(C_344, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_342), u1_struct_0(B_343)))) | ~v1_funct_2(C_344, u1_struct_0(A_342), u1_struct_0(B_343)) | ~v1_funct_1(C_344) | ~l1_orders_2(B_343) | ~l1_orders_2(A_342))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.64/2.56  tff(c_301, plain, (m1_subset_1('#skF_4'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | v5_orders_3('#skF_9', '#skF_5', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8') | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_133, c_291])).
% 7.64/2.56  tff(c_320, plain, (m1_subset_1('#skF_4'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | v5_orders_3('#skF_9', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_50, c_134, c_301])).
% 7.64/2.56  tff(c_369, plain, (v5_orders_3('#skF_9', '#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_320])).
% 7.64/2.56  tff(c_375, plain, (![A_351, B_352, C_353]: (m1_subset_1('#skF_3'(A_351, B_352, C_353), u1_struct_0(B_352)) | v5_orders_3(C_353, A_351, B_352) | ~m1_subset_1(C_353, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_351), u1_struct_0(B_352)))) | ~v1_funct_2(C_353, u1_struct_0(A_351), u1_struct_0(B_352)) | ~v1_funct_1(C_353) | ~l1_orders_2(B_352) | ~l1_orders_2(A_351))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.64/2.56  tff(c_379, plain, (![B_352, C_353]: (m1_subset_1('#skF_3'('#skF_7', B_352, C_353), u1_struct_0(B_352)) | v5_orders_3(C_353, '#skF_7', B_352) | ~m1_subset_1(C_353, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_352)))) | ~v1_funct_2(C_353, u1_struct_0('#skF_7'), u1_struct_0(B_352)) | ~v1_funct_1(C_353) | ~l1_orders_2(B_352) | ~l1_orders_2('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_238, c_375])).
% 7.64/2.56  tff(c_3009, plain, (![B_603, C_604]: (m1_subset_1('#skF_3'('#skF_7', B_603, C_604), u1_struct_0(B_603)) | v5_orders_3(C_604, '#skF_7', B_603) | ~m1_subset_1(C_604, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_603)))) | ~v1_funct_2(C_604, u1_struct_0('#skF_5'), u1_struct_0(B_603)) | ~v1_funct_1(C_604) | ~l1_orders_2(B_603))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_238, c_379])).
% 7.64/2.56  tff(c_3015, plain, (m1_subset_1('#skF_3'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | v5_orders_3('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_133, c_3009])).
% 7.64/2.56  tff(c_3028, plain, (m1_subset_1('#skF_3'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | v5_orders_3('#skF_9', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_134, c_3015])).
% 7.64/2.56  tff(c_3029, plain, (m1_subset_1('#skF_3'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_67, c_3028])).
% 7.64/2.56  tff(c_295, plain, (![B_343, C_344]: (m1_subset_1('#skF_4'('#skF_7', B_343, C_344), u1_struct_0(B_343)) | v5_orders_3(C_344, '#skF_7', B_343) | ~m1_subset_1(C_344, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_343)))) | ~v1_funct_2(C_344, u1_struct_0('#skF_7'), u1_struct_0(B_343)) | ~v1_funct_1(C_344) | ~l1_orders_2(B_343) | ~l1_orders_2('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_238, c_291])).
% 7.64/2.56  tff(c_2944, plain, (![B_599, C_600]: (m1_subset_1('#skF_4'('#skF_7', B_599, C_600), u1_struct_0(B_599)) | v5_orders_3(C_600, '#skF_7', B_599) | ~m1_subset_1(C_600, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_599)))) | ~v1_funct_2(C_600, u1_struct_0('#skF_5'), u1_struct_0(B_599)) | ~v1_funct_1(C_600) | ~l1_orders_2(B_599))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_238, c_295])).
% 7.64/2.56  tff(c_2950, plain, (m1_subset_1('#skF_4'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | v5_orders_3('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_133, c_2944])).
% 7.64/2.56  tff(c_2963, plain, (m1_subset_1('#skF_4'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | v5_orders_3('#skF_9', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_134, c_2950])).
% 7.64/2.56  tff(c_2964, plain, (m1_subset_1('#skF_4'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_67, c_2963])).
% 7.64/2.56  tff(c_576, plain, (![C_379, A_380, B_381]: (k1_funct_1(C_379, '#skF_1'(A_380, B_381, C_379))='#skF_3'(A_380, B_381, C_379) | v5_orders_3(C_379, A_380, B_381) | ~m1_subset_1(C_379, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_380), u1_struct_0(B_381)))) | ~v1_funct_2(C_379, u1_struct_0(A_380), u1_struct_0(B_381)) | ~v1_funct_1(C_379) | ~l1_orders_2(B_381) | ~l1_orders_2(A_380))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.64/2.56  tff(c_580, plain, (![C_379, B_381]: (k1_funct_1(C_379, '#skF_1'('#skF_7', B_381, C_379))='#skF_3'('#skF_7', B_381, C_379) | v5_orders_3(C_379, '#skF_7', B_381) | ~m1_subset_1(C_379, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_381)))) | ~v1_funct_2(C_379, u1_struct_0('#skF_7'), u1_struct_0(B_381)) | ~v1_funct_1(C_379) | ~l1_orders_2(B_381) | ~l1_orders_2('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_238, c_576])).
% 7.64/2.56  tff(c_3124, plain, (![C_615, B_616]: (k1_funct_1(C_615, '#skF_1'('#skF_7', B_616, C_615))='#skF_3'('#skF_7', B_616, C_615) | v5_orders_3(C_615, '#skF_7', B_616) | ~m1_subset_1(C_615, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_616)))) | ~v1_funct_2(C_615, u1_struct_0('#skF_5'), u1_struct_0(B_616)) | ~v1_funct_1(C_615) | ~l1_orders_2(B_616))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_238, c_580])).
% 7.64/2.56  tff(c_3130, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_7', '#skF_8', '#skF_9'))='#skF_3'('#skF_7', '#skF_8', '#skF_9') | v5_orders_3('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_133, c_3124])).
% 7.64/2.56  tff(c_3143, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_7', '#skF_8', '#skF_9'))='#skF_3'('#skF_7', '#skF_8', '#skF_9') | v5_orders_3('#skF_9', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_134, c_3130])).
% 7.64/2.56  tff(c_3144, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_7', '#skF_8', '#skF_9'))='#skF_3'('#skF_7', '#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_67, c_3143])).
% 7.64/2.56  tff(c_2497, plain, (![C_555, A_556, B_557]: (k1_funct_1(C_555, '#skF_2'(A_556, B_557, C_555))='#skF_4'(A_556, B_557, C_555) | v5_orders_3(C_555, A_556, B_557) | ~m1_subset_1(C_555, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_556), u1_struct_0(B_557)))) | ~v1_funct_2(C_555, u1_struct_0(A_556), u1_struct_0(B_557)) | ~v1_funct_1(C_555) | ~l1_orders_2(B_557) | ~l1_orders_2(A_556))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.64/2.56  tff(c_2501, plain, (![C_555, B_557]: (k1_funct_1(C_555, '#skF_2'('#skF_7', B_557, C_555))='#skF_4'('#skF_7', B_557, C_555) | v5_orders_3(C_555, '#skF_7', B_557) | ~m1_subset_1(C_555, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_557)))) | ~v1_funct_2(C_555, u1_struct_0('#skF_7'), u1_struct_0(B_557)) | ~v1_funct_1(C_555) | ~l1_orders_2(B_557) | ~l1_orders_2('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_238, c_2497])).
% 7.64/2.56  tff(c_3548, plain, (![C_657, B_658]: (k1_funct_1(C_657, '#skF_2'('#skF_7', B_658, C_657))='#skF_4'('#skF_7', B_658, C_657) | v5_orders_3(C_657, '#skF_7', B_658) | ~m1_subset_1(C_657, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_658)))) | ~v1_funct_2(C_657, u1_struct_0('#skF_5'), u1_struct_0(B_658)) | ~v1_funct_1(C_657) | ~l1_orders_2(B_658))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_238, c_2501])).
% 7.64/2.56  tff(c_3554, plain, (k1_funct_1('#skF_9', '#skF_2'('#skF_7', '#skF_8', '#skF_9'))='#skF_4'('#skF_7', '#skF_8', '#skF_9') | v5_orders_3('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_133, c_3548])).
% 7.64/2.56  tff(c_3567, plain, (k1_funct_1('#skF_9', '#skF_2'('#skF_7', '#skF_8', '#skF_9'))='#skF_4'('#skF_7', '#skF_8', '#skF_9') | v5_orders_3('#skF_9', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_134, c_3554])).
% 7.64/2.56  tff(c_3568, plain, (k1_funct_1('#skF_9', '#skF_2'('#skF_7', '#skF_8', '#skF_9'))='#skF_4'('#skF_7', '#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_67, c_3567])).
% 7.64/2.56  tff(c_500, plain, (![A_373, B_374, C_375]: (m1_subset_1('#skF_1'(A_373, B_374, C_375), u1_struct_0(A_373)) | v5_orders_3(C_375, A_373, B_374) | ~m1_subset_1(C_375, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_373), u1_struct_0(B_374)))) | ~v1_funct_2(C_375, u1_struct_0(A_373), u1_struct_0(B_374)) | ~v1_funct_1(C_375) | ~l1_orders_2(B_374) | ~l1_orders_2(A_373))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.64/2.56  tff(c_504, plain, (![B_374, C_375]: (m1_subset_1('#skF_1'('#skF_7', B_374, C_375), u1_struct_0('#skF_7')) | v5_orders_3(C_375, '#skF_7', B_374) | ~m1_subset_1(C_375, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_374)))) | ~v1_funct_2(C_375, u1_struct_0('#skF_7'), u1_struct_0(B_374)) | ~v1_funct_1(C_375) | ~l1_orders_2(B_374) | ~l1_orders_2('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_238, c_500])).
% 7.64/2.56  tff(c_2553, plain, (![B_560, C_561]: (m1_subset_1('#skF_1'('#skF_7', B_560, C_561), u1_struct_0('#skF_5')) | v5_orders_3(C_561, '#skF_7', B_560) | ~m1_subset_1(C_561, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_560)))) | ~v1_funct_2(C_561, u1_struct_0('#skF_5'), u1_struct_0(B_560)) | ~v1_funct_1(C_561) | ~l1_orders_2(B_560))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_238, c_238, c_504])).
% 7.64/2.56  tff(c_2562, plain, (m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | v5_orders_3('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_133, c_2553])).
% 7.64/2.56  tff(c_2577, plain, (m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | v5_orders_3('#skF_9', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_134, c_2562])).
% 7.64/2.56  tff(c_2578, plain, (m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_67, c_2577])).
% 7.64/2.56  tff(c_436, plain, (![A_362, B_363, C_364]: (m1_subset_1('#skF_2'(A_362, B_363, C_364), u1_struct_0(A_362)) | v5_orders_3(C_364, A_362, B_363) | ~m1_subset_1(C_364, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_362), u1_struct_0(B_363)))) | ~v1_funct_2(C_364, u1_struct_0(A_362), u1_struct_0(B_363)) | ~v1_funct_1(C_364) | ~l1_orders_2(B_363) | ~l1_orders_2(A_362))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.64/2.56  tff(c_440, plain, (![B_363, C_364]: (m1_subset_1('#skF_2'('#skF_7', B_363, C_364), u1_struct_0('#skF_7')) | v5_orders_3(C_364, '#skF_7', B_363) | ~m1_subset_1(C_364, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_363)))) | ~v1_funct_2(C_364, u1_struct_0('#skF_7'), u1_struct_0(B_363)) | ~v1_funct_1(C_364) | ~l1_orders_2(B_363) | ~l1_orders_2('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_238, c_436])).
% 7.64/2.56  tff(c_536, plain, (![B_376, C_377]: (m1_subset_1('#skF_2'('#skF_7', B_376, C_377), u1_struct_0('#skF_5')) | v5_orders_3(C_377, '#skF_7', B_376) | ~m1_subset_1(C_377, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_376)))) | ~v1_funct_2(C_377, u1_struct_0('#skF_5'), u1_struct_0(B_376)) | ~v1_funct_1(C_377) | ~l1_orders_2(B_376))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_238, c_238, c_440])).
% 7.64/2.56  tff(c_545, plain, (m1_subset_1('#skF_2'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | v5_orders_3('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_133, c_536])).
% 7.64/2.56  tff(c_560, plain, (m1_subset_1('#skF_2'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | v5_orders_3('#skF_9', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_134, c_545])).
% 7.64/2.56  tff(c_561, plain, (m1_subset_1('#skF_2'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_67, c_560])).
% 7.64/2.56  tff(c_2000, plain, (![A_507, B_508, C_509]: (r1_orders_2(A_507, '#skF_1'(A_507, B_508, C_509), '#skF_2'(A_507, B_508, C_509)) | v5_orders_3(C_509, A_507, B_508) | ~m1_subset_1(C_509, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_507), u1_struct_0(B_508)))) | ~v1_funct_2(C_509, u1_struct_0(A_507), u1_struct_0(B_508)) | ~v1_funct_1(C_509) | ~l1_orders_2(B_508) | ~l1_orders_2(A_507))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.64/2.56  tff(c_2004, plain, (![B_508, C_509]: (r1_orders_2('#skF_7', '#skF_1'('#skF_7', B_508, C_509), '#skF_2'('#skF_7', B_508, C_509)) | v5_orders_3(C_509, '#skF_7', B_508) | ~m1_subset_1(C_509, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_508)))) | ~v1_funct_2(C_509, u1_struct_0('#skF_7'), u1_struct_0(B_508)) | ~v1_funct_1(C_509) | ~l1_orders_2(B_508) | ~l1_orders_2('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_238, c_2000])).
% 7.64/2.56  tff(c_3588, plain, (![B_660, C_661]: (r1_orders_2('#skF_7', '#skF_1'('#skF_7', B_660, C_661), '#skF_2'('#skF_7', B_660, C_661)) | v5_orders_3(C_661, '#skF_7', B_660) | ~m1_subset_1(C_661, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_660)))) | ~v1_funct_2(C_661, u1_struct_0('#skF_5'), u1_struct_0(B_660)) | ~v1_funct_1(C_661) | ~l1_orders_2(B_660))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_238, c_2004])).
% 7.64/2.56  tff(c_3594, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_2'('#skF_7', '#skF_8', '#skF_9')) | v5_orders_3('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_133, c_3588])).
% 7.64/2.56  tff(c_3607, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_2'('#skF_7', '#skF_8', '#skF_9')) | v5_orders_3('#skF_9', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_134, c_3594])).
% 7.64/2.56  tff(c_3608, plain, (r1_orders_2('#skF_7', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_2'('#skF_7', '#skF_8', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_67, c_3607])).
% 7.64/2.56  tff(c_257, plain, (m1_subset_1(u1_orders_2('#skF_7'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_7')))) | ~l1_orders_2('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_238, c_6])).
% 7.64/2.56  tff(c_264, plain, (m1_subset_1(u1_orders_2('#skF_7'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_238, c_257])).
% 7.64/2.56  tff(c_249, plain, (g1_orders_2(u1_struct_0('#skF_5'), u1_orders_2('#skF_7'))=g1_orders_2(u1_struct_0('#skF_5'), u1_orders_2('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_238, c_38])).
% 7.64/2.56  tff(c_8, plain, (![D_14, B_10, C_13, A_9]: (D_14=B_10 | g1_orders_2(C_13, D_14)!=g1_orders_2(A_9, B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(k2_zfmisc_1(A_9, A_9))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.64/2.56  tff(c_279, plain, (![D_14, C_13]: (u1_orders_2('#skF_7')=D_14 | g1_orders_2(u1_struct_0('#skF_5'), u1_orders_2('#skF_5'))!=g1_orders_2(C_13, D_14) | ~m1_subset_1(u1_orders_2('#skF_7'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_5')))))), inference(superposition, [status(thm), theory('equality')], [c_249, c_8])).
% 7.64/2.56  tff(c_287, plain, (![D_14, C_13]: (u1_orders_2('#skF_7')=D_14 | g1_orders_2(u1_struct_0('#skF_5'), u1_orders_2('#skF_5'))!=g1_orders_2(C_13, D_14))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_279])).
% 7.64/2.56  tff(c_328, plain, (u1_orders_2('#skF_7')=u1_orders_2('#skF_5')), inference(reflexivity, [status(thm), theory('equality')], [c_287])).
% 7.64/2.56  tff(c_4, plain, (![B_5, C_7, A_1]: (r2_hidden(k4_tarski(B_5, C_7), u1_orders_2(A_1)) | ~r1_orders_2(A_1, B_5, C_7) | ~m1_subset_1(C_7, u1_struct_0(A_1)) | ~m1_subset_1(B_5, u1_struct_0(A_1)) | ~l1_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.64/2.56  tff(c_344, plain, (![B_5, C_7]: (r2_hidden(k4_tarski(B_5, C_7), u1_orders_2('#skF_5')) | ~r1_orders_2('#skF_7', B_5, C_7) | ~m1_subset_1(C_7, u1_struct_0('#skF_7')) | ~m1_subset_1(B_5, u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_328, c_4])).
% 7.64/2.56  tff(c_480, plain, (![B_369, C_370]: (r2_hidden(k4_tarski(B_369, C_370), u1_orders_2('#skF_5')) | ~r1_orders_2('#skF_7', B_369, C_370) | ~m1_subset_1(C_370, u1_struct_0('#skF_5')) | ~m1_subset_1(B_369, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_238, c_238, c_344])).
% 7.64/2.56  tff(c_2, plain, (![A_1, B_5, C_7]: (r1_orders_2(A_1, B_5, C_7) | ~r2_hidden(k4_tarski(B_5, C_7), u1_orders_2(A_1)) | ~m1_subset_1(C_7, u1_struct_0(A_1)) | ~m1_subset_1(B_5, u1_struct_0(A_1)) | ~l1_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.64/2.56  tff(c_486, plain, (![B_369, C_370]: (r1_orders_2('#skF_5', B_369, C_370) | ~l1_orders_2('#skF_5') | ~r1_orders_2('#skF_7', B_369, C_370) | ~m1_subset_1(C_370, u1_struct_0('#skF_5')) | ~m1_subset_1(B_369, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_480, c_2])).
% 7.64/2.56  tff(c_490, plain, (![B_369, C_370]: (r1_orders_2('#skF_5', B_369, C_370) | ~r1_orders_2('#skF_7', B_369, C_370) | ~m1_subset_1(C_370, u1_struct_0('#skF_5')) | ~m1_subset_1(B_369, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_486])).
% 7.64/2.56  tff(c_3637, plain, (r1_orders_2('#skF_5', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_2'('#skF_7', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_2'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_3608, c_490])).
% 7.64/2.56  tff(c_3643, plain, (r1_orders_2('#skF_5', '#skF_1'('#skF_7', '#skF_8', '#skF_9'), '#skF_2'('#skF_7', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_2578, c_561, c_3637])).
% 7.64/2.56  tff(c_12, plain, (![A_15, D_232, C_201, E_240, B_139]: (r1_orders_2(B_139, k1_funct_1(C_201, D_232), k1_funct_1(C_201, E_240)) | ~m1_subset_1(k1_funct_1(C_201, E_240), u1_struct_0(B_139)) | ~m1_subset_1(k1_funct_1(C_201, D_232), u1_struct_0(B_139)) | ~r1_orders_2(A_15, D_232, E_240) | ~m1_subset_1(E_240, u1_struct_0(A_15)) | ~m1_subset_1(D_232, u1_struct_0(A_15)) | ~v5_orders_3(C_201, A_15, B_139) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_15), u1_struct_0(B_139)))) | ~v1_funct_2(C_201, u1_struct_0(A_15), u1_struct_0(B_139)) | ~v1_funct_1(C_201) | ~l1_orders_2(B_139) | ~l1_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.64/2.56  tff(c_3645, plain, (![B_139, C_201]: (r1_orders_2(B_139, k1_funct_1(C_201, '#skF_1'('#skF_7', '#skF_8', '#skF_9')), k1_funct_1(C_201, '#skF_2'('#skF_7', '#skF_8', '#skF_9'))) | ~m1_subset_1(k1_funct_1(C_201, '#skF_2'('#skF_7', '#skF_8', '#skF_9')), u1_struct_0(B_139)) | ~m1_subset_1(k1_funct_1(C_201, '#skF_1'('#skF_7', '#skF_8', '#skF_9')), u1_struct_0(B_139)) | ~m1_subset_1('#skF_2'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | ~v5_orders_3(C_201, '#skF_5', B_139) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_139)))) | ~v1_funct_2(C_201, u1_struct_0('#skF_5'), u1_struct_0(B_139)) | ~v1_funct_1(C_201) | ~l1_orders_2(B_139) | ~l1_orders_2('#skF_5'))), inference(resolution, [status(thm)], [c_3643, c_12])).
% 7.64/2.56  tff(c_3894, plain, (![B_681, C_682]: (r1_orders_2(B_681, k1_funct_1(C_682, '#skF_1'('#skF_7', '#skF_8', '#skF_9')), k1_funct_1(C_682, '#skF_2'('#skF_7', '#skF_8', '#skF_9'))) | ~m1_subset_1(k1_funct_1(C_682, '#skF_2'('#skF_7', '#skF_8', '#skF_9')), u1_struct_0(B_681)) | ~m1_subset_1(k1_funct_1(C_682, '#skF_1'('#skF_7', '#skF_8', '#skF_9')), u1_struct_0(B_681)) | ~v5_orders_3(C_682, '#skF_5', B_681) | ~m1_subset_1(C_682, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_681)))) | ~v1_funct_2(C_682, u1_struct_0('#skF_5'), u1_struct_0(B_681)) | ~v1_funct_1(C_682) | ~l1_orders_2(B_681))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2578, c_561, c_3645])).
% 7.64/2.56  tff(c_3905, plain, (![B_681]: (r1_orders_2(B_681, k1_funct_1('#skF_9', '#skF_1'('#skF_7', '#skF_8', '#skF_9')), '#skF_4'('#skF_7', '#skF_8', '#skF_9')) | ~m1_subset_1(k1_funct_1('#skF_9', '#skF_2'('#skF_7', '#skF_8', '#skF_9')), u1_struct_0(B_681)) | ~m1_subset_1(k1_funct_1('#skF_9', '#skF_1'('#skF_7', '#skF_8', '#skF_9')), u1_struct_0(B_681)) | ~v5_orders_3('#skF_9', '#skF_5', B_681) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_681)))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0(B_681)) | ~v1_funct_1('#skF_9') | ~l1_orders_2(B_681))), inference(superposition, [status(thm), theory('equality')], [c_3568, c_3894])).
% 7.64/2.56  tff(c_3920, plain, (![B_683]: (r1_orders_2(B_683, '#skF_3'('#skF_7', '#skF_8', '#skF_9'), '#skF_4'('#skF_7', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_4'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0(B_683)) | ~m1_subset_1('#skF_3'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0(B_683)) | ~v5_orders_3('#skF_9', '#skF_5', B_683) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_683)))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0(B_683)) | ~l1_orders_2(B_683))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_3144, c_3568, c_3144, c_3905])).
% 7.64/2.56  tff(c_3926, plain, (r1_orders_2('#skF_8', '#skF_3'('#skF_7', '#skF_8', '#skF_9'), '#skF_4'('#skF_7', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_4'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_3'('#skF_7', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | ~v5_orders_3('#skF_9', '#skF_5', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_133, c_3920])).
% 7.64/2.56  tff(c_3934, plain, (r1_orders_2('#skF_8', '#skF_3'('#skF_7', '#skF_8', '#skF_9'), '#skF_4'('#skF_7', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_134, c_369, c_3029, c_2964, c_3926])).
% 7.64/2.56  tff(c_14, plain, (![B_139, A_15, C_201]: (~r1_orders_2(B_139, '#skF_3'(A_15, B_139, C_201), '#skF_4'(A_15, B_139, C_201)) | v5_orders_3(C_201, A_15, B_139) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_15), u1_struct_0(B_139)))) | ~v1_funct_2(C_201, u1_struct_0(A_15), u1_struct_0(B_139)) | ~v1_funct_1(C_201) | ~l1_orders_2(B_139) | ~l1_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.64/2.56  tff(c_3986, plain, (v5_orders_3('#skF_9', '#skF_7', '#skF_8') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_8')))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_7'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8') | ~l1_orders_2('#skF_7')), inference(resolution, [status(thm)], [c_3934, c_14])).
% 7.64/2.56  tff(c_3992, plain, (v5_orders_3('#skF_9', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_50, c_134, c_238, c_133, c_238, c_3986])).
% 7.64/2.56  tff(c_3994, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_3992])).
% 7.64/2.56  tff(c_3996, plain, (~v5_orders_3('#skF_9', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_320])).
% 7.64/2.56  tff(c_4013, plain, (![A_692, B_693, C_694]: (m1_subset_1('#skF_3'(A_692, B_693, C_694), u1_struct_0(B_693)) | v5_orders_3(C_694, A_692, B_693) | ~m1_subset_1(C_694, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_692), u1_struct_0(B_693)))) | ~v1_funct_2(C_694, u1_struct_0(A_692), u1_struct_0(B_693)) | ~v1_funct_1(C_694) | ~l1_orders_2(B_693) | ~l1_orders_2(A_692))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.64/2.56  tff(c_4023, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | v5_orders_3('#skF_9', '#skF_5', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8') | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_133, c_4013])).
% 7.64/2.56  tff(c_4042, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | v5_orders_3('#skF_9', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_50, c_134, c_4023])).
% 7.64/2.56  tff(c_4043, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_3996, c_4042])).
% 7.64/2.56  tff(c_3995, plain, (m1_subset_1('#skF_4'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_8'))), inference(splitRight, [status(thm)], [c_320])).
% 7.64/2.56  tff(c_60, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.64/2.56  tff(c_32, plain, (v5_orders_3('#skF_9', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.64/2.56  tff(c_4614, plain, (![C_753, A_754, B_755]: (k1_funct_1(C_753, '#skF_1'(A_754, B_755, C_753))='#skF_3'(A_754, B_755, C_753) | v5_orders_3(C_753, A_754, B_755) | ~m1_subset_1(C_753, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_754), u1_struct_0(B_755)))) | ~v1_funct_2(C_753, u1_struct_0(A_754), u1_struct_0(B_755)) | ~v1_funct_1(C_753) | ~l1_orders_2(B_755) | ~l1_orders_2(A_754))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.64/2.56  tff(c_4624, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_5', '#skF_8', '#skF_9'))='#skF_3'('#skF_5', '#skF_8', '#skF_9') | v5_orders_3('#skF_9', '#skF_5', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8') | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_133, c_4614])).
% 7.64/2.56  tff(c_4643, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_5', '#skF_8', '#skF_9'))='#skF_3'('#skF_5', '#skF_8', '#skF_9') | v5_orders_3('#skF_9', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_50, c_134, c_4624])).
% 7.64/2.56  tff(c_4644, plain, (k1_funct_1('#skF_9', '#skF_1'('#skF_5', '#skF_8', '#skF_9'))='#skF_3'('#skF_5', '#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_3996, c_4643])).
% 7.64/2.56  tff(c_4242, plain, (![C_722, A_723, B_724]: (k1_funct_1(C_722, '#skF_2'(A_723, B_724, C_722))='#skF_4'(A_723, B_724, C_722) | v5_orders_3(C_722, A_723, B_724) | ~m1_subset_1(C_722, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_723), u1_struct_0(B_724)))) | ~v1_funct_2(C_722, u1_struct_0(A_723), u1_struct_0(B_724)) | ~v1_funct_1(C_722) | ~l1_orders_2(B_724) | ~l1_orders_2(A_723))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.64/2.56  tff(c_4252, plain, (k1_funct_1('#skF_9', '#skF_2'('#skF_5', '#skF_8', '#skF_9'))='#skF_4'('#skF_5', '#skF_8', '#skF_9') | v5_orders_3('#skF_9', '#skF_5', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8') | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_133, c_4242])).
% 7.64/2.56  tff(c_4271, plain, (k1_funct_1('#skF_9', '#skF_2'('#skF_5', '#skF_8', '#skF_9'))='#skF_4'('#skF_5', '#skF_8', '#skF_9') | v5_orders_3('#skF_9', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_50, c_134, c_4252])).
% 7.64/2.56  tff(c_4272, plain, (k1_funct_1('#skF_9', '#skF_2'('#skF_5', '#skF_8', '#skF_9'))='#skF_4'('#skF_5', '#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_3996, c_4271])).
% 7.64/2.56  tff(c_4156, plain, (![A_715, B_716, C_717]: (m1_subset_1('#skF_1'(A_715, B_716, C_717), u1_struct_0(A_715)) | v5_orders_3(C_717, A_715, B_716) | ~m1_subset_1(C_717, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_715), u1_struct_0(B_716)))) | ~v1_funct_2(C_717, u1_struct_0(A_715), u1_struct_0(B_716)) | ~v1_funct_1(C_717) | ~l1_orders_2(B_716) | ~l1_orders_2(A_715))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.64/2.56  tff(c_4166, plain, (m1_subset_1('#skF_1'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | v5_orders_3('#skF_9', '#skF_5', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8') | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_133, c_4156])).
% 7.64/2.56  tff(c_4185, plain, (m1_subset_1('#skF_1'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | v5_orders_3('#skF_9', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_50, c_134, c_4166])).
% 7.64/2.56  tff(c_4186, plain, (m1_subset_1('#skF_1'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_3996, c_4185])).
% 7.64/2.56  tff(c_4091, plain, (![A_709, B_710, C_711]: (m1_subset_1('#skF_2'(A_709, B_710, C_711), u1_struct_0(A_709)) | v5_orders_3(C_711, A_709, B_710) | ~m1_subset_1(C_711, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_709), u1_struct_0(B_710)))) | ~v1_funct_2(C_711, u1_struct_0(A_709), u1_struct_0(B_710)) | ~v1_funct_1(C_711) | ~l1_orders_2(B_710) | ~l1_orders_2(A_709))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.64/2.56  tff(c_4101, plain, (m1_subset_1('#skF_2'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | v5_orders_3('#skF_9', '#skF_5', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8') | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_133, c_4091])).
% 7.64/2.56  tff(c_4120, plain, (m1_subset_1('#skF_2'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | v5_orders_3('#skF_9', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_50, c_134, c_4101])).
% 7.64/2.56  tff(c_4121, plain, (m1_subset_1('#skF_2'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_3996, c_4120])).
% 7.64/2.56  tff(c_4315, plain, (![A_727, B_728, C_729]: (r1_orders_2(A_727, '#skF_1'(A_727, B_728, C_729), '#skF_2'(A_727, B_728, C_729)) | v5_orders_3(C_729, A_727, B_728) | ~m1_subset_1(C_729, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_727), u1_struct_0(B_728)))) | ~v1_funct_2(C_729, u1_struct_0(A_727), u1_struct_0(B_728)) | ~v1_funct_1(C_729) | ~l1_orders_2(B_728) | ~l1_orders_2(A_727))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.64/2.56  tff(c_4325, plain, (r1_orders_2('#skF_5', '#skF_1'('#skF_5', '#skF_8', '#skF_9'), '#skF_2'('#skF_5', '#skF_8', '#skF_9')) | v5_orders_3('#skF_9', '#skF_5', '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8') | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_133, c_4315])).
% 7.64/2.56  tff(c_4344, plain, (r1_orders_2('#skF_5', '#skF_1'('#skF_5', '#skF_8', '#skF_9'), '#skF_2'('#skF_5', '#skF_8', '#skF_9')) | v5_orders_3('#skF_9', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_50, c_134, c_4325])).
% 7.64/2.56  tff(c_4345, plain, (r1_orders_2('#skF_5', '#skF_1'('#skF_5', '#skF_8', '#skF_9'), '#skF_2'('#skF_5', '#skF_8', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_3996, c_4344])).
% 7.64/2.56  tff(c_4798, plain, (![B_772, E_768, C_771, D_769, A_770]: (r1_orders_2(B_772, k1_funct_1(C_771, D_769), k1_funct_1(C_771, E_768)) | ~m1_subset_1(k1_funct_1(C_771, E_768), u1_struct_0(B_772)) | ~m1_subset_1(k1_funct_1(C_771, D_769), u1_struct_0(B_772)) | ~r1_orders_2(A_770, D_769, E_768) | ~m1_subset_1(E_768, u1_struct_0(A_770)) | ~m1_subset_1(D_769, u1_struct_0(A_770)) | ~v5_orders_3(C_771, A_770, B_772) | ~m1_subset_1(C_771, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_770), u1_struct_0(B_772)))) | ~v1_funct_2(C_771, u1_struct_0(A_770), u1_struct_0(B_772)) | ~v1_funct_1(C_771) | ~l1_orders_2(B_772) | ~l1_orders_2(A_770))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.64/2.56  tff(c_4804, plain, (![B_772, C_771]: (r1_orders_2(B_772, k1_funct_1(C_771, '#skF_1'('#skF_5', '#skF_8', '#skF_9')), k1_funct_1(C_771, '#skF_2'('#skF_5', '#skF_8', '#skF_9'))) | ~m1_subset_1(k1_funct_1(C_771, '#skF_2'('#skF_5', '#skF_8', '#skF_9')), u1_struct_0(B_772)) | ~m1_subset_1(k1_funct_1(C_771, '#skF_1'('#skF_5', '#skF_8', '#skF_9')), u1_struct_0(B_772)) | ~m1_subset_1('#skF_2'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_1'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_5')) | ~v5_orders_3(C_771, '#skF_5', B_772) | ~m1_subset_1(C_771, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_772)))) | ~v1_funct_2(C_771, u1_struct_0('#skF_5'), u1_struct_0(B_772)) | ~v1_funct_1(C_771) | ~l1_orders_2(B_772) | ~l1_orders_2('#skF_5'))), inference(resolution, [status(thm)], [c_4345, c_4798])).
% 7.64/2.56  tff(c_5654, plain, (![B_851, C_852]: (r1_orders_2(B_851, k1_funct_1(C_852, '#skF_1'('#skF_5', '#skF_8', '#skF_9')), k1_funct_1(C_852, '#skF_2'('#skF_5', '#skF_8', '#skF_9'))) | ~m1_subset_1(k1_funct_1(C_852, '#skF_2'('#skF_5', '#skF_8', '#skF_9')), u1_struct_0(B_851)) | ~m1_subset_1(k1_funct_1(C_852, '#skF_1'('#skF_5', '#skF_8', '#skF_9')), u1_struct_0(B_851)) | ~v5_orders_3(C_852, '#skF_5', B_851) | ~m1_subset_1(C_852, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_851)))) | ~v1_funct_2(C_852, u1_struct_0('#skF_5'), u1_struct_0(B_851)) | ~v1_funct_1(C_852) | ~l1_orders_2(B_851))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4186, c_4121, c_4804])).
% 7.64/2.56  tff(c_5665, plain, (![B_851]: (r1_orders_2(B_851, '#skF_3'('#skF_5', '#skF_8', '#skF_9'), k1_funct_1('#skF_9', '#skF_2'('#skF_5', '#skF_8', '#skF_9'))) | ~m1_subset_1(k1_funct_1('#skF_9', '#skF_2'('#skF_5', '#skF_8', '#skF_9')), u1_struct_0(B_851)) | ~m1_subset_1(k1_funct_1('#skF_9', '#skF_1'('#skF_5', '#skF_8', '#skF_9')), u1_struct_0(B_851)) | ~v5_orders_3('#skF_9', '#skF_5', B_851) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_851)))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0(B_851)) | ~v1_funct_1('#skF_9') | ~l1_orders_2(B_851))), inference(superposition, [status(thm), theory('equality')], [c_4644, c_5654])).
% 7.64/2.56  tff(c_5680, plain, (![B_853]: (r1_orders_2(B_853, '#skF_3'('#skF_5', '#skF_8', '#skF_9'), '#skF_4'('#skF_5', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0(B_853)) | ~m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0(B_853)) | ~v5_orders_3('#skF_9', '#skF_5', B_853) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_853)))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0(B_853)) | ~l1_orders_2(B_853))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_4644, c_4272, c_4272, c_5665])).
% 7.64/2.56  tff(c_5689, plain, (r1_orders_2('#skF_6', '#skF_3'('#skF_5', '#skF_8', '#skF_9'), '#skF_4'('#skF_5', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_6')) | ~v5_orders_3('#skF_9', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_8')))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_116, c_5680])).
% 7.64/2.56  tff(c_5696, plain, (r1_orders_2('#skF_6', '#skF_3'('#skF_5', '#skF_8', '#skF_9'), '#skF_4'('#skF_5', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_134, c_116, c_133, c_32, c_4043, c_116, c_3995, c_116, c_5689])).
% 7.64/2.56  tff(c_138, plain, (m1_subset_1(u1_orders_2('#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_6')))) | ~l1_orders_2('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_116, c_6])).
% 7.64/2.56  tff(c_145, plain, (m1_subset_1(u1_orders_2('#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_8'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_116, c_138])).
% 7.64/2.56  tff(c_132, plain, (g1_orders_2(u1_struct_0('#skF_8'), u1_orders_2('#skF_6'))=g1_orders_2(u1_struct_0('#skF_8'), u1_orders_2('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_36])).
% 7.64/2.56  tff(c_155, plain, (![D_14, C_13]: (u1_orders_2('#skF_6')=D_14 | g1_orders_2(u1_struct_0('#skF_8'), u1_orders_2('#skF_8'))!=g1_orders_2(C_13, D_14) | ~m1_subset_1(u1_orders_2('#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_8')))))), inference(superposition, [status(thm), theory('equality')], [c_132, c_8])).
% 7.64/2.56  tff(c_163, plain, (![D_14, C_13]: (u1_orders_2('#skF_6')=D_14 | g1_orders_2(u1_struct_0('#skF_8'), u1_orders_2('#skF_8'))!=g1_orders_2(C_13, D_14))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_155])).
% 7.64/2.56  tff(c_169, plain, (u1_orders_2('#skF_6')=u1_orders_2('#skF_8')), inference(reflexivity, [status(thm), theory('equality')], [c_163])).
% 7.64/2.56  tff(c_186, plain, (![B_5, C_7]: (r2_hidden(k4_tarski(B_5, C_7), u1_orders_2('#skF_8')) | ~r1_orders_2('#skF_6', B_5, C_7) | ~m1_subset_1(C_7, u1_struct_0('#skF_6')) | ~m1_subset_1(B_5, u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_169, c_4])).
% 7.64/2.56  tff(c_4079, plain, (![B_705, C_706]: (r2_hidden(k4_tarski(B_705, C_706), u1_orders_2('#skF_8')) | ~r1_orders_2('#skF_6', B_705, C_706) | ~m1_subset_1(C_706, u1_struct_0('#skF_8')) | ~m1_subset_1(B_705, u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_116, c_116, c_186])).
% 7.64/2.56  tff(c_4085, plain, (![B_705, C_706]: (r1_orders_2('#skF_8', B_705, C_706) | ~l1_orders_2('#skF_8') | ~r1_orders_2('#skF_6', B_705, C_706) | ~m1_subset_1(C_706, u1_struct_0('#skF_8')) | ~m1_subset_1(B_705, u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_4079, c_2])).
% 7.64/2.56  tff(c_4089, plain, (![B_705, C_706]: (r1_orders_2('#skF_8', B_705, C_706) | ~r1_orders_2('#skF_6', B_705, C_706) | ~m1_subset_1(C_706, u1_struct_0('#skF_8')) | ~m1_subset_1(B_705, u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_4085])).
% 7.64/2.56  tff(c_5726, plain, (r1_orders_2('#skF_8', '#skF_3'('#skF_5', '#skF_8', '#skF_9'), '#skF_4'('#skF_5', '#skF_8', '#skF_9')) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_9'), u1_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_5696, c_4089])).
% 7.64/2.56  tff(c_5732, plain, (r1_orders_2('#skF_8', '#skF_3'('#skF_5', '#skF_8', '#skF_9'), '#skF_4'('#skF_5', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_4043, c_3995, c_5726])).
% 7.64/2.56  tff(c_5736, plain, (v5_orders_3('#skF_9', '#skF_5', '#skF_8') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_8')))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_5'), u1_struct_0('#skF_8')) | ~v1_funct_1('#skF_9') | ~l1_orders_2('#skF_8') | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_5732, c_14])).
% 7.64/2.56  tff(c_5742, plain, (v5_orders_3('#skF_9', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_50, c_134, c_133, c_5736])).
% 7.64/2.56  tff(c_5744, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3996, c_5742])).
% 7.64/2.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.64/2.56  
% 7.64/2.56  Inference rules
% 7.64/2.56  ----------------------
% 7.64/2.56  #Ref     : 11
% 7.64/2.56  #Sup     : 1117
% 7.64/2.56  #Fact    : 0
% 7.64/2.56  #Define  : 0
% 7.64/2.56  #Split   : 10
% 7.64/2.56  #Chain   : 0
% 7.64/2.56  #Close   : 0
% 7.64/2.57  
% 7.64/2.57  Ordering : KBO
% 7.64/2.57  
% 7.64/2.57  Simplification rules
% 7.64/2.57  ----------------------
% 7.64/2.57  #Subsume      : 605
% 7.64/2.57  #Demod        : 3419
% 7.64/2.57  #Tautology    : 129
% 7.64/2.57  #SimpNegUnit  : 43
% 7.64/2.57  #BackRed      : 14
% 7.64/2.57  
% 7.64/2.57  #Partial instantiations: 0
% 7.64/2.57  #Strategies tried      : 1
% 7.64/2.57  
% 7.64/2.57  Timing (in seconds)
% 7.64/2.57  ----------------------
% 7.64/2.57  Preprocessing        : 0.33
% 7.64/2.57  Parsing              : 0.16
% 7.64/2.57  CNF conversion       : 0.04
% 7.64/2.57  Main loop            : 1.52
% 7.64/2.57  Inferencing          : 0.48
% 7.64/2.57  Reduction            : 0.64
% 7.64/2.57  Demodulation         : 0.47
% 7.64/2.57  BG Simplification    : 0.04
% 7.64/2.57  Subsumption          : 0.28
% 7.64/2.57  Abstraction          : 0.07
% 7.64/2.57  MUC search           : 0.00
% 7.64/2.57  Cooper               : 0.00
% 7.64/2.57  Total                : 1.90
% 7.64/2.57  Index Insertion      : 0.00
% 7.64/2.57  Index Deletion       : 0.00
% 7.64/2.57  Index Matching       : 0.00
% 7.64/2.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
