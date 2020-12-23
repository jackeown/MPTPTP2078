%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:55 EST 2020

% Result     : Theorem 5.69s
% Output     : CNFRefutation 5.69s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 800 expanded)
%              Number of leaves         :   28 ( 271 expanded)
%              Depth                    :   21
%              Number of atoms          :  562 (3009 expanded)
%              Number of equality atoms :   67 ( 792 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > m1_subset_1 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( l1_orders_2(B)
           => ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(B),u1_orders_2(B))
             => ! [C,D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ( D = E
                       => ( ( r2_lattice3(A,C,D)
                           => r2_lattice3(B,C,E) )
                          & ( r1_lattice3(A,C,D)
                           => r1_lattice3(B,C,E) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow_0)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

tff(c_28,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_42,plain,
    ( r2_lattice3('#skF_3','#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_4','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_49,plain,
    ( r2_lattice3('#skF_3','#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_42])).

tff(c_2559,plain,(
    ~ r1_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_49])).

tff(c_30,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_47,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30])).

tff(c_44,plain,
    ( ~ r2_lattice3('#skF_4','#skF_5','#skF_7')
    | r1_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_48,plain,
    ( ~ r2_lattice3('#skF_4','#skF_5','#skF_6')
    | r1_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_44])).

tff(c_55,plain,(
    ~ r2_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_61,plain,(
    ~ r1_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_49])).

tff(c_46,plain,
    ( r2_lattice3('#skF_3','#skF_5','#skF_6')
    | r1_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_56,plain,(
    r1_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_36,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_18,plain,(
    ! [A_15,B_22,C_23] :
      ( m1_subset_1('#skF_1'(A_15,B_22,C_23),u1_struct_0(A_15))
      | r1_lattice3(A_15,B_22,C_23)
      | ~ m1_subset_1(C_23,u1_struct_0(A_15))
      | ~ l1_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_38,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_6,plain,(
    ! [A_8] :
      ( m1_subset_1(u1_orders_2(A_8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8),u1_struct_0(A_8))))
      | ~ l1_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_34,plain,(
    g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_3')) = g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_67,plain,(
    ! [D_54,B_55,C_56,A_57] :
      ( D_54 = B_55
      | g1_orders_2(C_56,D_54) != g1_orders_2(A_57,B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k2_zfmisc_1(A_57,A_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_84,plain,(
    ! [B_71,A_72] :
      ( u1_orders_2('#skF_3') = B_71
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(A_72,B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k2_zfmisc_1(A_72,A_72))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_67])).

tff(c_88,plain,(
    ! [A_8] :
      ( u1_orders_2(A_8) = u1_orders_2('#skF_3')
      | g1_orders_2(u1_struct_0(A_8),u1_orders_2(A_8)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(A_8) ) ),
    inference(resolution,[status(thm)],[c_6,c_84])).

tff(c_91,plain,
    ( u1_orders_2('#skF_3') = u1_orders_2('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_88])).

tff(c_93,plain,(
    u1_orders_2('#skF_3') = u1_orders_2('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_91])).

tff(c_108,plain,
    ( m1_subset_1(u1_orders_2('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))))
    | ~ l1_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_6])).

tff(c_112,plain,(
    m1_subset_1(u1_orders_2('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_108])).

tff(c_104,plain,(
    g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_4')) = g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_34])).

tff(c_10,plain,(
    ! [C_13,A_9,D_14,B_10] :
      ( C_13 = A_9
      | g1_orders_2(C_13,D_14) != g1_orders_2(A_9,B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(k2_zfmisc_1(A_9,A_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_118,plain,(
    ! [C_13,D_14] :
      ( u1_struct_0('#skF_3') = C_13
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(C_13,D_14)
      | ~ m1_subset_1(u1_orders_2('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_10])).

tff(c_126,plain,(
    ! [C_13,D_14] :
      ( u1_struct_0('#skF_3') = C_13
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(C_13,D_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_118])).

tff(c_132,plain,(
    u1_struct_0('#skF_3') = u1_struct_0('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_126])).

tff(c_16,plain,(
    ! [A_15,B_22,C_23] :
      ( r2_hidden('#skF_1'(A_15,B_22,C_23),B_22)
      | r1_lattice3(A_15,B_22,C_23)
      | ~ m1_subset_1(C_23,u1_struct_0(A_15))
      | ~ l1_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_290,plain,(
    ! [A_112,C_113,D_114,B_115] :
      ( r1_orders_2(A_112,C_113,D_114)
      | ~ r2_hidden(D_114,B_115)
      | ~ m1_subset_1(D_114,u1_struct_0(A_112))
      | ~ r1_lattice3(A_112,B_115,C_113)
      | ~ m1_subset_1(C_113,u1_struct_0(A_112))
      | ~ l1_orders_2(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_537,plain,(
    ! [C_187,B_188,A_190,A_189,C_186] :
      ( r1_orders_2(A_190,C_186,'#skF_1'(A_189,B_188,C_187))
      | ~ m1_subset_1('#skF_1'(A_189,B_188,C_187),u1_struct_0(A_190))
      | ~ r1_lattice3(A_190,B_188,C_186)
      | ~ m1_subset_1(C_186,u1_struct_0(A_190))
      | ~ l1_orders_2(A_190)
      | r1_lattice3(A_189,B_188,C_187)
      | ~ m1_subset_1(C_187,u1_struct_0(A_189))
      | ~ l1_orders_2(A_189) ) ),
    inference(resolution,[status(thm)],[c_16,c_290])).

tff(c_543,plain,(
    ! [C_186,A_189,B_188,C_187] :
      ( r1_orders_2('#skF_3',C_186,'#skF_1'(A_189,B_188,C_187))
      | ~ m1_subset_1('#skF_1'(A_189,B_188,C_187),u1_struct_0('#skF_4'))
      | ~ r1_lattice3('#skF_3',B_188,C_186)
      | ~ m1_subset_1(C_186,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | r1_lattice3(A_189,B_188,C_187)
      | ~ m1_subset_1(C_187,u1_struct_0(A_189))
      | ~ l1_orders_2(A_189) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_537])).

tff(c_586,plain,(
    ! [C_197,A_198,B_199,C_200] :
      ( r1_orders_2('#skF_3',C_197,'#skF_1'(A_198,B_199,C_200))
      | ~ m1_subset_1('#skF_1'(A_198,B_199,C_200),u1_struct_0('#skF_4'))
      | ~ r1_lattice3('#skF_3',B_199,C_197)
      | ~ m1_subset_1(C_197,u1_struct_0('#skF_4'))
      | r1_lattice3(A_198,B_199,C_200)
      | ~ m1_subset_1(C_200,u1_struct_0(A_198))
      | ~ l1_orders_2(A_198) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_132,c_543])).

tff(c_591,plain,(
    ! [C_197,B_22,C_23] :
      ( r1_orders_2('#skF_3',C_197,'#skF_1'('#skF_4',B_22,C_23))
      | ~ r1_lattice3('#skF_3',B_22,C_197)
      | ~ m1_subset_1(C_197,u1_struct_0('#skF_4'))
      | r1_lattice3('#skF_4',B_22,C_23)
      | ~ m1_subset_1(C_23,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_586])).

tff(c_633,plain,(
    ! [C_221,B_222,C_223] :
      ( r1_orders_2('#skF_3',C_221,'#skF_1'('#skF_4',B_222,C_223))
      | ~ r1_lattice3('#skF_3',B_222,C_221)
      | ~ m1_subset_1(C_221,u1_struct_0('#skF_4'))
      | r1_lattice3('#skF_4',B_222,C_223)
      | ~ m1_subset_1(C_223,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_591])).

tff(c_189,plain,(
    ! [B_93,C_94,A_95] :
      ( r2_hidden(k4_tarski(B_93,C_94),u1_orders_2(A_95))
      | ~ r1_orders_2(A_95,B_93,C_94)
      | ~ m1_subset_1(C_94,u1_struct_0(A_95))
      | ~ m1_subset_1(B_93,u1_struct_0(A_95))
      | ~ l1_orders_2(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_192,plain,(
    ! [B_93,C_94] :
      ( r2_hidden(k4_tarski(B_93,C_94),u1_orders_2('#skF_4'))
      | ~ r1_orders_2('#skF_3',B_93,C_94)
      | ~ m1_subset_1(C_94,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_93,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_189])).

tff(c_194,plain,(
    ! [B_93,C_94] :
      ( r2_hidden(k4_tarski(B_93,C_94),u1_orders_2('#skF_4'))
      | ~ r1_orders_2('#skF_3',B_93,C_94)
      | ~ m1_subset_1(C_94,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_93,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_132,c_132,c_192])).

tff(c_196,plain,(
    ! [A_98,B_99,C_100] :
      ( r1_orders_2(A_98,B_99,C_100)
      | ~ r2_hidden(k4_tarski(B_99,C_100),u1_orders_2(A_98))
      | ~ m1_subset_1(C_100,u1_struct_0(A_98))
      | ~ m1_subset_1(B_99,u1_struct_0(A_98))
      | ~ l1_orders_2(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_199,plain,(
    ! [B_93,C_94] :
      ( r1_orders_2('#skF_4',B_93,C_94)
      | ~ l1_orders_2('#skF_4')
      | ~ r1_orders_2('#skF_3',B_93,C_94)
      | ~ m1_subset_1(C_94,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_93,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_194,c_196])).

tff(c_208,plain,(
    ! [B_93,C_94] :
      ( r1_orders_2('#skF_4',B_93,C_94)
      | ~ r1_orders_2('#skF_3',B_93,C_94)
      | ~ m1_subset_1(C_94,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_93,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_199])).

tff(c_845,plain,(
    ! [C_291,B_292,C_293] :
      ( r1_orders_2('#skF_4',C_291,'#skF_1'('#skF_4',B_292,C_293))
      | ~ m1_subset_1('#skF_1'('#skF_4',B_292,C_293),u1_struct_0('#skF_4'))
      | ~ r1_lattice3('#skF_3',B_292,C_291)
      | ~ m1_subset_1(C_291,u1_struct_0('#skF_4'))
      | r1_lattice3('#skF_4',B_292,C_293)
      | ~ m1_subset_1(C_293,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_633,c_208])).

tff(c_848,plain,(
    ! [C_291,B_22,C_23] :
      ( r1_orders_2('#skF_4',C_291,'#skF_1'('#skF_4',B_22,C_23))
      | ~ r1_lattice3('#skF_3',B_22,C_291)
      | ~ m1_subset_1(C_291,u1_struct_0('#skF_4'))
      | r1_lattice3('#skF_4',B_22,C_23)
      | ~ m1_subset_1(C_23,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_845])).

tff(c_852,plain,(
    ! [C_294,B_295,C_296] :
      ( r1_orders_2('#skF_4',C_294,'#skF_1'('#skF_4',B_295,C_296))
      | ~ r1_lattice3('#skF_3',B_295,C_294)
      | ~ m1_subset_1(C_294,u1_struct_0('#skF_4'))
      | r1_lattice3('#skF_4',B_295,C_296)
      | ~ m1_subset_1(C_296,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_848])).

tff(c_14,plain,(
    ! [A_15,C_23,B_22] :
      ( ~ r1_orders_2(A_15,C_23,'#skF_1'(A_15,B_22,C_23))
      | r1_lattice3(A_15,B_22,C_23)
      | ~ m1_subset_1(C_23,u1_struct_0(A_15))
      | ~ l1_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_860,plain,(
    ! [B_295,C_296] :
      ( ~ l1_orders_2('#skF_4')
      | ~ r1_lattice3('#skF_3',B_295,C_296)
      | r1_lattice3('#skF_4',B_295,C_296)
      | ~ m1_subset_1(C_296,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_852,c_14])).

tff(c_867,plain,(
    ! [B_297,C_298] :
      ( ~ r1_lattice3('#skF_3',B_297,C_298)
      | r1_lattice3('#skF_4',B_297,C_298)
      | ~ m1_subset_1(C_298,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_860])).

tff(c_879,plain,
    ( r1_lattice3('#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_867])).

tff(c_889,plain,(
    r1_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_879])).

tff(c_891,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_889])).

tff(c_892,plain,(
    r2_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_26,plain,(
    ! [A_27,B_34,C_35] :
      ( m1_subset_1('#skF_2'(A_27,B_34,C_35),u1_struct_0(A_27))
      | r2_lattice3(A_27,B_34,C_35)
      | ~ m1_subset_1(C_35,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_908,plain,(
    ! [D_304,B_305,C_306,A_307] :
      ( D_304 = B_305
      | g1_orders_2(C_306,D_304) != g1_orders_2(A_307,B_305)
      | ~ m1_subset_1(B_305,k1_zfmisc_1(k2_zfmisc_1(A_307,A_307))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_914,plain,(
    ! [B_311,A_312] :
      ( u1_orders_2('#skF_3') = B_311
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(A_312,B_311)
      | ~ m1_subset_1(B_311,k1_zfmisc_1(k2_zfmisc_1(A_312,A_312))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_908])).

tff(c_918,plain,(
    ! [A_8] :
      ( u1_orders_2(A_8) = u1_orders_2('#skF_3')
      | g1_orders_2(u1_struct_0(A_8),u1_orders_2(A_8)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(A_8) ) ),
    inference(resolution,[status(thm)],[c_6,c_914])).

tff(c_922,plain,
    ( u1_orders_2('#skF_3') = u1_orders_2('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_918])).

tff(c_924,plain,(
    u1_orders_2('#skF_3') = u1_orders_2('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_922])).

tff(c_939,plain,
    ( m1_subset_1(u1_orders_2('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))))
    | ~ l1_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_924,c_6])).

tff(c_943,plain,(
    m1_subset_1(u1_orders_2('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_939])).

tff(c_935,plain,(
    g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_4')) = g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_924,c_34])).

tff(c_953,plain,(
    ! [C_13,D_14] :
      ( u1_struct_0('#skF_3') = C_13
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(C_13,D_14)
      | ~ m1_subset_1(u1_orders_2('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_935,c_10])).

tff(c_959,plain,(
    ! [C_13,D_14] :
      ( u1_struct_0('#skF_3') = C_13
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(C_13,D_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_943,c_953])).

tff(c_973,plain,(
    u1_struct_0('#skF_3') = u1_struct_0('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_959])).

tff(c_24,plain,(
    ! [A_27,B_34,C_35] :
      ( r2_hidden('#skF_2'(A_27,B_34,C_35),B_34)
      | r2_lattice3(A_27,B_34,C_35)
      | ~ m1_subset_1(C_35,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1126,plain,(
    ! [A_358,D_359,C_360,B_361] :
      ( r1_orders_2(A_358,D_359,C_360)
      | ~ r2_hidden(D_359,B_361)
      | ~ m1_subset_1(D_359,u1_struct_0(A_358))
      | ~ r2_lattice3(A_358,B_361,C_360)
      | ~ m1_subset_1(C_360,u1_struct_0(A_358))
      | ~ l1_orders_2(A_358) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1315,plain,(
    ! [C_421,B_424,A_425,C_422,A_423] :
      ( r1_orders_2(A_423,'#skF_2'(A_425,B_424,C_421),C_422)
      | ~ m1_subset_1('#skF_2'(A_425,B_424,C_421),u1_struct_0(A_423))
      | ~ r2_lattice3(A_423,B_424,C_422)
      | ~ m1_subset_1(C_422,u1_struct_0(A_423))
      | ~ l1_orders_2(A_423)
      | r2_lattice3(A_425,B_424,C_421)
      | ~ m1_subset_1(C_421,u1_struct_0(A_425))
      | ~ l1_orders_2(A_425) ) ),
    inference(resolution,[status(thm)],[c_24,c_1126])).

tff(c_1321,plain,(
    ! [A_425,B_424,C_421,C_422] :
      ( r1_orders_2('#skF_3','#skF_2'(A_425,B_424,C_421),C_422)
      | ~ m1_subset_1('#skF_2'(A_425,B_424,C_421),u1_struct_0('#skF_4'))
      | ~ r2_lattice3('#skF_3',B_424,C_422)
      | ~ m1_subset_1(C_422,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | r2_lattice3(A_425,B_424,C_421)
      | ~ m1_subset_1(C_421,u1_struct_0(A_425))
      | ~ l1_orders_2(A_425) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_973,c_1315])).

tff(c_1373,plain,(
    ! [A_434,B_435,C_436,C_437] :
      ( r1_orders_2('#skF_3','#skF_2'(A_434,B_435,C_436),C_437)
      | ~ m1_subset_1('#skF_2'(A_434,B_435,C_436),u1_struct_0('#skF_4'))
      | ~ r2_lattice3('#skF_3',B_435,C_437)
      | ~ m1_subset_1(C_437,u1_struct_0('#skF_4'))
      | r2_lattice3(A_434,B_435,C_436)
      | ~ m1_subset_1(C_436,u1_struct_0(A_434))
      | ~ l1_orders_2(A_434) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_973,c_1321])).

tff(c_1378,plain,(
    ! [B_34,C_35,C_437] :
      ( r1_orders_2('#skF_3','#skF_2'('#skF_4',B_34,C_35),C_437)
      | ~ r2_lattice3('#skF_3',B_34,C_437)
      | ~ m1_subset_1(C_437,u1_struct_0('#skF_4'))
      | r2_lattice3('#skF_4',B_34,C_35)
      | ~ m1_subset_1(C_35,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_1373])).

tff(c_1403,plain,(
    ! [B_441,C_442,C_443] :
      ( r1_orders_2('#skF_3','#skF_2'('#skF_4',B_441,C_442),C_443)
      | ~ r2_lattice3('#skF_3',B_441,C_443)
      | ~ m1_subset_1(C_443,u1_struct_0('#skF_4'))
      | r2_lattice3('#skF_4',B_441,C_442)
      | ~ m1_subset_1(C_442,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1378])).

tff(c_1025,plain,(
    ! [B_339,C_340,A_341] :
      ( r2_hidden(k4_tarski(B_339,C_340),u1_orders_2(A_341))
      | ~ r1_orders_2(A_341,B_339,C_340)
      | ~ m1_subset_1(C_340,u1_struct_0(A_341))
      | ~ m1_subset_1(B_339,u1_struct_0(A_341))
      | ~ l1_orders_2(A_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1028,plain,(
    ! [B_339,C_340] :
      ( r2_hidden(k4_tarski(B_339,C_340),u1_orders_2('#skF_4'))
      | ~ r1_orders_2('#skF_3',B_339,C_340)
      | ~ m1_subset_1(C_340,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_339,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_924,c_1025])).

tff(c_1030,plain,(
    ! [B_339,C_340] :
      ( r2_hidden(k4_tarski(B_339,C_340),u1_orders_2('#skF_4'))
      | ~ r1_orders_2('#skF_3',B_339,C_340)
      | ~ m1_subset_1(C_340,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_339,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_973,c_973,c_1028])).

tff(c_1032,plain,(
    ! [A_344,B_345,C_346] :
      ( r1_orders_2(A_344,B_345,C_346)
      | ~ r2_hidden(k4_tarski(B_345,C_346),u1_orders_2(A_344))
      | ~ m1_subset_1(C_346,u1_struct_0(A_344))
      | ~ m1_subset_1(B_345,u1_struct_0(A_344))
      | ~ l1_orders_2(A_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1035,plain,(
    ! [B_339,C_340] :
      ( r1_orders_2('#skF_4',B_339,C_340)
      | ~ l1_orders_2('#skF_4')
      | ~ r1_orders_2('#skF_3',B_339,C_340)
      | ~ m1_subset_1(C_340,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_339,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1030,c_1032])).

tff(c_1044,plain,(
    ! [B_339,C_340] :
      ( r1_orders_2('#skF_4',B_339,C_340)
      | ~ r1_orders_2('#skF_3',B_339,C_340)
      | ~ m1_subset_1(C_340,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_339,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1035])).

tff(c_1579,plain,(
    ! [B_498,C_499,C_500] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_498,C_499),C_500)
      | ~ m1_subset_1('#skF_2'('#skF_4',B_498,C_499),u1_struct_0('#skF_4'))
      | ~ r2_lattice3('#skF_3',B_498,C_500)
      | ~ m1_subset_1(C_500,u1_struct_0('#skF_4'))
      | r2_lattice3('#skF_4',B_498,C_499)
      | ~ m1_subset_1(C_499,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1403,c_1044])).

tff(c_1582,plain,(
    ! [B_34,C_35,C_500] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_34,C_35),C_500)
      | ~ r2_lattice3('#skF_3',B_34,C_500)
      | ~ m1_subset_1(C_500,u1_struct_0('#skF_4'))
      | r2_lattice3('#skF_4',B_34,C_35)
      | ~ m1_subset_1(C_35,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_1579])).

tff(c_1627,plain,(
    ! [B_511,C_512,C_513] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_511,C_512),C_513)
      | ~ r2_lattice3('#skF_3',B_511,C_513)
      | ~ m1_subset_1(C_513,u1_struct_0('#skF_4'))
      | r2_lattice3('#skF_4',B_511,C_512)
      | ~ m1_subset_1(C_512,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1582])).

tff(c_22,plain,(
    ! [A_27,B_34,C_35] :
      ( ~ r1_orders_2(A_27,'#skF_2'(A_27,B_34,C_35),C_35)
      | r2_lattice3(A_27,B_34,C_35)
      | ~ m1_subset_1(C_35,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1635,plain,(
    ! [B_511,C_513] :
      ( ~ l1_orders_2('#skF_4')
      | ~ r2_lattice3('#skF_3',B_511,C_513)
      | r2_lattice3('#skF_4',B_511,C_513)
      | ~ m1_subset_1(C_513,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1627,c_22])).

tff(c_1647,plain,(
    ! [B_514,C_515] :
      ( ~ r2_lattice3('#skF_3',B_514,C_515)
      | r2_lattice3('#skF_4',B_514,C_515)
      | ~ m1_subset_1(C_515,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1635])).

tff(c_1651,plain,
    ( r2_lattice3('#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_892,c_1647])).

tff(c_1657,plain,(
    r2_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_1651])).

tff(c_1659,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_1657])).

tff(c_1660,plain,(
    r2_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1672,plain,(
    ! [C_517,A_518,D_519,B_520] :
      ( C_517 = A_518
      | g1_orders_2(C_517,D_519) != g1_orders_2(A_518,B_520)
      | ~ m1_subset_1(B_520,k1_zfmisc_1(k2_zfmisc_1(A_518,A_518))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1692,plain,(
    ! [A_543,B_544] :
      ( u1_struct_0('#skF_3') = A_543
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(A_543,B_544)
      | ~ m1_subset_1(B_544,k1_zfmisc_1(k2_zfmisc_1(A_543,A_543))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1672])).

tff(c_1696,plain,(
    ! [A_8] :
      ( u1_struct_0(A_8) = u1_struct_0('#skF_3')
      | g1_orders_2(u1_struct_0(A_8),u1_orders_2(A_8)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(A_8) ) ),
    inference(resolution,[status(thm)],[c_6,c_1692])).

tff(c_1699,plain,
    ( u1_struct_0('#skF_3') = u1_struct_0('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1696])).

tff(c_1701,plain,(
    u1_struct_0('#skF_3') = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1699])).

tff(c_1891,plain,(
    ! [A_573,D_574,C_575,B_576] :
      ( r1_orders_2(A_573,D_574,C_575)
      | ~ r2_hidden(D_574,B_576)
      | ~ m1_subset_1(D_574,u1_struct_0(A_573))
      | ~ r2_lattice3(A_573,B_576,C_575)
      | ~ m1_subset_1(C_575,u1_struct_0(A_573))
      | ~ l1_orders_2(A_573) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2274,plain,(
    ! [B_696,A_697,C_694,A_695,C_693] :
      ( r1_orders_2(A_695,'#skF_2'(A_697,B_696,C_694),C_693)
      | ~ m1_subset_1('#skF_2'(A_697,B_696,C_694),u1_struct_0(A_695))
      | ~ r2_lattice3(A_695,B_696,C_693)
      | ~ m1_subset_1(C_693,u1_struct_0(A_695))
      | ~ l1_orders_2(A_695)
      | r2_lattice3(A_697,B_696,C_694)
      | ~ m1_subset_1(C_694,u1_struct_0(A_697))
      | ~ l1_orders_2(A_697) ) ),
    inference(resolution,[status(thm)],[c_24,c_1891])).

tff(c_2278,plain,(
    ! [A_697,B_696,C_694,C_693] :
      ( r1_orders_2('#skF_3','#skF_2'(A_697,B_696,C_694),C_693)
      | ~ m1_subset_1('#skF_2'(A_697,B_696,C_694),u1_struct_0('#skF_4'))
      | ~ r2_lattice3('#skF_3',B_696,C_693)
      | ~ m1_subset_1(C_693,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | r2_lattice3(A_697,B_696,C_694)
      | ~ m1_subset_1(C_694,u1_struct_0(A_697))
      | ~ l1_orders_2(A_697) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1701,c_2274])).

tff(c_2422,plain,(
    ! [A_736,B_737,C_738,C_739] :
      ( r1_orders_2('#skF_3','#skF_2'(A_736,B_737,C_738),C_739)
      | ~ m1_subset_1('#skF_2'(A_736,B_737,C_738),u1_struct_0('#skF_4'))
      | ~ r2_lattice3('#skF_3',B_737,C_739)
      | ~ m1_subset_1(C_739,u1_struct_0('#skF_4'))
      | r2_lattice3(A_736,B_737,C_738)
      | ~ m1_subset_1(C_738,u1_struct_0(A_736))
      | ~ l1_orders_2(A_736) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1701,c_2278])).

tff(c_2427,plain,(
    ! [B_34,C_35,C_739] :
      ( r1_orders_2('#skF_3','#skF_2'('#skF_4',B_34,C_35),C_739)
      | ~ r2_lattice3('#skF_3',B_34,C_739)
      | ~ m1_subset_1(C_739,u1_struct_0('#skF_4'))
      | r2_lattice3('#skF_4',B_34,C_35)
      | ~ m1_subset_1(C_35,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_2422])).

tff(c_2452,plain,(
    ! [B_743,C_744,C_745] :
      ( r1_orders_2('#skF_3','#skF_2'('#skF_4',B_743,C_744),C_745)
      | ~ r2_lattice3('#skF_3',B_743,C_745)
      | ~ m1_subset_1(C_745,u1_struct_0('#skF_4'))
      | r2_lattice3('#skF_4',B_743,C_744)
      | ~ m1_subset_1(C_744,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2427])).

tff(c_1729,plain,
    ( m1_subset_1(u1_orders_2('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ l1_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1701,c_6])).

tff(c_1740,plain,(
    m1_subset_1(u1_orders_2('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1701,c_1729])).

tff(c_1717,plain,(
    g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_3')) = g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1701,c_34])).

tff(c_8,plain,(
    ! [D_14,B_10,C_13,A_9] :
      ( D_14 = B_10
      | g1_orders_2(C_13,D_14) != g1_orders_2(A_9,B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(k2_zfmisc_1(A_9,A_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1754,plain,(
    ! [D_14,C_13] :
      ( u1_orders_2('#skF_3') = D_14
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(C_13,D_14)
      | ~ m1_subset_1(u1_orders_2('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1717,c_8])).

tff(c_1762,plain,(
    ! [D_14,C_13] :
      ( u1_orders_2('#skF_3') = D_14
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(C_13,D_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1740,c_1754])).

tff(c_1768,plain,(
    u1_orders_2('#skF_3') = u1_orders_2('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1762])).

tff(c_1809,plain,(
    ! [B_561,C_562,A_563] :
      ( r2_hidden(k4_tarski(B_561,C_562),u1_orders_2(A_563))
      | ~ r1_orders_2(A_563,B_561,C_562)
      | ~ m1_subset_1(C_562,u1_struct_0(A_563))
      | ~ m1_subset_1(B_561,u1_struct_0(A_563))
      | ~ l1_orders_2(A_563) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1815,plain,(
    ! [B_561,C_562] :
      ( r2_hidden(k4_tarski(B_561,C_562),u1_orders_2('#skF_4'))
      | ~ r1_orders_2('#skF_3',B_561,C_562)
      | ~ m1_subset_1(C_562,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_561,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1768,c_1809])).

tff(c_1879,plain,(
    ! [B_569,C_570] :
      ( r2_hidden(k4_tarski(B_569,C_570),u1_orders_2('#skF_4'))
      | ~ r1_orders_2('#skF_3',B_569,C_570)
      | ~ m1_subset_1(C_570,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_569,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1701,c_1701,c_1815])).

tff(c_2,plain,(
    ! [A_1,B_5,C_7] :
      ( r1_orders_2(A_1,B_5,C_7)
      | ~ r2_hidden(k4_tarski(B_5,C_7),u1_orders_2(A_1))
      | ~ m1_subset_1(C_7,u1_struct_0(A_1))
      | ~ m1_subset_1(B_5,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1885,plain,(
    ! [B_569,C_570] :
      ( r1_orders_2('#skF_4',B_569,C_570)
      | ~ l1_orders_2('#skF_4')
      | ~ r1_orders_2('#skF_3',B_569,C_570)
      | ~ m1_subset_1(C_570,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_569,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1879,c_2])).

tff(c_1889,plain,(
    ! [B_569,C_570] :
      ( r1_orders_2('#skF_4',B_569,C_570)
      | ~ r1_orders_2('#skF_3',B_569,C_570)
      | ~ m1_subset_1(C_570,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_569,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1885])).

tff(c_2516,plain,(
    ! [B_762,C_763,C_764] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_762,C_763),C_764)
      | ~ m1_subset_1('#skF_2'('#skF_4',B_762,C_763),u1_struct_0('#skF_4'))
      | ~ r2_lattice3('#skF_3',B_762,C_764)
      | ~ m1_subset_1(C_764,u1_struct_0('#skF_4'))
      | r2_lattice3('#skF_4',B_762,C_763)
      | ~ m1_subset_1(C_763,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_2452,c_1889])).

tff(c_2519,plain,(
    ! [B_34,C_35,C_764] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_34,C_35),C_764)
      | ~ r2_lattice3('#skF_3',B_34,C_764)
      | ~ m1_subset_1(C_764,u1_struct_0('#skF_4'))
      | r2_lattice3('#skF_4',B_34,C_35)
      | ~ m1_subset_1(C_35,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_2516])).

tff(c_2523,plain,(
    ! [B_765,C_766,C_767] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_765,C_766),C_767)
      | ~ r2_lattice3('#skF_3',B_765,C_767)
      | ~ m1_subset_1(C_767,u1_struct_0('#skF_4'))
      | r2_lattice3('#skF_4',B_765,C_766)
      | ~ m1_subset_1(C_766,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2519])).

tff(c_2531,plain,(
    ! [B_765,C_767] :
      ( ~ l1_orders_2('#skF_4')
      | ~ r2_lattice3('#skF_3',B_765,C_767)
      | r2_lattice3('#skF_4',B_765,C_767)
      | ~ m1_subset_1(C_767,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_2523,c_22])).

tff(c_2544,plain,(
    ! [B_772,C_773] :
      ( ~ r2_lattice3('#skF_3',B_772,C_773)
      | r2_lattice3('#skF_4',B_772,C_773)
      | ~ m1_subset_1(C_773,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2531])).

tff(c_2548,plain,
    ( r2_lattice3('#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1660,c_2544])).

tff(c_2554,plain,(
    r2_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_2548])).

tff(c_2556,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_2554])).

tff(c_2557,plain,(
    r1_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2572,plain,(
    ! [C_775,A_776,D_777,B_778] :
      ( C_775 = A_776
      | g1_orders_2(C_775,D_777) != g1_orders_2(A_776,B_778)
      | ~ m1_subset_1(B_778,k1_zfmisc_1(k2_zfmisc_1(A_776,A_776))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2592,plain,(
    ! [A_801,B_802] :
      ( u1_struct_0('#skF_3') = A_801
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(A_801,B_802)
      | ~ m1_subset_1(B_802,k1_zfmisc_1(k2_zfmisc_1(A_801,A_801))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2572])).

tff(c_2596,plain,(
    ! [A_8] :
      ( u1_struct_0(A_8) = u1_struct_0('#skF_3')
      | g1_orders_2(u1_struct_0(A_8),u1_orders_2(A_8)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(A_8) ) ),
    inference(resolution,[status(thm)],[c_6,c_2592])).

tff(c_2599,plain,
    ( u1_struct_0('#skF_3') = u1_struct_0('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2596])).

tff(c_2601,plain,(
    u1_struct_0('#skF_3') = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2599])).

tff(c_2804,plain,(
    ! [A_835,C_836,D_837,B_838] :
      ( r1_orders_2(A_835,C_836,D_837)
      | ~ r2_hidden(D_837,B_838)
      | ~ m1_subset_1(D_837,u1_struct_0(A_835))
      | ~ r1_lattice3(A_835,B_838,C_836)
      | ~ m1_subset_1(C_836,u1_struct_0(A_835))
      | ~ l1_orders_2(A_835) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2997,plain,(
    ! [A_894,B_892,A_891,C_893,C_890] :
      ( r1_orders_2(A_891,C_893,'#skF_1'(A_894,B_892,C_890))
      | ~ m1_subset_1('#skF_1'(A_894,B_892,C_890),u1_struct_0(A_891))
      | ~ r1_lattice3(A_891,B_892,C_893)
      | ~ m1_subset_1(C_893,u1_struct_0(A_891))
      | ~ l1_orders_2(A_891)
      | r1_lattice3(A_894,B_892,C_890)
      | ~ m1_subset_1(C_890,u1_struct_0(A_894))
      | ~ l1_orders_2(A_894) ) ),
    inference(resolution,[status(thm)],[c_16,c_2804])).

tff(c_3001,plain,(
    ! [C_893,A_894,B_892,C_890] :
      ( r1_orders_2('#skF_3',C_893,'#skF_1'(A_894,B_892,C_890))
      | ~ m1_subset_1('#skF_1'(A_894,B_892,C_890),u1_struct_0('#skF_4'))
      | ~ r1_lattice3('#skF_3',B_892,C_893)
      | ~ m1_subset_1(C_893,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | r1_lattice3(A_894,B_892,C_890)
      | ~ m1_subset_1(C_890,u1_struct_0(A_894))
      | ~ l1_orders_2(A_894) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2601,c_2997])).

tff(c_3046,plain,(
    ! [C_901,A_902,B_903,C_904] :
      ( r1_orders_2('#skF_3',C_901,'#skF_1'(A_902,B_903,C_904))
      | ~ m1_subset_1('#skF_1'(A_902,B_903,C_904),u1_struct_0('#skF_4'))
      | ~ r1_lattice3('#skF_3',B_903,C_901)
      | ~ m1_subset_1(C_901,u1_struct_0('#skF_4'))
      | r1_lattice3(A_902,B_903,C_904)
      | ~ m1_subset_1(C_904,u1_struct_0(A_902))
      | ~ l1_orders_2(A_902) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2601,c_3001])).

tff(c_3051,plain,(
    ! [C_901,B_22,C_23] :
      ( r1_orders_2('#skF_3',C_901,'#skF_1'('#skF_4',B_22,C_23))
      | ~ r1_lattice3('#skF_3',B_22,C_901)
      | ~ m1_subset_1(C_901,u1_struct_0('#skF_4'))
      | r1_lattice3('#skF_4',B_22,C_23)
      | ~ m1_subset_1(C_23,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_3046])).

tff(c_3093,plain,(
    ! [C_925,B_926,C_927] :
      ( r1_orders_2('#skF_3',C_925,'#skF_1'('#skF_4',B_926,C_927))
      | ~ r1_lattice3('#skF_3',B_926,C_925)
      | ~ m1_subset_1(C_925,u1_struct_0('#skF_4'))
      | r1_lattice3('#skF_4',B_926,C_927)
      | ~ m1_subset_1(C_927,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3051])).

tff(c_2629,plain,
    ( m1_subset_1(u1_orders_2('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ l1_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2601,c_6])).

tff(c_2640,plain,(
    m1_subset_1(u1_orders_2('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2601,c_2629])).

tff(c_2617,plain,(
    g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_3')) = g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2601,c_34])).

tff(c_2654,plain,(
    ! [D_14,C_13] :
      ( u1_orders_2('#skF_3') = D_14
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(C_13,D_14)
      | ~ m1_subset_1(u1_orders_2('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2617,c_8])).

tff(c_2662,plain,(
    ! [D_14,C_13] :
      ( u1_orders_2('#skF_3') = D_14
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(C_13,D_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2640,c_2654])).

tff(c_2668,plain,(
    u1_orders_2('#skF_3') = u1_orders_2('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2662])).

tff(c_2709,plain,(
    ! [B_819,C_820,A_821] :
      ( r2_hidden(k4_tarski(B_819,C_820),u1_orders_2(A_821))
      | ~ r1_orders_2(A_821,B_819,C_820)
      | ~ m1_subset_1(C_820,u1_struct_0(A_821))
      | ~ m1_subset_1(B_819,u1_struct_0(A_821))
      | ~ l1_orders_2(A_821) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2715,plain,(
    ! [B_819,C_820] :
      ( r2_hidden(k4_tarski(B_819,C_820),u1_orders_2('#skF_4'))
      | ~ r1_orders_2('#skF_3',B_819,C_820)
      | ~ m1_subset_1(C_820,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_819,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2668,c_2709])).

tff(c_2779,plain,(
    ! [B_827,C_828] :
      ( r2_hidden(k4_tarski(B_827,C_828),u1_orders_2('#skF_4'))
      | ~ r1_orders_2('#skF_3',B_827,C_828)
      | ~ m1_subset_1(C_828,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_827,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2601,c_2601,c_2715])).

tff(c_2785,plain,(
    ! [B_827,C_828] :
      ( r1_orders_2('#skF_4',B_827,C_828)
      | ~ l1_orders_2('#skF_4')
      | ~ r1_orders_2('#skF_3',B_827,C_828)
      | ~ m1_subset_1(C_828,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_827,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_2779,c_2])).

tff(c_2789,plain,(
    ! [B_827,C_828] :
      ( r1_orders_2('#skF_4',B_827,C_828)
      | ~ r1_orders_2('#skF_3',B_827,C_828)
      | ~ m1_subset_1(C_828,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_827,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2785])).

tff(c_3175,plain,(
    ! [C_949,B_950,C_951] :
      ( r1_orders_2('#skF_4',C_949,'#skF_1'('#skF_4',B_950,C_951))
      | ~ m1_subset_1('#skF_1'('#skF_4',B_950,C_951),u1_struct_0('#skF_4'))
      | ~ r1_lattice3('#skF_3',B_950,C_949)
      | ~ m1_subset_1(C_949,u1_struct_0('#skF_4'))
      | r1_lattice3('#skF_4',B_950,C_951)
      | ~ m1_subset_1(C_951,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_3093,c_2789])).

tff(c_3178,plain,(
    ! [C_949,B_22,C_23] :
      ( r1_orders_2('#skF_4',C_949,'#skF_1'('#skF_4',B_22,C_23))
      | ~ r1_lattice3('#skF_3',B_22,C_949)
      | ~ m1_subset_1(C_949,u1_struct_0('#skF_4'))
      | r1_lattice3('#skF_4',B_22,C_23)
      | ~ m1_subset_1(C_23,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_3175])).

tff(c_3182,plain,(
    ! [C_952,B_953,C_954] :
      ( r1_orders_2('#skF_4',C_952,'#skF_1'('#skF_4',B_953,C_954))
      | ~ r1_lattice3('#skF_3',B_953,C_952)
      | ~ m1_subset_1(C_952,u1_struct_0('#skF_4'))
      | r1_lattice3('#skF_4',B_953,C_954)
      | ~ m1_subset_1(C_954,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3178])).

tff(c_3190,plain,(
    ! [B_953,C_954] :
      ( ~ l1_orders_2('#skF_4')
      | ~ r1_lattice3('#skF_3',B_953,C_954)
      | r1_lattice3('#skF_4',B_953,C_954)
      | ~ m1_subset_1(C_954,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_3182,c_14])).

tff(c_3210,plain,(
    ! [B_960,C_961] :
      ( ~ r1_lattice3('#skF_3',B_960,C_961)
      | r1_lattice3('#skF_4',B_960,C_961)
      | ~ m1_subset_1(C_961,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3190])).

tff(c_3222,plain,
    ( r1_lattice3('#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2557,c_3210])).

tff(c_3232,plain,(
    r1_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_3222])).

tff(c_3234,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2559,c_3232])).

tff(c_3236,plain,(
    r1_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_2558,plain,(
    r2_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_40,plain,
    ( ~ r2_lattice3('#skF_4','#skF_5','#skF_7')
    | ~ r1_lattice3('#skF_4','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_50,plain,
    ( ~ r2_lattice3('#skF_4','#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_40])).

tff(c_3239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3236,c_2558,c_50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:36:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.69/2.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.69/2.17  
% 5.69/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.69/2.17  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > m1_subset_1 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 5.69/2.17  
% 5.69/2.17  %Foreground sorts:
% 5.69/2.17  
% 5.69/2.17  
% 5.69/2.17  %Background operators:
% 5.69/2.17  
% 5.69/2.17  
% 5.69/2.17  %Foreground operators:
% 5.69/2.17  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.69/2.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.69/2.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.69/2.17  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.69/2.17  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 5.69/2.17  tff('#skF_7', type, '#skF_7': $i).
% 5.69/2.17  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 5.69/2.17  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 5.69/2.17  tff('#skF_5', type, '#skF_5': $i).
% 5.69/2.17  tff('#skF_6', type, '#skF_6': $i).
% 5.69/2.17  tff('#skF_3', type, '#skF_3': $i).
% 5.69/2.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.69/2.17  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 5.69/2.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.69/2.17  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.69/2.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.69/2.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.69/2.17  tff('#skF_4', type, '#skF_4': $i).
% 5.69/2.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.69/2.17  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 5.69/2.17  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.69/2.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.69/2.17  
% 5.69/2.20  tff(f_102, negated_conjecture, ~(![A]: (l1_orders_2(A) => (![B]: (l1_orders_2(B) => ((g1_orders_2(u1_struct_0(A), u1_orders_2(A)) = g1_orders_2(u1_struct_0(B), u1_orders_2(B))) => (![C, D]: (m1_subset_1(D, u1_struct_0(A)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => ((D = E) => ((r2_lattice3(A, C, D) => r2_lattice3(B, C, E)) & (r1_lattice3(A, C, D) => r1_lattice3(B, C, E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow_0)).
% 5.69/2.20  tff(f_64, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattice3)).
% 5.69/2.20  tff(f_41, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 5.69/2.20  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C, D]: ((g1_orders_2(A, B) = g1_orders_2(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_orders_2)).
% 5.69/2.20  tff(f_37, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_orders_2)).
% 5.69/2.20  tff(f_78, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 5.69/2.20  tff(c_28, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.69/2.20  tff(c_42, plain, (r2_lattice3('#skF_3', '#skF_5', '#skF_6') | ~r1_lattice3('#skF_4', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.69/2.20  tff(c_49, plain, (r2_lattice3('#skF_3', '#skF_5', '#skF_6') | ~r1_lattice3('#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_42])).
% 5.69/2.20  tff(c_2559, plain, (~r1_lattice3('#skF_4', '#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_49])).
% 5.69/2.20  tff(c_30, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.69/2.20  tff(c_47, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30])).
% 5.69/2.20  tff(c_44, plain, (~r2_lattice3('#skF_4', '#skF_5', '#skF_7') | r1_lattice3('#skF_3', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.69/2.20  tff(c_48, plain, (~r2_lattice3('#skF_4', '#skF_5', '#skF_6') | r1_lattice3('#skF_3', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_44])).
% 5.69/2.20  tff(c_55, plain, (~r2_lattice3('#skF_4', '#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_48])).
% 5.69/2.20  tff(c_61, plain, (~r1_lattice3('#skF_4', '#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_49])).
% 5.69/2.20  tff(c_46, plain, (r2_lattice3('#skF_3', '#skF_5', '#skF_6') | r1_lattice3('#skF_3', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.69/2.20  tff(c_56, plain, (r1_lattice3('#skF_3', '#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_46])).
% 5.69/2.20  tff(c_36, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.69/2.20  tff(c_18, plain, (![A_15, B_22, C_23]: (m1_subset_1('#skF_1'(A_15, B_22, C_23), u1_struct_0(A_15)) | r1_lattice3(A_15, B_22, C_23) | ~m1_subset_1(C_23, u1_struct_0(A_15)) | ~l1_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.69/2.20  tff(c_38, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.69/2.20  tff(c_6, plain, (![A_8]: (m1_subset_1(u1_orders_2(A_8), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8), u1_struct_0(A_8)))) | ~l1_orders_2(A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.69/2.20  tff(c_34, plain, (g1_orders_2(u1_struct_0('#skF_3'), u1_orders_2('#skF_3'))=g1_orders_2(u1_struct_0('#skF_4'), u1_orders_2('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.69/2.20  tff(c_67, plain, (![D_54, B_55, C_56, A_57]: (D_54=B_55 | g1_orders_2(C_56, D_54)!=g1_orders_2(A_57, B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(k2_zfmisc_1(A_57, A_57))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.69/2.20  tff(c_84, plain, (![B_71, A_72]: (u1_orders_2('#skF_3')=B_71 | g1_orders_2(u1_struct_0('#skF_4'), u1_orders_2('#skF_4'))!=g1_orders_2(A_72, B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(k2_zfmisc_1(A_72, A_72))))), inference(superposition, [status(thm), theory('equality')], [c_34, c_67])).
% 5.69/2.20  tff(c_88, plain, (![A_8]: (u1_orders_2(A_8)=u1_orders_2('#skF_3') | g1_orders_2(u1_struct_0(A_8), u1_orders_2(A_8))!=g1_orders_2(u1_struct_0('#skF_4'), u1_orders_2('#skF_4')) | ~l1_orders_2(A_8))), inference(resolution, [status(thm)], [c_6, c_84])).
% 5.69/2.20  tff(c_91, plain, (u1_orders_2('#skF_3')=u1_orders_2('#skF_4') | ~l1_orders_2('#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_88])).
% 5.69/2.20  tff(c_93, plain, (u1_orders_2('#skF_3')=u1_orders_2('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_91])).
% 5.69/2.20  tff(c_108, plain, (m1_subset_1(u1_orders_2('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')))) | ~l1_orders_2('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_93, c_6])).
% 5.69/2.20  tff(c_112, plain, (m1_subset_1(u1_orders_2('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_108])).
% 5.69/2.20  tff(c_104, plain, (g1_orders_2(u1_struct_0('#skF_3'), u1_orders_2('#skF_4'))=g1_orders_2(u1_struct_0('#skF_4'), u1_orders_2('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_34])).
% 5.69/2.20  tff(c_10, plain, (![C_13, A_9, D_14, B_10]: (C_13=A_9 | g1_orders_2(C_13, D_14)!=g1_orders_2(A_9, B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(k2_zfmisc_1(A_9, A_9))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.69/2.20  tff(c_118, plain, (![C_13, D_14]: (u1_struct_0('#skF_3')=C_13 | g1_orders_2(u1_struct_0('#skF_4'), u1_orders_2('#skF_4'))!=g1_orders_2(C_13, D_14) | ~m1_subset_1(u1_orders_2('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')))))), inference(superposition, [status(thm), theory('equality')], [c_104, c_10])).
% 5.69/2.20  tff(c_126, plain, (![C_13, D_14]: (u1_struct_0('#skF_3')=C_13 | g1_orders_2(u1_struct_0('#skF_4'), u1_orders_2('#skF_4'))!=g1_orders_2(C_13, D_14))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_118])).
% 5.69/2.20  tff(c_132, plain, (u1_struct_0('#skF_3')=u1_struct_0('#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_126])).
% 5.69/2.20  tff(c_16, plain, (![A_15, B_22, C_23]: (r2_hidden('#skF_1'(A_15, B_22, C_23), B_22) | r1_lattice3(A_15, B_22, C_23) | ~m1_subset_1(C_23, u1_struct_0(A_15)) | ~l1_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.69/2.20  tff(c_290, plain, (![A_112, C_113, D_114, B_115]: (r1_orders_2(A_112, C_113, D_114) | ~r2_hidden(D_114, B_115) | ~m1_subset_1(D_114, u1_struct_0(A_112)) | ~r1_lattice3(A_112, B_115, C_113) | ~m1_subset_1(C_113, u1_struct_0(A_112)) | ~l1_orders_2(A_112))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.69/2.20  tff(c_537, plain, (![C_187, B_188, A_190, A_189, C_186]: (r1_orders_2(A_190, C_186, '#skF_1'(A_189, B_188, C_187)) | ~m1_subset_1('#skF_1'(A_189, B_188, C_187), u1_struct_0(A_190)) | ~r1_lattice3(A_190, B_188, C_186) | ~m1_subset_1(C_186, u1_struct_0(A_190)) | ~l1_orders_2(A_190) | r1_lattice3(A_189, B_188, C_187) | ~m1_subset_1(C_187, u1_struct_0(A_189)) | ~l1_orders_2(A_189))), inference(resolution, [status(thm)], [c_16, c_290])).
% 5.69/2.20  tff(c_543, plain, (![C_186, A_189, B_188, C_187]: (r1_orders_2('#skF_3', C_186, '#skF_1'(A_189, B_188, C_187)) | ~m1_subset_1('#skF_1'(A_189, B_188, C_187), u1_struct_0('#skF_4')) | ~r1_lattice3('#skF_3', B_188, C_186) | ~m1_subset_1(C_186, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | r1_lattice3(A_189, B_188, C_187) | ~m1_subset_1(C_187, u1_struct_0(A_189)) | ~l1_orders_2(A_189))), inference(superposition, [status(thm), theory('equality')], [c_132, c_537])).
% 5.69/2.20  tff(c_586, plain, (![C_197, A_198, B_199, C_200]: (r1_orders_2('#skF_3', C_197, '#skF_1'(A_198, B_199, C_200)) | ~m1_subset_1('#skF_1'(A_198, B_199, C_200), u1_struct_0('#skF_4')) | ~r1_lattice3('#skF_3', B_199, C_197) | ~m1_subset_1(C_197, u1_struct_0('#skF_4')) | r1_lattice3(A_198, B_199, C_200) | ~m1_subset_1(C_200, u1_struct_0(A_198)) | ~l1_orders_2(A_198))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_132, c_543])).
% 5.69/2.20  tff(c_591, plain, (![C_197, B_22, C_23]: (r1_orders_2('#skF_3', C_197, '#skF_1'('#skF_4', B_22, C_23)) | ~r1_lattice3('#skF_3', B_22, C_197) | ~m1_subset_1(C_197, u1_struct_0('#skF_4')) | r1_lattice3('#skF_4', B_22, C_23) | ~m1_subset_1(C_23, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_586])).
% 5.69/2.20  tff(c_633, plain, (![C_221, B_222, C_223]: (r1_orders_2('#skF_3', C_221, '#skF_1'('#skF_4', B_222, C_223)) | ~r1_lattice3('#skF_3', B_222, C_221) | ~m1_subset_1(C_221, u1_struct_0('#skF_4')) | r1_lattice3('#skF_4', B_222, C_223) | ~m1_subset_1(C_223, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_591])).
% 5.69/2.20  tff(c_189, plain, (![B_93, C_94, A_95]: (r2_hidden(k4_tarski(B_93, C_94), u1_orders_2(A_95)) | ~r1_orders_2(A_95, B_93, C_94) | ~m1_subset_1(C_94, u1_struct_0(A_95)) | ~m1_subset_1(B_93, u1_struct_0(A_95)) | ~l1_orders_2(A_95))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.69/2.20  tff(c_192, plain, (![B_93, C_94]: (r2_hidden(k4_tarski(B_93, C_94), u1_orders_2('#skF_4')) | ~r1_orders_2('#skF_3', B_93, C_94) | ~m1_subset_1(C_94, u1_struct_0('#skF_3')) | ~m1_subset_1(B_93, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_93, c_189])).
% 5.69/2.20  tff(c_194, plain, (![B_93, C_94]: (r2_hidden(k4_tarski(B_93, C_94), u1_orders_2('#skF_4')) | ~r1_orders_2('#skF_3', B_93, C_94) | ~m1_subset_1(C_94, u1_struct_0('#skF_4')) | ~m1_subset_1(B_93, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_132, c_132, c_192])).
% 5.69/2.20  tff(c_196, plain, (![A_98, B_99, C_100]: (r1_orders_2(A_98, B_99, C_100) | ~r2_hidden(k4_tarski(B_99, C_100), u1_orders_2(A_98)) | ~m1_subset_1(C_100, u1_struct_0(A_98)) | ~m1_subset_1(B_99, u1_struct_0(A_98)) | ~l1_orders_2(A_98))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.69/2.20  tff(c_199, plain, (![B_93, C_94]: (r1_orders_2('#skF_4', B_93, C_94) | ~l1_orders_2('#skF_4') | ~r1_orders_2('#skF_3', B_93, C_94) | ~m1_subset_1(C_94, u1_struct_0('#skF_4')) | ~m1_subset_1(B_93, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_194, c_196])).
% 5.69/2.20  tff(c_208, plain, (![B_93, C_94]: (r1_orders_2('#skF_4', B_93, C_94) | ~r1_orders_2('#skF_3', B_93, C_94) | ~m1_subset_1(C_94, u1_struct_0('#skF_4')) | ~m1_subset_1(B_93, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_199])).
% 5.69/2.20  tff(c_845, plain, (![C_291, B_292, C_293]: (r1_orders_2('#skF_4', C_291, '#skF_1'('#skF_4', B_292, C_293)) | ~m1_subset_1('#skF_1'('#skF_4', B_292, C_293), u1_struct_0('#skF_4')) | ~r1_lattice3('#skF_3', B_292, C_291) | ~m1_subset_1(C_291, u1_struct_0('#skF_4')) | r1_lattice3('#skF_4', B_292, C_293) | ~m1_subset_1(C_293, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_633, c_208])).
% 5.69/2.20  tff(c_848, plain, (![C_291, B_22, C_23]: (r1_orders_2('#skF_4', C_291, '#skF_1'('#skF_4', B_22, C_23)) | ~r1_lattice3('#skF_3', B_22, C_291) | ~m1_subset_1(C_291, u1_struct_0('#skF_4')) | r1_lattice3('#skF_4', B_22, C_23) | ~m1_subset_1(C_23, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_845])).
% 5.69/2.20  tff(c_852, plain, (![C_294, B_295, C_296]: (r1_orders_2('#skF_4', C_294, '#skF_1'('#skF_4', B_295, C_296)) | ~r1_lattice3('#skF_3', B_295, C_294) | ~m1_subset_1(C_294, u1_struct_0('#skF_4')) | r1_lattice3('#skF_4', B_295, C_296) | ~m1_subset_1(C_296, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_848])).
% 5.69/2.20  tff(c_14, plain, (![A_15, C_23, B_22]: (~r1_orders_2(A_15, C_23, '#skF_1'(A_15, B_22, C_23)) | r1_lattice3(A_15, B_22, C_23) | ~m1_subset_1(C_23, u1_struct_0(A_15)) | ~l1_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.69/2.20  tff(c_860, plain, (![B_295, C_296]: (~l1_orders_2('#skF_4') | ~r1_lattice3('#skF_3', B_295, C_296) | r1_lattice3('#skF_4', B_295, C_296) | ~m1_subset_1(C_296, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_852, c_14])).
% 5.69/2.20  tff(c_867, plain, (![B_297, C_298]: (~r1_lattice3('#skF_3', B_297, C_298) | r1_lattice3('#skF_4', B_297, C_298) | ~m1_subset_1(C_298, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_860])).
% 5.69/2.20  tff(c_879, plain, (r1_lattice3('#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_867])).
% 5.69/2.20  tff(c_889, plain, (r1_lattice3('#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_879])).
% 5.69/2.20  tff(c_891, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_889])).
% 5.69/2.20  tff(c_892, plain, (r2_lattice3('#skF_3', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_49])).
% 5.69/2.20  tff(c_26, plain, (![A_27, B_34, C_35]: (m1_subset_1('#skF_2'(A_27, B_34, C_35), u1_struct_0(A_27)) | r2_lattice3(A_27, B_34, C_35) | ~m1_subset_1(C_35, u1_struct_0(A_27)) | ~l1_orders_2(A_27))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.69/2.20  tff(c_908, plain, (![D_304, B_305, C_306, A_307]: (D_304=B_305 | g1_orders_2(C_306, D_304)!=g1_orders_2(A_307, B_305) | ~m1_subset_1(B_305, k1_zfmisc_1(k2_zfmisc_1(A_307, A_307))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.69/2.20  tff(c_914, plain, (![B_311, A_312]: (u1_orders_2('#skF_3')=B_311 | g1_orders_2(u1_struct_0('#skF_4'), u1_orders_2('#skF_4'))!=g1_orders_2(A_312, B_311) | ~m1_subset_1(B_311, k1_zfmisc_1(k2_zfmisc_1(A_312, A_312))))), inference(superposition, [status(thm), theory('equality')], [c_34, c_908])).
% 5.69/2.20  tff(c_918, plain, (![A_8]: (u1_orders_2(A_8)=u1_orders_2('#skF_3') | g1_orders_2(u1_struct_0(A_8), u1_orders_2(A_8))!=g1_orders_2(u1_struct_0('#skF_4'), u1_orders_2('#skF_4')) | ~l1_orders_2(A_8))), inference(resolution, [status(thm)], [c_6, c_914])).
% 5.69/2.20  tff(c_922, plain, (u1_orders_2('#skF_3')=u1_orders_2('#skF_4') | ~l1_orders_2('#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_918])).
% 5.69/2.20  tff(c_924, plain, (u1_orders_2('#skF_3')=u1_orders_2('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_922])).
% 5.69/2.20  tff(c_939, plain, (m1_subset_1(u1_orders_2('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')))) | ~l1_orders_2('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_924, c_6])).
% 5.69/2.20  tff(c_943, plain, (m1_subset_1(u1_orders_2('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_939])).
% 5.69/2.20  tff(c_935, plain, (g1_orders_2(u1_struct_0('#skF_3'), u1_orders_2('#skF_4'))=g1_orders_2(u1_struct_0('#skF_4'), u1_orders_2('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_924, c_34])).
% 5.69/2.20  tff(c_953, plain, (![C_13, D_14]: (u1_struct_0('#skF_3')=C_13 | g1_orders_2(u1_struct_0('#skF_4'), u1_orders_2('#skF_4'))!=g1_orders_2(C_13, D_14) | ~m1_subset_1(u1_orders_2('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')))))), inference(superposition, [status(thm), theory('equality')], [c_935, c_10])).
% 5.69/2.20  tff(c_959, plain, (![C_13, D_14]: (u1_struct_0('#skF_3')=C_13 | g1_orders_2(u1_struct_0('#skF_4'), u1_orders_2('#skF_4'))!=g1_orders_2(C_13, D_14))), inference(demodulation, [status(thm), theory('equality')], [c_943, c_953])).
% 5.69/2.20  tff(c_973, plain, (u1_struct_0('#skF_3')=u1_struct_0('#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_959])).
% 5.69/2.20  tff(c_24, plain, (![A_27, B_34, C_35]: (r2_hidden('#skF_2'(A_27, B_34, C_35), B_34) | r2_lattice3(A_27, B_34, C_35) | ~m1_subset_1(C_35, u1_struct_0(A_27)) | ~l1_orders_2(A_27))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.69/2.20  tff(c_1126, plain, (![A_358, D_359, C_360, B_361]: (r1_orders_2(A_358, D_359, C_360) | ~r2_hidden(D_359, B_361) | ~m1_subset_1(D_359, u1_struct_0(A_358)) | ~r2_lattice3(A_358, B_361, C_360) | ~m1_subset_1(C_360, u1_struct_0(A_358)) | ~l1_orders_2(A_358))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.69/2.20  tff(c_1315, plain, (![C_421, B_424, A_425, C_422, A_423]: (r1_orders_2(A_423, '#skF_2'(A_425, B_424, C_421), C_422) | ~m1_subset_1('#skF_2'(A_425, B_424, C_421), u1_struct_0(A_423)) | ~r2_lattice3(A_423, B_424, C_422) | ~m1_subset_1(C_422, u1_struct_0(A_423)) | ~l1_orders_2(A_423) | r2_lattice3(A_425, B_424, C_421) | ~m1_subset_1(C_421, u1_struct_0(A_425)) | ~l1_orders_2(A_425))), inference(resolution, [status(thm)], [c_24, c_1126])).
% 5.69/2.20  tff(c_1321, plain, (![A_425, B_424, C_421, C_422]: (r1_orders_2('#skF_3', '#skF_2'(A_425, B_424, C_421), C_422) | ~m1_subset_1('#skF_2'(A_425, B_424, C_421), u1_struct_0('#skF_4')) | ~r2_lattice3('#skF_3', B_424, C_422) | ~m1_subset_1(C_422, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | r2_lattice3(A_425, B_424, C_421) | ~m1_subset_1(C_421, u1_struct_0(A_425)) | ~l1_orders_2(A_425))), inference(superposition, [status(thm), theory('equality')], [c_973, c_1315])).
% 5.69/2.20  tff(c_1373, plain, (![A_434, B_435, C_436, C_437]: (r1_orders_2('#skF_3', '#skF_2'(A_434, B_435, C_436), C_437) | ~m1_subset_1('#skF_2'(A_434, B_435, C_436), u1_struct_0('#skF_4')) | ~r2_lattice3('#skF_3', B_435, C_437) | ~m1_subset_1(C_437, u1_struct_0('#skF_4')) | r2_lattice3(A_434, B_435, C_436) | ~m1_subset_1(C_436, u1_struct_0(A_434)) | ~l1_orders_2(A_434))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_973, c_1321])).
% 5.69/2.20  tff(c_1378, plain, (![B_34, C_35, C_437]: (r1_orders_2('#skF_3', '#skF_2'('#skF_4', B_34, C_35), C_437) | ~r2_lattice3('#skF_3', B_34, C_437) | ~m1_subset_1(C_437, u1_struct_0('#skF_4')) | r2_lattice3('#skF_4', B_34, C_35) | ~m1_subset_1(C_35, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_1373])).
% 5.69/2.20  tff(c_1403, plain, (![B_441, C_442, C_443]: (r1_orders_2('#skF_3', '#skF_2'('#skF_4', B_441, C_442), C_443) | ~r2_lattice3('#skF_3', B_441, C_443) | ~m1_subset_1(C_443, u1_struct_0('#skF_4')) | r2_lattice3('#skF_4', B_441, C_442) | ~m1_subset_1(C_442, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1378])).
% 5.69/2.20  tff(c_1025, plain, (![B_339, C_340, A_341]: (r2_hidden(k4_tarski(B_339, C_340), u1_orders_2(A_341)) | ~r1_orders_2(A_341, B_339, C_340) | ~m1_subset_1(C_340, u1_struct_0(A_341)) | ~m1_subset_1(B_339, u1_struct_0(A_341)) | ~l1_orders_2(A_341))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.69/2.20  tff(c_1028, plain, (![B_339, C_340]: (r2_hidden(k4_tarski(B_339, C_340), u1_orders_2('#skF_4')) | ~r1_orders_2('#skF_3', B_339, C_340) | ~m1_subset_1(C_340, u1_struct_0('#skF_3')) | ~m1_subset_1(B_339, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_924, c_1025])).
% 5.69/2.20  tff(c_1030, plain, (![B_339, C_340]: (r2_hidden(k4_tarski(B_339, C_340), u1_orders_2('#skF_4')) | ~r1_orders_2('#skF_3', B_339, C_340) | ~m1_subset_1(C_340, u1_struct_0('#skF_4')) | ~m1_subset_1(B_339, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_973, c_973, c_1028])).
% 5.69/2.20  tff(c_1032, plain, (![A_344, B_345, C_346]: (r1_orders_2(A_344, B_345, C_346) | ~r2_hidden(k4_tarski(B_345, C_346), u1_orders_2(A_344)) | ~m1_subset_1(C_346, u1_struct_0(A_344)) | ~m1_subset_1(B_345, u1_struct_0(A_344)) | ~l1_orders_2(A_344))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.69/2.20  tff(c_1035, plain, (![B_339, C_340]: (r1_orders_2('#skF_4', B_339, C_340) | ~l1_orders_2('#skF_4') | ~r1_orders_2('#skF_3', B_339, C_340) | ~m1_subset_1(C_340, u1_struct_0('#skF_4')) | ~m1_subset_1(B_339, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1030, c_1032])).
% 5.69/2.20  tff(c_1044, plain, (![B_339, C_340]: (r1_orders_2('#skF_4', B_339, C_340) | ~r1_orders_2('#skF_3', B_339, C_340) | ~m1_subset_1(C_340, u1_struct_0('#skF_4')) | ~m1_subset_1(B_339, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1035])).
% 5.69/2.20  tff(c_1579, plain, (![B_498, C_499, C_500]: (r1_orders_2('#skF_4', '#skF_2'('#skF_4', B_498, C_499), C_500) | ~m1_subset_1('#skF_2'('#skF_4', B_498, C_499), u1_struct_0('#skF_4')) | ~r2_lattice3('#skF_3', B_498, C_500) | ~m1_subset_1(C_500, u1_struct_0('#skF_4')) | r2_lattice3('#skF_4', B_498, C_499) | ~m1_subset_1(C_499, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1403, c_1044])).
% 5.69/2.20  tff(c_1582, plain, (![B_34, C_35, C_500]: (r1_orders_2('#skF_4', '#skF_2'('#skF_4', B_34, C_35), C_500) | ~r2_lattice3('#skF_3', B_34, C_500) | ~m1_subset_1(C_500, u1_struct_0('#skF_4')) | r2_lattice3('#skF_4', B_34, C_35) | ~m1_subset_1(C_35, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_1579])).
% 5.69/2.20  tff(c_1627, plain, (![B_511, C_512, C_513]: (r1_orders_2('#skF_4', '#skF_2'('#skF_4', B_511, C_512), C_513) | ~r2_lattice3('#skF_3', B_511, C_513) | ~m1_subset_1(C_513, u1_struct_0('#skF_4')) | r2_lattice3('#skF_4', B_511, C_512) | ~m1_subset_1(C_512, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1582])).
% 5.69/2.20  tff(c_22, plain, (![A_27, B_34, C_35]: (~r1_orders_2(A_27, '#skF_2'(A_27, B_34, C_35), C_35) | r2_lattice3(A_27, B_34, C_35) | ~m1_subset_1(C_35, u1_struct_0(A_27)) | ~l1_orders_2(A_27))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.69/2.20  tff(c_1635, plain, (![B_511, C_513]: (~l1_orders_2('#skF_4') | ~r2_lattice3('#skF_3', B_511, C_513) | r2_lattice3('#skF_4', B_511, C_513) | ~m1_subset_1(C_513, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1627, c_22])).
% 5.69/2.20  tff(c_1647, plain, (![B_514, C_515]: (~r2_lattice3('#skF_3', B_514, C_515) | r2_lattice3('#skF_4', B_514, C_515) | ~m1_subset_1(C_515, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1635])).
% 5.69/2.20  tff(c_1651, plain, (r2_lattice3('#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_892, c_1647])).
% 5.69/2.20  tff(c_1657, plain, (r2_lattice3('#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_1651])).
% 5.69/2.20  tff(c_1659, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_1657])).
% 5.69/2.20  tff(c_1660, plain, (r2_lattice3('#skF_3', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_46])).
% 5.69/2.20  tff(c_1672, plain, (![C_517, A_518, D_519, B_520]: (C_517=A_518 | g1_orders_2(C_517, D_519)!=g1_orders_2(A_518, B_520) | ~m1_subset_1(B_520, k1_zfmisc_1(k2_zfmisc_1(A_518, A_518))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.69/2.20  tff(c_1692, plain, (![A_543, B_544]: (u1_struct_0('#skF_3')=A_543 | g1_orders_2(u1_struct_0('#skF_4'), u1_orders_2('#skF_4'))!=g1_orders_2(A_543, B_544) | ~m1_subset_1(B_544, k1_zfmisc_1(k2_zfmisc_1(A_543, A_543))))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1672])).
% 5.69/2.20  tff(c_1696, plain, (![A_8]: (u1_struct_0(A_8)=u1_struct_0('#skF_3') | g1_orders_2(u1_struct_0(A_8), u1_orders_2(A_8))!=g1_orders_2(u1_struct_0('#skF_4'), u1_orders_2('#skF_4')) | ~l1_orders_2(A_8))), inference(resolution, [status(thm)], [c_6, c_1692])).
% 5.69/2.20  tff(c_1699, plain, (u1_struct_0('#skF_3')=u1_struct_0('#skF_4') | ~l1_orders_2('#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_1696])).
% 5.69/2.20  tff(c_1701, plain, (u1_struct_0('#skF_3')=u1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1699])).
% 5.69/2.20  tff(c_1891, plain, (![A_573, D_574, C_575, B_576]: (r1_orders_2(A_573, D_574, C_575) | ~r2_hidden(D_574, B_576) | ~m1_subset_1(D_574, u1_struct_0(A_573)) | ~r2_lattice3(A_573, B_576, C_575) | ~m1_subset_1(C_575, u1_struct_0(A_573)) | ~l1_orders_2(A_573))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.69/2.20  tff(c_2274, plain, (![B_696, A_697, C_694, A_695, C_693]: (r1_orders_2(A_695, '#skF_2'(A_697, B_696, C_694), C_693) | ~m1_subset_1('#skF_2'(A_697, B_696, C_694), u1_struct_0(A_695)) | ~r2_lattice3(A_695, B_696, C_693) | ~m1_subset_1(C_693, u1_struct_0(A_695)) | ~l1_orders_2(A_695) | r2_lattice3(A_697, B_696, C_694) | ~m1_subset_1(C_694, u1_struct_0(A_697)) | ~l1_orders_2(A_697))), inference(resolution, [status(thm)], [c_24, c_1891])).
% 5.69/2.20  tff(c_2278, plain, (![A_697, B_696, C_694, C_693]: (r1_orders_2('#skF_3', '#skF_2'(A_697, B_696, C_694), C_693) | ~m1_subset_1('#skF_2'(A_697, B_696, C_694), u1_struct_0('#skF_4')) | ~r2_lattice3('#skF_3', B_696, C_693) | ~m1_subset_1(C_693, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | r2_lattice3(A_697, B_696, C_694) | ~m1_subset_1(C_694, u1_struct_0(A_697)) | ~l1_orders_2(A_697))), inference(superposition, [status(thm), theory('equality')], [c_1701, c_2274])).
% 5.69/2.20  tff(c_2422, plain, (![A_736, B_737, C_738, C_739]: (r1_orders_2('#skF_3', '#skF_2'(A_736, B_737, C_738), C_739) | ~m1_subset_1('#skF_2'(A_736, B_737, C_738), u1_struct_0('#skF_4')) | ~r2_lattice3('#skF_3', B_737, C_739) | ~m1_subset_1(C_739, u1_struct_0('#skF_4')) | r2_lattice3(A_736, B_737, C_738) | ~m1_subset_1(C_738, u1_struct_0(A_736)) | ~l1_orders_2(A_736))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1701, c_2278])).
% 5.69/2.20  tff(c_2427, plain, (![B_34, C_35, C_739]: (r1_orders_2('#skF_3', '#skF_2'('#skF_4', B_34, C_35), C_739) | ~r2_lattice3('#skF_3', B_34, C_739) | ~m1_subset_1(C_739, u1_struct_0('#skF_4')) | r2_lattice3('#skF_4', B_34, C_35) | ~m1_subset_1(C_35, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_2422])).
% 5.69/2.20  tff(c_2452, plain, (![B_743, C_744, C_745]: (r1_orders_2('#skF_3', '#skF_2'('#skF_4', B_743, C_744), C_745) | ~r2_lattice3('#skF_3', B_743, C_745) | ~m1_subset_1(C_745, u1_struct_0('#skF_4')) | r2_lattice3('#skF_4', B_743, C_744) | ~m1_subset_1(C_744, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2427])).
% 5.69/2.20  tff(c_1729, plain, (m1_subset_1(u1_orders_2('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~l1_orders_2('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1701, c_6])).
% 5.69/2.20  tff(c_1740, plain, (m1_subset_1(u1_orders_2('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1701, c_1729])).
% 5.69/2.20  tff(c_1717, plain, (g1_orders_2(u1_struct_0('#skF_4'), u1_orders_2('#skF_3'))=g1_orders_2(u1_struct_0('#skF_4'), u1_orders_2('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1701, c_34])).
% 5.69/2.20  tff(c_8, plain, (![D_14, B_10, C_13, A_9]: (D_14=B_10 | g1_orders_2(C_13, D_14)!=g1_orders_2(A_9, B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(k2_zfmisc_1(A_9, A_9))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.69/2.20  tff(c_1754, plain, (![D_14, C_13]: (u1_orders_2('#skF_3')=D_14 | g1_orders_2(u1_struct_0('#skF_4'), u1_orders_2('#skF_4'))!=g1_orders_2(C_13, D_14) | ~m1_subset_1(u1_orders_2('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_4')))))), inference(superposition, [status(thm), theory('equality')], [c_1717, c_8])).
% 5.69/2.20  tff(c_1762, plain, (![D_14, C_13]: (u1_orders_2('#skF_3')=D_14 | g1_orders_2(u1_struct_0('#skF_4'), u1_orders_2('#skF_4'))!=g1_orders_2(C_13, D_14))), inference(demodulation, [status(thm), theory('equality')], [c_1740, c_1754])).
% 5.69/2.20  tff(c_1768, plain, (u1_orders_2('#skF_3')=u1_orders_2('#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_1762])).
% 5.69/2.20  tff(c_1809, plain, (![B_561, C_562, A_563]: (r2_hidden(k4_tarski(B_561, C_562), u1_orders_2(A_563)) | ~r1_orders_2(A_563, B_561, C_562) | ~m1_subset_1(C_562, u1_struct_0(A_563)) | ~m1_subset_1(B_561, u1_struct_0(A_563)) | ~l1_orders_2(A_563))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.69/2.20  tff(c_1815, plain, (![B_561, C_562]: (r2_hidden(k4_tarski(B_561, C_562), u1_orders_2('#skF_4')) | ~r1_orders_2('#skF_3', B_561, C_562) | ~m1_subset_1(C_562, u1_struct_0('#skF_3')) | ~m1_subset_1(B_561, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1768, c_1809])).
% 5.69/2.20  tff(c_1879, plain, (![B_569, C_570]: (r2_hidden(k4_tarski(B_569, C_570), u1_orders_2('#skF_4')) | ~r1_orders_2('#skF_3', B_569, C_570) | ~m1_subset_1(C_570, u1_struct_0('#skF_4')) | ~m1_subset_1(B_569, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1701, c_1701, c_1815])).
% 5.69/2.20  tff(c_2, plain, (![A_1, B_5, C_7]: (r1_orders_2(A_1, B_5, C_7) | ~r2_hidden(k4_tarski(B_5, C_7), u1_orders_2(A_1)) | ~m1_subset_1(C_7, u1_struct_0(A_1)) | ~m1_subset_1(B_5, u1_struct_0(A_1)) | ~l1_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.69/2.20  tff(c_1885, plain, (![B_569, C_570]: (r1_orders_2('#skF_4', B_569, C_570) | ~l1_orders_2('#skF_4') | ~r1_orders_2('#skF_3', B_569, C_570) | ~m1_subset_1(C_570, u1_struct_0('#skF_4')) | ~m1_subset_1(B_569, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1879, c_2])).
% 5.69/2.20  tff(c_1889, plain, (![B_569, C_570]: (r1_orders_2('#skF_4', B_569, C_570) | ~r1_orders_2('#skF_3', B_569, C_570) | ~m1_subset_1(C_570, u1_struct_0('#skF_4')) | ~m1_subset_1(B_569, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1885])).
% 5.69/2.20  tff(c_2516, plain, (![B_762, C_763, C_764]: (r1_orders_2('#skF_4', '#skF_2'('#skF_4', B_762, C_763), C_764) | ~m1_subset_1('#skF_2'('#skF_4', B_762, C_763), u1_struct_0('#skF_4')) | ~r2_lattice3('#skF_3', B_762, C_764) | ~m1_subset_1(C_764, u1_struct_0('#skF_4')) | r2_lattice3('#skF_4', B_762, C_763) | ~m1_subset_1(C_763, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_2452, c_1889])).
% 5.69/2.20  tff(c_2519, plain, (![B_34, C_35, C_764]: (r1_orders_2('#skF_4', '#skF_2'('#skF_4', B_34, C_35), C_764) | ~r2_lattice3('#skF_3', B_34, C_764) | ~m1_subset_1(C_764, u1_struct_0('#skF_4')) | r2_lattice3('#skF_4', B_34, C_35) | ~m1_subset_1(C_35, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_2516])).
% 5.69/2.20  tff(c_2523, plain, (![B_765, C_766, C_767]: (r1_orders_2('#skF_4', '#skF_2'('#skF_4', B_765, C_766), C_767) | ~r2_lattice3('#skF_3', B_765, C_767) | ~m1_subset_1(C_767, u1_struct_0('#skF_4')) | r2_lattice3('#skF_4', B_765, C_766) | ~m1_subset_1(C_766, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2519])).
% 5.69/2.20  tff(c_2531, plain, (![B_765, C_767]: (~l1_orders_2('#skF_4') | ~r2_lattice3('#skF_3', B_765, C_767) | r2_lattice3('#skF_4', B_765, C_767) | ~m1_subset_1(C_767, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_2523, c_22])).
% 5.69/2.20  tff(c_2544, plain, (![B_772, C_773]: (~r2_lattice3('#skF_3', B_772, C_773) | r2_lattice3('#skF_4', B_772, C_773) | ~m1_subset_1(C_773, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2531])).
% 5.69/2.20  tff(c_2548, plain, (r2_lattice3('#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_1660, c_2544])).
% 5.69/2.20  tff(c_2554, plain, (r2_lattice3('#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_2548])).
% 5.69/2.20  tff(c_2556, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_2554])).
% 5.69/2.20  tff(c_2557, plain, (r1_lattice3('#skF_3', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_48])).
% 5.69/2.20  tff(c_2572, plain, (![C_775, A_776, D_777, B_778]: (C_775=A_776 | g1_orders_2(C_775, D_777)!=g1_orders_2(A_776, B_778) | ~m1_subset_1(B_778, k1_zfmisc_1(k2_zfmisc_1(A_776, A_776))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.69/2.20  tff(c_2592, plain, (![A_801, B_802]: (u1_struct_0('#skF_3')=A_801 | g1_orders_2(u1_struct_0('#skF_4'), u1_orders_2('#skF_4'))!=g1_orders_2(A_801, B_802) | ~m1_subset_1(B_802, k1_zfmisc_1(k2_zfmisc_1(A_801, A_801))))), inference(superposition, [status(thm), theory('equality')], [c_34, c_2572])).
% 5.69/2.20  tff(c_2596, plain, (![A_8]: (u1_struct_0(A_8)=u1_struct_0('#skF_3') | g1_orders_2(u1_struct_0(A_8), u1_orders_2(A_8))!=g1_orders_2(u1_struct_0('#skF_4'), u1_orders_2('#skF_4')) | ~l1_orders_2(A_8))), inference(resolution, [status(thm)], [c_6, c_2592])).
% 5.69/2.20  tff(c_2599, plain, (u1_struct_0('#skF_3')=u1_struct_0('#skF_4') | ~l1_orders_2('#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_2596])).
% 5.69/2.20  tff(c_2601, plain, (u1_struct_0('#skF_3')=u1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2599])).
% 5.69/2.20  tff(c_2804, plain, (![A_835, C_836, D_837, B_838]: (r1_orders_2(A_835, C_836, D_837) | ~r2_hidden(D_837, B_838) | ~m1_subset_1(D_837, u1_struct_0(A_835)) | ~r1_lattice3(A_835, B_838, C_836) | ~m1_subset_1(C_836, u1_struct_0(A_835)) | ~l1_orders_2(A_835))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.69/2.20  tff(c_2997, plain, (![A_894, B_892, A_891, C_893, C_890]: (r1_orders_2(A_891, C_893, '#skF_1'(A_894, B_892, C_890)) | ~m1_subset_1('#skF_1'(A_894, B_892, C_890), u1_struct_0(A_891)) | ~r1_lattice3(A_891, B_892, C_893) | ~m1_subset_1(C_893, u1_struct_0(A_891)) | ~l1_orders_2(A_891) | r1_lattice3(A_894, B_892, C_890) | ~m1_subset_1(C_890, u1_struct_0(A_894)) | ~l1_orders_2(A_894))), inference(resolution, [status(thm)], [c_16, c_2804])).
% 5.69/2.20  tff(c_3001, plain, (![C_893, A_894, B_892, C_890]: (r1_orders_2('#skF_3', C_893, '#skF_1'(A_894, B_892, C_890)) | ~m1_subset_1('#skF_1'(A_894, B_892, C_890), u1_struct_0('#skF_4')) | ~r1_lattice3('#skF_3', B_892, C_893) | ~m1_subset_1(C_893, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | r1_lattice3(A_894, B_892, C_890) | ~m1_subset_1(C_890, u1_struct_0(A_894)) | ~l1_orders_2(A_894))), inference(superposition, [status(thm), theory('equality')], [c_2601, c_2997])).
% 5.69/2.20  tff(c_3046, plain, (![C_901, A_902, B_903, C_904]: (r1_orders_2('#skF_3', C_901, '#skF_1'(A_902, B_903, C_904)) | ~m1_subset_1('#skF_1'(A_902, B_903, C_904), u1_struct_0('#skF_4')) | ~r1_lattice3('#skF_3', B_903, C_901) | ~m1_subset_1(C_901, u1_struct_0('#skF_4')) | r1_lattice3(A_902, B_903, C_904) | ~m1_subset_1(C_904, u1_struct_0(A_902)) | ~l1_orders_2(A_902))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2601, c_3001])).
% 5.69/2.20  tff(c_3051, plain, (![C_901, B_22, C_23]: (r1_orders_2('#skF_3', C_901, '#skF_1'('#skF_4', B_22, C_23)) | ~r1_lattice3('#skF_3', B_22, C_901) | ~m1_subset_1(C_901, u1_struct_0('#skF_4')) | r1_lattice3('#skF_4', B_22, C_23) | ~m1_subset_1(C_23, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_3046])).
% 5.69/2.20  tff(c_3093, plain, (![C_925, B_926, C_927]: (r1_orders_2('#skF_3', C_925, '#skF_1'('#skF_4', B_926, C_927)) | ~r1_lattice3('#skF_3', B_926, C_925) | ~m1_subset_1(C_925, u1_struct_0('#skF_4')) | r1_lattice3('#skF_4', B_926, C_927) | ~m1_subset_1(C_927, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3051])).
% 5.69/2.20  tff(c_2629, plain, (m1_subset_1(u1_orders_2('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~l1_orders_2('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2601, c_6])).
% 5.69/2.20  tff(c_2640, plain, (m1_subset_1(u1_orders_2('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2601, c_2629])).
% 5.69/2.20  tff(c_2617, plain, (g1_orders_2(u1_struct_0('#skF_4'), u1_orders_2('#skF_3'))=g1_orders_2(u1_struct_0('#skF_4'), u1_orders_2('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2601, c_34])).
% 5.69/2.20  tff(c_2654, plain, (![D_14, C_13]: (u1_orders_2('#skF_3')=D_14 | g1_orders_2(u1_struct_0('#skF_4'), u1_orders_2('#skF_4'))!=g1_orders_2(C_13, D_14) | ~m1_subset_1(u1_orders_2('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_4')))))), inference(superposition, [status(thm), theory('equality')], [c_2617, c_8])).
% 5.69/2.20  tff(c_2662, plain, (![D_14, C_13]: (u1_orders_2('#skF_3')=D_14 | g1_orders_2(u1_struct_0('#skF_4'), u1_orders_2('#skF_4'))!=g1_orders_2(C_13, D_14))), inference(demodulation, [status(thm), theory('equality')], [c_2640, c_2654])).
% 5.69/2.20  tff(c_2668, plain, (u1_orders_2('#skF_3')=u1_orders_2('#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_2662])).
% 5.69/2.20  tff(c_2709, plain, (![B_819, C_820, A_821]: (r2_hidden(k4_tarski(B_819, C_820), u1_orders_2(A_821)) | ~r1_orders_2(A_821, B_819, C_820) | ~m1_subset_1(C_820, u1_struct_0(A_821)) | ~m1_subset_1(B_819, u1_struct_0(A_821)) | ~l1_orders_2(A_821))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.69/2.20  tff(c_2715, plain, (![B_819, C_820]: (r2_hidden(k4_tarski(B_819, C_820), u1_orders_2('#skF_4')) | ~r1_orders_2('#skF_3', B_819, C_820) | ~m1_subset_1(C_820, u1_struct_0('#skF_3')) | ~m1_subset_1(B_819, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2668, c_2709])).
% 5.69/2.20  tff(c_2779, plain, (![B_827, C_828]: (r2_hidden(k4_tarski(B_827, C_828), u1_orders_2('#skF_4')) | ~r1_orders_2('#skF_3', B_827, C_828) | ~m1_subset_1(C_828, u1_struct_0('#skF_4')) | ~m1_subset_1(B_827, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2601, c_2601, c_2715])).
% 5.69/2.20  tff(c_2785, plain, (![B_827, C_828]: (r1_orders_2('#skF_4', B_827, C_828) | ~l1_orders_2('#skF_4') | ~r1_orders_2('#skF_3', B_827, C_828) | ~m1_subset_1(C_828, u1_struct_0('#skF_4')) | ~m1_subset_1(B_827, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_2779, c_2])).
% 5.69/2.20  tff(c_2789, plain, (![B_827, C_828]: (r1_orders_2('#skF_4', B_827, C_828) | ~r1_orders_2('#skF_3', B_827, C_828) | ~m1_subset_1(C_828, u1_struct_0('#skF_4')) | ~m1_subset_1(B_827, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2785])).
% 5.69/2.20  tff(c_3175, plain, (![C_949, B_950, C_951]: (r1_orders_2('#skF_4', C_949, '#skF_1'('#skF_4', B_950, C_951)) | ~m1_subset_1('#skF_1'('#skF_4', B_950, C_951), u1_struct_0('#skF_4')) | ~r1_lattice3('#skF_3', B_950, C_949) | ~m1_subset_1(C_949, u1_struct_0('#skF_4')) | r1_lattice3('#skF_4', B_950, C_951) | ~m1_subset_1(C_951, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_3093, c_2789])).
% 5.69/2.20  tff(c_3178, plain, (![C_949, B_22, C_23]: (r1_orders_2('#skF_4', C_949, '#skF_1'('#skF_4', B_22, C_23)) | ~r1_lattice3('#skF_3', B_22, C_949) | ~m1_subset_1(C_949, u1_struct_0('#skF_4')) | r1_lattice3('#skF_4', B_22, C_23) | ~m1_subset_1(C_23, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_3175])).
% 5.69/2.20  tff(c_3182, plain, (![C_952, B_953, C_954]: (r1_orders_2('#skF_4', C_952, '#skF_1'('#skF_4', B_953, C_954)) | ~r1_lattice3('#skF_3', B_953, C_952) | ~m1_subset_1(C_952, u1_struct_0('#skF_4')) | r1_lattice3('#skF_4', B_953, C_954) | ~m1_subset_1(C_954, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3178])).
% 5.69/2.20  tff(c_3190, plain, (![B_953, C_954]: (~l1_orders_2('#skF_4') | ~r1_lattice3('#skF_3', B_953, C_954) | r1_lattice3('#skF_4', B_953, C_954) | ~m1_subset_1(C_954, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_3182, c_14])).
% 5.69/2.20  tff(c_3210, plain, (![B_960, C_961]: (~r1_lattice3('#skF_3', B_960, C_961) | r1_lattice3('#skF_4', B_960, C_961) | ~m1_subset_1(C_961, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3190])).
% 5.69/2.20  tff(c_3222, plain, (r1_lattice3('#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_2557, c_3210])).
% 5.69/2.20  tff(c_3232, plain, (r1_lattice3('#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_3222])).
% 5.69/2.20  tff(c_3234, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2559, c_3232])).
% 5.69/2.20  tff(c_3236, plain, (r1_lattice3('#skF_4', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_49])).
% 5.69/2.20  tff(c_2558, plain, (r2_lattice3('#skF_4', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_48])).
% 5.69/2.20  tff(c_40, plain, (~r2_lattice3('#skF_4', '#skF_5', '#skF_7') | ~r1_lattice3('#skF_4', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.69/2.20  tff(c_50, plain, (~r2_lattice3('#skF_4', '#skF_5', '#skF_6') | ~r1_lattice3('#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_40])).
% 5.69/2.20  tff(c_3239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3236, c_2558, c_50])).
% 5.69/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.69/2.20  
% 5.69/2.20  Inference rules
% 5.69/2.20  ----------------------
% 5.69/2.20  #Ref     : 24
% 5.69/2.20  #Sup     : 576
% 5.69/2.20  #Fact    : 0
% 5.69/2.20  #Define  : 0
% 5.69/2.20  #Split   : 8
% 5.69/2.20  #Chain   : 0
% 5.69/2.20  #Close   : 0
% 5.69/2.20  
% 5.69/2.20  Ordering : KBO
% 5.69/2.20  
% 5.69/2.20  Simplification rules
% 5.69/2.20  ----------------------
% 5.69/2.20  #Subsume      : 63
% 5.69/2.20  #Demod        : 606
% 5.69/2.20  #Tautology    : 154
% 5.69/2.20  #SimpNegUnit  : 4
% 5.69/2.20  #BackRed      : 24
% 5.69/2.20  
% 5.69/2.20  #Partial instantiations: 0
% 5.69/2.20  #Strategies tried      : 1
% 5.69/2.20  
% 5.69/2.20  Timing (in seconds)
% 5.69/2.20  ----------------------
% 5.69/2.21  Preprocessing        : 0.40
% 5.69/2.21  Parsing              : 0.17
% 5.69/2.21  CNF conversion       : 0.05
% 5.69/2.21  Main loop            : 1.01
% 5.69/2.21  Inferencing          : 0.43
% 5.69/2.21  Reduction            : 0.28
% 5.69/2.21  Demodulation         : 0.19
% 5.69/2.21  BG Simplification    : 0.04
% 5.69/2.21  Subsumption          : 0.19
% 5.69/2.21  Abstraction          : 0.04
% 5.69/2.21  MUC search           : 0.00
% 5.69/2.21  Cooper               : 0.00
% 5.69/2.21  Total                : 1.47
% 5.69/2.21  Index Insertion      : 0.00
% 5.69/2.21  Index Deletion       : 0.00
% 5.69/2.21  Index Matching       : 0.00
% 5.69/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
