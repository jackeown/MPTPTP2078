%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1535+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:01 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 645 expanded)
%              Number of leaves         :   24 ( 220 expanded)
%              Depth                    :   18
%              Number of atoms          :  256 (1935 expanded)
%              Number of equality atoms :   66 ( 561 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_lattice3 > m1_subset_1 > v2_yellow_0 > v1_yellow_0 > l1_orders_2 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff(v2_yellow_0,type,(
    v2_yellow_0: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( l1_orders_2(B)
           => ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(B),u1_orders_2(B))
             => ( ( v1_yellow_0(A)
                 => v1_yellow_0(B) )
                & ( v2_yellow_0(A)
                 => v2_yellow_0(B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_0)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_yellow_0(A)
      <=> ? [B] :
            ( m1_subset_1(B,u1_struct_0(A))
            & r2_lattice3(A,u1_struct_0(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_0)).

tff(f_78,axiom,(
    ! [A] :
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

tff(f_33,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_yellow_0(A)
      <=> ? [B] :
            ( m1_subset_1(B,u1_struct_0(A))
            & r1_lattice3(A,u1_struct_0(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_yellow_0)).

tff(c_30,plain,
    ( ~ v1_yellow_0('#skF_4')
    | ~ v2_yellow_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_38,plain,(
    ~ v2_yellow_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_26,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_28,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_36,plain,
    ( v1_yellow_0('#skF_3')
    | v2_yellow_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_37,plain,(
    v2_yellow_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_14,plain,(
    ! [A_9] :
      ( m1_subset_1(u1_orders_2(A_9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9),u1_struct_0(A_9))))
      | ~ l1_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_3')) = g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_63,plain,(
    ! [D_45,B_46,C_47,A_48] :
      ( D_45 = B_46
      | g1_orders_2(C_47,D_45) != g1_orders_2(A_48,B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(k2_zfmisc_1(A_48,A_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_77,plain,(
    ! [B_53,A_54] :
      ( u1_orders_2('#skF_3') = B_53
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(A_54,B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(k2_zfmisc_1(A_54,A_54))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_63])).

tff(c_81,plain,(
    ! [A_9] :
      ( u1_orders_2(A_9) = u1_orders_2('#skF_3')
      | g1_orders_2(u1_struct_0(A_9),u1_orders_2(A_9)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(A_9) ) ),
    inference(resolution,[status(thm)],[c_14,c_77])).

tff(c_89,plain,
    ( u1_orders_2('#skF_3') = u1_orders_2('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_81])).

tff(c_91,plain,(
    u1_orders_2('#skF_3') = u1_orders_2('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_89])).

tff(c_106,plain,
    ( m1_subset_1(u1_orders_2('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))))
    | ~ l1_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_14])).

tff(c_110,plain,(
    m1_subset_1(u1_orders_2('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_106])).

tff(c_102,plain,(
    g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_4')) = g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_24])).

tff(c_18,plain,(
    ! [C_14,A_10,D_15,B_11] :
      ( C_14 = A_10
      | g1_orders_2(C_14,D_15) != g1_orders_2(A_10,B_11)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(k2_zfmisc_1(A_10,A_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_121,plain,(
    ! [C_14,D_15] :
      ( u1_struct_0('#skF_3') = C_14
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(C_14,D_15)
      | ~ m1_subset_1(u1_orders_2('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_18])).

tff(c_129,plain,(
    ! [C_14,D_15] :
      ( u1_struct_0('#skF_3') = C_14
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(C_14,D_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_121])).

tff(c_135,plain,(
    u1_struct_0('#skF_3') = u1_struct_0('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_129])).

tff(c_12,plain,(
    ! [A_5] :
      ( m1_subset_1('#skF_2'(A_5),u1_struct_0(A_5))
      | ~ v2_yellow_0(A_5)
      | ~ l1_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_170,plain,
    ( m1_subset_1('#skF_2'('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v2_yellow_0('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_12])).

tff(c_189,plain,(
    m1_subset_1('#skF_2'('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_37,c_170])).

tff(c_10,plain,(
    ! [A_5] :
      ( r2_lattice3(A_5,u1_struct_0(A_5),'#skF_2'(A_5))
      | ~ v2_yellow_0(A_5)
      | ~ l1_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_167,plain,
    ( r2_lattice3('#skF_3',u1_struct_0('#skF_4'),'#skF_2'('#skF_3'))
    | ~ v2_yellow_0('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_10])).

tff(c_187,plain,(
    r2_lattice3('#skF_3',u1_struct_0('#skF_4'),'#skF_2'('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_37,c_167])).

tff(c_196,plain,(
    ! [B_64,C_65,E_66,A_67] :
      ( r2_lattice3(B_64,C_65,E_66)
      | ~ r2_lattice3(A_67,C_65,E_66)
      | ~ m1_subset_1(E_66,u1_struct_0(B_64))
      | ~ m1_subset_1(E_66,u1_struct_0(A_67))
      | g1_orders_2(u1_struct_0(B_64),u1_orders_2(B_64)) != g1_orders_2(u1_struct_0(A_67),u1_orders_2(A_67))
      | ~ l1_orders_2(B_64)
      | ~ l1_orders_2(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_198,plain,(
    ! [B_64] :
      ( r2_lattice3(B_64,u1_struct_0('#skF_4'),'#skF_2'('#skF_3'))
      | ~ m1_subset_1('#skF_2'('#skF_3'),u1_struct_0(B_64))
      | ~ m1_subset_1('#skF_2'('#skF_3'),u1_struct_0('#skF_3'))
      | g1_orders_2(u1_struct_0(B_64),u1_orders_2(B_64)) != g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_3'))
      | ~ l1_orders_2(B_64)
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_187,c_196])).

tff(c_203,plain,(
    ! [B_64] :
      ( r2_lattice3(B_64,u1_struct_0('#skF_4'),'#skF_2'('#skF_3'))
      | ~ m1_subset_1('#skF_2'('#skF_3'),u1_struct_0(B_64))
      | g1_orders_2(u1_struct_0(B_64),u1_orders_2(B_64)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(B_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_135,c_91,c_189,c_135,c_198])).

tff(c_223,plain,
    ( r2_lattice3('#skF_4',u1_struct_0('#skF_4'),'#skF_2'('#skF_3'))
    | ~ m1_subset_1('#skF_2'('#skF_3'),u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_203])).

tff(c_225,plain,(
    r2_lattice3('#skF_4',u1_struct_0('#skF_4'),'#skF_2'('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_189,c_223])).

tff(c_8,plain,(
    ! [A_5,B_8] :
      ( v2_yellow_0(A_5)
      | ~ r2_lattice3(A_5,u1_struct_0(A_5),B_8)
      | ~ m1_subset_1(B_8,u1_struct_0(A_5))
      | ~ l1_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_239,plain,
    ( v2_yellow_0('#skF_4')
    | ~ m1_subset_1('#skF_2'('#skF_3'),u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_225,c_8])).

tff(c_245,plain,(
    v2_yellow_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_189,c_239])).

tff(c_247,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_245])).

tff(c_248,plain,(
    ~ v1_yellow_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_249,plain,(
    v2_yellow_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_32,plain,
    ( v1_yellow_0('#skF_3')
    | ~ v2_yellow_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_251,plain,(
    v1_yellow_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_32])).

tff(c_276,plain,(
    ! [C_83,A_84,D_85,B_86] :
      ( C_83 = A_84
      | g1_orders_2(C_83,D_85) != g1_orders_2(A_84,B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(k2_zfmisc_1(A_84,A_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_290,plain,(
    ! [A_91,B_92] :
      ( u1_struct_0('#skF_3') = A_91
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(A_91,B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k2_zfmisc_1(A_91,A_91))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_276])).

tff(c_294,plain,(
    ! [A_9] :
      ( u1_struct_0(A_9) = u1_struct_0('#skF_3')
      | g1_orders_2(u1_struct_0(A_9),u1_orders_2(A_9)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(A_9) ) ),
    inference(resolution,[status(thm)],[c_14,c_290])).

tff(c_297,plain,
    ( u1_struct_0('#skF_3') = u1_struct_0('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_294])).

tff(c_299,plain,(
    u1_struct_0('#skF_3') = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_297])).

tff(c_6,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),u1_struct_0(A_1))
      | ~ v1_yellow_0(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_335,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_yellow_0('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_6])).

tff(c_353,plain,(
    m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_251,c_335])).

tff(c_323,plain,
    ( m1_subset_1(u1_orders_2('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ l1_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_14])).

tff(c_345,plain,(
    m1_subset_1(u1_orders_2('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_299,c_323])).

tff(c_310,plain,(
    g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_3')) = g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_24])).

tff(c_16,plain,(
    ! [D_15,B_11,C_14,A_10] :
      ( D_15 = B_11
      | g1_orders_2(C_14,D_15) != g1_orders_2(A_10,B_11)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(k2_zfmisc_1(A_10,A_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_369,plain,(
    ! [D_15,C_14] :
      ( u1_orders_2('#skF_3') = D_15
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(C_14,D_15)
      | ~ m1_subset_1(u1_orders_2('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_16])).

tff(c_377,plain,(
    ! [D_15,C_14] :
      ( u1_orders_2('#skF_3') = D_15
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(C_14,D_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_369])).

tff(c_383,plain,(
    u1_orders_2('#skF_3') = u1_orders_2('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_377])).

tff(c_4,plain,(
    ! [A_1] :
      ( r1_lattice3(A_1,u1_struct_0(A_1),'#skF_1'(A_1))
      | ~ v1_yellow_0(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_329,plain,
    ( r1_lattice3('#skF_3',u1_struct_0('#skF_4'),'#skF_1'('#skF_3'))
    | ~ v1_yellow_0('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_4])).

tff(c_349,plain,(
    r1_lattice3('#skF_3',u1_struct_0('#skF_4'),'#skF_1'('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_251,c_329])).

tff(c_355,plain,(
    ! [B_94,C_95,E_96,A_97] :
      ( r1_lattice3(B_94,C_95,E_96)
      | ~ r1_lattice3(A_97,C_95,E_96)
      | ~ m1_subset_1(E_96,u1_struct_0(B_94))
      | ~ m1_subset_1(E_96,u1_struct_0(A_97))
      | g1_orders_2(u1_struct_0(B_94),u1_orders_2(B_94)) != g1_orders_2(u1_struct_0(A_97),u1_orders_2(A_97))
      | ~ l1_orders_2(B_94)
      | ~ l1_orders_2(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_357,plain,(
    ! [B_94] :
      ( r1_lattice3(B_94,u1_struct_0('#skF_4'),'#skF_1'('#skF_3'))
      | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0(B_94))
      | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_3'))
      | g1_orders_2(u1_struct_0(B_94),u1_orders_2(B_94)) != g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_3'))
      | ~ l1_orders_2(B_94)
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_349,c_355])).

tff(c_362,plain,(
    ! [B_94] :
      ( r1_lattice3(B_94,u1_struct_0('#skF_4'),'#skF_1'('#skF_3'))
      | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0(B_94))
      | g1_orders_2(u1_struct_0(B_94),u1_orders_2(B_94)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_3'))
      | ~ l1_orders_2(B_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_299,c_353,c_299,c_357])).

tff(c_453,plain,(
    ! [B_94] :
      ( r1_lattice3(B_94,u1_struct_0('#skF_4'),'#skF_1'('#skF_3'))
      | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0(B_94))
      | g1_orders_2(u1_struct_0(B_94),u1_orders_2(B_94)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(B_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_362])).

tff(c_456,plain,
    ( r1_lattice3('#skF_4',u1_struct_0('#skF_4'),'#skF_1'('#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_453])).

tff(c_458,plain,(
    r1_lattice3('#skF_4',u1_struct_0('#skF_4'),'#skF_1'('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_353,c_456])).

tff(c_2,plain,(
    ! [A_1,B_4] :
      ( v1_yellow_0(A_1)
      | ~ r1_lattice3(A_1,u1_struct_0(A_1),B_4)
      | ~ m1_subset_1(B_4,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_492,plain,
    ( v1_yellow_0('#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_458,c_2])).

tff(c_498,plain,(
    v1_yellow_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_353,c_492])).

tff(c_500,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_248,c_498])).

tff(c_502,plain,(
    ~ v2_yellow_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_34,plain,
    ( ~ v1_yellow_0('#skF_4')
    | v2_yellow_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_505,plain,(
    ~ v1_yellow_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_502,c_34])).

tff(c_501,plain,(
    v1_yellow_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_529,plain,(
    ! [C_121,A_122,D_123,B_124] :
      ( C_121 = A_122
      | g1_orders_2(C_121,D_123) != g1_orders_2(A_122,B_124)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(k2_zfmisc_1(A_122,A_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_543,plain,(
    ! [A_129,B_130] :
      ( u1_struct_0('#skF_3') = A_129
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(A_129,B_130)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(k2_zfmisc_1(A_129,A_129))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_529])).

tff(c_547,plain,(
    ! [A_9] :
      ( u1_struct_0(A_9) = u1_struct_0('#skF_3')
      | g1_orders_2(u1_struct_0(A_9),u1_orders_2(A_9)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(A_9) ) ),
    inference(resolution,[status(thm)],[c_14,c_543])).

tff(c_550,plain,
    ( u1_struct_0('#skF_3') = u1_struct_0('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_547])).

tff(c_552,plain,(
    u1_struct_0('#skF_3') = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_550])).

tff(c_592,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_yellow_0('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_552,c_6])).

tff(c_611,plain,(
    m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_501,c_592])).

tff(c_538,plain,(
    ! [D_125,B_126,C_127,A_128] :
      ( D_125 = B_126
      | g1_orders_2(C_127,D_125) != g1_orders_2(A_128,B_126)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(k2_zfmisc_1(A_128,A_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_639,plain,(
    ! [B_138,A_139] :
      ( u1_orders_2('#skF_3') = B_138
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(A_139,B_138)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(k2_zfmisc_1(A_139,A_139))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_538])).

tff(c_650,plain,(
    ! [A_9] :
      ( u1_orders_2(A_9) = u1_orders_2('#skF_3')
      | g1_orders_2(u1_struct_0(A_9),u1_orders_2(A_9)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(A_9) ) ),
    inference(resolution,[status(thm)],[c_14,c_639])).

tff(c_662,plain,
    ( u1_orders_2('#skF_3') = u1_orders_2('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_650])).

tff(c_664,plain,(
    u1_orders_2('#skF_3') = u1_orders_2('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_662])).

tff(c_651,plain,(
    ! [B_140,C_141,E_142,A_143] :
      ( r1_lattice3(B_140,C_141,E_142)
      | ~ r1_lattice3(A_143,C_141,E_142)
      | ~ m1_subset_1(E_142,u1_struct_0(B_140))
      | ~ m1_subset_1(E_142,u1_struct_0(A_143))
      | g1_orders_2(u1_struct_0(B_140),u1_orders_2(B_140)) != g1_orders_2(u1_struct_0(A_143),u1_orders_2(A_143))
      | ~ l1_orders_2(B_140)
      | ~ l1_orders_2(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_728,plain,(
    ! [B_150,A_151] :
      ( r1_lattice3(B_150,u1_struct_0(A_151),'#skF_1'(A_151))
      | ~ m1_subset_1('#skF_1'(A_151),u1_struct_0(B_150))
      | ~ m1_subset_1('#skF_1'(A_151),u1_struct_0(A_151))
      | g1_orders_2(u1_struct_0(B_150),u1_orders_2(B_150)) != g1_orders_2(u1_struct_0(A_151),u1_orders_2(A_151))
      | ~ l1_orders_2(B_150)
      | ~ v1_yellow_0(A_151)
      | ~ l1_orders_2(A_151) ) ),
    inference(resolution,[status(thm)],[c_4,c_651])).

tff(c_732,plain,(
    ! [B_150] :
      ( r1_lattice3(B_150,u1_struct_0('#skF_3'),'#skF_1'('#skF_3'))
      | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0(B_150))
      | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_3'))
      | g1_orders_2(u1_struct_0(B_150),u1_orders_2(B_150)) != g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(B_150)
      | ~ v1_yellow_0('#skF_3')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_664,c_728])).

tff(c_740,plain,(
    ! [B_150] :
      ( r1_lattice3(B_150,u1_struct_0('#skF_4'),'#skF_1'('#skF_3'))
      | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0(B_150))
      | g1_orders_2(u1_struct_0(B_150),u1_orders_2(B_150)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(B_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_501,c_552,c_611,c_552,c_552,c_732])).

tff(c_749,plain,
    ( r1_lattice3('#skF_4',u1_struct_0('#skF_4'),'#skF_1'('#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_740])).

tff(c_751,plain,(
    r1_lattice3('#skF_4',u1_struct_0('#skF_4'),'#skF_1'('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_611,c_749])).

tff(c_765,plain,
    ( v1_yellow_0('#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_751,c_2])).

tff(c_771,plain,(
    v1_yellow_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_611,c_765])).

tff(c_773,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_505,c_771])).

%------------------------------------------------------------------------------
