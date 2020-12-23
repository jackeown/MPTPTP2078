%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1549+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:02 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 971 expanded)
%              Number of leaves         :   29 ( 322 expanded)
%              Depth                    :   26
%              Number of atoms          :  306 (2614 expanded)
%              Number of equality atoms :   61 (1124 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_yellow_0 > r1_yellow_0 > m1_subset_1 > l1_orders_2 > k2_zfmisc_1 > k2_yellow_0 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k2_yellow_0,type,(
    k2_yellow_0: ( $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

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

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_142,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( l1_orders_2(B)
           => ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(B),u1_orders_2(B))
             => ! [C] :
                  ( r2_yellow_0(A,C)
                 => k2_yellow_0(A,C) = k2_yellow_0(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_0)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(f_75,axiom,(
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

tff(f_46,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k2_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_0)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_yellow_0(A,B)
           => ( C = k2_yellow_0(A,B)
            <=> ( r1_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r1_lattice3(A,B,D)
                     => r1_orders_2(A,D,C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_yellow_0)).

tff(f_129,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow_0)).

tff(f_106,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_0)).

tff(c_32,plain,(
    k2_yellow_0('#skF_2','#skF_4') != k2_yellow_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_38,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_40,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_14,plain,(
    ! [A_15] :
      ( m1_subset_1(u1_orders_2(A_15),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_15),u1_struct_0(A_15))))
      | ~ l1_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_36,plain,(
    g1_orders_2(u1_struct_0('#skF_2'),u1_orders_2('#skF_2')) = g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_51,plain,(
    ! [D_118,B_119,C_120,A_121] :
      ( D_118 = B_119
      | g1_orders_2(C_120,D_118) != g1_orders_2(A_121,B_119)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(k2_zfmisc_1(A_121,A_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_65,plain,(
    ! [B_126,A_127] :
      ( u1_orders_2('#skF_2') = B_126
      | g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_3')) != g1_orders_2(A_127,B_126)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(k2_zfmisc_1(A_127,A_127))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_51])).

tff(c_69,plain,(
    ! [A_15] :
      ( u1_orders_2(A_15) = u1_orders_2('#skF_2')
      | g1_orders_2(u1_struct_0(A_15),u1_orders_2(A_15)) != g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_3'))
      | ~ l1_orders_2(A_15) ) ),
    inference(resolution,[status(thm)],[c_14,c_65])).

tff(c_72,plain,
    ( u1_orders_2('#skF_2') = u1_orders_2('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_69])).

tff(c_74,plain,(
    u1_orders_2('#skF_2') = u1_orders_2('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_72])).

tff(c_89,plain,
    ( m1_subset_1(u1_orders_2('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2'))))
    | ~ l1_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_14])).

tff(c_93,plain,(
    m1_subset_1(u1_orders_2('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_89])).

tff(c_85,plain,(
    g1_orders_2(u1_struct_0('#skF_2'),u1_orders_2('#skF_3')) = g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_36])).

tff(c_18,plain,(
    ! [C_20,A_16,D_21,B_17] :
      ( C_20 = A_16
      | g1_orders_2(C_20,D_21) != g1_orders_2(A_16,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k2_zfmisc_1(A_16,A_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_99,plain,(
    ! [C_20,D_21] :
      ( u1_struct_0('#skF_2') = C_20
      | g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_3')) != g1_orders_2(C_20,D_21)
      | ~ m1_subset_1(u1_orders_2('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_18])).

tff(c_107,plain,(
    ! [C_20,D_21] :
      ( u1_struct_0('#skF_2') = C_20
      | g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_3')) != g1_orders_2(C_20,D_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_99])).

tff(c_113,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_107])).

tff(c_34,plain,(
    r2_yellow_0('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_172,plain,(
    ! [B_144,C_145,A_146] :
      ( r2_yellow_0(B_144,C_145)
      | ~ r2_yellow_0(A_146,C_145)
      | g1_orders_2(u1_struct_0(B_144),u1_orders_2(B_144)) != g1_orders_2(u1_struct_0(A_146),u1_orders_2(A_146))
      | ~ l1_orders_2(B_144)
      | ~ l1_orders_2(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_174,plain,(
    ! [B_144] :
      ( r2_yellow_0(B_144,'#skF_4')
      | g1_orders_2(u1_struct_0(B_144),u1_orders_2(B_144)) != g1_orders_2(u1_struct_0('#skF_2'),u1_orders_2('#skF_2'))
      | ~ l1_orders_2(B_144)
      | ~ l1_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_172])).

tff(c_177,plain,(
    ! [B_144] :
      ( r2_yellow_0(B_144,'#skF_4')
      | g1_orders_2(u1_struct_0(B_144),u1_orders_2(B_144)) != g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_3'))
      | ~ l1_orders_2(B_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_113,c_74,c_174])).

tff(c_180,plain,
    ( r2_yellow_0('#skF_3','#skF_4')
    | ~ l1_orders_2('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_177])).

tff(c_182,plain,(
    r2_yellow_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_180])).

tff(c_12,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k2_yellow_0(A_13,B_14),u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_138,plain,(
    ! [B_14] :
      ( m1_subset_1(k2_yellow_0('#skF_2',B_14),u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_12])).

tff(c_148,plain,(
    ! [B_14] : m1_subset_1(k2_yellow_0('#skF_2',B_14),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_138])).

tff(c_10,plain,(
    ! [A_1,B_8] :
      ( r1_lattice3(A_1,B_8,k2_yellow_0(A_1,B_8))
      | ~ r2_yellow_0(A_1,B_8)
      | ~ m1_subset_1(k2_yellow_0(A_1,B_8),u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_129,plain,(
    ! [B_8] :
      ( r1_lattice3('#skF_2',B_8,k2_yellow_0('#skF_2',B_8))
      | ~ r2_yellow_0('#skF_2',B_8)
      | ~ m1_subset_1(k2_yellow_0('#skF_2',B_8),u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_10])).

tff(c_142,plain,(
    ! [B_8] :
      ( r1_lattice3('#skF_2',B_8,k2_yellow_0('#skF_2',B_8))
      | ~ r2_yellow_0('#skF_2',B_8)
      | ~ m1_subset_1(k2_yellow_0('#skF_2',B_8),u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_129])).

tff(c_167,plain,(
    ! [B_8] :
      ( r1_lattice3('#skF_2',B_8,k2_yellow_0('#skF_2',B_8))
      | ~ r2_yellow_0('#skF_2',B_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_142])).

tff(c_233,plain,(
    ! [B_171,C_172,E_173,A_174] :
      ( r1_lattice3(B_171,C_172,E_173)
      | ~ r1_lattice3(A_174,C_172,E_173)
      | ~ m1_subset_1(E_173,u1_struct_0(B_171))
      | ~ m1_subset_1(E_173,u1_struct_0(A_174))
      | g1_orders_2(u1_struct_0(B_171),u1_orders_2(B_171)) != g1_orders_2(u1_struct_0(A_174),u1_orders_2(A_174))
      | ~ l1_orders_2(B_171)
      | ~ l1_orders_2(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_237,plain,(
    ! [B_171,B_8] :
      ( r1_lattice3(B_171,B_8,k2_yellow_0('#skF_2',B_8))
      | ~ m1_subset_1(k2_yellow_0('#skF_2',B_8),u1_struct_0(B_171))
      | ~ m1_subset_1(k2_yellow_0('#skF_2',B_8),u1_struct_0('#skF_2'))
      | g1_orders_2(u1_struct_0(B_171),u1_orders_2(B_171)) != g1_orders_2(u1_struct_0('#skF_2'),u1_orders_2('#skF_2'))
      | ~ l1_orders_2(B_171)
      | ~ l1_orders_2('#skF_2')
      | ~ r2_yellow_0('#skF_2',B_8) ) ),
    inference(resolution,[status(thm)],[c_167,c_233])).

tff(c_245,plain,(
    ! [B_175,B_176] :
      ( r1_lattice3(B_175,B_176,k2_yellow_0('#skF_2',B_176))
      | ~ m1_subset_1(k2_yellow_0('#skF_2',B_176),u1_struct_0(B_175))
      | g1_orders_2(u1_struct_0(B_175),u1_orders_2(B_175)) != g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_3'))
      | ~ l1_orders_2(B_175)
      | ~ r2_yellow_0('#skF_2',B_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_113,c_74,c_148,c_113,c_237])).

tff(c_247,plain,(
    ! [B_14] :
      ( r1_lattice3('#skF_3',B_14,k2_yellow_0('#skF_2',B_14))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_yellow_0('#skF_2',B_14) ) ),
    inference(resolution,[status(thm)],[c_148,c_245])).

tff(c_255,plain,(
    ! [B_14] :
      ( r1_lattice3('#skF_3',B_14,k2_yellow_0('#skF_2',B_14))
      | ~ r2_yellow_0('#skF_2',B_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_247])).

tff(c_6,plain,(
    ! [A_1,B_8,C_9] :
      ( m1_subset_1('#skF_1'(A_1,B_8,C_9),u1_struct_0(A_1))
      | k2_yellow_0(A_1,B_8) = C_9
      | ~ r1_lattice3(A_1,B_8,C_9)
      | ~ r2_yellow_0(A_1,B_8)
      | ~ m1_subset_1(C_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_1,B_8,C_9] :
      ( r1_lattice3(A_1,B_8,'#skF_1'(A_1,B_8,C_9))
      | k2_yellow_0(A_1,B_8) = C_9
      | ~ r1_lattice3(A_1,B_8,C_9)
      | ~ r2_yellow_0(A_1,B_8)
      | ~ m1_subset_1(C_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_347,plain,(
    ! [B_199,B_200,A_201,C_202] :
      ( r1_lattice3(B_199,B_200,'#skF_1'(A_201,B_200,C_202))
      | ~ m1_subset_1('#skF_1'(A_201,B_200,C_202),u1_struct_0(B_199))
      | ~ m1_subset_1('#skF_1'(A_201,B_200,C_202),u1_struct_0(A_201))
      | g1_orders_2(u1_struct_0(B_199),u1_orders_2(B_199)) != g1_orders_2(u1_struct_0(A_201),u1_orders_2(A_201))
      | ~ l1_orders_2(B_199)
      | k2_yellow_0(A_201,B_200) = C_202
      | ~ r1_lattice3(A_201,B_200,C_202)
      | ~ r2_yellow_0(A_201,B_200)
      | ~ m1_subset_1(C_202,u1_struct_0(A_201))
      | ~ l1_orders_2(A_201) ) ),
    inference(resolution,[status(thm)],[c_4,c_233])).

tff(c_353,plain,(
    ! [B_200,A_201,C_202] :
      ( r1_lattice3('#skF_2',B_200,'#skF_1'(A_201,B_200,C_202))
      | ~ m1_subset_1('#skF_1'(A_201,B_200,C_202),u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_1'(A_201,B_200,C_202),u1_struct_0(A_201))
      | g1_orders_2(u1_struct_0(A_201),u1_orders_2(A_201)) != g1_orders_2(u1_struct_0('#skF_2'),u1_orders_2('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | k2_yellow_0(A_201,B_200) = C_202
      | ~ r1_lattice3(A_201,B_200,C_202)
      | ~ r2_yellow_0(A_201,B_200)
      | ~ m1_subset_1(C_202,u1_struct_0(A_201))
      | ~ l1_orders_2(A_201) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_347])).

tff(c_386,plain,(
    ! [B_210,A_211,C_212] :
      ( r1_lattice3('#skF_2',B_210,'#skF_1'(A_211,B_210,C_212))
      | ~ m1_subset_1('#skF_1'(A_211,B_210,C_212),u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_1'(A_211,B_210,C_212),u1_struct_0(A_211))
      | g1_orders_2(u1_struct_0(A_211),u1_orders_2(A_211)) != g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_3'))
      | k2_yellow_0(A_211,B_210) = C_212
      | ~ r1_lattice3(A_211,B_210,C_212)
      | ~ r2_yellow_0(A_211,B_210)
      | ~ m1_subset_1(C_212,u1_struct_0(A_211))
      | ~ l1_orders_2(A_211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_113,c_74,c_353])).

tff(c_391,plain,(
    ! [B_8,C_9] :
      ( r1_lattice3('#skF_2',B_8,'#skF_1'('#skF_3',B_8,C_9))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_8,C_9),u1_struct_0('#skF_3'))
      | k2_yellow_0('#skF_3',B_8) = C_9
      | ~ r1_lattice3('#skF_3',B_8,C_9)
      | ~ r2_yellow_0('#skF_3',B_8)
      | ~ m1_subset_1(C_9,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_6,c_386])).

tff(c_428,plain,(
    ! [B_219,C_220] :
      ( r1_lattice3('#skF_2',B_219,'#skF_1'('#skF_3',B_219,C_220))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_219,C_220),u1_struct_0('#skF_3'))
      | k2_yellow_0('#skF_3',B_219) = C_220
      | ~ r1_lattice3('#skF_3',B_219,C_220)
      | ~ r2_yellow_0('#skF_3',B_219)
      | ~ m1_subset_1(C_220,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_391])).

tff(c_431,plain,(
    ! [B_8,C_9] :
      ( r1_lattice3('#skF_2',B_8,'#skF_1'('#skF_3',B_8,C_9))
      | k2_yellow_0('#skF_3',B_8) = C_9
      | ~ r1_lattice3('#skF_3',B_8,C_9)
      | ~ r2_yellow_0('#skF_3',B_8)
      | ~ m1_subset_1(C_9,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_6,c_428])).

tff(c_434,plain,(
    ! [B_8,C_9] :
      ( r1_lattice3('#skF_2',B_8,'#skF_1'('#skF_3',B_8,C_9))
      | k2_yellow_0('#skF_3',B_8) = C_9
      | ~ r1_lattice3('#skF_3',B_8,C_9)
      | ~ r2_yellow_0('#skF_3',B_8)
      | ~ m1_subset_1(C_9,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_431])).

tff(c_210,plain,(
    ! [A_159,D_160,B_161] :
      ( r1_orders_2(A_159,D_160,k2_yellow_0(A_159,B_161))
      | ~ r1_lattice3(A_159,B_161,D_160)
      | ~ m1_subset_1(D_160,u1_struct_0(A_159))
      | ~ r2_yellow_0(A_159,B_161)
      | ~ m1_subset_1(k2_yellow_0(A_159,B_161),u1_struct_0(A_159))
      | ~ l1_orders_2(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_212,plain,(
    ! [D_160,B_161] :
      ( r1_orders_2('#skF_2',D_160,k2_yellow_0('#skF_2',B_161))
      | ~ r1_lattice3('#skF_2',B_161,D_160)
      | ~ m1_subset_1(D_160,u1_struct_0('#skF_2'))
      | ~ r2_yellow_0('#skF_2',B_161)
      | ~ m1_subset_1(k2_yellow_0('#skF_2',B_161),u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_210])).

tff(c_216,plain,(
    ! [D_160,B_161] :
      ( r1_orders_2('#skF_2',D_160,k2_yellow_0('#skF_2',B_161))
      | ~ r1_lattice3('#skF_2',B_161,D_160)
      | ~ m1_subset_1(D_160,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_2',B_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_148,c_113,c_212])).

tff(c_267,plain,(
    ! [B_178,E_179,F_180,A_181] :
      ( r1_orders_2(B_178,E_179,F_180)
      | ~ r1_orders_2(A_181,E_179,F_180)
      | ~ m1_subset_1(F_180,u1_struct_0(B_178))
      | ~ m1_subset_1(E_179,u1_struct_0(B_178))
      | ~ m1_subset_1(F_180,u1_struct_0(A_181))
      | ~ m1_subset_1(E_179,u1_struct_0(A_181))
      | g1_orders_2(u1_struct_0(B_178),u1_orders_2(B_178)) != g1_orders_2(u1_struct_0(A_181),u1_orders_2(A_181))
      | ~ l1_orders_2(B_178)
      | ~ l1_orders_2(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_271,plain,(
    ! [B_178,D_160,B_161] :
      ( r1_orders_2(B_178,D_160,k2_yellow_0('#skF_2',B_161))
      | ~ m1_subset_1(k2_yellow_0('#skF_2',B_161),u1_struct_0(B_178))
      | ~ m1_subset_1(D_160,u1_struct_0(B_178))
      | ~ m1_subset_1(k2_yellow_0('#skF_2',B_161),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_160,u1_struct_0('#skF_2'))
      | g1_orders_2(u1_struct_0(B_178),u1_orders_2(B_178)) != g1_orders_2(u1_struct_0('#skF_2'),u1_orders_2('#skF_2'))
      | ~ l1_orders_2(B_178)
      | ~ l1_orders_2('#skF_2')
      | ~ r1_lattice3('#skF_2',B_161,D_160)
      | ~ m1_subset_1(D_160,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_2',B_161) ) ),
    inference(resolution,[status(thm)],[c_216,c_267])).

tff(c_370,plain,(
    ! [B_207,D_208,B_209] :
      ( r1_orders_2(B_207,D_208,k2_yellow_0('#skF_2',B_209))
      | ~ m1_subset_1(k2_yellow_0('#skF_2',B_209),u1_struct_0(B_207))
      | ~ m1_subset_1(D_208,u1_struct_0(B_207))
      | g1_orders_2(u1_struct_0(B_207),u1_orders_2(B_207)) != g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_3'))
      | ~ l1_orders_2(B_207)
      | ~ r1_lattice3('#skF_2',B_209,D_208)
      | ~ m1_subset_1(D_208,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_2',B_209) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_113,c_74,c_113,c_148,c_113,c_271])).

tff(c_372,plain,(
    ! [D_208,B_14] :
      ( r1_orders_2('#skF_3',D_208,k2_yellow_0('#skF_2',B_14))
      | ~ l1_orders_2('#skF_3')
      | ~ r1_lattice3('#skF_2',B_14,D_208)
      | ~ m1_subset_1(D_208,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_2',B_14) ) ),
    inference(resolution,[status(thm)],[c_148,c_370])).

tff(c_398,plain,(
    ! [D_213,B_214] :
      ( r1_orders_2('#skF_3',D_213,k2_yellow_0('#skF_2',B_214))
      | ~ r1_lattice3('#skF_2',B_214,D_213)
      | ~ m1_subset_1(D_213,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_2',B_214) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_372])).

tff(c_2,plain,(
    ! [A_1,B_8,C_9] :
      ( ~ r1_orders_2(A_1,'#skF_1'(A_1,B_8,C_9),C_9)
      | k2_yellow_0(A_1,B_8) = C_9
      | ~ r1_lattice3(A_1,B_8,C_9)
      | ~ r2_yellow_0(A_1,B_8)
      | ~ m1_subset_1(C_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_404,plain,(
    ! [B_8,B_214] :
      ( k2_yellow_0('#skF_3',B_8) = k2_yellow_0('#skF_2',B_214)
      | ~ r1_lattice3('#skF_3',B_8,k2_yellow_0('#skF_2',B_214))
      | ~ r2_yellow_0('#skF_3',B_8)
      | ~ m1_subset_1(k2_yellow_0('#skF_2',B_214),u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r1_lattice3('#skF_2',B_214,'#skF_1'('#skF_3',B_8,k2_yellow_0('#skF_2',B_214)))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_8,k2_yellow_0('#skF_2',B_214)),u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_2',B_214) ) ),
    inference(resolution,[status(thm)],[c_398,c_2])).

tff(c_454,plain,(
    ! [B_226,B_227] :
      ( k2_yellow_0('#skF_3',B_226) = k2_yellow_0('#skF_2',B_227)
      | ~ r1_lattice3('#skF_3',B_226,k2_yellow_0('#skF_2',B_227))
      | ~ r2_yellow_0('#skF_3',B_226)
      | ~ r1_lattice3('#skF_2',B_227,'#skF_1'('#skF_3',B_226,k2_yellow_0('#skF_2',B_227)))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_226,k2_yellow_0('#skF_2',B_227)),u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_2',B_227) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_148,c_404])).

tff(c_457,plain,(
    ! [B_8] :
      ( ~ m1_subset_1('#skF_1'('#skF_3',B_8,k2_yellow_0('#skF_2',B_8)),u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_2',B_8)
      | k2_yellow_0('#skF_2',B_8) = k2_yellow_0('#skF_3',B_8)
      | ~ r1_lattice3('#skF_3',B_8,k2_yellow_0('#skF_2',B_8))
      | ~ r2_yellow_0('#skF_3',B_8)
      | ~ m1_subset_1(k2_yellow_0('#skF_2',B_8),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_434,c_454])).

tff(c_461,plain,(
    ! [B_228] :
      ( ~ m1_subset_1('#skF_1'('#skF_3',B_228,k2_yellow_0('#skF_2',B_228)),u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_2',B_228)
      | k2_yellow_0('#skF_2',B_228) = k2_yellow_0('#skF_3',B_228)
      | ~ r1_lattice3('#skF_3',B_228,k2_yellow_0('#skF_2',B_228))
      | ~ r2_yellow_0('#skF_3',B_228) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_457])).

tff(c_465,plain,(
    ! [B_8] :
      ( ~ r2_yellow_0('#skF_2',B_8)
      | k2_yellow_0('#skF_2',B_8) = k2_yellow_0('#skF_3',B_8)
      | ~ r1_lattice3('#skF_3',B_8,k2_yellow_0('#skF_2',B_8))
      | ~ r2_yellow_0('#skF_3',B_8)
      | ~ m1_subset_1(k2_yellow_0('#skF_2',B_8),u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_6,c_461])).

tff(c_469,plain,(
    ! [B_229] :
      ( ~ r2_yellow_0('#skF_2',B_229)
      | k2_yellow_0('#skF_2',B_229) = k2_yellow_0('#skF_3',B_229)
      | ~ r1_lattice3('#skF_3',B_229,k2_yellow_0('#skF_2',B_229))
      | ~ r2_yellow_0('#skF_3',B_229) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_148,c_465])).

tff(c_474,plain,(
    ! [B_230] :
      ( k2_yellow_0('#skF_2',B_230) = k2_yellow_0('#skF_3',B_230)
      | ~ r2_yellow_0('#skF_3',B_230)
      | ~ r2_yellow_0('#skF_2',B_230) ) ),
    inference(resolution,[status(thm)],[c_255,c_469])).

tff(c_477,plain,
    ( k2_yellow_0('#skF_2','#skF_4') = k2_yellow_0('#skF_3','#skF_4')
    | ~ r2_yellow_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_474])).

tff(c_480,plain,(
    k2_yellow_0('#skF_2','#skF_4') = k2_yellow_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_477])).

tff(c_482,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_480])).

%------------------------------------------------------------------------------
