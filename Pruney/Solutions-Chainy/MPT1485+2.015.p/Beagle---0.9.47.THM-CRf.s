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
% DateTime   : Thu Dec  3 10:24:42 EST 2020

% Result     : Theorem 6.62s
% Output     : CNFRefutation 6.62s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 234 expanded)
%              Number of leaves         :   29 ( 104 expanded)
%              Depth                    :   12
%              Number of atoms          :  199 ( 949 expanded)
%              Number of equality atoms :   21 ( 102 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k13_lattice3,type,(
    k13_lattice3: ( $i * $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k10_lattice3,type,(
    k10_lattice3: ( $i * $i * $i ) > $i )).

tff(k11_lattice3,type,(
    k11_lattice3: ( $i * $i * $i ) > $i )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k12_lattice3,type,(
    k12_lattice3: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_165,negated_conjecture,(
    ~ ! [A] :
        ( ( v3_orders_2(A)
          & v5_orders_2(A)
          & v1_lattice3(A)
          & v2_lattice3(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k12_lattice3(A,B,k13_lattice3(A,B,C)) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_lattice3)).

tff(f_37,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,B,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_146,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k13_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k13_lattice3)).

tff(f_134,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_89,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( D = k10_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,B,D)
                      & r1_orders_2(A,C,D)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,B,E)
                              & r1_orders_2(A,C,E) )
                           => r1_orders_2(A,D,E) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l26_lattice3)).

tff(f_122,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( D = k11_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,D,B)
                      & r1_orders_2(A,D,C)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,E,B)
                              & r1_orders_2(A,E,C) )
                           => r1_orders_2(A,E,D) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l28_lattice3)).

tff(c_46,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_50,plain,(
    v1_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_54,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_56,plain,(
    ! [A_111,B_112] :
      ( r1_orders_2(A_111,B_112,B_112)
      | ~ m1_subset_1(B_112,u1_struct_0(A_111))
      | ~ l1_orders_2(A_111)
      | ~ v3_orders_2(A_111)
      | v2_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_58,plain,
    ( r1_orders_2('#skF_3','#skF_5','#skF_5')
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_56])).

tff(c_63,plain,
    ( r1_orders_2('#skF_3','#skF_5','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_46,c_58])).

tff(c_67,plain,(
    v2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_4,plain,(
    ! [A_4] :
      ( ~ v2_struct_0(A_4)
      | ~ v1_lattice3(A_4)
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_70,plain,
    ( ~ v1_lattice3('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_67,c_4])).

tff(c_74,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_50,c_70])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_52,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_48,plain,(
    v2_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_82,plain,(
    ! [A_116,B_117,C_118] :
      ( k13_lattice3(A_116,B_117,C_118) = k10_lattice3(A_116,B_117,C_118)
      | ~ m1_subset_1(C_118,u1_struct_0(A_116))
      | ~ m1_subset_1(B_117,u1_struct_0(A_116))
      | ~ l1_orders_2(A_116)
      | ~ v1_lattice3(A_116)
      | ~ v5_orders_2(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_86,plain,(
    ! [B_117] :
      ( k13_lattice3('#skF_3',B_117,'#skF_5') = k10_lattice3('#skF_3',B_117,'#skF_5')
      | ~ m1_subset_1(B_117,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_82])).

tff(c_96,plain,(
    ! [B_119] :
      ( k13_lattice3('#skF_3',B_119,'#skF_5') = k10_lattice3('#skF_3',B_119,'#skF_5')
      | ~ m1_subset_1(B_119,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_86])).

tff(c_111,plain,(
    k13_lattice3('#skF_3','#skF_4','#skF_5') = k10_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_96])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( m1_subset_1(k13_lattice3(A_5,B_6,C_7),u1_struct_0(A_5))
      | ~ m1_subset_1(C_7,u1_struct_0(A_5))
      | ~ m1_subset_1(B_6,u1_struct_0(A_5))
      | ~ l1_orders_2(A_5)
      | ~ v1_lattice3(A_5)
      | ~ v5_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_125,plain,
    ( m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v1_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_6])).

tff(c_129,plain,(
    m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_44,c_42,c_125])).

tff(c_161,plain,(
    ! [A_120,B_121,C_122] :
      ( k12_lattice3(A_120,B_121,C_122) = k11_lattice3(A_120,B_121,C_122)
      | ~ m1_subset_1(C_122,u1_struct_0(A_120))
      | ~ m1_subset_1(B_121,u1_struct_0(A_120))
      | ~ l1_orders_2(A_120)
      | ~ v2_lattice3(A_120)
      | ~ v5_orders_2(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_163,plain,(
    ! [B_121] :
      ( k12_lattice3('#skF_3',B_121,k10_lattice3('#skF_3','#skF_4','#skF_5')) = k11_lattice3('#skF_3',B_121,k10_lattice3('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(B_121,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_129,c_161])).

tff(c_1205,plain,(
    ! [B_159] :
      ( k12_lattice3('#skF_3',B_159,k10_lattice3('#skF_3','#skF_4','#skF_5')) = k11_lattice3('#skF_3',B_159,k10_lattice3('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(B_159,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_46,c_163])).

tff(c_1296,plain,(
    k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) = k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_44,c_1205])).

tff(c_40,plain,(
    k12_lattice3('#skF_3','#skF_4',k13_lattice3('#skF_3','#skF_4','#skF_5')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_121,plain,(
    k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_40])).

tff(c_1301,plain,(
    k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1296,c_121])).

tff(c_60,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_56])).

tff(c_66,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_46,c_60])).

tff(c_77,plain,(
    r1_orders_2('#skF_3','#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_66])).

tff(c_719,plain,(
    ! [A_135,B_136,C_137] :
      ( r1_orders_2(A_135,B_136,k10_lattice3(A_135,B_136,C_137))
      | ~ m1_subset_1(k10_lattice3(A_135,B_136,C_137),u1_struct_0(A_135))
      | ~ m1_subset_1(C_137,u1_struct_0(A_135))
      | ~ m1_subset_1(B_136,u1_struct_0(A_135))
      | ~ l1_orders_2(A_135)
      | ~ v1_lattice3(A_135)
      | ~ v5_orders_2(A_135)
      | v2_struct_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_739,plain,
    ( r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v1_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_129,c_719])).

tff(c_780,plain,
    ( r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_44,c_42,c_739])).

tff(c_781,plain,(
    r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_780])).

tff(c_26,plain,(
    ! [A_54,B_78,C_90,D_96] :
      ( r1_orders_2(A_54,'#skF_2'(A_54,B_78,C_90,D_96),B_78)
      | k11_lattice3(A_54,B_78,C_90) = D_96
      | ~ r1_orders_2(A_54,D_96,C_90)
      | ~ r1_orders_2(A_54,D_96,B_78)
      | ~ m1_subset_1(D_96,u1_struct_0(A_54))
      | ~ m1_subset_1(C_90,u1_struct_0(A_54))
      | ~ m1_subset_1(B_78,u1_struct_0(A_54))
      | ~ l1_orders_2(A_54)
      | ~ v2_lattice3(A_54)
      | ~ v5_orders_2(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1463,plain,(
    ! [A_161,B_162,C_163,D_164] :
      ( ~ r1_orders_2(A_161,'#skF_2'(A_161,B_162,C_163,D_164),D_164)
      | k11_lattice3(A_161,B_162,C_163) = D_164
      | ~ r1_orders_2(A_161,D_164,C_163)
      | ~ r1_orders_2(A_161,D_164,B_162)
      | ~ m1_subset_1(D_164,u1_struct_0(A_161))
      | ~ m1_subset_1(C_163,u1_struct_0(A_161))
      | ~ m1_subset_1(B_162,u1_struct_0(A_161))
      | ~ l1_orders_2(A_161)
      | ~ v2_lattice3(A_161)
      | ~ v5_orders_2(A_161)
      | v2_struct_0(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_3763,plain,(
    ! [A_200,B_201,C_202] :
      ( k11_lattice3(A_200,B_201,C_202) = B_201
      | ~ r1_orders_2(A_200,B_201,C_202)
      | ~ r1_orders_2(A_200,B_201,B_201)
      | ~ m1_subset_1(C_202,u1_struct_0(A_200))
      | ~ m1_subset_1(B_201,u1_struct_0(A_200))
      | ~ l1_orders_2(A_200)
      | ~ v2_lattice3(A_200)
      | ~ v5_orders_2(A_200)
      | v2_struct_0(A_200) ) ),
    inference(resolution,[status(thm)],[c_26,c_1463])).

tff(c_3885,plain,
    ( k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) = '#skF_4'
    | ~ r1_orders_2('#skF_3','#skF_4','#skF_4')
    | ~ m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v2_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_781,c_3763])).

tff(c_4141,plain,
    ( k11_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_46,c_44,c_129,c_77,c_3885])).

tff(c_4143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1301,c_4141])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:40:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.62/2.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.62/2.38  
% 6.62/2.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.62/2.38  %$ r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.62/2.38  
% 6.62/2.38  %Foreground sorts:
% 6.62/2.38  
% 6.62/2.38  
% 6.62/2.38  %Background operators:
% 6.62/2.38  
% 6.62/2.38  
% 6.62/2.38  %Foreground operators:
% 6.62/2.38  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.62/2.38  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 6.62/2.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.62/2.38  tff(k13_lattice3, type, k13_lattice3: ($i * $i * $i) > $i).
% 6.62/2.38  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 6.62/2.38  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 6.62/2.38  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 6.62/2.38  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 6.62/2.38  tff('#skF_5', type, '#skF_5': $i).
% 6.62/2.38  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 6.62/2.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 6.62/2.38  tff('#skF_3', type, '#skF_3': $i).
% 6.62/2.38  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 6.62/2.38  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 6.62/2.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.62/2.38  tff('#skF_4', type, '#skF_4': $i).
% 6.62/2.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.62/2.38  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 6.62/2.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 6.62/2.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.62/2.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.62/2.38  
% 6.62/2.40  tff(f_165, negated_conjecture, ~(![A]: (((((v3_orders_2(A) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k12_lattice3(A, B, k13_lattice3(A, B, C)) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_lattice3)).
% 6.62/2.40  tff(f_37, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_orders_2)).
% 6.62/2.40  tff(f_44, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 6.62/2.40  tff(f_146, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k10_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 6.62/2.40  tff(f_56, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k13_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k13_lattice3)).
% 6.62/2.40  tff(f_134, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 6.62/2.40  tff(f_89, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k10_lattice3(A, B, C)) <=> ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l26_lattice3)).
% 6.62/2.40  tff(f_122, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k11_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l28_lattice3)).
% 6.62/2.40  tff(c_46, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.62/2.40  tff(c_50, plain, (v1_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.62/2.40  tff(c_54, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.62/2.40  tff(c_42, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.62/2.40  tff(c_56, plain, (![A_111, B_112]: (r1_orders_2(A_111, B_112, B_112) | ~m1_subset_1(B_112, u1_struct_0(A_111)) | ~l1_orders_2(A_111) | ~v3_orders_2(A_111) | v2_struct_0(A_111))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.62/2.40  tff(c_58, plain, (r1_orders_2('#skF_3', '#skF_5', '#skF_5') | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_56])).
% 6.62/2.40  tff(c_63, plain, (r1_orders_2('#skF_3', '#skF_5', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_46, c_58])).
% 6.62/2.40  tff(c_67, plain, (v2_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_63])).
% 6.62/2.40  tff(c_4, plain, (![A_4]: (~v2_struct_0(A_4) | ~v1_lattice3(A_4) | ~l1_orders_2(A_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.62/2.40  tff(c_70, plain, (~v1_lattice3('#skF_3') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_67, c_4])).
% 6.62/2.40  tff(c_74, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_50, c_70])).
% 6.62/2.40  tff(c_76, plain, (~v2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_63])).
% 6.62/2.40  tff(c_44, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.62/2.40  tff(c_52, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.62/2.40  tff(c_48, plain, (v2_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.62/2.40  tff(c_82, plain, (![A_116, B_117, C_118]: (k13_lattice3(A_116, B_117, C_118)=k10_lattice3(A_116, B_117, C_118) | ~m1_subset_1(C_118, u1_struct_0(A_116)) | ~m1_subset_1(B_117, u1_struct_0(A_116)) | ~l1_orders_2(A_116) | ~v1_lattice3(A_116) | ~v5_orders_2(A_116))), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.62/2.40  tff(c_86, plain, (![B_117]: (k13_lattice3('#skF_3', B_117, '#skF_5')=k10_lattice3('#skF_3', B_117, '#skF_5') | ~m1_subset_1(B_117, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_82])).
% 6.62/2.40  tff(c_96, plain, (![B_119]: (k13_lattice3('#skF_3', B_119, '#skF_5')=k10_lattice3('#skF_3', B_119, '#skF_5') | ~m1_subset_1(B_119, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_86])).
% 6.62/2.40  tff(c_111, plain, (k13_lattice3('#skF_3', '#skF_4', '#skF_5')=k10_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_96])).
% 6.62/2.40  tff(c_6, plain, (![A_5, B_6, C_7]: (m1_subset_1(k13_lattice3(A_5, B_6, C_7), u1_struct_0(A_5)) | ~m1_subset_1(C_7, u1_struct_0(A_5)) | ~m1_subset_1(B_6, u1_struct_0(A_5)) | ~l1_orders_2(A_5) | ~v1_lattice3(A_5) | ~v5_orders_2(A_5))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.62/2.40  tff(c_125, plain, (m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_111, c_6])).
% 6.62/2.40  tff(c_129, plain, (m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_44, c_42, c_125])).
% 6.62/2.40  tff(c_161, plain, (![A_120, B_121, C_122]: (k12_lattice3(A_120, B_121, C_122)=k11_lattice3(A_120, B_121, C_122) | ~m1_subset_1(C_122, u1_struct_0(A_120)) | ~m1_subset_1(B_121, u1_struct_0(A_120)) | ~l1_orders_2(A_120) | ~v2_lattice3(A_120) | ~v5_orders_2(A_120))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.62/2.40  tff(c_163, plain, (![B_121]: (k12_lattice3('#skF_3', B_121, k10_lattice3('#skF_3', '#skF_4', '#skF_5'))=k11_lattice3('#skF_3', B_121, k10_lattice3('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(B_121, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_129, c_161])).
% 6.62/2.40  tff(c_1205, plain, (![B_159]: (k12_lattice3('#skF_3', B_159, k10_lattice3('#skF_3', '#skF_4', '#skF_5'))=k11_lattice3('#skF_3', B_159, k10_lattice3('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(B_159, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_46, c_163])).
% 6.62/2.40  tff(c_1296, plain, (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))=k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_1205])).
% 6.62/2.40  tff(c_40, plain, (k12_lattice3('#skF_3', '#skF_4', k13_lattice3('#skF_3', '#skF_4', '#skF_5'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.62/2.40  tff(c_121, plain, (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_111, c_40])).
% 6.62/2.40  tff(c_1301, plain, (k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1296, c_121])).
% 6.62/2.40  tff(c_60, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4') | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_56])).
% 6.62/2.40  tff(c_66, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_46, c_60])).
% 6.62/2.40  tff(c_77, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_76, c_66])).
% 6.62/2.40  tff(c_719, plain, (![A_135, B_136, C_137]: (r1_orders_2(A_135, B_136, k10_lattice3(A_135, B_136, C_137)) | ~m1_subset_1(k10_lattice3(A_135, B_136, C_137), u1_struct_0(A_135)) | ~m1_subset_1(C_137, u1_struct_0(A_135)) | ~m1_subset_1(B_136, u1_struct_0(A_135)) | ~l1_orders_2(A_135) | ~v1_lattice3(A_135) | ~v5_orders_2(A_135) | v2_struct_0(A_135))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.62/2.40  tff(c_739, plain, (r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_129, c_719])).
% 6.62/2.40  tff(c_780, plain, (r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_44, c_42, c_739])).
% 6.62/2.40  tff(c_781, plain, (r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_76, c_780])).
% 6.62/2.40  tff(c_26, plain, (![A_54, B_78, C_90, D_96]: (r1_orders_2(A_54, '#skF_2'(A_54, B_78, C_90, D_96), B_78) | k11_lattice3(A_54, B_78, C_90)=D_96 | ~r1_orders_2(A_54, D_96, C_90) | ~r1_orders_2(A_54, D_96, B_78) | ~m1_subset_1(D_96, u1_struct_0(A_54)) | ~m1_subset_1(C_90, u1_struct_0(A_54)) | ~m1_subset_1(B_78, u1_struct_0(A_54)) | ~l1_orders_2(A_54) | ~v2_lattice3(A_54) | ~v5_orders_2(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.62/2.40  tff(c_1463, plain, (![A_161, B_162, C_163, D_164]: (~r1_orders_2(A_161, '#skF_2'(A_161, B_162, C_163, D_164), D_164) | k11_lattice3(A_161, B_162, C_163)=D_164 | ~r1_orders_2(A_161, D_164, C_163) | ~r1_orders_2(A_161, D_164, B_162) | ~m1_subset_1(D_164, u1_struct_0(A_161)) | ~m1_subset_1(C_163, u1_struct_0(A_161)) | ~m1_subset_1(B_162, u1_struct_0(A_161)) | ~l1_orders_2(A_161) | ~v2_lattice3(A_161) | ~v5_orders_2(A_161) | v2_struct_0(A_161))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.62/2.40  tff(c_3763, plain, (![A_200, B_201, C_202]: (k11_lattice3(A_200, B_201, C_202)=B_201 | ~r1_orders_2(A_200, B_201, C_202) | ~r1_orders_2(A_200, B_201, B_201) | ~m1_subset_1(C_202, u1_struct_0(A_200)) | ~m1_subset_1(B_201, u1_struct_0(A_200)) | ~l1_orders_2(A_200) | ~v2_lattice3(A_200) | ~v5_orders_2(A_200) | v2_struct_0(A_200))), inference(resolution, [status(thm)], [c_26, c_1463])).
% 6.62/2.40  tff(c_3885, plain, (k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', '#skF_4') | ~m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_781, c_3763])).
% 6.62/2.40  tff(c_4141, plain, (k11_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_46, c_44, c_129, c_77, c_3885])).
% 6.62/2.40  tff(c_4143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_1301, c_4141])).
% 6.62/2.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.62/2.40  
% 6.62/2.40  Inference rules
% 6.62/2.40  ----------------------
% 6.62/2.40  #Ref     : 0
% 6.62/2.40  #Sup     : 881
% 6.62/2.40  #Fact    : 0
% 6.62/2.40  #Define  : 0
% 6.62/2.40  #Split   : 2
% 6.62/2.40  #Chain   : 0
% 6.62/2.40  #Close   : 0
% 6.62/2.40  
% 6.62/2.40  Ordering : KBO
% 6.62/2.40  
% 6.62/2.40  Simplification rules
% 6.62/2.40  ----------------------
% 6.62/2.40  #Subsume      : 0
% 6.62/2.40  #Demod        : 1954
% 6.62/2.40  #Tautology    : 193
% 6.62/2.40  #SimpNegUnit  : 308
% 6.62/2.40  #BackRed      : 7
% 6.62/2.40  
% 6.62/2.40  #Partial instantiations: 0
% 6.62/2.40  #Strategies tried      : 1
% 6.62/2.40  
% 6.62/2.40  Timing (in seconds)
% 6.62/2.40  ----------------------
% 6.62/2.40  Preprocessing        : 0.34
% 6.62/2.40  Parsing              : 0.17
% 6.62/2.40  CNF conversion       : 0.03
% 6.62/2.40  Main loop            : 1.25
% 6.62/2.40  Inferencing          : 0.35
% 6.62/2.40  Reduction            : 0.52
% 6.62/2.40  Demodulation         : 0.41
% 6.62/2.40  BG Simplification    : 0.04
% 6.62/2.40  Subsumption          : 0.26
% 6.62/2.40  Abstraction          : 0.06
% 6.62/2.40  MUC search           : 0.00
% 6.62/2.40  Cooper               : 0.00
% 6.62/2.40  Total                : 1.62
% 6.62/2.40  Index Insertion      : 0.00
% 6.62/2.40  Index Deletion       : 0.00
% 6.62/2.40  Index Matching       : 0.00
% 6.62/2.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
