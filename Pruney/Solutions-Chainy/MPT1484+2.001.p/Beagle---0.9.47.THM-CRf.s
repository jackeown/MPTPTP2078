%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:39 EST 2020

% Result     : Theorem 5.18s
% Output     : CNFRefutation 5.50s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 336 expanded)
%              Number of leaves         :   32 ( 140 expanded)
%              Depth                    :   14
%              Number of atoms          :  253 (1361 expanded)
%              Number of equality atoms :   34 ( 169 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

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

tff(f_196,negated_conjecture,(
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
               => k13_lattice3(A,k12_lattice3(A,B,C),C) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_lattice3)).

tff(f_165,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k12_lattice3(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k12_lattice3)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k11_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).

tff(f_177,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => r3_orders_2(A,B,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

tff(f_153,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_120,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l26_lattice3)).

tff(c_54,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_60,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_56,plain,(
    v2_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_242,plain,(
    ! [A_141,B_142,C_143] :
      ( k12_lattice3(A_141,B_142,C_143) = k11_lattice3(A_141,B_142,C_143)
      | ~ m1_subset_1(C_143,u1_struct_0(A_141))
      | ~ m1_subset_1(B_142,u1_struct_0(A_141))
      | ~ l1_orders_2(A_141)
      | ~ v2_lattice3(A_141)
      | ~ v5_orders_2(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_246,plain,(
    ! [B_142] :
      ( k12_lattice3('#skF_3',B_142,'#skF_5') = k11_lattice3('#skF_3',B_142,'#skF_5')
      | ~ m1_subset_1(B_142,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_242])).

tff(c_272,plain,(
    ! [B_147] :
      ( k12_lattice3('#skF_3',B_147,'#skF_5') = k11_lattice3('#skF_3',B_147,'#skF_5')
      | ~ m1_subset_1(B_147,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_54,c_246])).

tff(c_287,plain,(
    k12_lattice3('#skF_3','#skF_4','#skF_5') = k11_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_272])).

tff(c_93,plain,(
    ! [A_125,C_126,B_127] :
      ( k12_lattice3(A_125,C_126,B_127) = k12_lattice3(A_125,B_127,C_126)
      | ~ m1_subset_1(C_126,u1_struct_0(A_125))
      | ~ m1_subset_1(B_127,u1_struct_0(A_125))
      | ~ l1_orders_2(A_125)
      | ~ v2_lattice3(A_125)
      | ~ v5_orders_2(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_99,plain,(
    ! [B_127] :
      ( k12_lattice3('#skF_3',B_127,'#skF_4') = k12_lattice3('#skF_3','#skF_4',B_127)
      | ~ m1_subset_1(B_127,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_52,c_93])).

tff(c_121,plain,(
    ! [B_129] :
      ( k12_lattice3('#skF_3',B_129,'#skF_4') = k12_lattice3('#skF_3','#skF_4',B_129)
      | ~ m1_subset_1(B_129,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_54,c_99])).

tff(c_135,plain,(
    k12_lattice3('#skF_3','#skF_5','#skF_4') = k12_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_121])).

tff(c_292,plain,(
    k12_lattice3('#skF_3','#skF_5','#skF_4') = k11_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_135])).

tff(c_248,plain,(
    ! [B_142] :
      ( k12_lattice3('#skF_3',B_142,'#skF_4') = k11_lattice3('#skF_3',B_142,'#skF_4')
      | ~ m1_subset_1(B_142,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_52,c_242])).

tff(c_344,plain,(
    ! [B_153] :
      ( k12_lattice3('#skF_3',B_153,'#skF_4') = k11_lattice3('#skF_3',B_153,'#skF_4')
      | ~ m1_subset_1(B_153,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_54,c_248])).

tff(c_351,plain,(
    k12_lattice3('#skF_3','#skF_5','#skF_4') = k11_lattice3('#skF_3','#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_344])).

tff(c_359,plain,(
    k11_lattice3('#skF_3','#skF_5','#skF_4') = k11_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_351])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] :
      ( m1_subset_1(k11_lattice3(A_12,B_13,C_14),u1_struct_0(A_12))
      | ~ m1_subset_1(C_14,u1_struct_0(A_12))
      | ~ m1_subset_1(B_13,u1_struct_0(A_12))
      | ~ l1_orders_2(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_376,plain,
    ( m1_subset_1(k11_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_14])).

tff(c_387,plain,(
    m1_subset_1(k11_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_52,c_376])).

tff(c_58,plain,(
    v1_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_161,plain,(
    ! [A_133,B_134,C_135] :
      ( k13_lattice3(A_133,B_134,C_135) = k10_lattice3(A_133,B_134,C_135)
      | ~ m1_subset_1(C_135,u1_struct_0(A_133))
      | ~ m1_subset_1(B_134,u1_struct_0(A_133))
      | ~ l1_orders_2(A_133)
      | ~ v1_lattice3(A_133)
      | ~ v5_orders_2(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_165,plain,(
    ! [B_134] :
      ( k13_lattice3('#skF_3',B_134,'#skF_5') = k10_lattice3('#skF_3',B_134,'#skF_5')
      | ~ m1_subset_1(B_134,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_161])).

tff(c_171,plain,(
    ! [B_134] :
      ( k13_lattice3('#skF_3',B_134,'#skF_5') = k10_lattice3('#skF_3',B_134,'#skF_5')
      | ~ m1_subset_1(B_134,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_165])).

tff(c_442,plain,(
    k13_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') = k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_387,c_171])).

tff(c_48,plain,(
    k13_lattice3('#skF_3',k12_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_293,plain,(
    k13_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_48])).

tff(c_521,plain,(
    k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_293])).

tff(c_62,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_66,plain,(
    ! [A_122,B_123,C_124] :
      ( r3_orders_2(A_122,B_123,B_123)
      | ~ m1_subset_1(C_124,u1_struct_0(A_122))
      | ~ m1_subset_1(B_123,u1_struct_0(A_122))
      | ~ l1_orders_2(A_122)
      | ~ v3_orders_2(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_70,plain,(
    ! [B_123] :
      ( r3_orders_2('#skF_3',B_123,B_123)
      | ~ m1_subset_1(B_123,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_66])).

tff(c_76,plain,(
    ! [B_123] :
      ( r3_orders_2('#skF_3',B_123,B_123)
      | ~ m1_subset_1(B_123,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_54,c_70])).

tff(c_80,plain,(
    v2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_10,plain,(
    ! [A_8] :
      ( ~ v2_struct_0(A_8)
      | ~ v2_lattice3(A_8)
      | ~ l1_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_83,plain,
    ( ~ v2_lattice3('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_10])).

tff(c_90,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_83])).

tff(c_92,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_40,plain,(
    ! [A_61,B_85,C_97] :
      ( r1_orders_2(A_61,k11_lattice3(A_61,B_85,C_97),C_97)
      | ~ m1_subset_1(k11_lattice3(A_61,B_85,C_97),u1_struct_0(A_61))
      | ~ m1_subset_1(C_97,u1_struct_0(A_61))
      | ~ m1_subset_1(B_85,u1_struct_0(A_61))
      | ~ l1_orders_2(A_61)
      | ~ v2_lattice3(A_61)
      | ~ v5_orders_2(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_393,plain,
    ( r1_orders_2('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v2_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_387,c_40])).

tff(c_430,plain,
    ( r1_orders_2('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_54,c_52,c_50,c_393])).

tff(c_431,plain,(
    r1_orders_2('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_430])).

tff(c_107,plain,(
    ! [B_128] :
      ( r3_orders_2('#skF_3',B_128,B_128)
      | ~ m1_subset_1(B_128,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_118,plain,(
    r3_orders_2('#skF_3','#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_107])).

tff(c_175,plain,(
    ! [A_136,B_137,C_138] :
      ( r1_orders_2(A_136,B_137,C_138)
      | ~ r3_orders_2(A_136,B_137,C_138)
      | ~ m1_subset_1(C_138,u1_struct_0(A_136))
      | ~ m1_subset_1(B_137,u1_struct_0(A_136))
      | ~ l1_orders_2(A_136)
      | ~ v3_orders_2(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_181,plain,
    ( r1_orders_2('#skF_3','#skF_5','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_118,c_175])).

tff(c_192,plain,
    ( r1_orders_2('#skF_3','#skF_5','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_54,c_50,c_181])).

tff(c_193,plain,(
    r1_orders_2('#skF_3','#skF_5','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_192])).

tff(c_18,plain,(
    ! [A_15,C_51,B_39,D_57] :
      ( r1_orders_2(A_15,C_51,'#skF_1'(A_15,B_39,C_51,D_57))
      | k10_lattice3(A_15,B_39,C_51) = D_57
      | ~ r1_orders_2(A_15,C_51,D_57)
      | ~ r1_orders_2(A_15,B_39,D_57)
      | ~ m1_subset_1(D_57,u1_struct_0(A_15))
      | ~ m1_subset_1(C_51,u1_struct_0(A_15))
      | ~ m1_subset_1(B_39,u1_struct_0(A_15))
      | ~ l1_orders_2(A_15)
      | ~ v1_lattice3(A_15)
      | ~ v5_orders_2(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1643,plain,(
    ! [A_207,D_208,B_209,C_210] :
      ( ~ r1_orders_2(A_207,D_208,'#skF_1'(A_207,B_209,C_210,D_208))
      | k10_lattice3(A_207,B_209,C_210) = D_208
      | ~ r1_orders_2(A_207,C_210,D_208)
      | ~ r1_orders_2(A_207,B_209,D_208)
      | ~ m1_subset_1(D_208,u1_struct_0(A_207))
      | ~ m1_subset_1(C_210,u1_struct_0(A_207))
      | ~ m1_subset_1(B_209,u1_struct_0(A_207))
      | ~ l1_orders_2(A_207)
      | ~ v1_lattice3(A_207)
      | ~ v5_orders_2(A_207)
      | v2_struct_0(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2591,plain,(
    ! [A_254,B_255,D_256] :
      ( k10_lattice3(A_254,B_255,D_256) = D_256
      | ~ r1_orders_2(A_254,D_256,D_256)
      | ~ r1_orders_2(A_254,B_255,D_256)
      | ~ m1_subset_1(D_256,u1_struct_0(A_254))
      | ~ m1_subset_1(B_255,u1_struct_0(A_254))
      | ~ l1_orders_2(A_254)
      | ~ v1_lattice3(A_254)
      | ~ v5_orders_2(A_254)
      | v2_struct_0(A_254) ) ),
    inference(resolution,[status(thm)],[c_18,c_1643])).

tff(c_2602,plain,(
    ! [B_255] :
      ( k10_lattice3('#skF_3',B_255,'#skF_5') = '#skF_5'
      | ~ r1_orders_2('#skF_3',B_255,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_255,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_193,c_2591])).

tff(c_2623,plain,(
    ! [B_255] :
      ( k10_lattice3('#skF_3',B_255,'#skF_5') = '#skF_5'
      | ~ r1_orders_2('#skF_3',B_255,'#skF_5')
      | ~ m1_subset_1(B_255,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_50,c_2602])).

tff(c_2629,plain,(
    ! [B_257] :
      ( k10_lattice3('#skF_3',B_257,'#skF_5') = '#skF_5'
      | ~ r1_orders_2('#skF_3',B_257,'#skF_5')
      | ~ m1_subset_1(B_257,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_2623])).

tff(c_2646,plain,
    ( k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') = '#skF_5'
    | ~ r1_orders_2('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_387,c_2629])).

tff(c_2671,plain,(
    k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_2646])).

tff(c_2673,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_521,c_2671])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:06:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.18/2.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.18/2.04  
% 5.18/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.18/2.05  %$ r3_orders_2 > r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.18/2.05  
% 5.18/2.05  %Foreground sorts:
% 5.18/2.05  
% 5.18/2.05  
% 5.18/2.05  %Background operators:
% 5.18/2.05  
% 5.18/2.05  
% 5.18/2.05  %Foreground operators:
% 5.18/2.05  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.18/2.05  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 5.18/2.05  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.18/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.18/2.05  tff(k13_lattice3, type, k13_lattice3: ($i * $i * $i) > $i).
% 5.18/2.05  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 5.18/2.05  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 5.18/2.05  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 5.18/2.05  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 5.18/2.05  tff('#skF_5', type, '#skF_5': $i).
% 5.18/2.05  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 5.18/2.05  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.18/2.05  tff('#skF_3', type, '#skF_3': $i).
% 5.18/2.05  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.18/2.05  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.18/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.18/2.05  tff('#skF_4', type, '#skF_4': $i).
% 5.18/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.18/2.05  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 5.18/2.05  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 5.18/2.05  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.18/2.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.18/2.05  
% 5.50/2.06  tff(f_196, negated_conjecture, ~(![A]: (((((v3_orders_2(A) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k13_lattice3(A, k12_lattice3(A, B, C), C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_lattice3)).
% 5.50/2.06  tff(f_165, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 5.50/2.06  tff(f_79, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k12_lattice3(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k12_lattice3)).
% 5.50/2.06  tff(f_87, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k11_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k11_lattice3)).
% 5.50/2.06  tff(f_177, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k10_lattice3(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 5.50/2.06  tff(f_53, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => r3_orders_2(A, B, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 5.50/2.06  tff(f_67, axiom, (![A]: (l1_orders_2(A) => (v2_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_lattice3)).
% 5.50/2.06  tff(f_153, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k11_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l28_lattice3)).
% 5.50/2.06  tff(f_40, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 5.50/2.06  tff(f_120, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k10_lattice3(A, B, C)) <=> ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l26_lattice3)).
% 5.50/2.06  tff(c_54, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.50/2.06  tff(c_50, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.50/2.06  tff(c_52, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.50/2.06  tff(c_60, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.50/2.06  tff(c_56, plain, (v2_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.50/2.06  tff(c_242, plain, (![A_141, B_142, C_143]: (k12_lattice3(A_141, B_142, C_143)=k11_lattice3(A_141, B_142, C_143) | ~m1_subset_1(C_143, u1_struct_0(A_141)) | ~m1_subset_1(B_142, u1_struct_0(A_141)) | ~l1_orders_2(A_141) | ~v2_lattice3(A_141) | ~v5_orders_2(A_141))), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.50/2.06  tff(c_246, plain, (![B_142]: (k12_lattice3('#skF_3', B_142, '#skF_5')=k11_lattice3('#skF_3', B_142, '#skF_5') | ~m1_subset_1(B_142, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_242])).
% 5.50/2.06  tff(c_272, plain, (![B_147]: (k12_lattice3('#skF_3', B_147, '#skF_5')=k11_lattice3('#skF_3', B_147, '#skF_5') | ~m1_subset_1(B_147, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_54, c_246])).
% 5.50/2.06  tff(c_287, plain, (k12_lattice3('#skF_3', '#skF_4', '#skF_5')=k11_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_52, c_272])).
% 5.50/2.06  tff(c_93, plain, (![A_125, C_126, B_127]: (k12_lattice3(A_125, C_126, B_127)=k12_lattice3(A_125, B_127, C_126) | ~m1_subset_1(C_126, u1_struct_0(A_125)) | ~m1_subset_1(B_127, u1_struct_0(A_125)) | ~l1_orders_2(A_125) | ~v2_lattice3(A_125) | ~v5_orders_2(A_125))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.50/2.06  tff(c_99, plain, (![B_127]: (k12_lattice3('#skF_3', B_127, '#skF_4')=k12_lattice3('#skF_3', '#skF_4', B_127) | ~m1_subset_1(B_127, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_93])).
% 5.50/2.06  tff(c_121, plain, (![B_129]: (k12_lattice3('#skF_3', B_129, '#skF_4')=k12_lattice3('#skF_3', '#skF_4', B_129) | ~m1_subset_1(B_129, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_54, c_99])).
% 5.50/2.06  tff(c_135, plain, (k12_lattice3('#skF_3', '#skF_5', '#skF_4')=k12_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_121])).
% 5.50/2.06  tff(c_292, plain, (k12_lattice3('#skF_3', '#skF_5', '#skF_4')=k11_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_287, c_135])).
% 5.50/2.06  tff(c_248, plain, (![B_142]: (k12_lattice3('#skF_3', B_142, '#skF_4')=k11_lattice3('#skF_3', B_142, '#skF_4') | ~m1_subset_1(B_142, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_242])).
% 5.50/2.06  tff(c_344, plain, (![B_153]: (k12_lattice3('#skF_3', B_153, '#skF_4')=k11_lattice3('#skF_3', B_153, '#skF_4') | ~m1_subset_1(B_153, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_54, c_248])).
% 5.50/2.06  tff(c_351, plain, (k12_lattice3('#skF_3', '#skF_5', '#skF_4')=k11_lattice3('#skF_3', '#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_344])).
% 5.50/2.06  tff(c_359, plain, (k11_lattice3('#skF_3', '#skF_5', '#skF_4')=k11_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_292, c_351])).
% 5.50/2.06  tff(c_14, plain, (![A_12, B_13, C_14]: (m1_subset_1(k11_lattice3(A_12, B_13, C_14), u1_struct_0(A_12)) | ~m1_subset_1(C_14, u1_struct_0(A_12)) | ~m1_subset_1(B_13, u1_struct_0(A_12)) | ~l1_orders_2(A_12))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.50/2.06  tff(c_376, plain, (m1_subset_1(k11_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_359, c_14])).
% 5.50/2.06  tff(c_387, plain, (m1_subset_1(k11_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_52, c_376])).
% 5.50/2.06  tff(c_58, plain, (v1_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.50/2.06  tff(c_161, plain, (![A_133, B_134, C_135]: (k13_lattice3(A_133, B_134, C_135)=k10_lattice3(A_133, B_134, C_135) | ~m1_subset_1(C_135, u1_struct_0(A_133)) | ~m1_subset_1(B_134, u1_struct_0(A_133)) | ~l1_orders_2(A_133) | ~v1_lattice3(A_133) | ~v5_orders_2(A_133))), inference(cnfTransformation, [status(thm)], [f_177])).
% 5.50/2.06  tff(c_165, plain, (![B_134]: (k13_lattice3('#skF_3', B_134, '#skF_5')=k10_lattice3('#skF_3', B_134, '#skF_5') | ~m1_subset_1(B_134, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_161])).
% 5.50/2.06  tff(c_171, plain, (![B_134]: (k13_lattice3('#skF_3', B_134, '#skF_5')=k10_lattice3('#skF_3', B_134, '#skF_5') | ~m1_subset_1(B_134, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_165])).
% 5.50/2.06  tff(c_442, plain, (k13_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')=k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_387, c_171])).
% 5.50/2.06  tff(c_48, plain, (k13_lattice3('#skF_3', k12_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.50/2.06  tff(c_293, plain, (k13_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_287, c_48])).
% 5.50/2.06  tff(c_521, plain, (k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_442, c_293])).
% 5.50/2.06  tff(c_62, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.50/2.06  tff(c_66, plain, (![A_122, B_123, C_124]: (r3_orders_2(A_122, B_123, B_123) | ~m1_subset_1(C_124, u1_struct_0(A_122)) | ~m1_subset_1(B_123, u1_struct_0(A_122)) | ~l1_orders_2(A_122) | ~v3_orders_2(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.50/2.06  tff(c_70, plain, (![B_123]: (r3_orders_2('#skF_3', B_123, B_123) | ~m1_subset_1(B_123, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_66])).
% 5.50/2.06  tff(c_76, plain, (![B_123]: (r3_orders_2('#skF_3', B_123, B_123) | ~m1_subset_1(B_123, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_54, c_70])).
% 5.50/2.06  tff(c_80, plain, (v2_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_76])).
% 5.50/2.06  tff(c_10, plain, (![A_8]: (~v2_struct_0(A_8) | ~v2_lattice3(A_8) | ~l1_orders_2(A_8))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.50/2.06  tff(c_83, plain, (~v2_lattice3('#skF_3') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_80, c_10])).
% 5.50/2.06  tff(c_90, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_83])).
% 5.50/2.06  tff(c_92, plain, (~v2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_76])).
% 5.50/2.06  tff(c_40, plain, (![A_61, B_85, C_97]: (r1_orders_2(A_61, k11_lattice3(A_61, B_85, C_97), C_97) | ~m1_subset_1(k11_lattice3(A_61, B_85, C_97), u1_struct_0(A_61)) | ~m1_subset_1(C_97, u1_struct_0(A_61)) | ~m1_subset_1(B_85, u1_struct_0(A_61)) | ~l1_orders_2(A_61) | ~v2_lattice3(A_61) | ~v5_orders_2(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.50/2.06  tff(c_393, plain, (r1_orders_2('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_387, c_40])).
% 5.50/2.06  tff(c_430, plain, (r1_orders_2('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_54, c_52, c_50, c_393])).
% 5.50/2.06  tff(c_431, plain, (r1_orders_2('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_92, c_430])).
% 5.50/2.06  tff(c_107, plain, (![B_128]: (r3_orders_2('#skF_3', B_128, B_128) | ~m1_subset_1(B_128, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_76])).
% 5.50/2.06  tff(c_118, plain, (r3_orders_2('#skF_3', '#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_107])).
% 5.50/2.06  tff(c_175, plain, (![A_136, B_137, C_138]: (r1_orders_2(A_136, B_137, C_138) | ~r3_orders_2(A_136, B_137, C_138) | ~m1_subset_1(C_138, u1_struct_0(A_136)) | ~m1_subset_1(B_137, u1_struct_0(A_136)) | ~l1_orders_2(A_136) | ~v3_orders_2(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.50/2.06  tff(c_181, plain, (r1_orders_2('#skF_3', '#skF_5', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_118, c_175])).
% 5.50/2.06  tff(c_192, plain, (r1_orders_2('#skF_3', '#skF_5', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_54, c_50, c_181])).
% 5.50/2.06  tff(c_193, plain, (r1_orders_2('#skF_3', '#skF_5', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_92, c_192])).
% 5.50/2.06  tff(c_18, plain, (![A_15, C_51, B_39, D_57]: (r1_orders_2(A_15, C_51, '#skF_1'(A_15, B_39, C_51, D_57)) | k10_lattice3(A_15, B_39, C_51)=D_57 | ~r1_orders_2(A_15, C_51, D_57) | ~r1_orders_2(A_15, B_39, D_57) | ~m1_subset_1(D_57, u1_struct_0(A_15)) | ~m1_subset_1(C_51, u1_struct_0(A_15)) | ~m1_subset_1(B_39, u1_struct_0(A_15)) | ~l1_orders_2(A_15) | ~v1_lattice3(A_15) | ~v5_orders_2(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.50/2.06  tff(c_1643, plain, (![A_207, D_208, B_209, C_210]: (~r1_orders_2(A_207, D_208, '#skF_1'(A_207, B_209, C_210, D_208)) | k10_lattice3(A_207, B_209, C_210)=D_208 | ~r1_orders_2(A_207, C_210, D_208) | ~r1_orders_2(A_207, B_209, D_208) | ~m1_subset_1(D_208, u1_struct_0(A_207)) | ~m1_subset_1(C_210, u1_struct_0(A_207)) | ~m1_subset_1(B_209, u1_struct_0(A_207)) | ~l1_orders_2(A_207) | ~v1_lattice3(A_207) | ~v5_orders_2(A_207) | v2_struct_0(A_207))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.50/2.06  tff(c_2591, plain, (![A_254, B_255, D_256]: (k10_lattice3(A_254, B_255, D_256)=D_256 | ~r1_orders_2(A_254, D_256, D_256) | ~r1_orders_2(A_254, B_255, D_256) | ~m1_subset_1(D_256, u1_struct_0(A_254)) | ~m1_subset_1(B_255, u1_struct_0(A_254)) | ~l1_orders_2(A_254) | ~v1_lattice3(A_254) | ~v5_orders_2(A_254) | v2_struct_0(A_254))), inference(resolution, [status(thm)], [c_18, c_1643])).
% 5.50/2.06  tff(c_2602, plain, (![B_255]: (k10_lattice3('#skF_3', B_255, '#skF_5')='#skF_5' | ~r1_orders_2('#skF_3', B_255, '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1(B_255, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_193, c_2591])).
% 5.50/2.06  tff(c_2623, plain, (![B_255]: (k10_lattice3('#skF_3', B_255, '#skF_5')='#skF_5' | ~r1_orders_2('#skF_3', B_255, '#skF_5') | ~m1_subset_1(B_255, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_50, c_2602])).
% 5.50/2.06  tff(c_2629, plain, (![B_257]: (k10_lattice3('#skF_3', B_257, '#skF_5')='#skF_5' | ~r1_orders_2('#skF_3', B_257, '#skF_5') | ~m1_subset_1(B_257, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_92, c_2623])).
% 5.50/2.06  tff(c_2646, plain, (k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')='#skF_5' | ~r1_orders_2('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_387, c_2629])).
% 5.50/2.06  tff(c_2671, plain, (k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_431, c_2646])).
% 5.50/2.06  tff(c_2673, plain, $false, inference(negUnitSimplification, [status(thm)], [c_521, c_2671])).
% 5.50/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.50/2.06  
% 5.50/2.06  Inference rules
% 5.50/2.06  ----------------------
% 5.50/2.06  #Ref     : 0
% 5.50/2.06  #Sup     : 552
% 5.50/2.06  #Fact    : 0
% 5.50/2.06  #Define  : 0
% 5.50/2.06  #Split   : 5
% 5.50/2.06  #Chain   : 0
% 5.50/2.06  #Close   : 0
% 5.50/2.06  
% 5.50/2.06  Ordering : KBO
% 5.50/2.06  
% 5.50/2.06  Simplification rules
% 5.50/2.07  ----------------------
% 5.50/2.07  #Subsume      : 10
% 5.50/2.07  #Demod        : 795
% 5.50/2.07  #Tautology    : 238
% 5.50/2.07  #SimpNegUnit  : 124
% 5.50/2.07  #BackRed      : 15
% 5.50/2.07  
% 5.50/2.07  #Partial instantiations: 0
% 5.50/2.07  #Strategies tried      : 1
% 5.50/2.07  
% 5.50/2.07  Timing (in seconds)
% 5.50/2.07  ----------------------
% 5.50/2.07  Preprocessing        : 0.37
% 5.50/2.07  Parsing              : 0.19
% 5.50/2.07  CNF conversion       : 0.03
% 5.50/2.07  Main loop            : 0.85
% 5.50/2.07  Inferencing          : 0.27
% 5.50/2.07  Reduction            : 0.30
% 5.50/2.07  Demodulation         : 0.22
% 5.50/2.07  BG Simplification    : 0.04
% 5.50/2.07  Subsumption          : 0.18
% 5.50/2.07  Abstraction          : 0.05
% 5.50/2.07  MUC search           : 0.00
% 5.50/2.07  Cooper               : 0.00
% 5.50/2.07  Total                : 1.26
% 5.50/2.07  Index Insertion      : 0.00
% 5.50/2.07  Index Deletion       : 0.00
% 5.50/2.07  Index Matching       : 0.00
% 5.50/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
