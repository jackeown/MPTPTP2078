%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:40 EST 2020

% Result     : Theorem 7.45s
% Output     : CNFRefutation 7.45s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 701 expanded)
%              Number of leaves         :   31 ( 291 expanded)
%              Depth                    :   19
%              Number of atoms          :  313 (3054 expanded)
%              Number of equality atoms :   48 ( 384 expanded)
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

tff(f_202,negated_conjecture,(
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

tff(f_165,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k13_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k13_lattice3)).

tff(f_108,axiom,(
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

tff(f_32,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_153,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k12_lattice3(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k12_lattice3)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k12_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k12_lattice3)).

tff(f_183,axiom,(
    ! [A] :
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_lattice3)).

tff(f_141,axiom,(
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

tff(c_50,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_58,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_56,plain,(
    v1_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_52,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_115,plain,(
    ! [A_133,B_134,C_135] :
      ( k13_lattice3(A_133,B_134,C_135) = k10_lattice3(A_133,B_134,C_135)
      | ~ m1_subset_1(C_135,u1_struct_0(A_133))
      | ~ m1_subset_1(B_134,u1_struct_0(A_133))
      | ~ l1_orders_2(A_133)
      | ~ v1_lattice3(A_133)
      | ~ v5_orders_2(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_121,plain,(
    ! [B_134] :
      ( k13_lattice3('#skF_3',B_134,'#skF_5') = k10_lattice3('#skF_3',B_134,'#skF_5')
      | ~ m1_subset_1(B_134,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_115])).

tff(c_175,plain,(
    ! [B_137] :
      ( k13_lattice3('#skF_3',B_137,'#skF_5') = k10_lattice3('#skF_3',B_137,'#skF_5')
      | ~ m1_subset_1(B_137,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_121])).

tff(c_201,plain,(
    k13_lattice3('#skF_3','#skF_4','#skF_5') = k10_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_175])).

tff(c_46,plain,(
    k12_lattice3('#skF_3','#skF_4',k13_lattice3('#skF_3','#skF_4','#skF_5')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_233,plain,(
    k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_46])).

tff(c_123,plain,(
    ! [B_134] :
      ( k13_lattice3('#skF_3',B_134,'#skF_4') = k10_lattice3('#skF_3',B_134,'#skF_4')
      | ~ m1_subset_1(B_134,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_115])).

tff(c_265,plain,(
    ! [B_138] :
      ( k13_lattice3('#skF_3',B_138,'#skF_4') = k10_lattice3('#skF_3',B_138,'#skF_4')
      | ~ m1_subset_1(B_138,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_123])).

tff(c_299,plain,(
    k13_lattice3('#skF_3','#skF_4','#skF_4') = k10_lattice3('#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_265])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11] :
      ( m1_subset_1(k13_lattice3(A_9,B_10,C_11),u1_struct_0(A_9))
      | ~ m1_subset_1(C_11,u1_struct_0(A_9))
      | ~ m1_subset_1(B_10,u1_struct_0(A_9))
      | ~ l1_orders_2(A_9)
      | ~ v1_lattice3(A_9)
      | ~ v5_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_375,plain,
    ( m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_4'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v1_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_10])).

tff(c_379,plain,(
    m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_50,c_375])).

tff(c_778,plain,(
    ! [A_148,B_149,C_150] :
      ( r1_orders_2(A_148,B_149,k10_lattice3(A_148,B_149,C_150))
      | ~ m1_subset_1(k10_lattice3(A_148,B_149,C_150),u1_struct_0(A_148))
      | ~ m1_subset_1(C_150,u1_struct_0(A_148))
      | ~ m1_subset_1(B_149,u1_struct_0(A_148))
      | ~ l1_orders_2(A_148)
      | ~ v1_lattice3(A_148)
      | ~ v5_orders_2(A_148)
      | v2_struct_0(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_780,plain,
    ( r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v1_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_379,c_778])).

tff(c_789,plain,
    ( r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_780])).

tff(c_799,plain,(
    v2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_789])).

tff(c_2,plain,(
    ! [A_1] :
      ( ~ v2_struct_0(A_1)
      | ~ v1_lattice3(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_802,plain,
    ( ~ v1_lattice3('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_799,c_2])).

tff(c_809,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_802])).

tff(c_811,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_789])).

tff(c_237,plain,
    ( m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v1_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_10])).

tff(c_241,plain,(
    m1_subset_1(k10_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_48,c_237])).

tff(c_784,plain,
    ( r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v1_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_241,c_778])).

tff(c_795,plain,
    ( r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_48,c_784])).

tff(c_918,plain,(
    r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_811,c_795])).

tff(c_54,plain,(
    v2_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_300,plain,(
    ! [A_139,B_140,C_141] :
      ( k12_lattice3(A_139,B_140,C_141) = k11_lattice3(A_139,B_140,C_141)
      | ~ m1_subset_1(C_141,u1_struct_0(A_139))
      | ~ m1_subset_1(B_140,u1_struct_0(A_139))
      | ~ l1_orders_2(A_139)
      | ~ v2_lattice3(A_139)
      | ~ v5_orders_2(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_312,plain,(
    ! [B_140] :
      ( k12_lattice3('#skF_3',B_140,'#skF_5') = k11_lattice3('#skF_3',B_140,'#skF_5')
      | ~ m1_subset_1(B_140,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_300])).

tff(c_381,plain,(
    ! [B_142] :
      ( k12_lattice3('#skF_3',B_142,'#skF_5') = k11_lattice3('#skF_3',B_142,'#skF_5')
      | ~ m1_subset_1(B_142,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_52,c_312])).

tff(c_419,plain,(
    k12_lattice3('#skF_3','#skF_4','#skF_5') = k11_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_381])).

tff(c_65,plain,(
    ! [A_129,C_130,B_131] :
      ( k12_lattice3(A_129,C_130,B_131) = k12_lattice3(A_129,B_131,C_130)
      | ~ m1_subset_1(C_130,u1_struct_0(A_129))
      | ~ m1_subset_1(B_131,u1_struct_0(A_129))
      | ~ l1_orders_2(A_129)
      | ~ v2_lattice3(A_129)
      | ~ v5_orders_2(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_71,plain,(
    ! [B_131] :
      ( k12_lattice3('#skF_3',B_131,'#skF_5') = k12_lattice3('#skF_3','#skF_5',B_131)
      | ~ m1_subset_1(B_131,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_65])).

tff(c_82,plain,(
    ! [B_132] :
      ( k12_lattice3('#skF_3',B_132,'#skF_5') = k12_lattice3('#skF_3','#skF_5',B_132)
      | ~ m1_subset_1(B_132,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_52,c_71])).

tff(c_105,plain,(
    k12_lattice3('#skF_3','#skF_5','#skF_4') = k12_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_82])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] :
      ( m1_subset_1(k12_lattice3(A_6,B_7,C_8),u1_struct_0(A_6))
      | ~ m1_subset_1(C_8,u1_struct_0(A_6))
      | ~ m1_subset_1(B_7,u1_struct_0(A_6))
      | ~ l1_orders_2(A_6)
      | ~ v2_lattice3(A_6)
      | ~ v5_orders_2(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_109,plain,
    ( m1_subset_1(k12_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v2_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_8])).

tff(c_113,plain,(
    m1_subset_1(k12_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_52,c_48,c_50,c_109])).

tff(c_499,plain,(
    m1_subset_1(k11_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_113])).

tff(c_500,plain,(
    k12_lattice3('#skF_3','#skF_5','#skF_4') = k11_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_105])).

tff(c_60,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_545,plain,(
    ! [A_143,B_144,C_145] :
      ( k13_lattice3(A_143,k12_lattice3(A_143,B_144,C_145),C_145) = C_145
      | ~ m1_subset_1(C_145,u1_struct_0(A_143))
      | ~ m1_subset_1(B_144,u1_struct_0(A_143))
      | ~ l1_orders_2(A_143)
      | ~ v2_lattice3(A_143)
      | ~ v1_lattice3(A_143)
      | ~ v5_orders_2(A_143)
      | ~ v3_orders_2(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_565,plain,(
    ! [B_144] :
      ( k13_lattice3('#skF_3',k12_lattice3('#skF_3',B_144,'#skF_4'),'#skF_4') = '#skF_4'
      | ~ m1_subset_1(B_144,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_545])).

tff(c_707,plain,(
    ! [B_147] :
      ( k13_lattice3('#skF_3',k12_lattice3('#skF_3',B_147,'#skF_4'),'#skF_4') = '#skF_4'
      | ~ m1_subset_1(B_147,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_52,c_565])).

tff(c_739,plain,(
    k13_lattice3('#skF_3',k12_lattice3('#skF_3','#skF_5','#skF_4'),'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_48,c_707])).

tff(c_757,plain,(
    k13_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_500,c_739])).

tff(c_291,plain,(
    k13_lattice3('#skF_3',k12_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4') = k10_lattice3('#skF_3',k12_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_113,c_265])).

tff(c_2357,plain,(
    k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_757,c_419,c_291])).

tff(c_22,plain,(
    ! [A_12,C_48,B_36] :
      ( r1_orders_2(A_12,C_48,k10_lattice3(A_12,B_36,C_48))
      | ~ m1_subset_1(k10_lattice3(A_12,B_36,C_48),u1_struct_0(A_12))
      | ~ m1_subset_1(C_48,u1_struct_0(A_12))
      | ~ m1_subset_1(B_36,u1_struct_0(A_12))
      | ~ l1_orders_2(A_12)
      | ~ v1_lattice3(A_12)
      | ~ v5_orders_2(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2360,plain,
    ( r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3',k11_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k11_lattice3('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v1_lattice3('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2357,c_22])).

tff(c_2366,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_499,c_50,c_50,c_2357,c_2360])).

tff(c_2367,plain,(
    r1_orders_2('#skF_3','#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_811,c_2366])).

tff(c_2159,plain,(
    ! [A_181,B_182,C_183,D_184] :
      ( r1_orders_2(A_181,'#skF_2'(A_181,B_182,C_183,D_184),C_183)
      | k11_lattice3(A_181,B_182,C_183) = D_184
      | ~ r1_orders_2(A_181,D_184,C_183)
      | ~ r1_orders_2(A_181,D_184,B_182)
      | ~ m1_subset_1(D_184,u1_struct_0(A_181))
      | ~ m1_subset_1(C_183,u1_struct_0(A_181))
      | ~ m1_subset_1(B_182,u1_struct_0(A_181))
      | ~ l1_orders_2(A_181)
      | ~ v2_lattice3(A_181)
      | ~ v5_orders_2(A_181)
      | v2_struct_0(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_26,plain,(
    ! [A_58,B_82,C_94,D_100] :
      ( ~ r1_orders_2(A_58,'#skF_2'(A_58,B_82,C_94,D_100),D_100)
      | k11_lattice3(A_58,B_82,C_94) = D_100
      | ~ r1_orders_2(A_58,D_100,C_94)
      | ~ r1_orders_2(A_58,D_100,B_82)
      | ~ m1_subset_1(D_100,u1_struct_0(A_58))
      | ~ m1_subset_1(C_94,u1_struct_0(A_58))
      | ~ m1_subset_1(B_82,u1_struct_0(A_58))
      | ~ l1_orders_2(A_58)
      | ~ v2_lattice3(A_58)
      | ~ v5_orders_2(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_3155,plain,(
    ! [A_201,B_202,C_203] :
      ( k11_lattice3(A_201,B_202,C_203) = C_203
      | ~ r1_orders_2(A_201,C_203,C_203)
      | ~ r1_orders_2(A_201,C_203,B_202)
      | ~ m1_subset_1(C_203,u1_struct_0(A_201))
      | ~ m1_subset_1(B_202,u1_struct_0(A_201))
      | ~ l1_orders_2(A_201)
      | ~ v2_lattice3(A_201)
      | ~ v5_orders_2(A_201)
      | v2_struct_0(A_201) ) ),
    inference(resolution,[status(thm)],[c_2159,c_26])).

tff(c_3157,plain,(
    ! [B_202] :
      ( k11_lattice3('#skF_3',B_202,'#skF_4') = '#skF_4'
      | ~ r1_orders_2('#skF_3','#skF_4',B_202)
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_202,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2367,c_3155])).

tff(c_3162,plain,(
    ! [B_202] :
      ( k11_lattice3('#skF_3',B_202,'#skF_4') = '#skF_4'
      | ~ r1_orders_2('#skF_3','#skF_4',B_202)
      | ~ m1_subset_1(B_202,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_52,c_50,c_3157])).

tff(c_3168,plain,(
    ! [B_204] :
      ( k11_lattice3('#skF_3',B_204,'#skF_4') = '#skF_4'
      | ~ r1_orders_2('#skF_3','#skF_4',B_204)
      | ~ m1_subset_1(B_204,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_811,c_3162])).

tff(c_3254,plain,
    ( k11_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4') = '#skF_4'
    | ~ r1_orders_2('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_241,c_3168])).

tff(c_3319,plain,(
    k11_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_918,c_3254])).

tff(c_314,plain,(
    ! [B_140] :
      ( k12_lattice3('#skF_3',B_140,'#skF_4') = k11_lattice3('#skF_3',B_140,'#skF_4')
      | ~ m1_subset_1(B_140,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_300])).

tff(c_602,plain,(
    ! [B_146] :
      ( k12_lattice3('#skF_3',B_146,'#skF_4') = k11_lattice3('#skF_3',B_146,'#skF_4')
      | ~ m1_subset_1(B_146,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_52,c_314])).

tff(c_639,plain,(
    k12_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4') = k11_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_241,c_602])).

tff(c_5497,plain,(
    k12_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3319,c_639])).

tff(c_73,plain,(
    ! [B_131] :
      ( k12_lattice3('#skF_3',B_131,'#skF_4') = k12_lattice3('#skF_3','#skF_4',B_131)
      | ~ m1_subset_1(B_131,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v5_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_65])).

tff(c_81,plain,(
    ! [B_131] :
      ( k12_lattice3('#skF_3',B_131,'#skF_4') = k12_lattice3('#skF_3','#skF_4',B_131)
      | ~ m1_subset_1(B_131,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_52,c_73])).

tff(c_257,plain,(
    k12_lattice3('#skF_3',k10_lattice3('#skF_3','#skF_4','#skF_5'),'#skF_4') = k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_241,c_81])).

tff(c_5498,plain,(
    k12_lattice3('#skF_3','#skF_4',k10_lattice3('#skF_3','#skF_4','#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5497,c_257])).

tff(c_5500,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_5498])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:58:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.45/2.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.45/2.57  
% 7.45/2.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.45/2.57  %$ r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 7.45/2.57  
% 7.45/2.57  %Foreground sorts:
% 7.45/2.57  
% 7.45/2.57  
% 7.45/2.57  %Background operators:
% 7.45/2.57  
% 7.45/2.57  
% 7.45/2.57  %Foreground operators:
% 7.45/2.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.45/2.57  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 7.45/2.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.45/2.57  tff(k13_lattice3, type, k13_lattice3: ($i * $i * $i) > $i).
% 7.45/2.57  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 7.45/2.57  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 7.45/2.57  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 7.45/2.57  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 7.45/2.57  tff('#skF_5', type, '#skF_5': $i).
% 7.45/2.57  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 7.45/2.57  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 7.45/2.57  tff('#skF_3', type, '#skF_3': $i).
% 7.45/2.57  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 7.45/2.57  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 7.45/2.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.45/2.57  tff('#skF_4', type, '#skF_4': $i).
% 7.45/2.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.45/2.57  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 7.45/2.57  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 7.45/2.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.45/2.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.45/2.57  
% 7.45/2.59  tff(f_202, negated_conjecture, ~(![A]: (((((v3_orders_2(A) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k12_lattice3(A, B, k13_lattice3(A, B, C)) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_lattice3)).
% 7.45/2.59  tff(f_165, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k10_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 7.45/2.59  tff(f_75, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k13_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k13_lattice3)).
% 7.45/2.59  tff(f_108, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k10_lattice3(A, B, C)) <=> ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l26_lattice3)).
% 7.45/2.59  tff(f_32, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 7.45/2.59  tff(f_153, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 7.45/2.59  tff(f_51, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k12_lattice3(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k12_lattice3)).
% 7.45/2.59  tff(f_63, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k12_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k12_lattice3)).
% 7.45/2.59  tff(f_183, axiom, (![A]: (((((v3_orders_2(A) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k13_lattice3(A, k12_lattice3(A, B, C), C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_lattice3)).
% 7.45/2.59  tff(f_141, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k11_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l28_lattice3)).
% 7.45/2.59  tff(c_50, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_202])).
% 7.45/2.59  tff(c_58, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_202])).
% 7.45/2.59  tff(c_56, plain, (v1_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_202])).
% 7.45/2.59  tff(c_52, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_202])).
% 7.45/2.59  tff(c_48, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_202])).
% 7.45/2.59  tff(c_115, plain, (![A_133, B_134, C_135]: (k13_lattice3(A_133, B_134, C_135)=k10_lattice3(A_133, B_134, C_135) | ~m1_subset_1(C_135, u1_struct_0(A_133)) | ~m1_subset_1(B_134, u1_struct_0(A_133)) | ~l1_orders_2(A_133) | ~v1_lattice3(A_133) | ~v5_orders_2(A_133))), inference(cnfTransformation, [status(thm)], [f_165])).
% 7.45/2.59  tff(c_121, plain, (![B_134]: (k13_lattice3('#skF_3', B_134, '#skF_5')=k10_lattice3('#skF_3', B_134, '#skF_5') | ~m1_subset_1(B_134, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_115])).
% 7.45/2.59  tff(c_175, plain, (![B_137]: (k13_lattice3('#skF_3', B_137, '#skF_5')=k10_lattice3('#skF_3', B_137, '#skF_5') | ~m1_subset_1(B_137, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_121])).
% 7.45/2.59  tff(c_201, plain, (k13_lattice3('#skF_3', '#skF_4', '#skF_5')=k10_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_175])).
% 7.45/2.59  tff(c_46, plain, (k12_lattice3('#skF_3', '#skF_4', k13_lattice3('#skF_3', '#skF_4', '#skF_5'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_202])).
% 7.45/2.59  tff(c_233, plain, (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_201, c_46])).
% 7.45/2.59  tff(c_123, plain, (![B_134]: (k13_lattice3('#skF_3', B_134, '#skF_4')=k10_lattice3('#skF_3', B_134, '#skF_4') | ~m1_subset_1(B_134, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_115])).
% 7.45/2.59  tff(c_265, plain, (![B_138]: (k13_lattice3('#skF_3', B_138, '#skF_4')=k10_lattice3('#skF_3', B_138, '#skF_4') | ~m1_subset_1(B_138, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_123])).
% 7.45/2.59  tff(c_299, plain, (k13_lattice3('#skF_3', '#skF_4', '#skF_4')=k10_lattice3('#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_265])).
% 7.45/2.59  tff(c_10, plain, (![A_9, B_10, C_11]: (m1_subset_1(k13_lattice3(A_9, B_10, C_11), u1_struct_0(A_9)) | ~m1_subset_1(C_11, u1_struct_0(A_9)) | ~m1_subset_1(B_10, u1_struct_0(A_9)) | ~l1_orders_2(A_9) | ~v1_lattice3(A_9) | ~v5_orders_2(A_9))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.45/2.59  tff(c_375, plain, (m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_4'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_299, c_10])).
% 7.45/2.59  tff(c_379, plain, (m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_50, c_375])).
% 7.45/2.59  tff(c_778, plain, (![A_148, B_149, C_150]: (r1_orders_2(A_148, B_149, k10_lattice3(A_148, B_149, C_150)) | ~m1_subset_1(k10_lattice3(A_148, B_149, C_150), u1_struct_0(A_148)) | ~m1_subset_1(C_150, u1_struct_0(A_148)) | ~m1_subset_1(B_149, u1_struct_0(A_148)) | ~l1_orders_2(A_148) | ~v1_lattice3(A_148) | ~v5_orders_2(A_148) | v2_struct_0(A_148))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.45/2.59  tff(c_780, plain, (r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_4')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_379, c_778])).
% 7.45/2.59  tff(c_789, plain, (r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_780])).
% 7.45/2.59  tff(c_799, plain, (v2_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_789])).
% 7.45/2.59  tff(c_2, plain, (![A_1]: (~v2_struct_0(A_1) | ~v1_lattice3(A_1) | ~l1_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.45/2.59  tff(c_802, plain, (~v1_lattice3('#skF_3') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_799, c_2])).
% 7.45/2.59  tff(c_809, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_56, c_802])).
% 7.45/2.59  tff(c_811, plain, (~v2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_789])).
% 7.45/2.59  tff(c_237, plain, (m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_201, c_10])).
% 7.45/2.59  tff(c_241, plain, (m1_subset_1(k10_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_48, c_237])).
% 7.45/2.59  tff(c_784, plain, (r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_241, c_778])).
% 7.45/2.59  tff(c_795, plain, (r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_48, c_784])).
% 7.45/2.59  tff(c_918, plain, (r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_811, c_795])).
% 7.45/2.59  tff(c_54, plain, (v2_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_202])).
% 7.45/2.59  tff(c_300, plain, (![A_139, B_140, C_141]: (k12_lattice3(A_139, B_140, C_141)=k11_lattice3(A_139, B_140, C_141) | ~m1_subset_1(C_141, u1_struct_0(A_139)) | ~m1_subset_1(B_140, u1_struct_0(A_139)) | ~l1_orders_2(A_139) | ~v2_lattice3(A_139) | ~v5_orders_2(A_139))), inference(cnfTransformation, [status(thm)], [f_153])).
% 7.45/2.59  tff(c_312, plain, (![B_140]: (k12_lattice3('#skF_3', B_140, '#skF_5')=k11_lattice3('#skF_3', B_140, '#skF_5') | ~m1_subset_1(B_140, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_300])).
% 7.45/2.59  tff(c_381, plain, (![B_142]: (k12_lattice3('#skF_3', B_142, '#skF_5')=k11_lattice3('#skF_3', B_142, '#skF_5') | ~m1_subset_1(B_142, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_52, c_312])).
% 7.45/2.59  tff(c_419, plain, (k12_lattice3('#skF_3', '#skF_4', '#skF_5')=k11_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_381])).
% 7.45/2.59  tff(c_65, plain, (![A_129, C_130, B_131]: (k12_lattice3(A_129, C_130, B_131)=k12_lattice3(A_129, B_131, C_130) | ~m1_subset_1(C_130, u1_struct_0(A_129)) | ~m1_subset_1(B_131, u1_struct_0(A_129)) | ~l1_orders_2(A_129) | ~v2_lattice3(A_129) | ~v5_orders_2(A_129))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.45/2.59  tff(c_71, plain, (![B_131]: (k12_lattice3('#skF_3', B_131, '#skF_5')=k12_lattice3('#skF_3', '#skF_5', B_131) | ~m1_subset_1(B_131, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_65])).
% 7.45/2.59  tff(c_82, plain, (![B_132]: (k12_lattice3('#skF_3', B_132, '#skF_5')=k12_lattice3('#skF_3', '#skF_5', B_132) | ~m1_subset_1(B_132, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_52, c_71])).
% 7.45/2.59  tff(c_105, plain, (k12_lattice3('#skF_3', '#skF_5', '#skF_4')=k12_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_82])).
% 7.45/2.59  tff(c_8, plain, (![A_6, B_7, C_8]: (m1_subset_1(k12_lattice3(A_6, B_7, C_8), u1_struct_0(A_6)) | ~m1_subset_1(C_8, u1_struct_0(A_6)) | ~m1_subset_1(B_7, u1_struct_0(A_6)) | ~l1_orders_2(A_6) | ~v2_lattice3(A_6) | ~v5_orders_2(A_6))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.45/2.59  tff(c_109, plain, (m1_subset_1(k12_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_105, c_8])).
% 7.45/2.59  tff(c_113, plain, (m1_subset_1(k12_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_52, c_48, c_50, c_109])).
% 7.45/2.59  tff(c_499, plain, (m1_subset_1(k11_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_419, c_113])).
% 7.45/2.59  tff(c_500, plain, (k12_lattice3('#skF_3', '#skF_5', '#skF_4')=k11_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_419, c_105])).
% 7.45/2.59  tff(c_60, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_202])).
% 7.45/2.59  tff(c_545, plain, (![A_143, B_144, C_145]: (k13_lattice3(A_143, k12_lattice3(A_143, B_144, C_145), C_145)=C_145 | ~m1_subset_1(C_145, u1_struct_0(A_143)) | ~m1_subset_1(B_144, u1_struct_0(A_143)) | ~l1_orders_2(A_143) | ~v2_lattice3(A_143) | ~v1_lattice3(A_143) | ~v5_orders_2(A_143) | ~v3_orders_2(A_143))), inference(cnfTransformation, [status(thm)], [f_183])).
% 7.45/2.59  tff(c_565, plain, (![B_144]: (k13_lattice3('#skF_3', k12_lattice3('#skF_3', B_144, '#skF_4'), '#skF_4')='#skF_4' | ~m1_subset_1(B_144, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | ~v3_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_545])).
% 7.45/2.59  tff(c_707, plain, (![B_147]: (k13_lattice3('#skF_3', k12_lattice3('#skF_3', B_147, '#skF_4'), '#skF_4')='#skF_4' | ~m1_subset_1(B_147, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_52, c_565])).
% 7.45/2.59  tff(c_739, plain, (k13_lattice3('#skF_3', k12_lattice3('#skF_3', '#skF_5', '#skF_4'), '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_48, c_707])).
% 7.45/2.59  tff(c_757, plain, (k13_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_500, c_739])).
% 7.45/2.59  tff(c_291, plain, (k13_lattice3('#skF_3', k12_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')=k10_lattice3('#skF_3', k12_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_113, c_265])).
% 7.45/2.59  tff(c_2357, plain, (k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_419, c_757, c_419, c_291])).
% 7.45/2.59  tff(c_22, plain, (![A_12, C_48, B_36]: (r1_orders_2(A_12, C_48, k10_lattice3(A_12, B_36, C_48)) | ~m1_subset_1(k10_lattice3(A_12, B_36, C_48), u1_struct_0(A_12)) | ~m1_subset_1(C_48, u1_struct_0(A_12)) | ~m1_subset_1(B_36, u1_struct_0(A_12)) | ~l1_orders_2(A_12) | ~v1_lattice3(A_12) | ~v5_orders_2(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.45/2.59  tff(c_2360, plain, (r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', k11_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1(k11_lattice3('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v1_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2357, c_22])).
% 7.45/2.59  tff(c_2366, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_499, c_50, c_50, c_2357, c_2360])).
% 7.45/2.59  tff(c_2367, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_811, c_2366])).
% 7.45/2.59  tff(c_2159, plain, (![A_181, B_182, C_183, D_184]: (r1_orders_2(A_181, '#skF_2'(A_181, B_182, C_183, D_184), C_183) | k11_lattice3(A_181, B_182, C_183)=D_184 | ~r1_orders_2(A_181, D_184, C_183) | ~r1_orders_2(A_181, D_184, B_182) | ~m1_subset_1(D_184, u1_struct_0(A_181)) | ~m1_subset_1(C_183, u1_struct_0(A_181)) | ~m1_subset_1(B_182, u1_struct_0(A_181)) | ~l1_orders_2(A_181) | ~v2_lattice3(A_181) | ~v5_orders_2(A_181) | v2_struct_0(A_181))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.45/2.59  tff(c_26, plain, (![A_58, B_82, C_94, D_100]: (~r1_orders_2(A_58, '#skF_2'(A_58, B_82, C_94, D_100), D_100) | k11_lattice3(A_58, B_82, C_94)=D_100 | ~r1_orders_2(A_58, D_100, C_94) | ~r1_orders_2(A_58, D_100, B_82) | ~m1_subset_1(D_100, u1_struct_0(A_58)) | ~m1_subset_1(C_94, u1_struct_0(A_58)) | ~m1_subset_1(B_82, u1_struct_0(A_58)) | ~l1_orders_2(A_58) | ~v2_lattice3(A_58) | ~v5_orders_2(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.45/2.59  tff(c_3155, plain, (![A_201, B_202, C_203]: (k11_lattice3(A_201, B_202, C_203)=C_203 | ~r1_orders_2(A_201, C_203, C_203) | ~r1_orders_2(A_201, C_203, B_202) | ~m1_subset_1(C_203, u1_struct_0(A_201)) | ~m1_subset_1(B_202, u1_struct_0(A_201)) | ~l1_orders_2(A_201) | ~v2_lattice3(A_201) | ~v5_orders_2(A_201) | v2_struct_0(A_201))), inference(resolution, [status(thm)], [c_2159, c_26])).
% 7.45/2.59  tff(c_3157, plain, (![B_202]: (k11_lattice3('#skF_3', B_202, '#skF_4')='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', B_202) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1(B_202, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_2367, c_3155])).
% 7.45/2.59  tff(c_3162, plain, (![B_202]: (k11_lattice3('#skF_3', B_202, '#skF_4')='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', B_202) | ~m1_subset_1(B_202, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_52, c_50, c_3157])).
% 7.45/2.59  tff(c_3168, plain, (![B_204]: (k11_lattice3('#skF_3', B_204, '#skF_4')='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', B_204) | ~m1_subset_1(B_204, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_811, c_3162])).
% 7.45/2.59  tff(c_3254, plain, (k11_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')='#skF_4' | ~r1_orders_2('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_241, c_3168])).
% 7.45/2.59  tff(c_3319, plain, (k11_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_918, c_3254])).
% 7.45/2.59  tff(c_314, plain, (![B_140]: (k12_lattice3('#skF_3', B_140, '#skF_4')=k11_lattice3('#skF_3', B_140, '#skF_4') | ~m1_subset_1(B_140, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_300])).
% 7.45/2.59  tff(c_602, plain, (![B_146]: (k12_lattice3('#skF_3', B_146, '#skF_4')=k11_lattice3('#skF_3', B_146, '#skF_4') | ~m1_subset_1(B_146, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_52, c_314])).
% 7.45/2.59  tff(c_639, plain, (k12_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')=k11_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_241, c_602])).
% 7.45/2.59  tff(c_5497, plain, (k12_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3319, c_639])).
% 7.45/2.59  tff(c_73, plain, (![B_131]: (k12_lattice3('#skF_3', B_131, '#skF_4')=k12_lattice3('#skF_3', '#skF_4', B_131) | ~m1_subset_1(B_131, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v2_lattice3('#skF_3') | ~v5_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_65])).
% 7.45/2.59  tff(c_81, plain, (![B_131]: (k12_lattice3('#skF_3', B_131, '#skF_4')=k12_lattice3('#skF_3', '#skF_4', B_131) | ~m1_subset_1(B_131, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_52, c_73])).
% 7.45/2.59  tff(c_257, plain, (k12_lattice3('#skF_3', k10_lattice3('#skF_3', '#skF_4', '#skF_5'), '#skF_4')=k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_241, c_81])).
% 7.45/2.59  tff(c_5498, plain, (k12_lattice3('#skF_3', '#skF_4', k10_lattice3('#skF_3', '#skF_4', '#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5497, c_257])).
% 7.45/2.59  tff(c_5500, plain, $false, inference(negUnitSimplification, [status(thm)], [c_233, c_5498])).
% 7.45/2.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.45/2.59  
% 7.45/2.59  Inference rules
% 7.45/2.59  ----------------------
% 7.45/2.59  #Ref     : 0
% 7.45/2.59  #Sup     : 1197
% 7.45/2.59  #Fact    : 0
% 7.45/2.59  #Define  : 0
% 7.45/2.59  #Split   : 3
% 7.45/2.59  #Chain   : 0
% 7.45/2.59  #Close   : 0
% 7.45/2.59  
% 7.45/2.59  Ordering : KBO
% 7.45/2.59  
% 7.45/2.59  Simplification rules
% 7.45/2.59  ----------------------
% 7.45/2.59  #Subsume      : 2
% 7.45/2.59  #Demod        : 2920
% 7.45/2.59  #Tautology    : 449
% 7.45/2.59  #SimpNegUnit  : 243
% 7.45/2.59  #BackRed      : 102
% 7.45/2.59  
% 7.45/2.59  #Partial instantiations: 0
% 7.45/2.59  #Strategies tried      : 1
% 7.45/2.59  
% 7.70/2.59  Timing (in seconds)
% 7.70/2.59  ----------------------
% 7.70/2.60  Preprocessing        : 0.39
% 7.70/2.60  Parsing              : 0.20
% 7.70/2.60  CNF conversion       : 0.03
% 7.70/2.60  Main loop            : 1.41
% 7.70/2.60  Inferencing          : 0.37
% 7.70/2.60  Reduction            : 0.58
% 7.70/2.60  Demodulation         : 0.44
% 7.70/2.60  BG Simplification    : 0.06
% 7.70/2.60  Subsumption          : 0.30
% 7.70/2.60  Abstraction          : 0.08
% 7.70/2.60  MUC search           : 0.00
% 7.70/2.60  Cooper               : 0.00
% 7.70/2.60  Total                : 1.84
% 7.70/2.60  Index Insertion      : 0.00
% 7.70/2.60  Index Deletion       : 0.00
% 7.70/2.60  Index Matching       : 0.00
% 7.70/2.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
