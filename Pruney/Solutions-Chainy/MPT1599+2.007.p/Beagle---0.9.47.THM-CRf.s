%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:23 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 183 expanded)
%              Number of leaves         :   35 (  85 expanded)
%              Depth                    :   12
%              Number of atoms          :  254 ( 482 expanded)
%              Number of equality atoms :    4 (  68 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k11_lattice3 > k3_xboole_0 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k11_lattice3,type,(
    k11_lattice3: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_145,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( v2_lattice3(k2_yellow_1(A))
         => ! [B] :
              ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(A),B,C),k3_xboole_0(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_1)).

tff(f_118,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k11_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_lattice3)).

tff(f_106,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_94,axiom,(
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

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_131,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

tff(c_28,plain,(
    ! [A_57] : l1_orders_2(k2_yellow_1(A_57)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_56,plain,(
    v2_lattice3(k2_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_42,plain,(
    ! [A_60] : u1_struct_0(k2_yellow_1(A_60)) = A_60 ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_59,plain,(
    m1_subset_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_54])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_60,plain,(
    m1_subset_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_52])).

tff(c_228,plain,(
    ! [A_148,B_149,C_150] :
      ( m1_subset_1(k11_lattice3(A_148,B_149,C_150),u1_struct_0(A_148))
      | ~ m1_subset_1(C_150,u1_struct_0(A_148))
      | ~ m1_subset_1(B_149,u1_struct_0(A_148))
      | ~ l1_orders_2(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_231,plain,(
    ! [A_60,B_149,C_150] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_60),B_149,C_150),A_60)
      | ~ m1_subset_1(C_150,u1_struct_0(k2_yellow_1(A_60)))
      | ~ m1_subset_1(B_149,u1_struct_0(k2_yellow_1(A_60)))
      | ~ l1_orders_2(k2_yellow_1(A_60)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_228])).

tff(c_233,plain,(
    ! [A_60,B_149,C_150] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_60),B_149,C_150),A_60)
      | ~ m1_subset_1(C_150,A_60)
      | ~ m1_subset_1(B_149,A_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_42,c_42,c_231])).

tff(c_36,plain,(
    ! [A_58] : v5_orders_2(k2_yellow_1(A_58)) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k11_lattice3(A_8,B_9,C_10),u1_struct_0(A_8))
      | ~ m1_subset_1(C_10,u1_struct_0(A_8))
      | ~ m1_subset_1(B_9,u1_struct_0(A_8))
      | ~ l1_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_269,plain,(
    ! [A_169,B_170,C_171] :
      ( r1_orders_2(A_169,k11_lattice3(A_169,B_170,C_171),C_171)
      | ~ m1_subset_1(k11_lattice3(A_169,B_170,C_171),u1_struct_0(A_169))
      | ~ m1_subset_1(C_171,u1_struct_0(A_169))
      | ~ m1_subset_1(B_170,u1_struct_0(A_169))
      | ~ l1_orders_2(A_169)
      | ~ v2_lattice3(A_169)
      | ~ v5_orders_2(A_169)
      | v2_struct_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_285,plain,(
    ! [A_175,B_176,C_177] :
      ( r1_orders_2(A_175,k11_lattice3(A_175,B_176,C_177),C_177)
      | ~ v2_lattice3(A_175)
      | ~ v5_orders_2(A_175)
      | v2_struct_0(A_175)
      | ~ m1_subset_1(C_177,u1_struct_0(A_175))
      | ~ m1_subset_1(B_176,u1_struct_0(A_175))
      | ~ l1_orders_2(A_175) ) ),
    inference(resolution,[status(thm)],[c_10,c_269])).

tff(c_32,plain,(
    ! [A_58] : v3_orders_2(k2_yellow_1(A_58)) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_242,plain,(
    ! [A_160,B_161,C_162] :
      ( r3_orders_2(A_160,B_161,C_162)
      | ~ r1_orders_2(A_160,B_161,C_162)
      | ~ m1_subset_1(C_162,u1_struct_0(A_160))
      | ~ m1_subset_1(B_161,u1_struct_0(A_160))
      | ~ l1_orders_2(A_160)
      | ~ v3_orders_2(A_160)
      | v2_struct_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_249,plain,(
    ! [A_60,B_161,C_162] :
      ( r3_orders_2(k2_yellow_1(A_60),B_161,C_162)
      | ~ r1_orders_2(k2_yellow_1(A_60),B_161,C_162)
      | ~ m1_subset_1(C_162,A_60)
      | ~ m1_subset_1(B_161,u1_struct_0(k2_yellow_1(A_60)))
      | ~ l1_orders_2(k2_yellow_1(A_60))
      | ~ v3_orders_2(k2_yellow_1(A_60))
      | v2_struct_0(k2_yellow_1(A_60)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_242])).

tff(c_254,plain,(
    ! [A_163,B_164,C_165] :
      ( r3_orders_2(k2_yellow_1(A_163),B_164,C_165)
      | ~ r1_orders_2(k2_yellow_1(A_163),B_164,C_165)
      | ~ m1_subset_1(C_165,A_163)
      | ~ m1_subset_1(B_164,A_163)
      | v2_struct_0(k2_yellow_1(A_163)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_42,c_249])).

tff(c_48,plain,(
    ! [B_65,C_67,A_61] :
      ( r1_tarski(B_65,C_67)
      | ~ r3_orders_2(k2_yellow_1(A_61),B_65,C_67)
      | ~ m1_subset_1(C_67,u1_struct_0(k2_yellow_1(A_61)))
      | ~ m1_subset_1(B_65,u1_struct_0(k2_yellow_1(A_61)))
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_61,plain,(
    ! [B_65,C_67,A_61] :
      ( r1_tarski(B_65,C_67)
      | ~ r3_orders_2(k2_yellow_1(A_61),B_65,C_67)
      | ~ m1_subset_1(C_67,A_61)
      | ~ m1_subset_1(B_65,A_61)
      | v1_xboole_0(A_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_48])).

tff(c_263,plain,(
    ! [B_164,C_165,A_163] :
      ( r1_tarski(B_164,C_165)
      | v1_xboole_0(A_163)
      | ~ r1_orders_2(k2_yellow_1(A_163),B_164,C_165)
      | ~ m1_subset_1(C_165,A_163)
      | ~ m1_subset_1(B_164,A_163)
      | v2_struct_0(k2_yellow_1(A_163)) ) ),
    inference(resolution,[status(thm)],[c_254,c_61])).

tff(c_289,plain,(
    ! [A_163,B_176,C_177] :
      ( r1_tarski(k11_lattice3(k2_yellow_1(A_163),B_176,C_177),C_177)
      | v1_xboole_0(A_163)
      | ~ m1_subset_1(C_177,A_163)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(A_163),B_176,C_177),A_163)
      | ~ v2_lattice3(k2_yellow_1(A_163))
      | ~ v5_orders_2(k2_yellow_1(A_163))
      | v2_struct_0(k2_yellow_1(A_163))
      | ~ m1_subset_1(C_177,u1_struct_0(k2_yellow_1(A_163)))
      | ~ m1_subset_1(B_176,u1_struct_0(k2_yellow_1(A_163)))
      | ~ l1_orders_2(k2_yellow_1(A_163)) ) ),
    inference(resolution,[status(thm)],[c_285,c_263])).

tff(c_324,plain,(
    ! [A_197,B_198,C_199] :
      ( r1_tarski(k11_lattice3(k2_yellow_1(A_197),B_198,C_199),C_199)
      | v1_xboole_0(A_197)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(A_197),B_198,C_199),A_197)
      | ~ v2_lattice3(k2_yellow_1(A_197))
      | v2_struct_0(k2_yellow_1(A_197))
      | ~ m1_subset_1(C_199,A_197)
      | ~ m1_subset_1(B_198,A_197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_42,c_42,c_36,c_289])).

tff(c_328,plain,(
    ! [A_200,B_201,C_202] :
      ( r1_tarski(k11_lattice3(k2_yellow_1(A_200),B_201,C_202),C_202)
      | v1_xboole_0(A_200)
      | ~ v2_lattice3(k2_yellow_1(A_200))
      | v2_struct_0(k2_yellow_1(A_200))
      | ~ m1_subset_1(C_202,A_200)
      | ~ m1_subset_1(B_201,A_200) ) ),
    inference(resolution,[status(thm)],[c_233,c_324])).

tff(c_102,plain,(
    ! [A_90,B_91,C_92] :
      ( m1_subset_1(k11_lattice3(A_90,B_91,C_92),u1_struct_0(A_90))
      | ~ m1_subset_1(C_92,u1_struct_0(A_90))
      | ~ m1_subset_1(B_91,u1_struct_0(A_90))
      | ~ l1_orders_2(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_105,plain,(
    ! [A_60,B_91,C_92] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_60),B_91,C_92),A_60)
      | ~ m1_subset_1(C_92,u1_struct_0(k2_yellow_1(A_60)))
      | ~ m1_subset_1(B_91,u1_struct_0(k2_yellow_1(A_60)))
      | ~ l1_orders_2(k2_yellow_1(A_60)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_102])).

tff(c_107,plain,(
    ! [A_60,B_91,C_92] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_60),B_91,C_92),A_60)
      | ~ m1_subset_1(C_92,A_60)
      | ~ m1_subset_1(B_91,A_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_42,c_42,c_105])).

tff(c_138,plain,(
    ! [A_108,B_109,C_110] :
      ( r1_orders_2(A_108,k11_lattice3(A_108,B_109,C_110),B_109)
      | ~ m1_subset_1(k11_lattice3(A_108,B_109,C_110),u1_struct_0(A_108))
      | ~ m1_subset_1(C_110,u1_struct_0(A_108))
      | ~ m1_subset_1(B_109,u1_struct_0(A_108))
      | ~ l1_orders_2(A_108)
      | ~ v2_lattice3(A_108)
      | ~ v5_orders_2(A_108)
      | v2_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_151,plain,(
    ! [A_114,B_115,C_116] :
      ( r1_orders_2(A_114,k11_lattice3(A_114,B_115,C_116),B_115)
      | ~ v2_lattice3(A_114)
      | ~ v5_orders_2(A_114)
      | v2_struct_0(A_114)
      | ~ m1_subset_1(C_116,u1_struct_0(A_114))
      | ~ m1_subset_1(B_115,u1_struct_0(A_114))
      | ~ l1_orders_2(A_114) ) ),
    inference(resolution,[status(thm)],[c_10,c_138])).

tff(c_109,plain,(
    ! [A_96,B_97,C_98] :
      ( r3_orders_2(A_96,B_97,C_98)
      | ~ r1_orders_2(A_96,B_97,C_98)
      | ~ m1_subset_1(C_98,u1_struct_0(A_96))
      | ~ m1_subset_1(B_97,u1_struct_0(A_96))
      | ~ l1_orders_2(A_96)
      | ~ v3_orders_2(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_116,plain,(
    ! [A_60,B_97,C_98] :
      ( r3_orders_2(k2_yellow_1(A_60),B_97,C_98)
      | ~ r1_orders_2(k2_yellow_1(A_60),B_97,C_98)
      | ~ m1_subset_1(C_98,A_60)
      | ~ m1_subset_1(B_97,u1_struct_0(k2_yellow_1(A_60)))
      | ~ l1_orders_2(k2_yellow_1(A_60))
      | ~ v3_orders_2(k2_yellow_1(A_60))
      | v2_struct_0(k2_yellow_1(A_60)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_109])).

tff(c_121,plain,(
    ! [A_99,B_100,C_101] :
      ( r3_orders_2(k2_yellow_1(A_99),B_100,C_101)
      | ~ r1_orders_2(k2_yellow_1(A_99),B_100,C_101)
      | ~ m1_subset_1(C_101,A_99)
      | ~ m1_subset_1(B_100,A_99)
      | v2_struct_0(k2_yellow_1(A_99)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_42,c_116])).

tff(c_125,plain,(
    ! [B_100,C_101,A_99] :
      ( r1_tarski(B_100,C_101)
      | v1_xboole_0(A_99)
      | ~ r1_orders_2(k2_yellow_1(A_99),B_100,C_101)
      | ~ m1_subset_1(C_101,A_99)
      | ~ m1_subset_1(B_100,A_99)
      | v2_struct_0(k2_yellow_1(A_99)) ) ),
    inference(resolution,[status(thm)],[c_121,c_61])).

tff(c_155,plain,(
    ! [A_99,B_115,C_116] :
      ( r1_tarski(k11_lattice3(k2_yellow_1(A_99),B_115,C_116),B_115)
      | v1_xboole_0(A_99)
      | ~ m1_subset_1(B_115,A_99)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(A_99),B_115,C_116),A_99)
      | ~ v2_lattice3(k2_yellow_1(A_99))
      | ~ v5_orders_2(k2_yellow_1(A_99))
      | v2_struct_0(k2_yellow_1(A_99))
      | ~ m1_subset_1(C_116,u1_struct_0(k2_yellow_1(A_99)))
      | ~ m1_subset_1(B_115,u1_struct_0(k2_yellow_1(A_99)))
      | ~ l1_orders_2(k2_yellow_1(A_99)) ) ),
    inference(resolution,[status(thm)],[c_151,c_125])).

tff(c_190,plain,(
    ! [A_135,B_136,C_137] :
      ( r1_tarski(k11_lattice3(k2_yellow_1(A_135),B_136,C_137),B_136)
      | v1_xboole_0(A_135)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(A_135),B_136,C_137),A_135)
      | ~ v2_lattice3(k2_yellow_1(A_135))
      | v2_struct_0(k2_yellow_1(A_135))
      | ~ m1_subset_1(C_137,A_135)
      | ~ m1_subset_1(B_136,A_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_42,c_42,c_36,c_155])).

tff(c_203,plain,(
    ! [A_142,B_143,C_144] :
      ( r1_tarski(k11_lattice3(k2_yellow_1(A_142),B_143,C_144),B_143)
      | v1_xboole_0(A_142)
      | ~ v2_lattice3(k2_yellow_1(A_142))
      | v2_struct_0(k2_yellow_1(A_142))
      | ~ m1_subset_1(C_144,A_142)
      | ~ m1_subset_1(B_143,A_142) ) ),
    inference(resolution,[status(thm)],[c_107,c_190])).

tff(c_90,plain,(
    ! [A_81,B_82,C_83] :
      ( r1_tarski(A_81,k3_xboole_0(B_82,C_83))
      | ~ r1_tarski(A_81,C_83)
      | ~ r1_tarski(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),k3_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_94,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4')
    | ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_50])).

tff(c_96,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_206,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v2_lattice3(k2_yellow_1('#skF_2'))
    | v2_struct_0(k2_yellow_1('#skF_2'))
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_203,c_96])).

tff(c_209,plain,
    ( v1_xboole_0('#skF_2')
    | v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_60,c_56,c_206])).

tff(c_210,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_209])).

tff(c_8,plain,(
    ! [A_7] :
      ( ~ v2_struct_0(A_7)
      | ~ v2_lattice3(A_7)
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_213,plain,
    ( ~ v2_lattice3(k2_yellow_1('#skF_2'))
    | ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_210,c_8])).

tff(c_220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_56,c_213])).

tff(c_221,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_331,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v2_lattice3(k2_yellow_1('#skF_2'))
    | v2_struct_0(k2_yellow_1('#skF_2'))
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_328,c_221])).

tff(c_334,plain,
    ( v1_xboole_0('#skF_2')
    | v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_60,c_56,c_331])).

tff(c_335,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_334])).

tff(c_338,plain,
    ( ~ v2_lattice3(k2_yellow_1('#skF_2'))
    | ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_335,c_8])).

tff(c_345,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_56,c_338])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n024.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 10:41:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.39  
% 2.68/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.40  %$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k11_lattice3 > k3_xboole_0 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.68/1.40  
% 2.68/1.40  %Foreground sorts:
% 2.68/1.40  
% 2.68/1.40  
% 2.68/1.40  %Background operators:
% 2.68/1.40  
% 2.68/1.40  
% 2.68/1.40  %Foreground operators:
% 2.68/1.40  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.68/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.68/1.40  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 2.68/1.40  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.68/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.40  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.68/1.40  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.68/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.68/1.40  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 2.68/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.68/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.68/1.40  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.68/1.40  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.68/1.40  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.68/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.68/1.40  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.68/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.68/1.40  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 2.68/1.40  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.68/1.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.68/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.68/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.68/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.68/1.40  
% 2.68/1.42  tff(f_98, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.68/1.42  tff(f_145, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (v2_lattice3(k2_yellow_1(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => r1_tarski(k11_lattice3(k2_yellow_1(A), B, C), k3_xboole_0(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_yellow_1)).
% 2.68/1.42  tff(f_118, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.68/1.42  tff(f_61, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k11_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k11_lattice3)).
% 2.68/1.42  tff(f_106, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 2.68/1.42  tff(f_94, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k11_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l28_lattice3)).
% 2.68/1.42  tff(f_46, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 2.68/1.42  tff(f_131, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 2.68/1.42  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.68/1.42  tff(f_53, axiom, (![A]: (l1_orders_2(A) => (v2_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_lattice3)).
% 2.68/1.42  tff(c_28, plain, (![A_57]: (l1_orders_2(k2_yellow_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.68/1.42  tff(c_56, plain, (v2_lattice3(k2_yellow_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.68/1.42  tff(c_58, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.68/1.42  tff(c_42, plain, (![A_60]: (u1_struct_0(k2_yellow_1(A_60))=A_60)), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.68/1.42  tff(c_54, plain, (m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.68/1.42  tff(c_59, plain, (m1_subset_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_54])).
% 2.68/1.42  tff(c_52, plain, (m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.68/1.42  tff(c_60, plain, (m1_subset_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_52])).
% 2.68/1.42  tff(c_228, plain, (![A_148, B_149, C_150]: (m1_subset_1(k11_lattice3(A_148, B_149, C_150), u1_struct_0(A_148)) | ~m1_subset_1(C_150, u1_struct_0(A_148)) | ~m1_subset_1(B_149, u1_struct_0(A_148)) | ~l1_orders_2(A_148))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.68/1.42  tff(c_231, plain, (![A_60, B_149, C_150]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_60), B_149, C_150), A_60) | ~m1_subset_1(C_150, u1_struct_0(k2_yellow_1(A_60))) | ~m1_subset_1(B_149, u1_struct_0(k2_yellow_1(A_60))) | ~l1_orders_2(k2_yellow_1(A_60)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_228])).
% 2.68/1.42  tff(c_233, plain, (![A_60, B_149, C_150]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_60), B_149, C_150), A_60) | ~m1_subset_1(C_150, A_60) | ~m1_subset_1(B_149, A_60))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_42, c_42, c_231])).
% 2.68/1.42  tff(c_36, plain, (![A_58]: (v5_orders_2(k2_yellow_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.68/1.42  tff(c_10, plain, (![A_8, B_9, C_10]: (m1_subset_1(k11_lattice3(A_8, B_9, C_10), u1_struct_0(A_8)) | ~m1_subset_1(C_10, u1_struct_0(A_8)) | ~m1_subset_1(B_9, u1_struct_0(A_8)) | ~l1_orders_2(A_8))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.68/1.42  tff(c_269, plain, (![A_169, B_170, C_171]: (r1_orders_2(A_169, k11_lattice3(A_169, B_170, C_171), C_171) | ~m1_subset_1(k11_lattice3(A_169, B_170, C_171), u1_struct_0(A_169)) | ~m1_subset_1(C_171, u1_struct_0(A_169)) | ~m1_subset_1(B_170, u1_struct_0(A_169)) | ~l1_orders_2(A_169) | ~v2_lattice3(A_169) | ~v5_orders_2(A_169) | v2_struct_0(A_169))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.68/1.42  tff(c_285, plain, (![A_175, B_176, C_177]: (r1_orders_2(A_175, k11_lattice3(A_175, B_176, C_177), C_177) | ~v2_lattice3(A_175) | ~v5_orders_2(A_175) | v2_struct_0(A_175) | ~m1_subset_1(C_177, u1_struct_0(A_175)) | ~m1_subset_1(B_176, u1_struct_0(A_175)) | ~l1_orders_2(A_175))), inference(resolution, [status(thm)], [c_10, c_269])).
% 2.68/1.42  tff(c_32, plain, (![A_58]: (v3_orders_2(k2_yellow_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.68/1.42  tff(c_242, plain, (![A_160, B_161, C_162]: (r3_orders_2(A_160, B_161, C_162) | ~r1_orders_2(A_160, B_161, C_162) | ~m1_subset_1(C_162, u1_struct_0(A_160)) | ~m1_subset_1(B_161, u1_struct_0(A_160)) | ~l1_orders_2(A_160) | ~v3_orders_2(A_160) | v2_struct_0(A_160))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.68/1.42  tff(c_249, plain, (![A_60, B_161, C_162]: (r3_orders_2(k2_yellow_1(A_60), B_161, C_162) | ~r1_orders_2(k2_yellow_1(A_60), B_161, C_162) | ~m1_subset_1(C_162, A_60) | ~m1_subset_1(B_161, u1_struct_0(k2_yellow_1(A_60))) | ~l1_orders_2(k2_yellow_1(A_60)) | ~v3_orders_2(k2_yellow_1(A_60)) | v2_struct_0(k2_yellow_1(A_60)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_242])).
% 2.68/1.42  tff(c_254, plain, (![A_163, B_164, C_165]: (r3_orders_2(k2_yellow_1(A_163), B_164, C_165) | ~r1_orders_2(k2_yellow_1(A_163), B_164, C_165) | ~m1_subset_1(C_165, A_163) | ~m1_subset_1(B_164, A_163) | v2_struct_0(k2_yellow_1(A_163)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_42, c_249])).
% 2.68/1.42  tff(c_48, plain, (![B_65, C_67, A_61]: (r1_tarski(B_65, C_67) | ~r3_orders_2(k2_yellow_1(A_61), B_65, C_67) | ~m1_subset_1(C_67, u1_struct_0(k2_yellow_1(A_61))) | ~m1_subset_1(B_65, u1_struct_0(k2_yellow_1(A_61))) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.68/1.42  tff(c_61, plain, (![B_65, C_67, A_61]: (r1_tarski(B_65, C_67) | ~r3_orders_2(k2_yellow_1(A_61), B_65, C_67) | ~m1_subset_1(C_67, A_61) | ~m1_subset_1(B_65, A_61) | v1_xboole_0(A_61))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_48])).
% 2.68/1.42  tff(c_263, plain, (![B_164, C_165, A_163]: (r1_tarski(B_164, C_165) | v1_xboole_0(A_163) | ~r1_orders_2(k2_yellow_1(A_163), B_164, C_165) | ~m1_subset_1(C_165, A_163) | ~m1_subset_1(B_164, A_163) | v2_struct_0(k2_yellow_1(A_163)))), inference(resolution, [status(thm)], [c_254, c_61])).
% 2.68/1.42  tff(c_289, plain, (![A_163, B_176, C_177]: (r1_tarski(k11_lattice3(k2_yellow_1(A_163), B_176, C_177), C_177) | v1_xboole_0(A_163) | ~m1_subset_1(C_177, A_163) | ~m1_subset_1(k11_lattice3(k2_yellow_1(A_163), B_176, C_177), A_163) | ~v2_lattice3(k2_yellow_1(A_163)) | ~v5_orders_2(k2_yellow_1(A_163)) | v2_struct_0(k2_yellow_1(A_163)) | ~m1_subset_1(C_177, u1_struct_0(k2_yellow_1(A_163))) | ~m1_subset_1(B_176, u1_struct_0(k2_yellow_1(A_163))) | ~l1_orders_2(k2_yellow_1(A_163)))), inference(resolution, [status(thm)], [c_285, c_263])).
% 2.68/1.42  tff(c_324, plain, (![A_197, B_198, C_199]: (r1_tarski(k11_lattice3(k2_yellow_1(A_197), B_198, C_199), C_199) | v1_xboole_0(A_197) | ~m1_subset_1(k11_lattice3(k2_yellow_1(A_197), B_198, C_199), A_197) | ~v2_lattice3(k2_yellow_1(A_197)) | v2_struct_0(k2_yellow_1(A_197)) | ~m1_subset_1(C_199, A_197) | ~m1_subset_1(B_198, A_197))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_42, c_42, c_36, c_289])).
% 2.68/1.42  tff(c_328, plain, (![A_200, B_201, C_202]: (r1_tarski(k11_lattice3(k2_yellow_1(A_200), B_201, C_202), C_202) | v1_xboole_0(A_200) | ~v2_lattice3(k2_yellow_1(A_200)) | v2_struct_0(k2_yellow_1(A_200)) | ~m1_subset_1(C_202, A_200) | ~m1_subset_1(B_201, A_200))), inference(resolution, [status(thm)], [c_233, c_324])).
% 2.68/1.42  tff(c_102, plain, (![A_90, B_91, C_92]: (m1_subset_1(k11_lattice3(A_90, B_91, C_92), u1_struct_0(A_90)) | ~m1_subset_1(C_92, u1_struct_0(A_90)) | ~m1_subset_1(B_91, u1_struct_0(A_90)) | ~l1_orders_2(A_90))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.68/1.42  tff(c_105, plain, (![A_60, B_91, C_92]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_60), B_91, C_92), A_60) | ~m1_subset_1(C_92, u1_struct_0(k2_yellow_1(A_60))) | ~m1_subset_1(B_91, u1_struct_0(k2_yellow_1(A_60))) | ~l1_orders_2(k2_yellow_1(A_60)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_102])).
% 2.68/1.42  tff(c_107, plain, (![A_60, B_91, C_92]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_60), B_91, C_92), A_60) | ~m1_subset_1(C_92, A_60) | ~m1_subset_1(B_91, A_60))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_42, c_42, c_105])).
% 2.68/1.42  tff(c_138, plain, (![A_108, B_109, C_110]: (r1_orders_2(A_108, k11_lattice3(A_108, B_109, C_110), B_109) | ~m1_subset_1(k11_lattice3(A_108, B_109, C_110), u1_struct_0(A_108)) | ~m1_subset_1(C_110, u1_struct_0(A_108)) | ~m1_subset_1(B_109, u1_struct_0(A_108)) | ~l1_orders_2(A_108) | ~v2_lattice3(A_108) | ~v5_orders_2(A_108) | v2_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.68/1.42  tff(c_151, plain, (![A_114, B_115, C_116]: (r1_orders_2(A_114, k11_lattice3(A_114, B_115, C_116), B_115) | ~v2_lattice3(A_114) | ~v5_orders_2(A_114) | v2_struct_0(A_114) | ~m1_subset_1(C_116, u1_struct_0(A_114)) | ~m1_subset_1(B_115, u1_struct_0(A_114)) | ~l1_orders_2(A_114))), inference(resolution, [status(thm)], [c_10, c_138])).
% 2.68/1.42  tff(c_109, plain, (![A_96, B_97, C_98]: (r3_orders_2(A_96, B_97, C_98) | ~r1_orders_2(A_96, B_97, C_98) | ~m1_subset_1(C_98, u1_struct_0(A_96)) | ~m1_subset_1(B_97, u1_struct_0(A_96)) | ~l1_orders_2(A_96) | ~v3_orders_2(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.68/1.42  tff(c_116, plain, (![A_60, B_97, C_98]: (r3_orders_2(k2_yellow_1(A_60), B_97, C_98) | ~r1_orders_2(k2_yellow_1(A_60), B_97, C_98) | ~m1_subset_1(C_98, A_60) | ~m1_subset_1(B_97, u1_struct_0(k2_yellow_1(A_60))) | ~l1_orders_2(k2_yellow_1(A_60)) | ~v3_orders_2(k2_yellow_1(A_60)) | v2_struct_0(k2_yellow_1(A_60)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_109])).
% 2.68/1.42  tff(c_121, plain, (![A_99, B_100, C_101]: (r3_orders_2(k2_yellow_1(A_99), B_100, C_101) | ~r1_orders_2(k2_yellow_1(A_99), B_100, C_101) | ~m1_subset_1(C_101, A_99) | ~m1_subset_1(B_100, A_99) | v2_struct_0(k2_yellow_1(A_99)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_42, c_116])).
% 2.68/1.42  tff(c_125, plain, (![B_100, C_101, A_99]: (r1_tarski(B_100, C_101) | v1_xboole_0(A_99) | ~r1_orders_2(k2_yellow_1(A_99), B_100, C_101) | ~m1_subset_1(C_101, A_99) | ~m1_subset_1(B_100, A_99) | v2_struct_0(k2_yellow_1(A_99)))), inference(resolution, [status(thm)], [c_121, c_61])).
% 2.68/1.42  tff(c_155, plain, (![A_99, B_115, C_116]: (r1_tarski(k11_lattice3(k2_yellow_1(A_99), B_115, C_116), B_115) | v1_xboole_0(A_99) | ~m1_subset_1(B_115, A_99) | ~m1_subset_1(k11_lattice3(k2_yellow_1(A_99), B_115, C_116), A_99) | ~v2_lattice3(k2_yellow_1(A_99)) | ~v5_orders_2(k2_yellow_1(A_99)) | v2_struct_0(k2_yellow_1(A_99)) | ~m1_subset_1(C_116, u1_struct_0(k2_yellow_1(A_99))) | ~m1_subset_1(B_115, u1_struct_0(k2_yellow_1(A_99))) | ~l1_orders_2(k2_yellow_1(A_99)))), inference(resolution, [status(thm)], [c_151, c_125])).
% 2.68/1.42  tff(c_190, plain, (![A_135, B_136, C_137]: (r1_tarski(k11_lattice3(k2_yellow_1(A_135), B_136, C_137), B_136) | v1_xboole_0(A_135) | ~m1_subset_1(k11_lattice3(k2_yellow_1(A_135), B_136, C_137), A_135) | ~v2_lattice3(k2_yellow_1(A_135)) | v2_struct_0(k2_yellow_1(A_135)) | ~m1_subset_1(C_137, A_135) | ~m1_subset_1(B_136, A_135))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_42, c_42, c_36, c_155])).
% 2.68/1.42  tff(c_203, plain, (![A_142, B_143, C_144]: (r1_tarski(k11_lattice3(k2_yellow_1(A_142), B_143, C_144), B_143) | v1_xboole_0(A_142) | ~v2_lattice3(k2_yellow_1(A_142)) | v2_struct_0(k2_yellow_1(A_142)) | ~m1_subset_1(C_144, A_142) | ~m1_subset_1(B_143, A_142))), inference(resolution, [status(thm)], [c_107, c_190])).
% 2.68/1.42  tff(c_90, plain, (![A_81, B_82, C_83]: (r1_tarski(A_81, k3_xboole_0(B_82, C_83)) | ~r1_tarski(A_81, C_83) | ~r1_tarski(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.68/1.42  tff(c_50, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), k3_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.68/1.42  tff(c_94, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4') | ~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_90, c_50])).
% 2.68/1.42  tff(c_96, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_94])).
% 2.68/1.42  tff(c_206, plain, (v1_xboole_0('#skF_2') | ~v2_lattice3(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_203, c_96])).
% 2.68/1.42  tff(c_209, plain, (v1_xboole_0('#skF_2') | v2_struct_0(k2_yellow_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_60, c_56, c_206])).
% 2.68/1.42  tff(c_210, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_58, c_209])).
% 2.68/1.42  tff(c_8, plain, (![A_7]: (~v2_struct_0(A_7) | ~v2_lattice3(A_7) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.68/1.42  tff(c_213, plain, (~v2_lattice3(k2_yellow_1('#skF_2')) | ~l1_orders_2(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_210, c_8])).
% 2.68/1.42  tff(c_220, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_56, c_213])).
% 2.68/1.42  tff(c_221, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_94])).
% 2.68/1.42  tff(c_331, plain, (v1_xboole_0('#skF_2') | ~v2_lattice3(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_328, c_221])).
% 2.68/1.42  tff(c_334, plain, (v1_xboole_0('#skF_2') | v2_struct_0(k2_yellow_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_60, c_56, c_331])).
% 2.68/1.42  tff(c_335, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_58, c_334])).
% 2.68/1.42  tff(c_338, plain, (~v2_lattice3(k2_yellow_1('#skF_2')) | ~l1_orders_2(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_335, c_8])).
% 2.68/1.42  tff(c_345, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_56, c_338])).
% 2.68/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.42  
% 2.68/1.42  Inference rules
% 2.68/1.42  ----------------------
% 2.68/1.42  #Ref     : 0
% 2.68/1.42  #Sup     : 52
% 2.68/1.42  #Fact    : 0
% 2.68/1.42  #Define  : 0
% 2.68/1.42  #Split   : 1
% 2.68/1.42  #Chain   : 0
% 2.68/1.42  #Close   : 0
% 2.68/1.42  
% 2.68/1.42  Ordering : KBO
% 2.68/1.42  
% 2.68/1.42  Simplification rules
% 2.68/1.42  ----------------------
% 2.68/1.42  #Subsume      : 8
% 2.68/1.42  #Demod        : 88
% 2.68/1.42  #Tautology    : 12
% 2.68/1.42  #SimpNegUnit  : 2
% 2.68/1.42  #BackRed      : 0
% 2.68/1.42  
% 2.68/1.42  #Partial instantiations: 0
% 2.68/1.42  #Strategies tried      : 1
% 2.68/1.42  
% 2.68/1.42  Timing (in seconds)
% 2.68/1.42  ----------------------
% 2.68/1.42  Preprocessing        : 0.33
% 2.68/1.42  Parsing              : 0.18
% 2.68/1.42  CNF conversion       : 0.03
% 2.68/1.42  Main loop            : 0.30
% 2.68/1.42  Inferencing          : 0.12
% 2.68/1.42  Reduction            : 0.08
% 2.68/1.42  Demodulation         : 0.06
% 2.68/1.42  BG Simplification    : 0.02
% 2.68/1.42  Subsumption          : 0.06
% 2.68/1.42  Abstraction          : 0.01
% 2.68/1.42  MUC search           : 0.00
% 2.68/1.42  Cooper               : 0.00
% 2.68/1.42  Total                : 0.67
% 2.68/1.42  Index Insertion      : 0.00
% 2.68/1.42  Index Deletion       : 0.00
% 2.68/1.42  Index Matching       : 0.00
% 2.68/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
