%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:22 EST 2020

% Result     : Theorem 4.66s
% Output     : CNFRefutation 4.71s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 973 expanded)
%              Number of leaves         :   43 ( 398 expanded)
%              Depth                    :   22
%              Number of atoms          :  693 (3210 expanded)
%              Number of equality atoms :   68 ( 598 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k2_enumset1 > k1_enumset1 > k12_lattice3 > k11_lattice3 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k11_lattice3,type,(
    k11_lattice3: ( $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k12_lattice3,type,(
    k12_lattice3: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_151,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_178,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( v2_lattice3(k2_yellow_1(A))
         => ! [B] :
              ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(A),B,C),k3_xboole_0(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_1)).

tff(f_139,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k11_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_lattice3)).

tff(f_147,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_164,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_135,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( B = k12_lattice3(A,B,C)
              <=> r3_orders_2(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_yellow_0)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_91,axiom,(
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

tff(f_50,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_117,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k11_lattice3(A,B,C) = k11_lattice3(A,C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_lattice3)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_54,plain,(
    ! [A_82] : u1_struct_0(k2_yellow_1(A_82)) = A_82 ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_71,plain,(
    m1_subset_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_66])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_72,plain,(
    m1_subset_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_64])).

tff(c_44,plain,(
    ! [A_80] : l1_orders_2(k2_yellow_1(A_80)) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1201,plain,(
    ! [A_249,B_250,C_251] :
      ( m1_subset_1(k11_lattice3(A_249,B_250,C_251),u1_struct_0(A_249))
      | ~ m1_subset_1(C_251,u1_struct_0(A_249))
      | ~ m1_subset_1(B_250,u1_struct_0(A_249))
      | ~ l1_orders_2(A_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1204,plain,(
    ! [A_82,B_250,C_251] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_82),B_250,C_251),A_82)
      | ~ m1_subset_1(C_251,u1_struct_0(k2_yellow_1(A_82)))
      | ~ m1_subset_1(B_250,u1_struct_0(k2_yellow_1(A_82)))
      | ~ l1_orders_2(k2_yellow_1(A_82)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1201])).

tff(c_1206,plain,(
    ! [A_82,B_250,C_251] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_82),B_250,C_251),A_82)
      | ~ m1_subset_1(C_251,A_82)
      | ~ m1_subset_1(B_250,A_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_54,c_54,c_1204])).

tff(c_68,plain,(
    v2_lattice3(k2_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_52,plain,(
    ! [A_81] : v5_orders_2(k2_yellow_1(A_81)) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_48,plain,(
    ! [A_81] : v3_orders_2(k2_yellow_1(A_81)) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_58,plain,(
    ! [A_83,B_87,C_89] :
      ( r3_orders_2(k2_yellow_1(A_83),B_87,C_89)
      | ~ r1_tarski(B_87,C_89)
      | ~ m1_subset_1(C_89,u1_struct_0(k2_yellow_1(A_83)))
      | ~ m1_subset_1(B_87,u1_struct_0(k2_yellow_1(A_83)))
      | v1_xboole_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_74,plain,(
    ! [A_83,B_87,C_89] :
      ( r3_orders_2(k2_yellow_1(A_83),B_87,C_89)
      | ~ r1_tarski(B_87,C_89)
      | ~ m1_subset_1(C_89,A_83)
      | ~ m1_subset_1(B_87,A_83)
      | v1_xboole_0(A_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_58])).

tff(c_1370,plain,(
    ! [A_280,B_281,C_282] :
      ( k12_lattice3(A_280,B_281,C_282) = B_281
      | ~ r3_orders_2(A_280,B_281,C_282)
      | ~ m1_subset_1(C_282,u1_struct_0(A_280))
      | ~ m1_subset_1(B_281,u1_struct_0(A_280))
      | ~ l1_orders_2(A_280)
      | ~ v2_lattice3(A_280)
      | ~ v5_orders_2(A_280)
      | ~ v3_orders_2(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1374,plain,(
    ! [A_83,B_87,C_89] :
      ( k12_lattice3(k2_yellow_1(A_83),B_87,C_89) = B_87
      | ~ m1_subset_1(C_89,u1_struct_0(k2_yellow_1(A_83)))
      | ~ m1_subset_1(B_87,u1_struct_0(k2_yellow_1(A_83)))
      | ~ l1_orders_2(k2_yellow_1(A_83))
      | ~ v2_lattice3(k2_yellow_1(A_83))
      | ~ v5_orders_2(k2_yellow_1(A_83))
      | ~ v3_orders_2(k2_yellow_1(A_83))
      | ~ r1_tarski(B_87,C_89)
      | ~ m1_subset_1(C_89,A_83)
      | ~ m1_subset_1(B_87,A_83)
      | v1_xboole_0(A_83) ) ),
    inference(resolution,[status(thm)],[c_74,c_1370])).

tff(c_1381,plain,(
    ! [A_283,B_284,C_285] :
      ( k12_lattice3(k2_yellow_1(A_283),B_284,C_285) = B_284
      | ~ v2_lattice3(k2_yellow_1(A_283))
      | ~ r1_tarski(B_284,C_285)
      | ~ m1_subset_1(C_285,A_283)
      | ~ m1_subset_1(B_284,A_283)
      | v1_xboole_0(A_283) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52,c_44,c_54,c_54,c_1374])).

tff(c_1383,plain,(
    ! [B_284,C_285] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_284,C_285) = B_284
      | ~ r1_tarski(B_284,C_285)
      | ~ m1_subset_1(C_285,'#skF_2')
      | ~ m1_subset_1(B_284,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_68,c_1381])).

tff(c_1387,plain,(
    ! [B_286,C_287] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_286,C_287) = B_286
      | ~ r1_tarski(B_286,C_287)
      | ~ m1_subset_1(C_287,'#skF_2')
      | ~ m1_subset_1(B_286,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1383])).

tff(c_1318,plain,(
    ! [A_266,B_267,C_268] :
      ( k12_lattice3(A_266,B_267,C_268) = k11_lattice3(A_266,B_267,C_268)
      | ~ m1_subset_1(C_268,u1_struct_0(A_266))
      | ~ m1_subset_1(B_267,u1_struct_0(A_266))
      | ~ l1_orders_2(A_266)
      | ~ v2_lattice3(A_266)
      | ~ v5_orders_2(A_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1325,plain,(
    ! [A_82,B_267,C_268] :
      ( k12_lattice3(k2_yellow_1(A_82),B_267,C_268) = k11_lattice3(k2_yellow_1(A_82),B_267,C_268)
      | ~ m1_subset_1(C_268,A_82)
      | ~ m1_subset_1(B_267,u1_struct_0(k2_yellow_1(A_82)))
      | ~ l1_orders_2(k2_yellow_1(A_82))
      | ~ v2_lattice3(k2_yellow_1(A_82))
      | ~ v5_orders_2(k2_yellow_1(A_82)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1318])).

tff(c_1352,plain,(
    ! [A_272,B_273,C_274] :
      ( k12_lattice3(k2_yellow_1(A_272),B_273,C_274) = k11_lattice3(k2_yellow_1(A_272),B_273,C_274)
      | ~ m1_subset_1(C_274,A_272)
      | ~ m1_subset_1(B_273,A_272)
      | ~ v2_lattice3(k2_yellow_1(A_272)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_44,c_54,c_1325])).

tff(c_1355,plain,(
    ! [B_273,C_274] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_273,C_274) = k11_lattice3(k2_yellow_1('#skF_2'),B_273,C_274)
      | ~ m1_subset_1(C_274,'#skF_2')
      | ~ m1_subset_1(B_273,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_68,c_1352])).

tff(c_1393,plain,(
    ! [B_286,C_287] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),B_286,C_287) = B_286
      | ~ m1_subset_1(C_287,'#skF_2')
      | ~ m1_subset_1(B_286,'#skF_2')
      | ~ r1_tarski(B_286,C_287)
      | ~ m1_subset_1(C_287,'#skF_2')
      | ~ m1_subset_1(B_286,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1387,c_1355])).

tff(c_1494,plain,(
    ! [A_295,B_296,C_297] :
      ( r1_orders_2(A_295,k11_lattice3(A_295,B_296,C_297),B_296)
      | ~ m1_subset_1(k11_lattice3(A_295,B_296,C_297),u1_struct_0(A_295))
      | ~ m1_subset_1(C_297,u1_struct_0(A_295))
      | ~ m1_subset_1(B_296,u1_struct_0(A_295))
      | ~ l1_orders_2(A_295)
      | ~ v2_lattice3(A_295)
      | ~ v5_orders_2(A_295)
      | v2_struct_0(A_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1496,plain,(
    ! [B_286,C_287] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_286,C_287),B_286)
      | ~ m1_subset_1(B_286,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(C_287,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_286,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_287,'#skF_2')
      | ~ m1_subset_1(B_286,'#skF_2')
      | ~ r1_tarski(B_286,C_287)
      | ~ m1_subset_1(C_287,'#skF_2')
      | ~ m1_subset_1(B_286,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1393,c_1494])).

tff(c_1506,plain,(
    ! [B_286,C_287] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_286,C_287),B_286)
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ r1_tarski(B_286,C_287)
      | ~ m1_subset_1(C_287,'#skF_2')
      | ~ m1_subset_1(B_286,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_68,c_44,c_54,c_54,c_54,c_1496])).

tff(c_1547,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1506])).

tff(c_16,plain,(
    ! [A_13] :
      ( ~ v2_struct_0(A_13)
      | ~ v2_lattice3(A_13)
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1550,plain,
    ( ~ v2_lattice3(k2_yellow_1('#skF_2'))
    | ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1547,c_16])).

tff(c_1554,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_68,c_1550])).

tff(c_1556,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1506])).

tff(c_18,plain,(
    ! [A_14,B_15,C_16] :
      ( m1_subset_1(k11_lattice3(A_14,B_15,C_16),u1_struct_0(A_14))
      | ~ m1_subset_1(C_16,u1_struct_0(A_14))
      | ~ m1_subset_1(B_15,u1_struct_0(A_14))
      | ~ l1_orders_2(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1527,plain,(
    ! [A_300,B_301,C_302] :
      ( r1_orders_2(A_300,k11_lattice3(A_300,B_301,C_302),C_302)
      | ~ m1_subset_1(k11_lattice3(A_300,B_301,C_302),u1_struct_0(A_300))
      | ~ m1_subset_1(C_302,u1_struct_0(A_300))
      | ~ m1_subset_1(B_301,u1_struct_0(A_300))
      | ~ l1_orders_2(A_300)
      | ~ v2_lattice3(A_300)
      | ~ v5_orders_2(A_300)
      | v2_struct_0(A_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1544,plain,(
    ! [A_14,B_15,C_16] :
      ( r1_orders_2(A_14,k11_lattice3(A_14,B_15,C_16),C_16)
      | ~ v2_lattice3(A_14)
      | ~ v5_orders_2(A_14)
      | v2_struct_0(A_14)
      | ~ m1_subset_1(C_16,u1_struct_0(A_14))
      | ~ m1_subset_1(B_15,u1_struct_0(A_14))
      | ~ l1_orders_2(A_14) ) ),
    inference(resolution,[status(thm)],[c_18,c_1527])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1706,plain,(
    ! [A_313,B_314,C_315] :
      ( r1_orders_2(A_313,k11_lattice3(A_313,B_314,C_315),C_315)
      | ~ v2_lattice3(A_313)
      | ~ v5_orders_2(A_313)
      | v2_struct_0(A_313)
      | ~ m1_subset_1(C_315,u1_struct_0(A_313))
      | ~ m1_subset_1(B_314,u1_struct_0(A_313))
      | ~ l1_orders_2(A_313) ) ),
    inference(resolution,[status(thm)],[c_18,c_1527])).

tff(c_1712,plain,(
    ! [B_286,C_287] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),B_286,C_287)
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_287,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_286,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_287,'#skF_2')
      | ~ m1_subset_1(B_286,'#skF_2')
      | ~ r1_tarski(B_286,C_287)
      | ~ m1_subset_1(C_287,'#skF_2')
      | ~ m1_subset_1(B_286,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1393,c_1706])).

tff(c_1723,plain,(
    ! [B_286,C_287] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),B_286,C_287)
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ r1_tarski(B_286,C_287)
      | ~ m1_subset_1(C_287,'#skF_2')
      | ~ m1_subset_1(B_286,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_54,c_54,c_52,c_68,c_1712])).

tff(c_1724,plain,(
    ! [B_286,C_287] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),B_286,C_287)
      | ~ r1_tarski(B_286,C_287)
      | ~ m1_subset_1(C_287,'#skF_2')
      | ~ m1_subset_1(B_286,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1556,c_1723])).

tff(c_1839,plain,(
    ! [A_338,B_339,C_340,D_341] :
      ( r1_orders_2(A_338,'#skF_1'(A_338,B_339,C_340,D_341),C_340)
      | k11_lattice3(A_338,B_339,C_340) = D_341
      | ~ r1_orders_2(A_338,D_341,C_340)
      | ~ r1_orders_2(A_338,D_341,B_339)
      | ~ m1_subset_1(D_341,u1_struct_0(A_338))
      | ~ m1_subset_1(C_340,u1_struct_0(A_338))
      | ~ m1_subset_1(B_339,u1_struct_0(A_338))
      | ~ l1_orders_2(A_338)
      | ~ v2_lattice3(A_338)
      | ~ v5_orders_2(A_338)
      | v2_struct_0(A_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_20,plain,(
    ! [A_17,B_41,C_53,D_59] :
      ( ~ r1_orders_2(A_17,'#skF_1'(A_17,B_41,C_53,D_59),D_59)
      | k11_lattice3(A_17,B_41,C_53) = D_59
      | ~ r1_orders_2(A_17,D_59,C_53)
      | ~ r1_orders_2(A_17,D_59,B_41)
      | ~ m1_subset_1(D_59,u1_struct_0(A_17))
      | ~ m1_subset_1(C_53,u1_struct_0(A_17))
      | ~ m1_subset_1(B_41,u1_struct_0(A_17))
      | ~ l1_orders_2(A_17)
      | ~ v2_lattice3(A_17)
      | ~ v5_orders_2(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1918,plain,(
    ! [A_359,B_360,C_361] :
      ( k11_lattice3(A_359,B_360,C_361) = C_361
      | ~ r1_orders_2(A_359,C_361,C_361)
      | ~ r1_orders_2(A_359,C_361,B_360)
      | ~ m1_subset_1(C_361,u1_struct_0(A_359))
      | ~ m1_subset_1(B_360,u1_struct_0(A_359))
      | ~ l1_orders_2(A_359)
      | ~ v2_lattice3(A_359)
      | ~ v5_orders_2(A_359)
      | v2_struct_0(A_359) ) ),
    inference(resolution,[status(thm)],[c_1839,c_20])).

tff(c_1923,plain,(
    ! [B_360,C_287] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),B_360,C_287) = C_287
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),C_287,B_360)
      | ~ m1_subset_1(C_287,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_360,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ r1_tarski(C_287,C_287)
      | ~ m1_subset_1(C_287,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1724,c_1918])).

tff(c_1930,plain,(
    ! [B_360,C_287] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),B_360,C_287) = C_287
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),C_287,B_360)
      | ~ m1_subset_1(B_360,'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_287,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_52,c_68,c_44,c_54,c_54,c_1923])).

tff(c_1932,plain,(
    ! [B_362,C_363] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),B_362,C_363) = C_363
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),C_363,B_362)
      | ~ m1_subset_1(B_362,'#skF_2')
      | ~ m1_subset_1(C_363,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1556,c_1930])).

tff(c_1968,plain,(
    ! [C_16,B_15] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),C_16,k11_lattice3(k2_yellow_1('#skF_2'),B_15,C_16)) = k11_lattice3(k2_yellow_1('#skF_2'),B_15,C_16)
      | ~ m1_subset_1(C_16,'#skF_2')
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_15,C_16),'#skF_2')
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_16,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_15,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1544,c_1932])).

tff(c_1995,plain,(
    ! [C_16,B_15] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),C_16,k11_lattice3(k2_yellow_1('#skF_2'),B_15,C_16)) = k11_lattice3(k2_yellow_1('#skF_2'),B_15,C_16)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_15,C_16),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_16,'#skF_2')
      | ~ m1_subset_1(B_15,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_54,c_54,c_52,c_68,c_1968])).

tff(c_2209,plain,(
    ! [C_367,B_368] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),C_367,k11_lattice3(k2_yellow_1('#skF_2'),B_368,C_367)) = k11_lattice3(k2_yellow_1('#skF_2'),B_368,C_367)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_368,C_367),'#skF_2')
      | ~ m1_subset_1(C_367,'#skF_2')
      | ~ m1_subset_1(B_368,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1556,c_1995])).

tff(c_1213,plain,(
    ! [A_258,C_259,B_260] :
      ( k11_lattice3(A_258,C_259,B_260) = k11_lattice3(A_258,B_260,C_259)
      | ~ m1_subset_1(C_259,u1_struct_0(A_258))
      | ~ m1_subset_1(B_260,u1_struct_0(A_258))
      | ~ l1_orders_2(A_258)
      | ~ v2_lattice3(A_258)
      | ~ v5_orders_2(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1220,plain,(
    ! [A_82,C_259,B_260] :
      ( k11_lattice3(k2_yellow_1(A_82),C_259,B_260) = k11_lattice3(k2_yellow_1(A_82),B_260,C_259)
      | ~ m1_subset_1(C_259,A_82)
      | ~ m1_subset_1(B_260,u1_struct_0(k2_yellow_1(A_82)))
      | ~ l1_orders_2(k2_yellow_1(A_82))
      | ~ v2_lattice3(k2_yellow_1(A_82))
      | ~ v5_orders_2(k2_yellow_1(A_82)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1213])).

tff(c_1225,plain,(
    ! [A_261,C_262,B_263] :
      ( k11_lattice3(k2_yellow_1(A_261),C_262,B_263) = k11_lattice3(k2_yellow_1(A_261),B_263,C_262)
      | ~ m1_subset_1(C_262,A_261)
      | ~ m1_subset_1(B_263,A_261)
      | ~ v2_lattice3(k2_yellow_1(A_261)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_44,c_54,c_1220])).

tff(c_1228,plain,(
    ! [C_262,B_263] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),C_262,B_263) = k11_lattice3(k2_yellow_1('#skF_2'),B_263,C_262)
      | ~ m1_subset_1(C_262,'#skF_2')
      | ~ m1_subset_1(B_263,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_68,c_1225])).

tff(c_1340,plain,(
    ! [A_269,B_270,C_271] :
      ( r3_orders_2(A_269,B_270,C_271)
      | k12_lattice3(A_269,B_270,C_271) != B_270
      | ~ m1_subset_1(C_271,u1_struct_0(A_269))
      | ~ m1_subset_1(B_270,u1_struct_0(A_269))
      | ~ l1_orders_2(A_269)
      | ~ v2_lattice3(A_269)
      | ~ v5_orders_2(A_269)
      | ~ v3_orders_2(A_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1347,plain,(
    ! [A_82,B_270,C_271] :
      ( r3_orders_2(k2_yellow_1(A_82),B_270,C_271)
      | k12_lattice3(k2_yellow_1(A_82),B_270,C_271) != B_270
      | ~ m1_subset_1(C_271,A_82)
      | ~ m1_subset_1(B_270,u1_struct_0(k2_yellow_1(A_82)))
      | ~ l1_orders_2(k2_yellow_1(A_82))
      | ~ v2_lattice3(k2_yellow_1(A_82))
      | ~ v5_orders_2(k2_yellow_1(A_82))
      | ~ v3_orders_2(k2_yellow_1(A_82)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1340])).

tff(c_1365,plain,(
    ! [A_277,B_278,C_279] :
      ( r3_orders_2(k2_yellow_1(A_277),B_278,C_279)
      | k12_lattice3(k2_yellow_1(A_277),B_278,C_279) != B_278
      | ~ m1_subset_1(C_279,A_277)
      | ~ m1_subset_1(B_278,A_277)
      | ~ v2_lattice3(k2_yellow_1(A_277)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52,c_44,c_54,c_1347])).

tff(c_60,plain,(
    ! [B_87,C_89,A_83] :
      ( r1_tarski(B_87,C_89)
      | ~ r3_orders_2(k2_yellow_1(A_83),B_87,C_89)
      | ~ m1_subset_1(C_89,u1_struct_0(k2_yellow_1(A_83)))
      | ~ m1_subset_1(B_87,u1_struct_0(k2_yellow_1(A_83)))
      | v1_xboole_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_73,plain,(
    ! [B_87,C_89,A_83] :
      ( r1_tarski(B_87,C_89)
      | ~ r3_orders_2(k2_yellow_1(A_83),B_87,C_89)
      | ~ m1_subset_1(C_89,A_83)
      | ~ m1_subset_1(B_87,A_83)
      | v1_xboole_0(A_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_60])).

tff(c_1402,plain,(
    ! [B_288,C_289,A_290] :
      ( r1_tarski(B_288,C_289)
      | v1_xboole_0(A_290)
      | k12_lattice3(k2_yellow_1(A_290),B_288,C_289) != B_288
      | ~ m1_subset_1(C_289,A_290)
      | ~ m1_subset_1(B_288,A_290)
      | ~ v2_lattice3(k2_yellow_1(A_290)) ) ),
    inference(resolution,[status(thm)],[c_1365,c_73])).

tff(c_1406,plain,(
    ! [B_273,C_274] :
      ( r1_tarski(B_273,C_274)
      | v1_xboole_0('#skF_2')
      | k11_lattice3(k2_yellow_1('#skF_2'),B_273,C_274) != B_273
      | ~ m1_subset_1(C_274,'#skF_2')
      | ~ m1_subset_1(B_273,'#skF_2')
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_274,'#skF_2')
      | ~ m1_subset_1(B_273,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1355,c_1402])).

tff(c_1412,plain,(
    ! [B_273,C_274] :
      ( r1_tarski(B_273,C_274)
      | v1_xboole_0('#skF_2')
      | k11_lattice3(k2_yellow_1('#skF_2'),B_273,C_274) != B_273
      | ~ m1_subset_1(C_274,'#skF_2')
      | ~ m1_subset_1(B_273,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1406])).

tff(c_1414,plain,(
    ! [B_291,C_292] :
      ( r1_tarski(B_291,C_292)
      | k11_lattice3(k2_yellow_1('#skF_2'),B_291,C_292) != B_291
      | ~ m1_subset_1(C_292,'#skF_2')
      | ~ m1_subset_1(B_291,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1412])).

tff(c_1420,plain,(
    ! [C_262,B_263] :
      ( r1_tarski(C_262,B_263)
      | k11_lattice3(k2_yellow_1('#skF_2'),B_263,C_262) != C_262
      | ~ m1_subset_1(B_263,'#skF_2')
      | ~ m1_subset_1(C_262,'#skF_2')
      | ~ m1_subset_1(C_262,'#skF_2')
      | ~ m1_subset_1(B_263,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1228,c_1414])).

tff(c_2300,plain,(
    ! [B_369,C_370] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_369,C_370),C_370)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_369,C_370),'#skF_2')
      | ~ m1_subset_1(C_370,'#skF_2')
      | ~ m1_subset_1(B_369,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2209,c_1420])).

tff(c_163,plain,(
    ! [A_124,B_125,C_126] :
      ( m1_subset_1(k11_lattice3(A_124,B_125,C_126),u1_struct_0(A_124))
      | ~ m1_subset_1(C_126,u1_struct_0(A_124))
      | ~ m1_subset_1(B_125,u1_struct_0(A_124))
      | ~ l1_orders_2(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_166,plain,(
    ! [A_82,B_125,C_126] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_82),B_125,C_126),A_82)
      | ~ m1_subset_1(C_126,u1_struct_0(k2_yellow_1(A_82)))
      | ~ m1_subset_1(B_125,u1_struct_0(k2_yellow_1(A_82)))
      | ~ l1_orders_2(k2_yellow_1(A_82)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_163])).

tff(c_168,plain,(
    ! [A_82,B_125,C_126] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_82),B_125,C_126),A_82)
      | ~ m1_subset_1(C_126,A_82)
      | ~ m1_subset_1(B_125,A_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_54,c_54,c_166])).

tff(c_301,plain,(
    ! [A_152,B_153,C_154] :
      ( k12_lattice3(A_152,B_153,C_154) = B_153
      | ~ r3_orders_2(A_152,B_153,C_154)
      | ~ m1_subset_1(C_154,u1_struct_0(A_152))
      | ~ m1_subset_1(B_153,u1_struct_0(A_152))
      | ~ l1_orders_2(A_152)
      | ~ v2_lattice3(A_152)
      | ~ v5_orders_2(A_152)
      | ~ v3_orders_2(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_305,plain,(
    ! [A_83,B_87,C_89] :
      ( k12_lattice3(k2_yellow_1(A_83),B_87,C_89) = B_87
      | ~ m1_subset_1(C_89,u1_struct_0(k2_yellow_1(A_83)))
      | ~ m1_subset_1(B_87,u1_struct_0(k2_yellow_1(A_83)))
      | ~ l1_orders_2(k2_yellow_1(A_83))
      | ~ v2_lattice3(k2_yellow_1(A_83))
      | ~ v5_orders_2(k2_yellow_1(A_83))
      | ~ v3_orders_2(k2_yellow_1(A_83))
      | ~ r1_tarski(B_87,C_89)
      | ~ m1_subset_1(C_89,A_83)
      | ~ m1_subset_1(B_87,A_83)
      | v1_xboole_0(A_83) ) ),
    inference(resolution,[status(thm)],[c_74,c_301])).

tff(c_312,plain,(
    ! [A_155,B_156,C_157] :
      ( k12_lattice3(k2_yellow_1(A_155),B_156,C_157) = B_156
      | ~ v2_lattice3(k2_yellow_1(A_155))
      | ~ r1_tarski(B_156,C_157)
      | ~ m1_subset_1(C_157,A_155)
      | ~ m1_subset_1(B_156,A_155)
      | v1_xboole_0(A_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52,c_44,c_54,c_54,c_305])).

tff(c_314,plain,(
    ! [B_156,C_157] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_156,C_157) = B_156
      | ~ r1_tarski(B_156,C_157)
      | ~ m1_subset_1(C_157,'#skF_2')
      | ~ m1_subset_1(B_156,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_68,c_312])).

tff(c_318,plain,(
    ! [B_158,C_159] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_158,C_159) = B_158
      | ~ r1_tarski(B_158,C_159)
      | ~ m1_subset_1(C_159,'#skF_2')
      | ~ m1_subset_1(B_158,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_314])).

tff(c_259,plain,(
    ! [A_138,B_139,C_140] :
      ( k12_lattice3(A_138,B_139,C_140) = k11_lattice3(A_138,B_139,C_140)
      | ~ m1_subset_1(C_140,u1_struct_0(A_138))
      | ~ m1_subset_1(B_139,u1_struct_0(A_138))
      | ~ l1_orders_2(A_138)
      | ~ v2_lattice3(A_138)
      | ~ v5_orders_2(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_266,plain,(
    ! [A_82,B_139,C_140] :
      ( k12_lattice3(k2_yellow_1(A_82),B_139,C_140) = k11_lattice3(k2_yellow_1(A_82),B_139,C_140)
      | ~ m1_subset_1(C_140,A_82)
      | ~ m1_subset_1(B_139,u1_struct_0(k2_yellow_1(A_82)))
      | ~ l1_orders_2(k2_yellow_1(A_82))
      | ~ v2_lattice3(k2_yellow_1(A_82))
      | ~ v5_orders_2(k2_yellow_1(A_82)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_259])).

tff(c_283,plain,(
    ! [A_144,B_145,C_146] :
      ( k12_lattice3(k2_yellow_1(A_144),B_145,C_146) = k11_lattice3(k2_yellow_1(A_144),B_145,C_146)
      | ~ m1_subset_1(C_146,A_144)
      | ~ m1_subset_1(B_145,A_144)
      | ~ v2_lattice3(k2_yellow_1(A_144)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_44,c_54,c_266])).

tff(c_286,plain,(
    ! [B_145,C_146] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_145,C_146) = k11_lattice3(k2_yellow_1('#skF_2'),B_145,C_146)
      | ~ m1_subset_1(C_146,'#skF_2')
      | ~ m1_subset_1(B_145,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_68,c_283])).

tff(c_324,plain,(
    ! [B_158,C_159] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),B_158,C_159) = B_158
      | ~ m1_subset_1(C_159,'#skF_2')
      | ~ m1_subset_1(B_158,'#skF_2')
      | ~ r1_tarski(B_158,C_159)
      | ~ m1_subset_1(C_159,'#skF_2')
      | ~ m1_subset_1(B_158,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_286])).

tff(c_405,plain,(
    ! [A_167,B_168,C_169] :
      ( r1_orders_2(A_167,k11_lattice3(A_167,B_168,C_169),C_169)
      | ~ m1_subset_1(k11_lattice3(A_167,B_168,C_169),u1_struct_0(A_167))
      | ~ m1_subset_1(C_169,u1_struct_0(A_167))
      | ~ m1_subset_1(B_168,u1_struct_0(A_167))
      | ~ l1_orders_2(A_167)
      | ~ v2_lattice3(A_167)
      | ~ v5_orders_2(A_167)
      | v2_struct_0(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_407,plain,(
    ! [B_158,C_159] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_158,C_159),C_159)
      | ~ m1_subset_1(B_158,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(C_159,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_158,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_159,'#skF_2')
      | ~ m1_subset_1(B_158,'#skF_2')
      | ~ r1_tarski(B_158,C_159)
      | ~ m1_subset_1(C_159,'#skF_2')
      | ~ m1_subset_1(B_158,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_405])).

tff(c_417,plain,(
    ! [B_158,C_159] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_158,C_159),C_159)
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ r1_tarski(B_158,C_159)
      | ~ m1_subset_1(C_159,'#skF_2')
      | ~ m1_subset_1(B_158,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_68,c_44,c_54,c_54,c_54,c_407])).

tff(c_438,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_417])).

tff(c_441,plain,
    ( ~ v2_lattice3(k2_yellow_1('#skF_2'))
    | ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_438,c_16])).

tff(c_445,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_68,c_441])).

tff(c_447,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_417])).

tff(c_169,plain,(
    ! [A_127,C_128,B_129] :
      ( k11_lattice3(A_127,C_128,B_129) = k11_lattice3(A_127,B_129,C_128)
      | ~ m1_subset_1(C_128,u1_struct_0(A_127))
      | ~ m1_subset_1(B_129,u1_struct_0(A_127))
      | ~ l1_orders_2(A_127)
      | ~ v2_lattice3(A_127)
      | ~ v5_orders_2(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_173,plain,(
    ! [A_82,C_128,B_129] :
      ( k11_lattice3(k2_yellow_1(A_82),C_128,B_129) = k11_lattice3(k2_yellow_1(A_82),B_129,C_128)
      | ~ m1_subset_1(C_128,A_82)
      | ~ m1_subset_1(B_129,u1_struct_0(k2_yellow_1(A_82)))
      | ~ l1_orders_2(k2_yellow_1(A_82))
      | ~ v2_lattice3(k2_yellow_1(A_82))
      | ~ v5_orders_2(k2_yellow_1(A_82)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_169])).

tff(c_182,plain,(
    ! [A_133,C_134,B_135] :
      ( k11_lattice3(k2_yellow_1(A_133),C_134,B_135) = k11_lattice3(k2_yellow_1(A_133),B_135,C_134)
      | ~ m1_subset_1(C_134,A_133)
      | ~ m1_subset_1(B_135,A_133)
      | ~ v2_lattice3(k2_yellow_1(A_133)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_44,c_54,c_173])).

tff(c_185,plain,(
    ! [C_134,B_135] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),C_134,B_135) = k11_lattice3(k2_yellow_1('#skF_2'),B_135,C_134)
      | ~ m1_subset_1(C_134,'#skF_2')
      | ~ m1_subset_1(B_135,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_68,c_182])).

tff(c_448,plain,(
    ! [A_172,B_173,C_174] :
      ( r1_orders_2(A_172,k11_lattice3(A_172,B_173,C_174),B_173)
      | ~ m1_subset_1(k11_lattice3(A_172,B_173,C_174),u1_struct_0(A_172))
      | ~ m1_subset_1(C_174,u1_struct_0(A_172))
      | ~ m1_subset_1(B_173,u1_struct_0(A_172))
      | ~ l1_orders_2(A_172)
      | ~ v2_lattice3(A_172)
      | ~ v5_orders_2(A_172)
      | v2_struct_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_511,plain,(
    ! [A_183,B_184,C_185] :
      ( r1_orders_2(A_183,k11_lattice3(A_183,B_184,C_185),B_184)
      | ~ v2_lattice3(A_183)
      | ~ v5_orders_2(A_183)
      | v2_struct_0(A_183)
      | ~ m1_subset_1(C_185,u1_struct_0(A_183))
      | ~ m1_subset_1(B_184,u1_struct_0(A_183))
      | ~ l1_orders_2(A_183) ) ),
    inference(resolution,[status(thm)],[c_18,c_448])).

tff(c_517,plain,(
    ! [C_134,B_135] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),C_134,B_135),B_135)
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_134,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_135,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_134,'#skF_2')
      | ~ m1_subset_1(B_135,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_511])).

tff(c_525,plain,(
    ! [C_134,B_135] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),C_134,B_135),B_135)
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_134,'#skF_2')
      | ~ m1_subset_1(B_135,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_54,c_54,c_52,c_68,c_517])).

tff(c_526,plain,(
    ! [C_134,B_135] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),C_134,B_135),B_135)
      | ~ m1_subset_1(C_134,'#skF_2')
      | ~ m1_subset_1(B_135,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_447,c_525])).

tff(c_559,plain,(
    ! [A_197,B_198,C_199] :
      ( r1_orders_2(A_197,k11_lattice3(A_197,B_198,C_199),C_199)
      | ~ v2_lattice3(A_197)
      | ~ v5_orders_2(A_197)
      | v2_struct_0(A_197)
      | ~ m1_subset_1(C_199,u1_struct_0(A_197))
      | ~ m1_subset_1(B_198,u1_struct_0(A_197))
      | ~ l1_orders_2(A_197) ) ),
    inference(resolution,[status(thm)],[c_18,c_405])).

tff(c_562,plain,(
    ! [B_158,C_159] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),B_158,C_159)
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_159,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_158,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_159,'#skF_2')
      | ~ m1_subset_1(B_158,'#skF_2')
      | ~ r1_tarski(B_158,C_159)
      | ~ m1_subset_1(C_159,'#skF_2')
      | ~ m1_subset_1(B_158,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_559])).

tff(c_570,plain,(
    ! [B_158,C_159] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),B_158,C_159)
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ r1_tarski(B_158,C_159)
      | ~ m1_subset_1(C_159,'#skF_2')
      | ~ m1_subset_1(B_158,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_54,c_54,c_52,c_68,c_562])).

tff(c_571,plain,(
    ! [B_158,C_159] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),B_158,C_159)
      | ~ r1_tarski(B_158,C_159)
      | ~ m1_subset_1(C_159,'#skF_2')
      | ~ m1_subset_1(B_158,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_447,c_570])).

tff(c_597,plain,(
    ! [A_204,B_205,C_206,D_207] :
      ( r1_orders_2(A_204,'#skF_1'(A_204,B_205,C_206,D_207),C_206)
      | k11_lattice3(A_204,B_205,C_206) = D_207
      | ~ r1_orders_2(A_204,D_207,C_206)
      | ~ r1_orders_2(A_204,D_207,B_205)
      | ~ m1_subset_1(D_207,u1_struct_0(A_204))
      | ~ m1_subset_1(C_206,u1_struct_0(A_204))
      | ~ m1_subset_1(B_205,u1_struct_0(A_204))
      | ~ l1_orders_2(A_204)
      | ~ v2_lattice3(A_204)
      | ~ v5_orders_2(A_204)
      | v2_struct_0(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_767,plain,(
    ! [A_227,B_228,C_229] :
      ( k11_lattice3(A_227,B_228,C_229) = C_229
      | ~ r1_orders_2(A_227,C_229,C_229)
      | ~ r1_orders_2(A_227,C_229,B_228)
      | ~ m1_subset_1(C_229,u1_struct_0(A_227))
      | ~ m1_subset_1(B_228,u1_struct_0(A_227))
      | ~ l1_orders_2(A_227)
      | ~ v2_lattice3(A_227)
      | ~ v5_orders_2(A_227)
      | v2_struct_0(A_227) ) ),
    inference(resolution,[status(thm)],[c_597,c_20])).

tff(c_770,plain,(
    ! [B_228,C_159] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),B_228,C_159) = C_159
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),C_159,B_228)
      | ~ m1_subset_1(C_159,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_228,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ r1_tarski(C_159,C_159)
      | ~ m1_subset_1(C_159,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_571,c_767])).

tff(c_775,plain,(
    ! [B_228,C_159] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),B_228,C_159) = C_159
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),C_159,B_228)
      | ~ m1_subset_1(B_228,'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_159,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_52,c_68,c_44,c_54,c_54,c_770])).

tff(c_781,plain,(
    ! [B_230,C_231] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),B_230,C_231) = C_231
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),C_231,B_230)
      | ~ m1_subset_1(B_230,'#skF_2')
      | ~ m1_subset_1(C_231,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_447,c_775])).

tff(c_1043,plain,(
    ! [B_239,C_240] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),B_239,k11_lattice3(k2_yellow_1('#skF_2'),C_240,B_239)) = k11_lattice3(k2_yellow_1('#skF_2'),C_240,B_239)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_240,B_239),'#skF_2')
      | ~ m1_subset_1(C_240,'#skF_2')
      | ~ m1_subset_1(B_239,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_526,c_781])).

tff(c_271,plain,(
    ! [A_141,B_142,C_143] :
      ( r3_orders_2(A_141,B_142,C_143)
      | k12_lattice3(A_141,B_142,C_143) != B_142
      | ~ m1_subset_1(C_143,u1_struct_0(A_141))
      | ~ m1_subset_1(B_142,u1_struct_0(A_141))
      | ~ l1_orders_2(A_141)
      | ~ v2_lattice3(A_141)
      | ~ v5_orders_2(A_141)
      | ~ v3_orders_2(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_278,plain,(
    ! [A_82,B_142,C_143] :
      ( r3_orders_2(k2_yellow_1(A_82),B_142,C_143)
      | k12_lattice3(k2_yellow_1(A_82),B_142,C_143) != B_142
      | ~ m1_subset_1(C_143,A_82)
      | ~ m1_subset_1(B_142,u1_struct_0(k2_yellow_1(A_82)))
      | ~ l1_orders_2(k2_yellow_1(A_82))
      | ~ v2_lattice3(k2_yellow_1(A_82))
      | ~ v5_orders_2(k2_yellow_1(A_82))
      | ~ v3_orders_2(k2_yellow_1(A_82)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_271])).

tff(c_296,plain,(
    ! [A_149,B_150,C_151] :
      ( r3_orders_2(k2_yellow_1(A_149),B_150,C_151)
      | k12_lattice3(k2_yellow_1(A_149),B_150,C_151) != B_150
      | ~ m1_subset_1(C_151,A_149)
      | ~ m1_subset_1(B_150,A_149)
      | ~ v2_lattice3(k2_yellow_1(A_149)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52,c_44,c_54,c_278])).

tff(c_333,plain,(
    ! [B_160,C_161,A_162] :
      ( r1_tarski(B_160,C_161)
      | v1_xboole_0(A_162)
      | k12_lattice3(k2_yellow_1(A_162),B_160,C_161) != B_160
      | ~ m1_subset_1(C_161,A_162)
      | ~ m1_subset_1(B_160,A_162)
      | ~ v2_lattice3(k2_yellow_1(A_162)) ) ),
    inference(resolution,[status(thm)],[c_296,c_73])).

tff(c_337,plain,(
    ! [B_145,C_146] :
      ( r1_tarski(B_145,C_146)
      | v1_xboole_0('#skF_2')
      | k11_lattice3(k2_yellow_1('#skF_2'),B_145,C_146) != B_145
      | ~ m1_subset_1(C_146,'#skF_2')
      | ~ m1_subset_1(B_145,'#skF_2')
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_146,'#skF_2')
      | ~ m1_subset_1(B_145,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_333])).

tff(c_343,plain,(
    ! [B_145,C_146] :
      ( r1_tarski(B_145,C_146)
      | v1_xboole_0('#skF_2')
      | k11_lattice3(k2_yellow_1('#skF_2'),B_145,C_146) != B_145
      | ~ m1_subset_1(C_146,'#skF_2')
      | ~ m1_subset_1(B_145,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_337])).

tff(c_345,plain,(
    ! [B_163,C_164] :
      ( r1_tarski(B_163,C_164)
      | k11_lattice3(k2_yellow_1('#skF_2'),B_163,C_164) != B_163
      | ~ m1_subset_1(C_164,'#skF_2')
      | ~ m1_subset_1(B_163,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_343])).

tff(c_351,plain,(
    ! [C_134,B_135] :
      ( r1_tarski(C_134,B_135)
      | k11_lattice3(k2_yellow_1('#skF_2'),B_135,C_134) != C_134
      | ~ m1_subset_1(B_135,'#skF_2')
      | ~ m1_subset_1(C_134,'#skF_2')
      | ~ m1_subset_1(C_134,'#skF_2')
      | ~ m1_subset_1(B_135,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_345])).

tff(c_1134,plain,(
    ! [C_241,B_242] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),C_241,B_242),B_242)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_241,B_242),'#skF_2')
      | ~ m1_subset_1(C_241,'#skF_2')
      | ~ m1_subset_1(B_242,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1043,c_351])).

tff(c_186,plain,(
    ! [C_136,B_137] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),C_136,B_137) = k11_lattice3(k2_yellow_1('#skF_2'),B_137,C_136)
      | ~ m1_subset_1(C_136,'#skF_2')
      | ~ m1_subset_1(B_137,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_68,c_182])).

tff(c_136,plain,(
    ! [A_112,B_113,C_114] :
      ( r1_tarski(A_112,k3_xboole_0(B_113,C_114))
      | ~ r1_tarski(A_112,C_114)
      | ~ r1_tarski(A_112,B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_62,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),k3_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_143,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4')
    | ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_136,c_62])).

tff(c_144,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_143])).

tff(c_213,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_144])).

tff(c_244,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_72,c_213])).

tff(c_1137,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_1134,c_244])).

tff(c_1160,plain,(
    ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_72,c_1137])).

tff(c_1173,plain,
    ( ~ m1_subset_1('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_168,c_1160])).

tff(c_1181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_71,c_1173])).

tff(c_1182,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_2303,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_2300,c_1182])).

tff(c_2326,plain,(
    ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_72,c_2303])).

tff(c_2383,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_1206,c_2326])).

tff(c_2395,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_72,c_2383])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:20:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.66/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.71/1.82  
% 4.71/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.71/1.83  %$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k2_enumset1 > k1_enumset1 > k12_lattice3 > k11_lattice3 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.71/1.83  
% 4.71/1.83  %Foreground sorts:
% 4.71/1.83  
% 4.71/1.83  
% 4.71/1.83  %Background operators:
% 4.71/1.83  
% 4.71/1.83  
% 4.71/1.83  %Foreground operators:
% 4.71/1.83  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 4.71/1.83  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.71/1.83  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 4.71/1.83  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.71/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.71/1.83  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.71/1.83  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 4.71/1.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.71/1.83  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.71/1.83  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 4.71/1.83  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.71/1.83  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 4.71/1.83  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.71/1.83  tff('#skF_2', type, '#skF_2': $i).
% 4.71/1.83  tff('#skF_3', type, '#skF_3': $i).
% 4.71/1.83  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.71/1.83  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.71/1.83  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.71/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.71/1.83  tff('#skF_4', type, '#skF_4': $i).
% 4.71/1.83  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 4.71/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.71/1.83  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.71/1.83  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 4.71/1.83  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 4.71/1.83  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 4.71/1.83  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.71/1.83  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.71/1.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.71/1.83  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.71/1.83  
% 4.71/1.85  tff(f_151, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 4.71/1.85  tff(f_178, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (v2_lattice3(k2_yellow_1(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => r1_tarski(k11_lattice3(k2_yellow_1(A), B, C), k3_xboole_0(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_yellow_1)).
% 4.71/1.85  tff(f_139, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 4.71/1.85  tff(f_58, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k11_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k11_lattice3)).
% 4.71/1.85  tff(f_147, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 4.71/1.85  tff(f_164, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 4.71/1.85  tff(f_135, axiom, (![A]: ((((v3_orders_2(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((B = k12_lattice3(A, B, C)) <=> r3_orders_2(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_yellow_0)).
% 4.71/1.85  tff(f_103, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 4.71/1.85  tff(f_91, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k11_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l28_lattice3)).
% 4.71/1.85  tff(f_50, axiom, (![A]: (l1_orders_2(A) => (v2_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_lattice3)).
% 4.71/1.85  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.71/1.85  tff(f_117, axiom, (![A]: (((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k11_lattice3(A, B, C) = k11_lattice3(A, C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_lattice3)).
% 4.71/1.85  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 4.71/1.85  tff(c_54, plain, (![A_82]: (u1_struct_0(k2_yellow_1(A_82))=A_82)), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.71/1.85  tff(c_66, plain, (m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.71/1.85  tff(c_71, plain, (m1_subset_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_66])).
% 4.71/1.85  tff(c_64, plain, (m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.71/1.85  tff(c_72, plain, (m1_subset_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_64])).
% 4.71/1.85  tff(c_44, plain, (![A_80]: (l1_orders_2(k2_yellow_1(A_80)))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.71/1.85  tff(c_1201, plain, (![A_249, B_250, C_251]: (m1_subset_1(k11_lattice3(A_249, B_250, C_251), u1_struct_0(A_249)) | ~m1_subset_1(C_251, u1_struct_0(A_249)) | ~m1_subset_1(B_250, u1_struct_0(A_249)) | ~l1_orders_2(A_249))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.71/1.85  tff(c_1204, plain, (![A_82, B_250, C_251]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_82), B_250, C_251), A_82) | ~m1_subset_1(C_251, u1_struct_0(k2_yellow_1(A_82))) | ~m1_subset_1(B_250, u1_struct_0(k2_yellow_1(A_82))) | ~l1_orders_2(k2_yellow_1(A_82)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1201])).
% 4.71/1.85  tff(c_1206, plain, (![A_82, B_250, C_251]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_82), B_250, C_251), A_82) | ~m1_subset_1(C_251, A_82) | ~m1_subset_1(B_250, A_82))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_54, c_54, c_1204])).
% 4.71/1.85  tff(c_68, plain, (v2_lattice3(k2_yellow_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.71/1.85  tff(c_52, plain, (![A_81]: (v5_orders_2(k2_yellow_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.71/1.85  tff(c_70, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.71/1.85  tff(c_48, plain, (![A_81]: (v3_orders_2(k2_yellow_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.71/1.85  tff(c_58, plain, (![A_83, B_87, C_89]: (r3_orders_2(k2_yellow_1(A_83), B_87, C_89) | ~r1_tarski(B_87, C_89) | ~m1_subset_1(C_89, u1_struct_0(k2_yellow_1(A_83))) | ~m1_subset_1(B_87, u1_struct_0(k2_yellow_1(A_83))) | v1_xboole_0(A_83))), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.71/1.85  tff(c_74, plain, (![A_83, B_87, C_89]: (r3_orders_2(k2_yellow_1(A_83), B_87, C_89) | ~r1_tarski(B_87, C_89) | ~m1_subset_1(C_89, A_83) | ~m1_subset_1(B_87, A_83) | v1_xboole_0(A_83))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_58])).
% 4.71/1.85  tff(c_1370, plain, (![A_280, B_281, C_282]: (k12_lattice3(A_280, B_281, C_282)=B_281 | ~r3_orders_2(A_280, B_281, C_282) | ~m1_subset_1(C_282, u1_struct_0(A_280)) | ~m1_subset_1(B_281, u1_struct_0(A_280)) | ~l1_orders_2(A_280) | ~v2_lattice3(A_280) | ~v5_orders_2(A_280) | ~v3_orders_2(A_280))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.71/1.85  tff(c_1374, plain, (![A_83, B_87, C_89]: (k12_lattice3(k2_yellow_1(A_83), B_87, C_89)=B_87 | ~m1_subset_1(C_89, u1_struct_0(k2_yellow_1(A_83))) | ~m1_subset_1(B_87, u1_struct_0(k2_yellow_1(A_83))) | ~l1_orders_2(k2_yellow_1(A_83)) | ~v2_lattice3(k2_yellow_1(A_83)) | ~v5_orders_2(k2_yellow_1(A_83)) | ~v3_orders_2(k2_yellow_1(A_83)) | ~r1_tarski(B_87, C_89) | ~m1_subset_1(C_89, A_83) | ~m1_subset_1(B_87, A_83) | v1_xboole_0(A_83))), inference(resolution, [status(thm)], [c_74, c_1370])).
% 4.71/1.85  tff(c_1381, plain, (![A_283, B_284, C_285]: (k12_lattice3(k2_yellow_1(A_283), B_284, C_285)=B_284 | ~v2_lattice3(k2_yellow_1(A_283)) | ~r1_tarski(B_284, C_285) | ~m1_subset_1(C_285, A_283) | ~m1_subset_1(B_284, A_283) | v1_xboole_0(A_283))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_52, c_44, c_54, c_54, c_1374])).
% 4.71/1.85  tff(c_1383, plain, (![B_284, C_285]: (k12_lattice3(k2_yellow_1('#skF_2'), B_284, C_285)=B_284 | ~r1_tarski(B_284, C_285) | ~m1_subset_1(C_285, '#skF_2') | ~m1_subset_1(B_284, '#skF_2') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_68, c_1381])).
% 4.71/1.85  tff(c_1387, plain, (![B_286, C_287]: (k12_lattice3(k2_yellow_1('#skF_2'), B_286, C_287)=B_286 | ~r1_tarski(B_286, C_287) | ~m1_subset_1(C_287, '#skF_2') | ~m1_subset_1(B_286, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_70, c_1383])).
% 4.71/1.85  tff(c_1318, plain, (![A_266, B_267, C_268]: (k12_lattice3(A_266, B_267, C_268)=k11_lattice3(A_266, B_267, C_268) | ~m1_subset_1(C_268, u1_struct_0(A_266)) | ~m1_subset_1(B_267, u1_struct_0(A_266)) | ~l1_orders_2(A_266) | ~v2_lattice3(A_266) | ~v5_orders_2(A_266))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.71/1.85  tff(c_1325, plain, (![A_82, B_267, C_268]: (k12_lattice3(k2_yellow_1(A_82), B_267, C_268)=k11_lattice3(k2_yellow_1(A_82), B_267, C_268) | ~m1_subset_1(C_268, A_82) | ~m1_subset_1(B_267, u1_struct_0(k2_yellow_1(A_82))) | ~l1_orders_2(k2_yellow_1(A_82)) | ~v2_lattice3(k2_yellow_1(A_82)) | ~v5_orders_2(k2_yellow_1(A_82)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1318])).
% 4.71/1.85  tff(c_1352, plain, (![A_272, B_273, C_274]: (k12_lattice3(k2_yellow_1(A_272), B_273, C_274)=k11_lattice3(k2_yellow_1(A_272), B_273, C_274) | ~m1_subset_1(C_274, A_272) | ~m1_subset_1(B_273, A_272) | ~v2_lattice3(k2_yellow_1(A_272)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_44, c_54, c_1325])).
% 4.71/1.85  tff(c_1355, plain, (![B_273, C_274]: (k12_lattice3(k2_yellow_1('#skF_2'), B_273, C_274)=k11_lattice3(k2_yellow_1('#skF_2'), B_273, C_274) | ~m1_subset_1(C_274, '#skF_2') | ~m1_subset_1(B_273, '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_1352])).
% 4.71/1.85  tff(c_1393, plain, (![B_286, C_287]: (k11_lattice3(k2_yellow_1('#skF_2'), B_286, C_287)=B_286 | ~m1_subset_1(C_287, '#skF_2') | ~m1_subset_1(B_286, '#skF_2') | ~r1_tarski(B_286, C_287) | ~m1_subset_1(C_287, '#skF_2') | ~m1_subset_1(B_286, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1387, c_1355])).
% 4.71/1.85  tff(c_1494, plain, (![A_295, B_296, C_297]: (r1_orders_2(A_295, k11_lattice3(A_295, B_296, C_297), B_296) | ~m1_subset_1(k11_lattice3(A_295, B_296, C_297), u1_struct_0(A_295)) | ~m1_subset_1(C_297, u1_struct_0(A_295)) | ~m1_subset_1(B_296, u1_struct_0(A_295)) | ~l1_orders_2(A_295) | ~v2_lattice3(A_295) | ~v5_orders_2(A_295) | v2_struct_0(A_295))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.71/1.85  tff(c_1496, plain, (![B_286, C_287]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_286, C_287), B_286) | ~m1_subset_1(B_286, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(C_287, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_286, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_287, '#skF_2') | ~m1_subset_1(B_286, '#skF_2') | ~r1_tarski(B_286, C_287) | ~m1_subset_1(C_287, '#skF_2') | ~m1_subset_1(B_286, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1393, c_1494])).
% 4.71/1.85  tff(c_1506, plain, (![B_286, C_287]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_286, C_287), B_286) | v2_struct_0(k2_yellow_1('#skF_2')) | ~r1_tarski(B_286, C_287) | ~m1_subset_1(C_287, '#skF_2') | ~m1_subset_1(B_286, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_68, c_44, c_54, c_54, c_54, c_1496])).
% 4.71/1.85  tff(c_1547, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_1506])).
% 4.71/1.85  tff(c_16, plain, (![A_13]: (~v2_struct_0(A_13) | ~v2_lattice3(A_13) | ~l1_orders_2(A_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.71/1.85  tff(c_1550, plain, (~v2_lattice3(k2_yellow_1('#skF_2')) | ~l1_orders_2(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_1547, c_16])).
% 4.71/1.85  tff(c_1554, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_68, c_1550])).
% 4.71/1.85  tff(c_1556, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_1506])).
% 4.71/1.85  tff(c_18, plain, (![A_14, B_15, C_16]: (m1_subset_1(k11_lattice3(A_14, B_15, C_16), u1_struct_0(A_14)) | ~m1_subset_1(C_16, u1_struct_0(A_14)) | ~m1_subset_1(B_15, u1_struct_0(A_14)) | ~l1_orders_2(A_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.71/1.85  tff(c_1527, plain, (![A_300, B_301, C_302]: (r1_orders_2(A_300, k11_lattice3(A_300, B_301, C_302), C_302) | ~m1_subset_1(k11_lattice3(A_300, B_301, C_302), u1_struct_0(A_300)) | ~m1_subset_1(C_302, u1_struct_0(A_300)) | ~m1_subset_1(B_301, u1_struct_0(A_300)) | ~l1_orders_2(A_300) | ~v2_lattice3(A_300) | ~v5_orders_2(A_300) | v2_struct_0(A_300))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.71/1.85  tff(c_1544, plain, (![A_14, B_15, C_16]: (r1_orders_2(A_14, k11_lattice3(A_14, B_15, C_16), C_16) | ~v2_lattice3(A_14) | ~v5_orders_2(A_14) | v2_struct_0(A_14) | ~m1_subset_1(C_16, u1_struct_0(A_14)) | ~m1_subset_1(B_15, u1_struct_0(A_14)) | ~l1_orders_2(A_14))), inference(resolution, [status(thm)], [c_18, c_1527])).
% 4.71/1.85  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.71/1.85  tff(c_1706, plain, (![A_313, B_314, C_315]: (r1_orders_2(A_313, k11_lattice3(A_313, B_314, C_315), C_315) | ~v2_lattice3(A_313) | ~v5_orders_2(A_313) | v2_struct_0(A_313) | ~m1_subset_1(C_315, u1_struct_0(A_313)) | ~m1_subset_1(B_314, u1_struct_0(A_313)) | ~l1_orders_2(A_313))), inference(resolution, [status(thm)], [c_18, c_1527])).
% 4.71/1.85  tff(c_1712, plain, (![B_286, C_287]: (r1_orders_2(k2_yellow_1('#skF_2'), B_286, C_287) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_287, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_286, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_287, '#skF_2') | ~m1_subset_1(B_286, '#skF_2') | ~r1_tarski(B_286, C_287) | ~m1_subset_1(C_287, '#skF_2') | ~m1_subset_1(B_286, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1393, c_1706])).
% 4.71/1.85  tff(c_1723, plain, (![B_286, C_287]: (r1_orders_2(k2_yellow_1('#skF_2'), B_286, C_287) | v2_struct_0(k2_yellow_1('#skF_2')) | ~r1_tarski(B_286, C_287) | ~m1_subset_1(C_287, '#skF_2') | ~m1_subset_1(B_286, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_54, c_54, c_52, c_68, c_1712])).
% 4.71/1.85  tff(c_1724, plain, (![B_286, C_287]: (r1_orders_2(k2_yellow_1('#skF_2'), B_286, C_287) | ~r1_tarski(B_286, C_287) | ~m1_subset_1(C_287, '#skF_2') | ~m1_subset_1(B_286, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_1556, c_1723])).
% 4.71/1.85  tff(c_1839, plain, (![A_338, B_339, C_340, D_341]: (r1_orders_2(A_338, '#skF_1'(A_338, B_339, C_340, D_341), C_340) | k11_lattice3(A_338, B_339, C_340)=D_341 | ~r1_orders_2(A_338, D_341, C_340) | ~r1_orders_2(A_338, D_341, B_339) | ~m1_subset_1(D_341, u1_struct_0(A_338)) | ~m1_subset_1(C_340, u1_struct_0(A_338)) | ~m1_subset_1(B_339, u1_struct_0(A_338)) | ~l1_orders_2(A_338) | ~v2_lattice3(A_338) | ~v5_orders_2(A_338) | v2_struct_0(A_338))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.71/1.85  tff(c_20, plain, (![A_17, B_41, C_53, D_59]: (~r1_orders_2(A_17, '#skF_1'(A_17, B_41, C_53, D_59), D_59) | k11_lattice3(A_17, B_41, C_53)=D_59 | ~r1_orders_2(A_17, D_59, C_53) | ~r1_orders_2(A_17, D_59, B_41) | ~m1_subset_1(D_59, u1_struct_0(A_17)) | ~m1_subset_1(C_53, u1_struct_0(A_17)) | ~m1_subset_1(B_41, u1_struct_0(A_17)) | ~l1_orders_2(A_17) | ~v2_lattice3(A_17) | ~v5_orders_2(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.71/1.85  tff(c_1918, plain, (![A_359, B_360, C_361]: (k11_lattice3(A_359, B_360, C_361)=C_361 | ~r1_orders_2(A_359, C_361, C_361) | ~r1_orders_2(A_359, C_361, B_360) | ~m1_subset_1(C_361, u1_struct_0(A_359)) | ~m1_subset_1(B_360, u1_struct_0(A_359)) | ~l1_orders_2(A_359) | ~v2_lattice3(A_359) | ~v5_orders_2(A_359) | v2_struct_0(A_359))), inference(resolution, [status(thm)], [c_1839, c_20])).
% 4.71/1.85  tff(c_1923, plain, (![B_360, C_287]: (k11_lattice3(k2_yellow_1('#skF_2'), B_360, C_287)=C_287 | ~r1_orders_2(k2_yellow_1('#skF_2'), C_287, B_360) | ~m1_subset_1(C_287, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_360, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~r1_tarski(C_287, C_287) | ~m1_subset_1(C_287, '#skF_2'))), inference(resolution, [status(thm)], [c_1724, c_1918])).
% 4.71/1.85  tff(c_1930, plain, (![B_360, C_287]: (k11_lattice3(k2_yellow_1('#skF_2'), B_360, C_287)=C_287 | ~r1_orders_2(k2_yellow_1('#skF_2'), C_287, B_360) | ~m1_subset_1(B_360, '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_287, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_52, c_68, c_44, c_54, c_54, c_1923])).
% 4.71/1.85  tff(c_1932, plain, (![B_362, C_363]: (k11_lattice3(k2_yellow_1('#skF_2'), B_362, C_363)=C_363 | ~r1_orders_2(k2_yellow_1('#skF_2'), C_363, B_362) | ~m1_subset_1(B_362, '#skF_2') | ~m1_subset_1(C_363, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_1556, c_1930])).
% 4.71/1.85  tff(c_1968, plain, (![C_16, B_15]: (k11_lattice3(k2_yellow_1('#skF_2'), C_16, k11_lattice3(k2_yellow_1('#skF_2'), B_15, C_16))=k11_lattice3(k2_yellow_1('#skF_2'), B_15, C_16) | ~m1_subset_1(C_16, '#skF_2') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_15, C_16), '#skF_2') | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_16, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_15, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_1544, c_1932])).
% 4.71/1.85  tff(c_1995, plain, (![C_16, B_15]: (k11_lattice3(k2_yellow_1('#skF_2'), C_16, k11_lattice3(k2_yellow_1('#skF_2'), B_15, C_16))=k11_lattice3(k2_yellow_1('#skF_2'), B_15, C_16) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_15, C_16), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_16, '#skF_2') | ~m1_subset_1(B_15, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_54, c_54, c_52, c_68, c_1968])).
% 4.71/1.85  tff(c_2209, plain, (![C_367, B_368]: (k11_lattice3(k2_yellow_1('#skF_2'), C_367, k11_lattice3(k2_yellow_1('#skF_2'), B_368, C_367))=k11_lattice3(k2_yellow_1('#skF_2'), B_368, C_367) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_368, C_367), '#skF_2') | ~m1_subset_1(C_367, '#skF_2') | ~m1_subset_1(B_368, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_1556, c_1995])).
% 4.71/1.85  tff(c_1213, plain, (![A_258, C_259, B_260]: (k11_lattice3(A_258, C_259, B_260)=k11_lattice3(A_258, B_260, C_259) | ~m1_subset_1(C_259, u1_struct_0(A_258)) | ~m1_subset_1(B_260, u1_struct_0(A_258)) | ~l1_orders_2(A_258) | ~v2_lattice3(A_258) | ~v5_orders_2(A_258))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.71/1.85  tff(c_1220, plain, (![A_82, C_259, B_260]: (k11_lattice3(k2_yellow_1(A_82), C_259, B_260)=k11_lattice3(k2_yellow_1(A_82), B_260, C_259) | ~m1_subset_1(C_259, A_82) | ~m1_subset_1(B_260, u1_struct_0(k2_yellow_1(A_82))) | ~l1_orders_2(k2_yellow_1(A_82)) | ~v2_lattice3(k2_yellow_1(A_82)) | ~v5_orders_2(k2_yellow_1(A_82)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1213])).
% 4.71/1.85  tff(c_1225, plain, (![A_261, C_262, B_263]: (k11_lattice3(k2_yellow_1(A_261), C_262, B_263)=k11_lattice3(k2_yellow_1(A_261), B_263, C_262) | ~m1_subset_1(C_262, A_261) | ~m1_subset_1(B_263, A_261) | ~v2_lattice3(k2_yellow_1(A_261)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_44, c_54, c_1220])).
% 4.71/1.85  tff(c_1228, plain, (![C_262, B_263]: (k11_lattice3(k2_yellow_1('#skF_2'), C_262, B_263)=k11_lattice3(k2_yellow_1('#skF_2'), B_263, C_262) | ~m1_subset_1(C_262, '#skF_2') | ~m1_subset_1(B_263, '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_1225])).
% 4.71/1.85  tff(c_1340, plain, (![A_269, B_270, C_271]: (r3_orders_2(A_269, B_270, C_271) | k12_lattice3(A_269, B_270, C_271)!=B_270 | ~m1_subset_1(C_271, u1_struct_0(A_269)) | ~m1_subset_1(B_270, u1_struct_0(A_269)) | ~l1_orders_2(A_269) | ~v2_lattice3(A_269) | ~v5_orders_2(A_269) | ~v3_orders_2(A_269))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.71/1.85  tff(c_1347, plain, (![A_82, B_270, C_271]: (r3_orders_2(k2_yellow_1(A_82), B_270, C_271) | k12_lattice3(k2_yellow_1(A_82), B_270, C_271)!=B_270 | ~m1_subset_1(C_271, A_82) | ~m1_subset_1(B_270, u1_struct_0(k2_yellow_1(A_82))) | ~l1_orders_2(k2_yellow_1(A_82)) | ~v2_lattice3(k2_yellow_1(A_82)) | ~v5_orders_2(k2_yellow_1(A_82)) | ~v3_orders_2(k2_yellow_1(A_82)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1340])).
% 4.71/1.85  tff(c_1365, plain, (![A_277, B_278, C_279]: (r3_orders_2(k2_yellow_1(A_277), B_278, C_279) | k12_lattice3(k2_yellow_1(A_277), B_278, C_279)!=B_278 | ~m1_subset_1(C_279, A_277) | ~m1_subset_1(B_278, A_277) | ~v2_lattice3(k2_yellow_1(A_277)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_52, c_44, c_54, c_1347])).
% 4.71/1.85  tff(c_60, plain, (![B_87, C_89, A_83]: (r1_tarski(B_87, C_89) | ~r3_orders_2(k2_yellow_1(A_83), B_87, C_89) | ~m1_subset_1(C_89, u1_struct_0(k2_yellow_1(A_83))) | ~m1_subset_1(B_87, u1_struct_0(k2_yellow_1(A_83))) | v1_xboole_0(A_83))), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.71/1.85  tff(c_73, plain, (![B_87, C_89, A_83]: (r1_tarski(B_87, C_89) | ~r3_orders_2(k2_yellow_1(A_83), B_87, C_89) | ~m1_subset_1(C_89, A_83) | ~m1_subset_1(B_87, A_83) | v1_xboole_0(A_83))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_60])).
% 4.71/1.85  tff(c_1402, plain, (![B_288, C_289, A_290]: (r1_tarski(B_288, C_289) | v1_xboole_0(A_290) | k12_lattice3(k2_yellow_1(A_290), B_288, C_289)!=B_288 | ~m1_subset_1(C_289, A_290) | ~m1_subset_1(B_288, A_290) | ~v2_lattice3(k2_yellow_1(A_290)))), inference(resolution, [status(thm)], [c_1365, c_73])).
% 4.71/1.85  tff(c_1406, plain, (![B_273, C_274]: (r1_tarski(B_273, C_274) | v1_xboole_0('#skF_2') | k11_lattice3(k2_yellow_1('#skF_2'), B_273, C_274)!=B_273 | ~m1_subset_1(C_274, '#skF_2') | ~m1_subset_1(B_273, '#skF_2') | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_274, '#skF_2') | ~m1_subset_1(B_273, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1355, c_1402])).
% 4.71/1.85  tff(c_1412, plain, (![B_273, C_274]: (r1_tarski(B_273, C_274) | v1_xboole_0('#skF_2') | k11_lattice3(k2_yellow_1('#skF_2'), B_273, C_274)!=B_273 | ~m1_subset_1(C_274, '#skF_2') | ~m1_subset_1(B_273, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1406])).
% 4.71/1.85  tff(c_1414, plain, (![B_291, C_292]: (r1_tarski(B_291, C_292) | k11_lattice3(k2_yellow_1('#skF_2'), B_291, C_292)!=B_291 | ~m1_subset_1(C_292, '#skF_2') | ~m1_subset_1(B_291, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_70, c_1412])).
% 4.71/1.85  tff(c_1420, plain, (![C_262, B_263]: (r1_tarski(C_262, B_263) | k11_lattice3(k2_yellow_1('#skF_2'), B_263, C_262)!=C_262 | ~m1_subset_1(B_263, '#skF_2') | ~m1_subset_1(C_262, '#skF_2') | ~m1_subset_1(C_262, '#skF_2') | ~m1_subset_1(B_263, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1228, c_1414])).
% 4.71/1.85  tff(c_2300, plain, (![B_369, C_370]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_369, C_370), C_370) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_369, C_370), '#skF_2') | ~m1_subset_1(C_370, '#skF_2') | ~m1_subset_1(B_369, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2209, c_1420])).
% 4.71/1.85  tff(c_163, plain, (![A_124, B_125, C_126]: (m1_subset_1(k11_lattice3(A_124, B_125, C_126), u1_struct_0(A_124)) | ~m1_subset_1(C_126, u1_struct_0(A_124)) | ~m1_subset_1(B_125, u1_struct_0(A_124)) | ~l1_orders_2(A_124))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.71/1.85  tff(c_166, plain, (![A_82, B_125, C_126]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_82), B_125, C_126), A_82) | ~m1_subset_1(C_126, u1_struct_0(k2_yellow_1(A_82))) | ~m1_subset_1(B_125, u1_struct_0(k2_yellow_1(A_82))) | ~l1_orders_2(k2_yellow_1(A_82)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_163])).
% 4.71/1.85  tff(c_168, plain, (![A_82, B_125, C_126]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_82), B_125, C_126), A_82) | ~m1_subset_1(C_126, A_82) | ~m1_subset_1(B_125, A_82))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_54, c_54, c_166])).
% 4.71/1.85  tff(c_301, plain, (![A_152, B_153, C_154]: (k12_lattice3(A_152, B_153, C_154)=B_153 | ~r3_orders_2(A_152, B_153, C_154) | ~m1_subset_1(C_154, u1_struct_0(A_152)) | ~m1_subset_1(B_153, u1_struct_0(A_152)) | ~l1_orders_2(A_152) | ~v2_lattice3(A_152) | ~v5_orders_2(A_152) | ~v3_orders_2(A_152))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.71/1.85  tff(c_305, plain, (![A_83, B_87, C_89]: (k12_lattice3(k2_yellow_1(A_83), B_87, C_89)=B_87 | ~m1_subset_1(C_89, u1_struct_0(k2_yellow_1(A_83))) | ~m1_subset_1(B_87, u1_struct_0(k2_yellow_1(A_83))) | ~l1_orders_2(k2_yellow_1(A_83)) | ~v2_lattice3(k2_yellow_1(A_83)) | ~v5_orders_2(k2_yellow_1(A_83)) | ~v3_orders_2(k2_yellow_1(A_83)) | ~r1_tarski(B_87, C_89) | ~m1_subset_1(C_89, A_83) | ~m1_subset_1(B_87, A_83) | v1_xboole_0(A_83))), inference(resolution, [status(thm)], [c_74, c_301])).
% 4.71/1.85  tff(c_312, plain, (![A_155, B_156, C_157]: (k12_lattice3(k2_yellow_1(A_155), B_156, C_157)=B_156 | ~v2_lattice3(k2_yellow_1(A_155)) | ~r1_tarski(B_156, C_157) | ~m1_subset_1(C_157, A_155) | ~m1_subset_1(B_156, A_155) | v1_xboole_0(A_155))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_52, c_44, c_54, c_54, c_305])).
% 4.71/1.85  tff(c_314, plain, (![B_156, C_157]: (k12_lattice3(k2_yellow_1('#skF_2'), B_156, C_157)=B_156 | ~r1_tarski(B_156, C_157) | ~m1_subset_1(C_157, '#skF_2') | ~m1_subset_1(B_156, '#skF_2') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_68, c_312])).
% 4.71/1.85  tff(c_318, plain, (![B_158, C_159]: (k12_lattice3(k2_yellow_1('#skF_2'), B_158, C_159)=B_158 | ~r1_tarski(B_158, C_159) | ~m1_subset_1(C_159, '#skF_2') | ~m1_subset_1(B_158, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_70, c_314])).
% 4.71/1.85  tff(c_259, plain, (![A_138, B_139, C_140]: (k12_lattice3(A_138, B_139, C_140)=k11_lattice3(A_138, B_139, C_140) | ~m1_subset_1(C_140, u1_struct_0(A_138)) | ~m1_subset_1(B_139, u1_struct_0(A_138)) | ~l1_orders_2(A_138) | ~v2_lattice3(A_138) | ~v5_orders_2(A_138))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.71/1.85  tff(c_266, plain, (![A_82, B_139, C_140]: (k12_lattice3(k2_yellow_1(A_82), B_139, C_140)=k11_lattice3(k2_yellow_1(A_82), B_139, C_140) | ~m1_subset_1(C_140, A_82) | ~m1_subset_1(B_139, u1_struct_0(k2_yellow_1(A_82))) | ~l1_orders_2(k2_yellow_1(A_82)) | ~v2_lattice3(k2_yellow_1(A_82)) | ~v5_orders_2(k2_yellow_1(A_82)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_259])).
% 4.71/1.85  tff(c_283, plain, (![A_144, B_145, C_146]: (k12_lattice3(k2_yellow_1(A_144), B_145, C_146)=k11_lattice3(k2_yellow_1(A_144), B_145, C_146) | ~m1_subset_1(C_146, A_144) | ~m1_subset_1(B_145, A_144) | ~v2_lattice3(k2_yellow_1(A_144)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_44, c_54, c_266])).
% 4.71/1.85  tff(c_286, plain, (![B_145, C_146]: (k12_lattice3(k2_yellow_1('#skF_2'), B_145, C_146)=k11_lattice3(k2_yellow_1('#skF_2'), B_145, C_146) | ~m1_subset_1(C_146, '#skF_2') | ~m1_subset_1(B_145, '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_283])).
% 4.71/1.85  tff(c_324, plain, (![B_158, C_159]: (k11_lattice3(k2_yellow_1('#skF_2'), B_158, C_159)=B_158 | ~m1_subset_1(C_159, '#skF_2') | ~m1_subset_1(B_158, '#skF_2') | ~r1_tarski(B_158, C_159) | ~m1_subset_1(C_159, '#skF_2') | ~m1_subset_1(B_158, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_318, c_286])).
% 4.71/1.85  tff(c_405, plain, (![A_167, B_168, C_169]: (r1_orders_2(A_167, k11_lattice3(A_167, B_168, C_169), C_169) | ~m1_subset_1(k11_lattice3(A_167, B_168, C_169), u1_struct_0(A_167)) | ~m1_subset_1(C_169, u1_struct_0(A_167)) | ~m1_subset_1(B_168, u1_struct_0(A_167)) | ~l1_orders_2(A_167) | ~v2_lattice3(A_167) | ~v5_orders_2(A_167) | v2_struct_0(A_167))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.71/1.85  tff(c_407, plain, (![B_158, C_159]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_158, C_159), C_159) | ~m1_subset_1(B_158, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(C_159, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_158, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_159, '#skF_2') | ~m1_subset_1(B_158, '#skF_2') | ~r1_tarski(B_158, C_159) | ~m1_subset_1(C_159, '#skF_2') | ~m1_subset_1(B_158, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_324, c_405])).
% 4.71/1.85  tff(c_417, plain, (![B_158, C_159]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_158, C_159), C_159) | v2_struct_0(k2_yellow_1('#skF_2')) | ~r1_tarski(B_158, C_159) | ~m1_subset_1(C_159, '#skF_2') | ~m1_subset_1(B_158, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_68, c_44, c_54, c_54, c_54, c_407])).
% 4.71/1.85  tff(c_438, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_417])).
% 4.71/1.85  tff(c_441, plain, (~v2_lattice3(k2_yellow_1('#skF_2')) | ~l1_orders_2(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_438, c_16])).
% 4.71/1.85  tff(c_445, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_68, c_441])).
% 4.71/1.85  tff(c_447, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_417])).
% 4.71/1.85  tff(c_169, plain, (![A_127, C_128, B_129]: (k11_lattice3(A_127, C_128, B_129)=k11_lattice3(A_127, B_129, C_128) | ~m1_subset_1(C_128, u1_struct_0(A_127)) | ~m1_subset_1(B_129, u1_struct_0(A_127)) | ~l1_orders_2(A_127) | ~v2_lattice3(A_127) | ~v5_orders_2(A_127))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.71/1.85  tff(c_173, plain, (![A_82, C_128, B_129]: (k11_lattice3(k2_yellow_1(A_82), C_128, B_129)=k11_lattice3(k2_yellow_1(A_82), B_129, C_128) | ~m1_subset_1(C_128, A_82) | ~m1_subset_1(B_129, u1_struct_0(k2_yellow_1(A_82))) | ~l1_orders_2(k2_yellow_1(A_82)) | ~v2_lattice3(k2_yellow_1(A_82)) | ~v5_orders_2(k2_yellow_1(A_82)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_169])).
% 4.71/1.85  tff(c_182, plain, (![A_133, C_134, B_135]: (k11_lattice3(k2_yellow_1(A_133), C_134, B_135)=k11_lattice3(k2_yellow_1(A_133), B_135, C_134) | ~m1_subset_1(C_134, A_133) | ~m1_subset_1(B_135, A_133) | ~v2_lattice3(k2_yellow_1(A_133)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_44, c_54, c_173])).
% 4.71/1.85  tff(c_185, plain, (![C_134, B_135]: (k11_lattice3(k2_yellow_1('#skF_2'), C_134, B_135)=k11_lattice3(k2_yellow_1('#skF_2'), B_135, C_134) | ~m1_subset_1(C_134, '#skF_2') | ~m1_subset_1(B_135, '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_182])).
% 4.71/1.85  tff(c_448, plain, (![A_172, B_173, C_174]: (r1_orders_2(A_172, k11_lattice3(A_172, B_173, C_174), B_173) | ~m1_subset_1(k11_lattice3(A_172, B_173, C_174), u1_struct_0(A_172)) | ~m1_subset_1(C_174, u1_struct_0(A_172)) | ~m1_subset_1(B_173, u1_struct_0(A_172)) | ~l1_orders_2(A_172) | ~v2_lattice3(A_172) | ~v5_orders_2(A_172) | v2_struct_0(A_172))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.71/1.85  tff(c_511, plain, (![A_183, B_184, C_185]: (r1_orders_2(A_183, k11_lattice3(A_183, B_184, C_185), B_184) | ~v2_lattice3(A_183) | ~v5_orders_2(A_183) | v2_struct_0(A_183) | ~m1_subset_1(C_185, u1_struct_0(A_183)) | ~m1_subset_1(B_184, u1_struct_0(A_183)) | ~l1_orders_2(A_183))), inference(resolution, [status(thm)], [c_18, c_448])).
% 4.71/1.85  tff(c_517, plain, (![C_134, B_135]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), C_134, B_135), B_135) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_134, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_135, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_134, '#skF_2') | ~m1_subset_1(B_135, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_185, c_511])).
% 4.71/1.85  tff(c_525, plain, (![C_134, B_135]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), C_134, B_135), B_135) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_134, '#skF_2') | ~m1_subset_1(B_135, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_54, c_54, c_52, c_68, c_517])).
% 4.71/1.85  tff(c_526, plain, (![C_134, B_135]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), C_134, B_135), B_135) | ~m1_subset_1(C_134, '#skF_2') | ~m1_subset_1(B_135, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_447, c_525])).
% 4.71/1.85  tff(c_559, plain, (![A_197, B_198, C_199]: (r1_orders_2(A_197, k11_lattice3(A_197, B_198, C_199), C_199) | ~v2_lattice3(A_197) | ~v5_orders_2(A_197) | v2_struct_0(A_197) | ~m1_subset_1(C_199, u1_struct_0(A_197)) | ~m1_subset_1(B_198, u1_struct_0(A_197)) | ~l1_orders_2(A_197))), inference(resolution, [status(thm)], [c_18, c_405])).
% 4.71/1.85  tff(c_562, plain, (![B_158, C_159]: (r1_orders_2(k2_yellow_1('#skF_2'), B_158, C_159) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_159, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_158, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_159, '#skF_2') | ~m1_subset_1(B_158, '#skF_2') | ~r1_tarski(B_158, C_159) | ~m1_subset_1(C_159, '#skF_2') | ~m1_subset_1(B_158, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_324, c_559])).
% 4.71/1.85  tff(c_570, plain, (![B_158, C_159]: (r1_orders_2(k2_yellow_1('#skF_2'), B_158, C_159) | v2_struct_0(k2_yellow_1('#skF_2')) | ~r1_tarski(B_158, C_159) | ~m1_subset_1(C_159, '#skF_2') | ~m1_subset_1(B_158, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_54, c_54, c_52, c_68, c_562])).
% 4.71/1.85  tff(c_571, plain, (![B_158, C_159]: (r1_orders_2(k2_yellow_1('#skF_2'), B_158, C_159) | ~r1_tarski(B_158, C_159) | ~m1_subset_1(C_159, '#skF_2') | ~m1_subset_1(B_158, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_447, c_570])).
% 4.71/1.85  tff(c_597, plain, (![A_204, B_205, C_206, D_207]: (r1_orders_2(A_204, '#skF_1'(A_204, B_205, C_206, D_207), C_206) | k11_lattice3(A_204, B_205, C_206)=D_207 | ~r1_orders_2(A_204, D_207, C_206) | ~r1_orders_2(A_204, D_207, B_205) | ~m1_subset_1(D_207, u1_struct_0(A_204)) | ~m1_subset_1(C_206, u1_struct_0(A_204)) | ~m1_subset_1(B_205, u1_struct_0(A_204)) | ~l1_orders_2(A_204) | ~v2_lattice3(A_204) | ~v5_orders_2(A_204) | v2_struct_0(A_204))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.71/1.85  tff(c_767, plain, (![A_227, B_228, C_229]: (k11_lattice3(A_227, B_228, C_229)=C_229 | ~r1_orders_2(A_227, C_229, C_229) | ~r1_orders_2(A_227, C_229, B_228) | ~m1_subset_1(C_229, u1_struct_0(A_227)) | ~m1_subset_1(B_228, u1_struct_0(A_227)) | ~l1_orders_2(A_227) | ~v2_lattice3(A_227) | ~v5_orders_2(A_227) | v2_struct_0(A_227))), inference(resolution, [status(thm)], [c_597, c_20])).
% 4.71/1.85  tff(c_770, plain, (![B_228, C_159]: (k11_lattice3(k2_yellow_1('#skF_2'), B_228, C_159)=C_159 | ~r1_orders_2(k2_yellow_1('#skF_2'), C_159, B_228) | ~m1_subset_1(C_159, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_228, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~r1_tarski(C_159, C_159) | ~m1_subset_1(C_159, '#skF_2'))), inference(resolution, [status(thm)], [c_571, c_767])).
% 4.71/1.85  tff(c_775, plain, (![B_228, C_159]: (k11_lattice3(k2_yellow_1('#skF_2'), B_228, C_159)=C_159 | ~r1_orders_2(k2_yellow_1('#skF_2'), C_159, B_228) | ~m1_subset_1(B_228, '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_159, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_52, c_68, c_44, c_54, c_54, c_770])).
% 4.71/1.85  tff(c_781, plain, (![B_230, C_231]: (k11_lattice3(k2_yellow_1('#skF_2'), B_230, C_231)=C_231 | ~r1_orders_2(k2_yellow_1('#skF_2'), C_231, B_230) | ~m1_subset_1(B_230, '#skF_2') | ~m1_subset_1(C_231, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_447, c_775])).
% 4.71/1.85  tff(c_1043, plain, (![B_239, C_240]: (k11_lattice3(k2_yellow_1('#skF_2'), B_239, k11_lattice3(k2_yellow_1('#skF_2'), C_240, B_239))=k11_lattice3(k2_yellow_1('#skF_2'), C_240, B_239) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_240, B_239), '#skF_2') | ~m1_subset_1(C_240, '#skF_2') | ~m1_subset_1(B_239, '#skF_2'))), inference(resolution, [status(thm)], [c_526, c_781])).
% 4.71/1.85  tff(c_271, plain, (![A_141, B_142, C_143]: (r3_orders_2(A_141, B_142, C_143) | k12_lattice3(A_141, B_142, C_143)!=B_142 | ~m1_subset_1(C_143, u1_struct_0(A_141)) | ~m1_subset_1(B_142, u1_struct_0(A_141)) | ~l1_orders_2(A_141) | ~v2_lattice3(A_141) | ~v5_orders_2(A_141) | ~v3_orders_2(A_141))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.71/1.85  tff(c_278, plain, (![A_82, B_142, C_143]: (r3_orders_2(k2_yellow_1(A_82), B_142, C_143) | k12_lattice3(k2_yellow_1(A_82), B_142, C_143)!=B_142 | ~m1_subset_1(C_143, A_82) | ~m1_subset_1(B_142, u1_struct_0(k2_yellow_1(A_82))) | ~l1_orders_2(k2_yellow_1(A_82)) | ~v2_lattice3(k2_yellow_1(A_82)) | ~v5_orders_2(k2_yellow_1(A_82)) | ~v3_orders_2(k2_yellow_1(A_82)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_271])).
% 4.71/1.85  tff(c_296, plain, (![A_149, B_150, C_151]: (r3_orders_2(k2_yellow_1(A_149), B_150, C_151) | k12_lattice3(k2_yellow_1(A_149), B_150, C_151)!=B_150 | ~m1_subset_1(C_151, A_149) | ~m1_subset_1(B_150, A_149) | ~v2_lattice3(k2_yellow_1(A_149)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_52, c_44, c_54, c_278])).
% 4.71/1.85  tff(c_333, plain, (![B_160, C_161, A_162]: (r1_tarski(B_160, C_161) | v1_xboole_0(A_162) | k12_lattice3(k2_yellow_1(A_162), B_160, C_161)!=B_160 | ~m1_subset_1(C_161, A_162) | ~m1_subset_1(B_160, A_162) | ~v2_lattice3(k2_yellow_1(A_162)))), inference(resolution, [status(thm)], [c_296, c_73])).
% 4.71/1.85  tff(c_337, plain, (![B_145, C_146]: (r1_tarski(B_145, C_146) | v1_xboole_0('#skF_2') | k11_lattice3(k2_yellow_1('#skF_2'), B_145, C_146)!=B_145 | ~m1_subset_1(C_146, '#skF_2') | ~m1_subset_1(B_145, '#skF_2') | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_146, '#skF_2') | ~m1_subset_1(B_145, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_286, c_333])).
% 4.71/1.85  tff(c_343, plain, (![B_145, C_146]: (r1_tarski(B_145, C_146) | v1_xboole_0('#skF_2') | k11_lattice3(k2_yellow_1('#skF_2'), B_145, C_146)!=B_145 | ~m1_subset_1(C_146, '#skF_2') | ~m1_subset_1(B_145, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_337])).
% 4.71/1.85  tff(c_345, plain, (![B_163, C_164]: (r1_tarski(B_163, C_164) | k11_lattice3(k2_yellow_1('#skF_2'), B_163, C_164)!=B_163 | ~m1_subset_1(C_164, '#skF_2') | ~m1_subset_1(B_163, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_70, c_343])).
% 4.71/1.85  tff(c_351, plain, (![C_134, B_135]: (r1_tarski(C_134, B_135) | k11_lattice3(k2_yellow_1('#skF_2'), B_135, C_134)!=C_134 | ~m1_subset_1(B_135, '#skF_2') | ~m1_subset_1(C_134, '#skF_2') | ~m1_subset_1(C_134, '#skF_2') | ~m1_subset_1(B_135, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_185, c_345])).
% 4.71/1.85  tff(c_1134, plain, (![C_241, B_242]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), C_241, B_242), B_242) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_241, B_242), '#skF_2') | ~m1_subset_1(C_241, '#skF_2') | ~m1_subset_1(B_242, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1043, c_351])).
% 4.71/1.85  tff(c_186, plain, (![C_136, B_137]: (k11_lattice3(k2_yellow_1('#skF_2'), C_136, B_137)=k11_lattice3(k2_yellow_1('#skF_2'), B_137, C_136) | ~m1_subset_1(C_136, '#skF_2') | ~m1_subset_1(B_137, '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_182])).
% 4.71/1.85  tff(c_136, plain, (![A_112, B_113, C_114]: (r1_tarski(A_112, k3_xboole_0(B_113, C_114)) | ~r1_tarski(A_112, C_114) | ~r1_tarski(A_112, B_113))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.71/1.85  tff(c_62, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), k3_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.71/1.85  tff(c_143, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4') | ~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_136, c_62])).
% 4.71/1.85  tff(c_144, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_143])).
% 4.71/1.85  tff(c_213, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_186, c_144])).
% 4.71/1.85  tff(c_244, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_72, c_213])).
% 4.71/1.85  tff(c_1137, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_1134, c_244])).
% 4.71/1.85  tff(c_1160, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_72, c_1137])).
% 4.71/1.85  tff(c_1173, plain, (~m1_subset_1('#skF_3', '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_168, c_1160])).
% 4.71/1.85  tff(c_1181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_71, c_1173])).
% 4.71/1.85  tff(c_1182, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_143])).
% 4.71/1.85  tff(c_2303, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_2300, c_1182])).
% 4.71/1.85  tff(c_2326, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_72, c_2303])).
% 4.71/1.85  tff(c_2383, plain, (~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_1206, c_2326])).
% 4.71/1.85  tff(c_2395, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_72, c_2383])).
% 4.71/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.71/1.85  
% 4.71/1.85  Inference rules
% 4.71/1.85  ----------------------
% 4.71/1.86  #Ref     : 0
% 4.71/1.86  #Sup     : 502
% 4.71/1.86  #Fact    : 0
% 4.71/1.86  #Define  : 0
% 4.71/1.86  #Split   : 4
% 4.71/1.86  #Chain   : 0
% 4.71/1.86  #Close   : 0
% 4.71/1.86  
% 4.71/1.86  Ordering : KBO
% 4.71/1.86  
% 4.71/1.86  Simplification rules
% 4.71/1.86  ----------------------
% 4.71/1.86  #Subsume      : 225
% 4.71/1.86  #Demod        : 772
% 4.71/1.86  #Tautology    : 124
% 4.71/1.86  #SimpNegUnit  : 100
% 4.71/1.86  #BackRed      : 0
% 4.71/1.86  
% 4.71/1.86  #Partial instantiations: 0
% 4.71/1.86  #Strategies tried      : 1
% 4.71/1.86  
% 4.71/1.86  Timing (in seconds)
% 4.71/1.86  ----------------------
% 4.71/1.86  Preprocessing        : 0.37
% 4.71/1.86  Parsing              : 0.19
% 4.71/1.86  CNF conversion       : 0.03
% 4.71/1.86  Main loop            : 0.69
% 4.71/1.86  Inferencing          : 0.25
% 4.71/1.86  Reduction            : 0.24
% 4.71/1.86  Demodulation         : 0.18
% 4.71/1.86  BG Simplification    : 0.04
% 4.71/1.86  Subsumption          : 0.13
% 4.71/1.86  Abstraction          : 0.04
% 4.71/1.86  MUC search           : 0.00
% 4.71/1.86  Cooper               : 0.00
% 4.71/1.86  Total                : 1.12
% 4.71/1.86  Index Insertion      : 0.00
% 4.71/1.86  Index Deletion       : 0.00
% 4.71/1.86  Index Matching       : 0.00
% 4.71/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
