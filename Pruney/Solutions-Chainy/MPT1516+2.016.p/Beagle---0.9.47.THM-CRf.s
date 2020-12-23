%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:53 EST 2020

% Result     : Theorem 22.14s
% Output     : CNFRefutation 22.41s
% Verified   : 
% Statistics : Number of formulae       :  299 (5145 expanded)
%              Number of leaves         :   62 (1812 expanded)
%              Depth                    :   53
%              Number of atoms          :  935 (19996 expanded)
%              Number of equality atoms :  113 (2149 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r1_lattices > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k6_domain_1 > k3_xboole_0 > k16_lattice3 > k15_lattice3 > a_2_6_lattice3 > a_2_5_lattice3 > #nlpp > u1_struct_0 > k5_lattices > k1_xboole_0 > #skF_9 > #skF_4 > #skF_6 > #skF_8 > #skF_3 > #skF_11 > #skF_7 > #skF_2 > #skF_1 > #skF_5 > #skF_12 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k2_lattices,type,(
    k2_lattices: ( $i * $i * $i ) > $i )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k16_lattice3,type,(
    k16_lattice3: ( $i * $i ) > $i )).

tff(k15_lattice3,type,(
    k15_lattice3: ( $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff(r4_lattice3,type,(
    r4_lattice3: ( $i * $i * $i ) > $o )).

tff(a_2_5_lattice3,type,(
    a_2_5_lattice3: ( $i * $i ) > $i )).

tff(v4_lattice3,type,(
    v4_lattice3: $i > $o )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v13_lattices,type,(
    v13_lattices: $i > $o )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_lattices,type,(
    k5_lattices: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(a_2_6_lattice3,type,(
    a_2_6_lattice3: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_300,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v13_lattices(A)
          & l3_lattices(A)
          & k5_lattices(A) = k15_lattice3(A,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattice3)).

tff(f_106,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_210,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k15_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_233,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v10_lattices(B)
        & v4_lattice3(B)
        & l3_lattices(B) )
     => ( r2_hidden(A,a_2_5_lattice3(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ? [E] :
                ( m1_subset_1(E,u1_struct_0(B))
                & r3_lattices(B,D,E)
                & r2_hidden(E,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_5_lattice3)).

tff(f_52,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_50,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_188,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B,C] :
            ( m1_subset_1(C,u1_struct_0(A))
           => ( C = k15_lattice3(A,B)
            <=> ( r4_lattice3(A,C,B)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r4_lattice3(A,D,B)
                     => r1_lattices(A,C,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).

tff(f_279,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( k15_lattice3(A,B) = k15_lattice3(A,a_2_5_lattice3(A,B))
          & k16_lattice3(A,B) = k16_lattice3(A,a_2_6_lattice3(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_lattice3)).

tff(f_142,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => ( v13_lattices(A)
      <=> ? [B] :
            ( m1_subset_1(B,u1_struct_0(A))
            & ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( k2_lattices(A,B,C) = B
                  & k2_lattices(A,C,B) = B ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_lattices)).

tff(f_74,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( ( ~ v2_struct_0(A)
          & v10_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v4_lattices(A)
          & v5_lattices(A)
          & v6_lattices(A)
          & v7_lattices(A)
          & v8_lattices(A)
          & v9_lattices(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

tff(f_125,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_lattices(A,B,C)
              <=> k2_lattices(A,B,C) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).

tff(f_160,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( r4_lattice3(A,B,C)
            <=> ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r2_hidden(D,C)
                   => r1_lattices(A,D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).

tff(f_100,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => m1_subset_1(k5_lattices(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

tff(f_203,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => ( v6_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k2_lattices(A,B,C) = k2_lattices(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_lattices)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => ( v13_lattices(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( B = k5_lattices(A)
            <=> ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( k2_lattices(A,B,C) = B
                    & k2_lattices(A,C,B) = B ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).

tff(c_112,plain,(
    l3_lattices('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_300])).

tff(c_123,plain,(
    ! [A_116] :
      ( l1_lattices(A_116)
      | ~ l3_lattices(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_127,plain,(
    l1_lattices('#skF_12') ),
    inference(resolution,[status(thm)],[c_112,c_123])).

tff(c_118,plain,(
    ~ v2_struct_0('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_300])).

tff(c_84,plain,(
    ! [A_89,B_90] :
      ( m1_subset_1(k15_lattice3(A_89,B_90),u1_struct_0(A_89))
      | ~ l3_lattices(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_116,plain,(
    v10_lattices('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_300])).

tff(c_114,plain,(
    v4_lattice3('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_300])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_598,plain,(
    ! [A_225,B_226,C_227] :
      ( r2_hidden('#skF_11'(A_225,B_226,C_227),C_227)
      | ~ r2_hidden(A_225,a_2_5_lattice3(B_226,C_227))
      | ~ l3_lattices(B_226)
      | ~ v4_lattice3(B_226)
      | ~ v10_lattices(B_226)
      | v2_struct_0(B_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_14,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_140,plain,(
    ! [A_125,B_126,C_127] :
      ( ~ r1_xboole_0(A_125,B_126)
      | ~ r2_hidden(C_127,k3_xboole_0(A_125,B_126)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_161,plain,(
    ! [A_133,B_134,B_135] :
      ( ~ r1_xboole_0(A_133,B_134)
      | r1_tarski(k3_xboole_0(A_133,B_134),B_135) ) ),
    inference(resolution,[status(thm)],[c_6,c_140])).

tff(c_12,plain,(
    ! [A_11] :
      ( k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_167,plain,(
    ! [A_136,B_137] :
      ( k3_xboole_0(A_136,B_137) = k1_xboole_0
      | ~ r1_xboole_0(A_136,B_137) ) ),
    inference(resolution,[status(thm)],[c_161,c_12])).

tff(c_172,plain,(
    ! [A_138] : k3_xboole_0(A_138,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_167])).

tff(c_10,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_180,plain,(
    ! [A_138,C_10] :
      ( ~ r1_xboole_0(A_138,k1_xboole_0)
      | ~ r2_hidden(C_10,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_10])).

tff(c_187,plain,(
    ! [C_10] : ~ r2_hidden(C_10,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_180])).

tff(c_617,plain,(
    ! [A_228,B_229] :
      ( ~ r2_hidden(A_228,a_2_5_lattice3(B_229,k1_xboole_0))
      | ~ l3_lattices(B_229)
      | ~ v4_lattice3(B_229)
      | ~ v10_lattices(B_229)
      | v2_struct_0(B_229) ) ),
    inference(resolution,[status(thm)],[c_598,c_187])).

tff(c_643,plain,(
    ! [B_230,B_231] :
      ( ~ l3_lattices(B_230)
      | ~ v4_lattice3(B_230)
      | ~ v10_lattices(B_230)
      | v2_struct_0(B_230)
      | r1_tarski(a_2_5_lattice3(B_230,k1_xboole_0),B_231) ) ),
    inference(resolution,[status(thm)],[c_6,c_617])).

tff(c_663,plain,(
    ! [B_232] :
      ( a_2_5_lattice3(B_232,k1_xboole_0) = k1_xboole_0
      | ~ l3_lattices(B_232)
      | ~ v4_lattice3(B_232)
      | ~ v10_lattices(B_232)
      | v2_struct_0(B_232) ) ),
    inference(resolution,[status(thm)],[c_643,c_12])).

tff(c_666,plain,
    ( a_2_5_lattice3('#skF_12',k1_xboole_0) = k1_xboole_0
    | ~ l3_lattices('#skF_12')
    | ~ v10_lattices('#skF_12')
    | v2_struct_0('#skF_12') ),
    inference(resolution,[status(thm)],[c_114,c_663])).

tff(c_669,plain,
    ( a_2_5_lattice3('#skF_12',k1_xboole_0) = k1_xboole_0
    | v2_struct_0('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_112,c_666])).

tff(c_670,plain,(
    a_2_5_lattice3('#skF_12',k1_xboole_0) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_669])).

tff(c_875,plain,(
    ! [A_266,B_267] :
      ( r4_lattice3(A_266,k15_lattice3(A_266,B_267),B_267)
      | ~ m1_subset_1(k15_lattice3(A_266,B_267),u1_struct_0(A_266))
      | ~ v4_lattice3(A_266)
      | ~ v10_lattices(A_266)
      | ~ l3_lattices(A_266)
      | v2_struct_0(A_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_882,plain,(
    ! [A_89,B_90] :
      ( r4_lattice3(A_89,k15_lattice3(A_89,B_90),B_90)
      | ~ v4_lattice3(A_89)
      | ~ v10_lattices(A_89)
      | ~ l3_lattices(A_89)
      | v2_struct_0(A_89) ) ),
    inference(resolution,[status(thm)],[c_84,c_875])).

tff(c_106,plain,(
    ! [A_112,B_114] :
      ( k15_lattice3(A_112,a_2_5_lattice3(A_112,B_114)) = k15_lattice3(A_112,B_114)
      | ~ l3_lattices(A_112)
      | ~ v4_lattice3(A_112)
      | ~ v10_lattices(A_112)
      | v2_struct_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_1685,plain,(
    ! [A_404,B_405,D_406] :
      ( r1_lattices(A_404,k15_lattice3(A_404,B_405),D_406)
      | ~ r4_lattice3(A_404,D_406,B_405)
      | ~ m1_subset_1(D_406,u1_struct_0(A_404))
      | ~ m1_subset_1(k15_lattice3(A_404,B_405),u1_struct_0(A_404))
      | ~ v4_lattice3(A_404)
      | ~ v10_lattices(A_404)
      | ~ l3_lattices(A_404)
      | v2_struct_0(A_404) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_1728,plain,(
    ! [A_409,B_410,D_411] :
      ( r1_lattices(A_409,k15_lattice3(A_409,B_410),D_411)
      | ~ r4_lattice3(A_409,D_411,B_410)
      | ~ m1_subset_1(D_411,u1_struct_0(A_409))
      | ~ v4_lattice3(A_409)
      | ~ v10_lattices(A_409)
      | ~ l3_lattices(A_409)
      | v2_struct_0(A_409) ) ),
    inference(resolution,[status(thm)],[c_84,c_1685])).

tff(c_5117,plain,(
    ! [A_838,B_839,D_840] :
      ( r1_lattices(A_838,k15_lattice3(A_838,B_839),D_840)
      | ~ r4_lattice3(A_838,D_840,a_2_5_lattice3(A_838,B_839))
      | ~ m1_subset_1(D_840,u1_struct_0(A_838))
      | ~ v4_lattice3(A_838)
      | ~ v10_lattices(A_838)
      | ~ l3_lattices(A_838)
      | v2_struct_0(A_838)
      | ~ l3_lattices(A_838)
      | ~ v4_lattice3(A_838)
      | ~ v10_lattices(A_838)
      | v2_struct_0(A_838) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_1728])).

tff(c_5310,plain,(
    ! [A_856,B_857] :
      ( r1_lattices(A_856,k15_lattice3(A_856,B_857),k15_lattice3(A_856,a_2_5_lattice3(A_856,B_857)))
      | ~ m1_subset_1(k15_lattice3(A_856,a_2_5_lattice3(A_856,B_857)),u1_struct_0(A_856))
      | ~ v4_lattice3(A_856)
      | ~ v10_lattices(A_856)
      | ~ l3_lattices(A_856)
      | v2_struct_0(A_856) ) ),
    inference(resolution,[status(thm)],[c_882,c_5117])).

tff(c_5330,plain,
    ( r1_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),k15_lattice3('#skF_12',k1_xboole_0))
    | ~ m1_subset_1(k15_lattice3('#skF_12',a_2_5_lattice3('#skF_12',k1_xboole_0)),u1_struct_0('#skF_12'))
    | ~ v4_lattice3('#skF_12')
    | ~ v10_lattices('#skF_12')
    | ~ l3_lattices('#skF_12')
    | v2_struct_0('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_670,c_5310])).

tff(c_5342,plain,
    ( r1_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),k15_lattice3('#skF_12',k1_xboole_0))
    | ~ m1_subset_1(k15_lattice3('#skF_12',k1_xboole_0),u1_struct_0('#skF_12'))
    | v2_struct_0('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_116,c_114,c_670,c_5330])).

tff(c_5343,plain,
    ( r1_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),k15_lattice3('#skF_12',k1_xboole_0))
    | ~ m1_subset_1(k15_lattice3('#skF_12',k1_xboole_0),u1_struct_0('#skF_12')) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_5342])).

tff(c_5344,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_12',k1_xboole_0),u1_struct_0('#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_5343])).

tff(c_5358,plain,
    ( ~ l3_lattices('#skF_12')
    | v2_struct_0('#skF_12') ),
    inference(resolution,[status(thm)],[c_84,c_5344])).

tff(c_5361,plain,(
    v2_struct_0('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_5358])).

tff(c_5363,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_5361])).

tff(c_5365,plain,(
    m1_subset_1(k15_lattice3('#skF_12',k1_xboole_0),u1_struct_0('#skF_12')) ),
    inference(splitRight,[status(thm)],[c_5343])).

tff(c_110,plain,
    ( k15_lattice3('#skF_12',k1_xboole_0) != k5_lattices('#skF_12')
    | ~ l3_lattices('#skF_12')
    | ~ v13_lattices('#skF_12')
    | ~ v10_lattices('#skF_12')
    | v2_struct_0('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_300])).

tff(c_120,plain,
    ( k15_lattice3('#skF_12',k1_xboole_0) != k5_lattices('#skF_12')
    | ~ v13_lattices('#skF_12')
    | v2_struct_0('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_112,c_110])).

tff(c_121,plain,
    ( k15_lattice3('#skF_12',k1_xboole_0) != k5_lattices('#skF_12')
    | ~ v13_lattices('#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_120])).

tff(c_133,plain,(
    ~ v13_lattices('#skF_12') ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_50,plain,(
    ! [A_33,B_42] :
      ( m1_subset_1('#skF_5'(A_33,B_42),u1_struct_0(A_33))
      | v13_lattices(A_33)
      | ~ m1_subset_1(B_42,u1_struct_0(A_33))
      | ~ l1_lattices(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_18,plain,(
    ! [A_13] :
      ( v8_lattices(A_13)
      | ~ v10_lattices(A_13)
      | v2_struct_0(A_13)
      | ~ l3_lattices(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_5364,plain,(
    r1_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),k15_lattice3('#skF_12',k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_5343])).

tff(c_46,plain,(
    ! [A_26,B_30,C_32] :
      ( k2_lattices(A_26,B_30,C_32) = B_30
      | ~ r1_lattices(A_26,B_30,C_32)
      | ~ m1_subset_1(C_32,u1_struct_0(A_26))
      | ~ m1_subset_1(B_30,u1_struct_0(A_26))
      | ~ l3_lattices(A_26)
      | ~ v9_lattices(A_26)
      | ~ v8_lattices(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_5464,plain,
    ( k2_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),k15_lattice3('#skF_12',k1_xboole_0)) = k15_lattice3('#skF_12',k1_xboole_0)
    | ~ m1_subset_1(k15_lattice3('#skF_12',k1_xboole_0),u1_struct_0('#skF_12'))
    | ~ l3_lattices('#skF_12')
    | ~ v9_lattices('#skF_12')
    | ~ v8_lattices('#skF_12')
    | v2_struct_0('#skF_12') ),
    inference(resolution,[status(thm)],[c_5364,c_46])).

tff(c_5467,plain,
    ( k2_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),k15_lattice3('#skF_12',k1_xboole_0)) = k15_lattice3('#skF_12',k1_xboole_0)
    | ~ v9_lattices('#skF_12')
    | ~ v8_lattices('#skF_12')
    | v2_struct_0('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_5365,c_5464])).

tff(c_5468,plain,
    ( k2_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),k15_lattice3('#skF_12',k1_xboole_0)) = k15_lattice3('#skF_12',k1_xboole_0)
    | ~ v9_lattices('#skF_12')
    | ~ v8_lattices('#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_5467])).

tff(c_5516,plain,(
    ~ v8_lattices('#skF_12') ),
    inference(splitLeft,[status(thm)],[c_5468])).

tff(c_5519,plain,
    ( ~ v10_lattices('#skF_12')
    | v2_struct_0('#skF_12')
    | ~ l3_lattices('#skF_12') ),
    inference(resolution,[status(thm)],[c_18,c_5516])).

tff(c_5522,plain,(
    v2_struct_0('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_116,c_5519])).

tff(c_5524,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_5522])).

tff(c_5526,plain,(
    v8_lattices('#skF_12') ),
    inference(splitRight,[status(thm)],[c_5468])).

tff(c_16,plain,(
    ! [A_13] :
      ( v9_lattices(A_13)
      | ~ v10_lattices(A_13)
      | v2_struct_0(A_13)
      | ~ l3_lattices(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_5525,plain,
    ( ~ v9_lattices('#skF_12')
    | k2_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),k15_lattice3('#skF_12',k1_xboole_0)) = k15_lattice3('#skF_12',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_5468])).

tff(c_5527,plain,(
    ~ v9_lattices('#skF_12') ),
    inference(splitLeft,[status(thm)],[c_5525])).

tff(c_5530,plain,
    ( ~ v10_lattices('#skF_12')
    | v2_struct_0('#skF_12')
    | ~ l3_lattices('#skF_12') ),
    inference(resolution,[status(thm)],[c_16,c_5527])).

tff(c_5533,plain,(
    v2_struct_0('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_116,c_5530])).

tff(c_5535,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_5533])).

tff(c_5537,plain,(
    v9_lattices('#skF_12') ),
    inference(splitRight,[status(thm)],[c_5525])).

tff(c_145,plain,(
    ! [A_125,B_126,B_2] :
      ( ~ r1_xboole_0(A_125,B_126)
      | r1_tarski(k3_xboole_0(A_125,B_126),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_140])).

tff(c_5536,plain,(
    k2_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),k15_lattice3('#skF_12',k1_xboole_0)) = k15_lattice3('#skF_12',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_5525])).

tff(c_734,plain,(
    ! [A_238,B_239,A_240,B_241] :
      ( ~ r1_xboole_0(A_238,B_239)
      | ~ r2_hidden(A_240,a_2_5_lattice3(B_241,k3_xboole_0(A_238,B_239)))
      | ~ l3_lattices(B_241)
      | ~ v4_lattice3(B_241)
      | ~ v10_lattices(B_241)
      | v2_struct_0(B_241) ) ),
    inference(resolution,[status(thm)],[c_598,c_10])).

tff(c_765,plain,(
    ! [A_242,B_243,B_244,B_245] :
      ( ~ r1_xboole_0(A_242,B_243)
      | ~ l3_lattices(B_244)
      | ~ v4_lattice3(B_244)
      | ~ v10_lattices(B_244)
      | v2_struct_0(B_244)
      | r1_tarski(a_2_5_lattice3(B_244,k3_xboole_0(A_242,B_243)),B_245) ) ),
    inference(resolution,[status(thm)],[c_6,c_734])).

tff(c_794,plain,(
    ! [B_246,A_247,B_248] :
      ( a_2_5_lattice3(B_246,k3_xboole_0(A_247,B_248)) = k1_xboole_0
      | ~ r1_xboole_0(A_247,B_248)
      | ~ l3_lattices(B_246)
      | ~ v4_lattice3(B_246)
      | ~ v10_lattices(B_246)
      | v2_struct_0(B_246) ) ),
    inference(resolution,[status(thm)],[c_765,c_12])).

tff(c_809,plain,(
    ! [B_246,A_247,B_248] :
      ( k15_lattice3(B_246,k3_xboole_0(A_247,B_248)) = k15_lattice3(B_246,k1_xboole_0)
      | ~ l3_lattices(B_246)
      | ~ v4_lattice3(B_246)
      | ~ v10_lattices(B_246)
      | v2_struct_0(B_246)
      | ~ r1_xboole_0(A_247,B_248)
      | ~ l3_lattices(B_246)
      | ~ v4_lattice3(B_246)
      | ~ v10_lattices(B_246)
      | v2_struct_0(B_246) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_794,c_106])).

tff(c_177,plain,(
    ! [A_138,B_2] :
      ( ~ r1_xboole_0(A_138,k1_xboole_0)
      | r1_tarski(k1_xboole_0,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_145])).

tff(c_185,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_177])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1394,plain,(
    ! [A_359,B_360,C_361,B_362] :
      ( r2_hidden('#skF_11'(A_359,B_360,C_361),B_362)
      | ~ r1_tarski(C_361,B_362)
      | ~ r2_hidden(A_359,a_2_5_lattice3(B_360,C_361))
      | ~ l3_lattices(B_360)
      | ~ v4_lattice3(B_360)
      | ~ v10_lattices(B_360)
      | v2_struct_0(B_360) ) ),
    inference(resolution,[status(thm)],[c_598,c_2])).

tff(c_1426,plain,(
    ! [C_363,A_364,B_365] :
      ( ~ r1_tarski(C_363,k1_xboole_0)
      | ~ r2_hidden(A_364,a_2_5_lattice3(B_365,C_363))
      | ~ l3_lattices(B_365)
      | ~ v4_lattice3(B_365)
      | ~ v10_lattices(B_365)
      | v2_struct_0(B_365) ) ),
    inference(resolution,[status(thm)],[c_1394,c_187])).

tff(c_1470,plain,(
    ! [C_363,B_365,B_2] :
      ( ~ r1_tarski(C_363,k1_xboole_0)
      | ~ l3_lattices(B_365)
      | ~ v4_lattice3(B_365)
      | ~ v10_lattices(B_365)
      | v2_struct_0(B_365)
      | r1_tarski(a_2_5_lattice3(B_365,C_363),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_1426])).

tff(c_1472,plain,(
    ! [C_369,B_370,B_371] :
      ( ~ r1_tarski(C_369,k1_xboole_0)
      | ~ l3_lattices(B_370)
      | ~ v4_lattice3(B_370)
      | ~ v10_lattices(B_370)
      | v2_struct_0(B_370)
      | r1_tarski(a_2_5_lattice3(B_370,C_369),B_371) ) ),
    inference(resolution,[status(thm)],[c_6,c_1426])).

tff(c_1514,plain,(
    ! [B_372,C_373] :
      ( a_2_5_lattice3(B_372,C_373) = k1_xboole_0
      | ~ r1_tarski(C_373,k1_xboole_0)
      | ~ l3_lattices(B_372)
      | ~ v4_lattice3(B_372)
      | ~ v10_lattices(B_372)
      | v2_struct_0(B_372) ) ),
    inference(resolution,[status(thm)],[c_1472,c_12])).

tff(c_1533,plain,(
    ! [B_372,B_365,C_363] :
      ( a_2_5_lattice3(B_372,a_2_5_lattice3(B_365,C_363)) = k1_xboole_0
      | ~ l3_lattices(B_372)
      | ~ v4_lattice3(B_372)
      | ~ v10_lattices(B_372)
      | v2_struct_0(B_372)
      | ~ r1_tarski(C_363,k1_xboole_0)
      | ~ l3_lattices(B_365)
      | ~ v4_lattice3(B_365)
      | ~ v10_lattices(B_365)
      | v2_struct_0(B_365) ) ),
    inference(resolution,[status(thm)],[c_1470,c_1514])).

tff(c_478,plain,(
    ! [A_197,B_198,C_199] :
      ( r2_hidden('#skF_6'(A_197,B_198,C_199),C_199)
      | r4_lattice3(A_197,B_198,C_199)
      | ~ m1_subset_1(B_198,u1_struct_0(A_197))
      | ~ l3_lattices(A_197)
      | v2_struct_0(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1204,plain,(
    ! [A_317,B_318,C_319,B_320] :
      ( r2_hidden('#skF_6'(A_317,B_318,C_319),B_320)
      | ~ r1_tarski(C_319,B_320)
      | r4_lattice3(A_317,B_318,C_319)
      | ~ m1_subset_1(B_318,u1_struct_0(A_317))
      | ~ l3_lattices(A_317)
      | v2_struct_0(A_317) ) ),
    inference(resolution,[status(thm)],[c_478,c_2])).

tff(c_1234,plain,(
    ! [C_319,A_317,B_318] :
      ( ~ r1_tarski(C_319,k1_xboole_0)
      | r4_lattice3(A_317,B_318,C_319)
      | ~ m1_subset_1(B_318,u1_struct_0(A_317))
      | ~ l3_lattices(A_317)
      | v2_struct_0(A_317) ) ),
    inference(resolution,[status(thm)],[c_1204,c_187])).

tff(c_5383,plain,(
    ! [C_319] :
      ( ~ r1_tarski(C_319,k1_xboole_0)
      | r4_lattice3('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),C_319)
      | ~ l3_lattices('#skF_12')
      | v2_struct_0('#skF_12') ) ),
    inference(resolution,[status(thm)],[c_5365,c_1234])).

tff(c_5433,plain,(
    ! [C_319] :
      ( ~ r1_tarski(C_319,k1_xboole_0)
      | r4_lattice3('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),C_319)
      | v2_struct_0('#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_5383])).

tff(c_5479,plain,(
    ! [C_861] :
      ( ~ r1_tarski(C_861,k1_xboole_0)
      | r4_lattice3('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),C_861) ) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_5433])).

tff(c_1740,plain,(
    ! [A_112,B_114,D_411] :
      ( r1_lattices(A_112,k15_lattice3(A_112,B_114),D_411)
      | ~ r4_lattice3(A_112,D_411,a_2_5_lattice3(A_112,B_114))
      | ~ m1_subset_1(D_411,u1_struct_0(A_112))
      | ~ v4_lattice3(A_112)
      | ~ v10_lattices(A_112)
      | ~ l3_lattices(A_112)
      | v2_struct_0(A_112)
      | ~ l3_lattices(A_112)
      | ~ v4_lattice3(A_112)
      | ~ v10_lattices(A_112)
      | v2_struct_0(A_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_1728])).

tff(c_5483,plain,(
    ! [B_114] :
      ( r1_lattices('#skF_12',k15_lattice3('#skF_12',B_114),k15_lattice3('#skF_12',k1_xboole_0))
      | ~ m1_subset_1(k15_lattice3('#skF_12',k1_xboole_0),u1_struct_0('#skF_12'))
      | ~ l3_lattices('#skF_12')
      | ~ v4_lattice3('#skF_12')
      | ~ v10_lattices('#skF_12')
      | v2_struct_0('#skF_12')
      | ~ r1_tarski(a_2_5_lattice3('#skF_12',B_114),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_5479,c_1740])).

tff(c_5486,plain,(
    ! [B_114] :
      ( r1_lattices('#skF_12',k15_lattice3('#skF_12',B_114),k15_lattice3('#skF_12',k1_xboole_0))
      | v2_struct_0('#skF_12')
      | ~ r1_tarski(a_2_5_lattice3('#skF_12',B_114),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_114,c_112,c_5365,c_5483])).

tff(c_5488,plain,(
    ! [B_862] :
      ( r1_lattices('#skF_12',k15_lattice3('#skF_12',B_862),k15_lattice3('#skF_12',k1_xboole_0))
      | ~ r1_tarski(a_2_5_lattice3('#skF_12',B_862),k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_5486])).

tff(c_5502,plain,(
    ! [B_114] :
      ( r1_lattices('#skF_12',k15_lattice3('#skF_12',B_114),k15_lattice3('#skF_12',k1_xboole_0))
      | ~ r1_tarski(a_2_5_lattice3('#skF_12',a_2_5_lattice3('#skF_12',B_114)),k1_xboole_0)
      | ~ l3_lattices('#skF_12')
      | ~ v4_lattice3('#skF_12')
      | ~ v10_lattices('#skF_12')
      | v2_struct_0('#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_5488])).

tff(c_5514,plain,(
    ! [B_114] :
      ( r1_lattices('#skF_12',k15_lattice3('#skF_12',B_114),k15_lattice3('#skF_12',k1_xboole_0))
      | ~ r1_tarski(a_2_5_lattice3('#skF_12',a_2_5_lattice3('#skF_12',B_114)),k1_xboole_0)
      | v2_struct_0('#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_114,c_112,c_5502])).

tff(c_5552,plain,(
    ! [B_866] :
      ( r1_lattices('#skF_12',k15_lattice3('#skF_12',B_866),k15_lattice3('#skF_12',k1_xboole_0))
      | ~ r1_tarski(a_2_5_lattice3('#skF_12',a_2_5_lattice3('#skF_12',B_866)),k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_5514])).

tff(c_5566,plain,(
    ! [B_114] :
      ( r1_lattices('#skF_12',k15_lattice3('#skF_12',B_114),k15_lattice3('#skF_12',k1_xboole_0))
      | ~ r1_tarski(a_2_5_lattice3('#skF_12',a_2_5_lattice3('#skF_12',a_2_5_lattice3('#skF_12',B_114))),k1_xboole_0)
      | ~ l3_lattices('#skF_12')
      | ~ v4_lattice3('#skF_12')
      | ~ v10_lattices('#skF_12')
      | v2_struct_0('#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_5552])).

tff(c_5578,plain,(
    ! [B_114] :
      ( r1_lattices('#skF_12',k15_lattice3('#skF_12',B_114),k15_lattice3('#skF_12',k1_xboole_0))
      | ~ r1_tarski(a_2_5_lattice3('#skF_12',a_2_5_lattice3('#skF_12',a_2_5_lattice3('#skF_12',B_114))),k1_xboole_0)
      | v2_struct_0('#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_114,c_112,c_5566])).

tff(c_5703,plain,(
    ! [B_868] :
      ( r1_lattices('#skF_12',k15_lattice3('#skF_12',B_868),k15_lattice3('#skF_12',k1_xboole_0))
      | ~ r1_tarski(a_2_5_lattice3('#skF_12',a_2_5_lattice3('#skF_12',a_2_5_lattice3('#skF_12',B_868))),k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_5578])).

tff(c_5725,plain,(
    ! [C_363] :
      ( r1_lattices('#skF_12',k15_lattice3('#skF_12',C_363),k15_lattice3('#skF_12',k1_xboole_0))
      | ~ r1_tarski(a_2_5_lattice3('#skF_12',k1_xboole_0),k1_xboole_0)
      | ~ l3_lattices('#skF_12')
      | ~ v4_lattice3('#skF_12')
      | ~ v10_lattices('#skF_12')
      | v2_struct_0('#skF_12')
      | ~ r1_tarski(C_363,k1_xboole_0)
      | ~ l3_lattices('#skF_12')
      | ~ v4_lattice3('#skF_12')
      | ~ v10_lattices('#skF_12')
      | v2_struct_0('#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1533,c_5703])).

tff(c_5765,plain,(
    ! [C_363] :
      ( r1_lattices('#skF_12',k15_lattice3('#skF_12',C_363),k15_lattice3('#skF_12',k1_xboole_0))
      | ~ r1_tarski(C_363,k1_xboole_0)
      | v2_struct_0('#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_114,c_112,c_116,c_114,c_112,c_185,c_670,c_5725])).

tff(c_5785,plain,(
    ! [C_869] :
      ( r1_lattices('#skF_12',k15_lattice3('#skF_12',C_869),k15_lattice3('#skF_12',k1_xboole_0))
      | ~ r1_tarski(C_869,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_5765])).

tff(c_5787,plain,(
    ! [C_869] :
      ( k2_lattices('#skF_12',k15_lattice3('#skF_12',C_869),k15_lattice3('#skF_12',k1_xboole_0)) = k15_lattice3('#skF_12',C_869)
      | ~ m1_subset_1(k15_lattice3('#skF_12',k1_xboole_0),u1_struct_0('#skF_12'))
      | ~ m1_subset_1(k15_lattice3('#skF_12',C_869),u1_struct_0('#skF_12'))
      | ~ l3_lattices('#skF_12')
      | ~ v9_lattices('#skF_12')
      | ~ v8_lattices('#skF_12')
      | v2_struct_0('#skF_12')
      | ~ r1_tarski(C_869,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_5785,c_46])).

tff(c_5802,plain,(
    ! [C_869] :
      ( k2_lattices('#skF_12',k15_lattice3('#skF_12',C_869),k15_lattice3('#skF_12',k1_xboole_0)) = k15_lattice3('#skF_12',C_869)
      | ~ m1_subset_1(k15_lattice3('#skF_12',C_869),u1_struct_0('#skF_12'))
      | v2_struct_0('#skF_12')
      | ~ r1_tarski(C_869,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5526,c_5537,c_112,c_5365,c_5787])).

tff(c_6282,plain,(
    ! [C_890] :
      ( k2_lattices('#skF_12',k15_lattice3('#skF_12',C_890),k15_lattice3('#skF_12',k1_xboole_0)) = k15_lattice3('#skF_12',C_890)
      | ~ m1_subset_1(k15_lattice3('#skF_12',C_890),u1_struct_0('#skF_12'))
      | ~ r1_tarski(C_890,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_5802])).

tff(c_6301,plain,(
    ! [B_90] :
      ( k2_lattices('#skF_12',k15_lattice3('#skF_12',B_90),k15_lattice3('#skF_12',k1_xboole_0)) = k15_lattice3('#skF_12',B_90)
      | ~ r1_tarski(B_90,k1_xboole_0)
      | ~ l3_lattices('#skF_12')
      | v2_struct_0('#skF_12') ) ),
    inference(resolution,[status(thm)],[c_84,c_6282])).

tff(c_6316,plain,(
    ! [B_90] :
      ( k2_lattices('#skF_12',k15_lattice3('#skF_12',B_90),k15_lattice3('#skF_12',k1_xboole_0)) = k15_lattice3('#skF_12',B_90)
      | ~ r1_tarski(B_90,k1_xboole_0)
      | v2_struct_0('#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_6301])).

tff(c_6318,plain,(
    ! [B_891] :
      ( k2_lattices('#skF_12',k15_lattice3('#skF_12',B_891),k15_lattice3('#skF_12',k1_xboole_0)) = k15_lattice3('#skF_12',B_891)
      | ~ r1_tarski(B_891,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_6316])).

tff(c_6346,plain,(
    ! [A_247,B_248] :
      ( k2_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),k15_lattice3('#skF_12',k1_xboole_0)) = k15_lattice3('#skF_12',k3_xboole_0(A_247,B_248))
      | ~ r1_tarski(k3_xboole_0(A_247,B_248),k1_xboole_0)
      | ~ l3_lattices('#skF_12')
      | ~ v4_lattice3('#skF_12')
      | ~ v10_lattices('#skF_12')
      | v2_struct_0('#skF_12')
      | ~ r1_xboole_0(A_247,B_248)
      | ~ l3_lattices('#skF_12')
      | ~ v4_lattice3('#skF_12')
      | ~ v10_lattices('#skF_12')
      | v2_struct_0('#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_809,c_6318])).

tff(c_6378,plain,(
    ! [A_247,B_248] :
      ( k15_lattice3('#skF_12',k3_xboole_0(A_247,B_248)) = k15_lattice3('#skF_12',k1_xboole_0)
      | ~ r1_tarski(k3_xboole_0(A_247,B_248),k1_xboole_0)
      | ~ r1_xboole_0(A_247,B_248)
      | v2_struct_0('#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_114,c_112,c_116,c_114,c_112,c_5536,c_6346])).

tff(c_6532,plain,(
    ! [A_897,B_898] :
      ( k15_lattice3('#skF_12',k3_xboole_0(A_897,B_898)) = k15_lattice3('#skF_12',k1_xboole_0)
      | ~ r1_tarski(k3_xboole_0(A_897,B_898),k1_xboole_0)
      | ~ r1_xboole_0(A_897,B_898) ) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_6378])).

tff(c_6543,plain,(
    ! [A_899,B_900] :
      ( k15_lattice3('#skF_12',k3_xboole_0(A_899,B_900)) = k15_lattice3('#skF_12',k1_xboole_0)
      | ~ r1_xboole_0(A_899,B_900) ) ),
    inference(resolution,[status(thm)],[c_145,c_6532])).

tff(c_764,plain,(
    ! [A_238,B_239,B_241,B_2] :
      ( ~ r1_xboole_0(A_238,B_239)
      | ~ l3_lattices(B_241)
      | ~ v4_lattice3(B_241)
      | ~ v10_lattices(B_241)
      | v2_struct_0(B_241)
      | r1_tarski(a_2_5_lattice3(B_241,k3_xboole_0(A_238,B_239)),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_734])).

tff(c_1310,plain,(
    ! [C_342,B_341,A_344,B_343,A_345] :
      ( ~ r1_xboole_0(A_344,B_343)
      | ~ r1_tarski(C_342,k3_xboole_0(A_344,B_343))
      | r4_lattice3(A_345,B_341,C_342)
      | ~ m1_subset_1(B_341,u1_struct_0(A_345))
      | ~ l3_lattices(A_345)
      | v2_struct_0(A_345) ) ),
    inference(resolution,[status(thm)],[c_1204,c_10])).

tff(c_1328,plain,(
    ! [B_341,B_239,A_344,B_343,A_345,B_241,A_238] :
      ( ~ r1_xboole_0(A_344,B_343)
      | r4_lattice3(A_345,B_341,a_2_5_lattice3(B_241,k3_xboole_0(A_238,B_239)))
      | ~ m1_subset_1(B_341,u1_struct_0(A_345))
      | ~ l3_lattices(A_345)
      | v2_struct_0(A_345)
      | ~ r1_xboole_0(A_238,B_239)
      | ~ l3_lattices(B_241)
      | ~ v4_lattice3(B_241)
      | ~ v10_lattices(B_241)
      | v2_struct_0(B_241) ) ),
    inference(resolution,[status(thm)],[c_764,c_1310])).

tff(c_4167,plain,(
    ! [A_344,B_343] : ~ r1_xboole_0(A_344,B_343) ),
    inference(splitLeft,[status(thm)],[c_1328])).

tff(c_4181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4167,c_14])).

tff(c_4182,plain,(
    ! [B_341,B_239,A_345,B_241,A_238] :
      ( r4_lattice3(A_345,B_341,a_2_5_lattice3(B_241,k3_xboole_0(A_238,B_239)))
      | ~ m1_subset_1(B_341,u1_struct_0(A_345))
      | ~ l3_lattices(A_345)
      | v2_struct_0(A_345)
      | ~ r1_xboole_0(A_238,B_239)
      | ~ l3_lattices(B_241)
      | ~ v4_lattice3(B_241)
      | ~ v10_lattices(B_241)
      | v2_struct_0(B_241) ) ),
    inference(splitRight,[status(thm)],[c_1328])).

tff(c_5201,plain,(
    ! [B_241,A_238,B_239,B_341] :
      ( r1_lattices(B_241,k15_lattice3(B_241,k3_xboole_0(A_238,B_239)),B_341)
      | ~ m1_subset_1(B_341,u1_struct_0(B_241))
      | ~ r1_xboole_0(A_238,B_239)
      | ~ l3_lattices(B_241)
      | ~ v4_lattice3(B_241)
      | ~ v10_lattices(B_241)
      | v2_struct_0(B_241) ) ),
    inference(resolution,[status(thm)],[c_4182,c_5117])).

tff(c_6576,plain,(
    ! [B_341,A_899,B_900] :
      ( r1_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),B_341)
      | ~ m1_subset_1(B_341,u1_struct_0('#skF_12'))
      | ~ r1_xboole_0(A_899,B_900)
      | ~ l3_lattices('#skF_12')
      | ~ v4_lattice3('#skF_12')
      | ~ v10_lattices('#skF_12')
      | v2_struct_0('#skF_12')
      | ~ r1_xboole_0(A_899,B_900) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6543,c_5201])).

tff(c_6696,plain,(
    ! [B_341,A_899,B_900] :
      ( r1_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),B_341)
      | ~ m1_subset_1(B_341,u1_struct_0('#skF_12'))
      | v2_struct_0('#skF_12')
      | ~ r1_xboole_0(A_899,B_900) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_114,c_112,c_6576])).

tff(c_6697,plain,(
    ! [B_341,A_899,B_900] :
      ( r1_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),B_341)
      | ~ m1_subset_1(B_341,u1_struct_0('#skF_12'))
      | ~ r1_xboole_0(A_899,B_900) ) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_6696])).

tff(c_6846,plain,(
    ! [A_899,B_900] : ~ r1_xboole_0(A_899,B_900) ),
    inference(splitLeft,[status(thm)],[c_6697])).

tff(c_6864,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6846,c_14])).

tff(c_6866,plain,(
    ! [B_908] :
      ( r1_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),B_908)
      | ~ m1_subset_1(B_908,u1_struct_0('#skF_12')) ) ),
    inference(splitRight,[status(thm)],[c_6697])).

tff(c_6872,plain,(
    ! [B_908] :
      ( k2_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),B_908) = k15_lattice3('#skF_12',k1_xboole_0)
      | ~ m1_subset_1(k15_lattice3('#skF_12',k1_xboole_0),u1_struct_0('#skF_12'))
      | ~ l3_lattices('#skF_12')
      | ~ v9_lattices('#skF_12')
      | ~ v8_lattices('#skF_12')
      | v2_struct_0('#skF_12')
      | ~ m1_subset_1(B_908,u1_struct_0('#skF_12')) ) ),
    inference(resolution,[status(thm)],[c_6866,c_46])).

tff(c_6879,plain,(
    ! [B_908] :
      ( k2_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),B_908) = k15_lattice3('#skF_12',k1_xboole_0)
      | v2_struct_0('#skF_12')
      | ~ m1_subset_1(B_908,u1_struct_0('#skF_12')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5526,c_5537,c_112,c_5365,c_6872])).

tff(c_6901,plain,(
    ! [B_911] :
      ( k2_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),B_911) = k15_lattice3('#skF_12',k1_xboole_0)
      | ~ m1_subset_1(B_911,u1_struct_0('#skF_12')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_6879])).

tff(c_6928,plain,(
    ! [B_42] :
      ( k2_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),'#skF_5'('#skF_12',B_42)) = k15_lattice3('#skF_12',k1_xboole_0)
      | v13_lattices('#skF_12')
      | ~ m1_subset_1(B_42,u1_struct_0('#skF_12'))
      | ~ l1_lattices('#skF_12')
      | v2_struct_0('#skF_12') ) ),
    inference(resolution,[status(thm)],[c_50,c_6901])).

tff(c_6973,plain,(
    ! [B_42] :
      ( k2_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),'#skF_5'('#skF_12',B_42)) = k15_lattice3('#skF_12',k1_xboole_0)
      | v13_lattices('#skF_12')
      | ~ m1_subset_1(B_42,u1_struct_0('#skF_12'))
      | v2_struct_0('#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_6928])).

tff(c_7384,plain,(
    ! [B_920] :
      ( k2_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),'#skF_5'('#skF_12',B_920)) = k15_lattice3('#skF_12',k1_xboole_0)
      | ~ m1_subset_1(B_920,u1_struct_0('#skF_12')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_133,c_6973])).

tff(c_22,plain,(
    ! [A_13] :
      ( v6_lattices(A_13)
      | ~ v10_lattices(A_13)
      | v2_struct_0(A_13)
      | ~ l3_lattices(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_38,plain,(
    ! [A_24] :
      ( m1_subset_1(k5_lattices(A_24),u1_struct_0(A_24))
      | ~ l1_lattices(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1032,plain,(
    ! [A_286,C_287,B_288] :
      ( k2_lattices(A_286,C_287,B_288) = k2_lattices(A_286,B_288,C_287)
      | ~ m1_subset_1(C_287,u1_struct_0(A_286))
      | ~ m1_subset_1(B_288,u1_struct_0(A_286))
      | ~ v6_lattices(A_286)
      | ~ l1_lattices(A_286)
      | v2_struct_0(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_1062,plain,(
    ! [A_24,B_288] :
      ( k2_lattices(A_24,k5_lattices(A_24),B_288) = k2_lattices(A_24,B_288,k5_lattices(A_24))
      | ~ m1_subset_1(B_288,u1_struct_0(A_24))
      | ~ v6_lattices(A_24)
      | ~ l1_lattices(A_24)
      | v2_struct_0(A_24) ) ),
    inference(resolution,[status(thm)],[c_38,c_1032])).

tff(c_5385,plain,
    ( k2_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),k5_lattices('#skF_12')) = k2_lattices('#skF_12',k5_lattices('#skF_12'),k15_lattice3('#skF_12',k1_xboole_0))
    | ~ v6_lattices('#skF_12')
    | ~ l1_lattices('#skF_12')
    | v2_struct_0('#skF_12') ),
    inference(resolution,[status(thm)],[c_5365,c_1062])).

tff(c_5437,plain,
    ( k2_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),k5_lattices('#skF_12')) = k2_lattices('#skF_12',k5_lattices('#skF_12'),k15_lattice3('#skF_12',k1_xboole_0))
    | ~ v6_lattices('#skF_12')
    | v2_struct_0('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_5385])).

tff(c_5438,plain,
    ( k2_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),k5_lattices('#skF_12')) = k2_lattices('#skF_12',k5_lattices('#skF_12'),k15_lattice3('#skF_12',k1_xboole_0))
    | ~ v6_lattices('#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_5437])).

tff(c_5580,plain,(
    ~ v6_lattices('#skF_12') ),
    inference(splitLeft,[status(thm)],[c_5438])).

tff(c_5665,plain,
    ( ~ v10_lattices('#skF_12')
    | v2_struct_0('#skF_12')
    | ~ l3_lattices('#skF_12') ),
    inference(resolution,[status(thm)],[c_22,c_5580])).

tff(c_5668,plain,(
    v2_struct_0('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_116,c_5665])).

tff(c_5670,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_5668])).

tff(c_5672,plain,(
    v6_lattices('#skF_12') ),
    inference(splitRight,[status(thm)],[c_5438])).

tff(c_76,plain,(
    ! [A_78,C_87,B_85] :
      ( k2_lattices(A_78,C_87,B_85) = k2_lattices(A_78,B_85,C_87)
      | ~ m1_subset_1(C_87,u1_struct_0(A_78))
      | ~ m1_subset_1(B_85,u1_struct_0(A_78))
      | ~ v6_lattices(A_78)
      | ~ l1_lattices(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_5387,plain,(
    ! [B_85] :
      ( k2_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),B_85) = k2_lattices('#skF_12',B_85,k15_lattice3('#skF_12',k1_xboole_0))
      | ~ m1_subset_1(B_85,u1_struct_0('#skF_12'))
      | ~ v6_lattices('#skF_12')
      | ~ l1_lattices('#skF_12')
      | v2_struct_0('#skF_12') ) ),
    inference(resolution,[status(thm)],[c_5365,c_76])).

tff(c_5441,plain,(
    ! [B_85] :
      ( k2_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),B_85) = k2_lattices('#skF_12',B_85,k15_lattice3('#skF_12',k1_xboole_0))
      | ~ m1_subset_1(B_85,u1_struct_0('#skF_12'))
      | ~ v6_lattices('#skF_12')
      | v2_struct_0('#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_5387])).

tff(c_5442,plain,(
    ! [B_85] :
      ( k2_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),B_85) = k2_lattices('#skF_12',B_85,k15_lattice3('#skF_12',k1_xboole_0))
      | ~ m1_subset_1(B_85,u1_struct_0('#skF_12'))
      | ~ v6_lattices('#skF_12') ) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_5441])).

tff(c_5875,plain,(
    ! [B_877] :
      ( k2_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),B_877) = k2_lattices('#skF_12',B_877,k15_lattice3('#skF_12',k1_xboole_0))
      | ~ m1_subset_1(B_877,u1_struct_0('#skF_12')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5672,c_5442])).

tff(c_5902,plain,(
    ! [B_42] :
      ( k2_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),'#skF_5'('#skF_12',B_42)) = k2_lattices('#skF_12','#skF_5'('#skF_12',B_42),k15_lattice3('#skF_12',k1_xboole_0))
      | v13_lattices('#skF_12')
      | ~ m1_subset_1(B_42,u1_struct_0('#skF_12'))
      | ~ l1_lattices('#skF_12')
      | v2_struct_0('#skF_12') ) ),
    inference(resolution,[status(thm)],[c_50,c_5875])).

tff(c_5947,plain,(
    ! [B_42] :
      ( k2_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),'#skF_5'('#skF_12',B_42)) = k2_lattices('#skF_12','#skF_5'('#skF_12',B_42),k15_lattice3('#skF_12',k1_xboole_0))
      | v13_lattices('#skF_12')
      | ~ m1_subset_1(B_42,u1_struct_0('#skF_12'))
      | v2_struct_0('#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_5902])).

tff(c_6201,plain,(
    ! [B_888] :
      ( k2_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),'#skF_5'('#skF_12',B_888)) = k2_lattices('#skF_12','#skF_5'('#skF_12',B_888),k15_lattice3('#skF_12',k1_xboole_0))
      | ~ m1_subset_1(B_888,u1_struct_0('#skF_12')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_133,c_5947])).

tff(c_48,plain,(
    ! [A_33,B_42] :
      ( k2_lattices(A_33,'#skF_5'(A_33,B_42),B_42) != B_42
      | k2_lattices(A_33,B_42,'#skF_5'(A_33,B_42)) != B_42
      | v13_lattices(A_33)
      | ~ m1_subset_1(B_42,u1_struct_0(A_33))
      | ~ l1_lattices(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_6216,plain,
    ( k2_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),'#skF_5'('#skF_12',k15_lattice3('#skF_12',k1_xboole_0))) != k15_lattice3('#skF_12',k1_xboole_0)
    | k2_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),'#skF_5'('#skF_12',k15_lattice3('#skF_12',k1_xboole_0))) != k15_lattice3('#skF_12',k1_xboole_0)
    | v13_lattices('#skF_12')
    | ~ m1_subset_1(k15_lattice3('#skF_12',k1_xboole_0),u1_struct_0('#skF_12'))
    | ~ l1_lattices('#skF_12')
    | v2_struct_0('#skF_12')
    | ~ m1_subset_1(k15_lattice3('#skF_12',k1_xboole_0),u1_struct_0('#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6201,c_48])).

tff(c_6242,plain,
    ( k2_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),'#skF_5'('#skF_12',k15_lattice3('#skF_12',k1_xboole_0))) != k15_lattice3('#skF_12',k1_xboole_0)
    | v13_lattices('#skF_12')
    | v2_struct_0('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5365,c_127,c_5365,c_6216])).

tff(c_6243,plain,(
    k2_lattices('#skF_12',k15_lattice3('#skF_12',k1_xboole_0),'#skF_5'('#skF_12',k15_lattice3('#skF_12',k1_xboole_0))) != k15_lattice3('#skF_12',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_133,c_6242])).

tff(c_7390,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_12',k1_xboole_0),u1_struct_0('#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7384,c_6243])).

tff(c_7411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5365,c_7390])).

tff(c_7413,plain,(
    v13_lattices('#skF_12') ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_52,plain,(
    ! [A_33] :
      ( m1_subset_1('#skF_4'(A_33),u1_struct_0(A_33))
      | ~ v13_lattices(A_33)
      | ~ l1_lattices(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_8193,plain,(
    ! [A_1082,C_1083] :
      ( k2_lattices(A_1082,k5_lattices(A_1082),C_1083) = k5_lattices(A_1082)
      | ~ m1_subset_1(C_1083,u1_struct_0(A_1082))
      | ~ m1_subset_1(k5_lattices(A_1082),u1_struct_0(A_1082))
      | ~ v13_lattices(A_1082)
      | ~ l1_lattices(A_1082)
      | v2_struct_0(A_1082) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_8224,plain,(
    ! [A_1084] :
      ( k2_lattices(A_1084,k5_lattices(A_1084),'#skF_4'(A_1084)) = k5_lattices(A_1084)
      | ~ m1_subset_1(k5_lattices(A_1084),u1_struct_0(A_1084))
      | ~ v13_lattices(A_1084)
      | ~ l1_lattices(A_1084)
      | v2_struct_0(A_1084) ) ),
    inference(resolution,[status(thm)],[c_52,c_8193])).

tff(c_8228,plain,(
    ! [A_1085] :
      ( k2_lattices(A_1085,k5_lattices(A_1085),'#skF_4'(A_1085)) = k5_lattices(A_1085)
      | ~ v13_lattices(A_1085)
      | ~ l1_lattices(A_1085)
      | v2_struct_0(A_1085) ) ),
    inference(resolution,[status(thm)],[c_38,c_8224])).

tff(c_7700,plain,(
    ! [A_993,C_994] :
      ( k2_lattices(A_993,C_994,'#skF_4'(A_993)) = '#skF_4'(A_993)
      | ~ m1_subset_1(C_994,u1_struct_0(A_993))
      | ~ v13_lattices(A_993)
      | ~ l1_lattices(A_993)
      | v2_struct_0(A_993) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_7718,plain,(
    ! [A_24] :
      ( k2_lattices(A_24,k5_lattices(A_24),'#skF_4'(A_24)) = '#skF_4'(A_24)
      | ~ v13_lattices(A_24)
      | ~ l1_lattices(A_24)
      | v2_struct_0(A_24) ) ),
    inference(resolution,[status(thm)],[c_38,c_7700])).

tff(c_8234,plain,(
    ! [A_1085] :
      ( k5_lattices(A_1085) = '#skF_4'(A_1085)
      | ~ v13_lattices(A_1085)
      | ~ l1_lattices(A_1085)
      | v2_struct_0(A_1085)
      | ~ v13_lattices(A_1085)
      | ~ l1_lattices(A_1085)
      | v2_struct_0(A_1085) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8228,c_7718])).

tff(c_8287,plain,(
    ! [A_1089] :
      ( k5_lattices(A_1089) = '#skF_4'(A_1089)
      | ~ v13_lattices(A_1089)
      | ~ l1_lattices(A_1089)
      | v2_struct_0(A_1089) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_8234])).

tff(c_8290,plain,
    ( k5_lattices('#skF_12') = '#skF_4'('#skF_12')
    | ~ v13_lattices('#skF_12')
    | ~ l1_lattices('#skF_12') ),
    inference(resolution,[status(thm)],[c_8287,c_118])).

tff(c_8293,plain,(
    k5_lattices('#skF_12') = '#skF_4'('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_7413,c_8290])).

tff(c_7412,plain,(
    k15_lattice3('#skF_12',k1_xboole_0) != k5_lattices('#skF_12') ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_8294,plain,(
    k15_lattice3('#skF_12',k1_xboole_0) != '#skF_4'('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8293,c_7412])).

tff(c_7416,plain,(
    ! [A_924,B_925,C_926] :
      ( ~ r1_xboole_0(A_924,B_925)
      | ~ r2_hidden(C_926,k3_xboole_0(A_924,B_925)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_7441,plain,(
    ! [A_936,B_937,B_938] :
      ( ~ r1_xboole_0(A_936,B_937)
      | r1_tarski(k3_xboole_0(A_936,B_937),B_938) ) ),
    inference(resolution,[status(thm)],[c_6,c_7416])).

tff(c_7447,plain,(
    ! [A_939,B_940] :
      ( k3_xboole_0(A_939,B_940) = k1_xboole_0
      | ~ r1_xboole_0(A_939,B_940) ) ),
    inference(resolution,[status(thm)],[c_7441,c_12])).

tff(c_7456,plain,(
    ! [A_944] : k3_xboole_0(A_944,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_7447])).

tff(c_7421,plain,(
    ! [A_924,B_925,B_2] :
      ( ~ r1_xboole_0(A_924,B_925)
      | r1_tarski(k3_xboole_0(A_924,B_925),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_7416])).

tff(c_7461,plain,(
    ! [A_944,B_2] :
      ( ~ r1_xboole_0(A_944,k1_xboole_0)
      | r1_tarski(k1_xboole_0,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7456,c_7421])).

tff(c_7469,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_7461])).

tff(c_7903,plain,(
    ! [A_1036,B_1037,C_1038] :
      ( r2_hidden('#skF_11'(A_1036,B_1037,C_1038),C_1038)
      | ~ r2_hidden(A_1036,a_2_5_lattice3(B_1037,C_1038))
      | ~ l3_lattices(B_1037)
      | ~ v4_lattice3(B_1037)
      | ~ v10_lattices(B_1037)
      | v2_struct_0(B_1037) ) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_7464,plain,(
    ! [A_944,C_10] :
      ( ~ r1_xboole_0(A_944,k1_xboole_0)
      | ~ r2_hidden(C_10,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7456,c_10])).

tff(c_7471,plain,(
    ! [C_10] : ~ r2_hidden(C_10,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_7464])).

tff(c_7922,plain,(
    ! [A_1039,B_1040] :
      ( ~ r2_hidden(A_1039,a_2_5_lattice3(B_1040,k1_xboole_0))
      | ~ l3_lattices(B_1040)
      | ~ v4_lattice3(B_1040)
      | ~ v10_lattices(B_1040)
      | v2_struct_0(B_1040) ) ),
    inference(resolution,[status(thm)],[c_7903,c_7471])).

tff(c_7957,plain,(
    ! [B_1043,B_1044] :
      ( ~ l3_lattices(B_1043)
      | ~ v4_lattice3(B_1043)
      | ~ v10_lattices(B_1043)
      | v2_struct_0(B_1043)
      | r1_tarski(a_2_5_lattice3(B_1043,k1_xboole_0),B_1044) ) ),
    inference(resolution,[status(thm)],[c_6,c_7922])).

tff(c_7977,plain,(
    ! [B_1045] :
      ( a_2_5_lattice3(B_1045,k1_xboole_0) = k1_xboole_0
      | ~ l3_lattices(B_1045)
      | ~ v4_lattice3(B_1045)
      | ~ v10_lattices(B_1045)
      | v2_struct_0(B_1045) ) ),
    inference(resolution,[status(thm)],[c_7957,c_12])).

tff(c_7980,plain,
    ( a_2_5_lattice3('#skF_12',k1_xboole_0) = k1_xboole_0
    | ~ l3_lattices('#skF_12')
    | ~ v10_lattices('#skF_12')
    | v2_struct_0('#skF_12') ),
    inference(resolution,[status(thm)],[c_114,c_7977])).

tff(c_7983,plain,
    ( a_2_5_lattice3('#skF_12',k1_xboole_0) = k1_xboole_0
    | v2_struct_0('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_112,c_7980])).

tff(c_7984,plain,(
    a_2_5_lattice3('#skF_12',k1_xboole_0) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_7983])).

tff(c_8310,plain,
    ( m1_subset_1('#skF_4'('#skF_12'),u1_struct_0('#skF_12'))
    | ~ l1_lattices('#skF_12')
    | v2_struct_0('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_8293,c_38])).

tff(c_8326,plain,
    ( m1_subset_1('#skF_4'('#skF_12'),u1_struct_0('#skF_12'))
    | v2_struct_0('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_8310])).

tff(c_8327,plain,(
    m1_subset_1('#skF_4'('#skF_12'),u1_struct_0('#skF_12')) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_8326])).

tff(c_9155,plain,(
    ! [A_1150,B_1151,C_1152] :
      ( r1_lattices(A_1150,B_1151,C_1152)
      | k2_lattices(A_1150,B_1151,C_1152) != B_1151
      | ~ m1_subset_1(C_1152,u1_struct_0(A_1150))
      | ~ m1_subset_1(B_1151,u1_struct_0(A_1150))
      | ~ l3_lattices(A_1150)
      | ~ v9_lattices(A_1150)
      | ~ v8_lattices(A_1150)
      | v2_struct_0(A_1150) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_9157,plain,(
    ! [B_1151] :
      ( r1_lattices('#skF_12',B_1151,'#skF_4'('#skF_12'))
      | k2_lattices('#skF_12',B_1151,'#skF_4'('#skF_12')) != B_1151
      | ~ m1_subset_1(B_1151,u1_struct_0('#skF_12'))
      | ~ l3_lattices('#skF_12')
      | ~ v9_lattices('#skF_12')
      | ~ v8_lattices('#skF_12')
      | v2_struct_0('#skF_12') ) ),
    inference(resolution,[status(thm)],[c_8327,c_9155])).

tff(c_9180,plain,(
    ! [B_1151] :
      ( r1_lattices('#skF_12',B_1151,'#skF_4'('#skF_12'))
      | k2_lattices('#skF_12',B_1151,'#skF_4'('#skF_12')) != B_1151
      | ~ m1_subset_1(B_1151,u1_struct_0('#skF_12'))
      | ~ v9_lattices('#skF_12')
      | ~ v8_lattices('#skF_12')
      | v2_struct_0('#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_9157])).

tff(c_9181,plain,(
    ! [B_1151] :
      ( r1_lattices('#skF_12',B_1151,'#skF_4'('#skF_12'))
      | k2_lattices('#skF_12',B_1151,'#skF_4'('#skF_12')) != B_1151
      | ~ m1_subset_1(B_1151,u1_struct_0('#skF_12'))
      | ~ v9_lattices('#skF_12')
      | ~ v8_lattices('#skF_12') ) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_9180])).

tff(c_9201,plain,(
    ~ v8_lattices('#skF_12') ),
    inference(splitLeft,[status(thm)],[c_9181])).

tff(c_9204,plain,
    ( ~ v10_lattices('#skF_12')
    | v2_struct_0('#skF_12')
    | ~ l3_lattices('#skF_12') ),
    inference(resolution,[status(thm)],[c_18,c_9201])).

tff(c_9207,plain,(
    v2_struct_0('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_116,c_9204])).

tff(c_9209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_9207])).

tff(c_9211,plain,(
    v8_lattices('#skF_12') ),
    inference(splitRight,[status(thm)],[c_9181])).

tff(c_9210,plain,(
    ! [B_1151] :
      ( ~ v9_lattices('#skF_12')
      | r1_lattices('#skF_12',B_1151,'#skF_4'('#skF_12'))
      | k2_lattices('#skF_12',B_1151,'#skF_4'('#skF_12')) != B_1151
      | ~ m1_subset_1(B_1151,u1_struct_0('#skF_12')) ) ),
    inference(splitRight,[status(thm)],[c_9181])).

tff(c_9213,plain,(
    ~ v9_lattices('#skF_12') ),
    inference(splitLeft,[status(thm)],[c_9210])).

tff(c_9216,plain,
    ( ~ v10_lattices('#skF_12')
    | v2_struct_0('#skF_12')
    | ~ l3_lattices('#skF_12') ),
    inference(resolution,[status(thm)],[c_16,c_9213])).

tff(c_9219,plain,(
    v2_struct_0('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_116,c_9216])).

tff(c_9221,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_9219])).

tff(c_9223,plain,(
    v9_lattices('#skF_12') ),
    inference(splitRight,[status(thm)],[c_9210])).

tff(c_8360,plain,(
    ! [A_1090,C_1091,B_1092] :
      ( k2_lattices(A_1090,C_1091,B_1092) = k2_lattices(A_1090,B_1092,C_1091)
      | ~ m1_subset_1(C_1091,u1_struct_0(A_1090))
      | ~ m1_subset_1(B_1092,u1_struct_0(A_1090))
      | ~ v6_lattices(A_1090)
      | ~ l1_lattices(A_1090)
      | v2_struct_0(A_1090) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_8362,plain,(
    ! [B_1092] :
      ( k2_lattices('#skF_12',B_1092,'#skF_4'('#skF_12')) = k2_lattices('#skF_12','#skF_4'('#skF_12'),B_1092)
      | ~ m1_subset_1(B_1092,u1_struct_0('#skF_12'))
      | ~ v6_lattices('#skF_12')
      | ~ l1_lattices('#skF_12')
      | v2_struct_0('#skF_12') ) ),
    inference(resolution,[status(thm)],[c_8327,c_8360])).

tff(c_8385,plain,(
    ! [B_1092] :
      ( k2_lattices('#skF_12',B_1092,'#skF_4'('#skF_12')) = k2_lattices('#skF_12','#skF_4'('#skF_12'),B_1092)
      | ~ m1_subset_1(B_1092,u1_struct_0('#skF_12'))
      | ~ v6_lattices('#skF_12')
      | v2_struct_0('#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_8362])).

tff(c_8386,plain,(
    ! [B_1092] :
      ( k2_lattices('#skF_12',B_1092,'#skF_4'('#skF_12')) = k2_lattices('#skF_12','#skF_4'('#skF_12'),B_1092)
      | ~ m1_subset_1(B_1092,u1_struct_0('#skF_12'))
      | ~ v6_lattices('#skF_12') ) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_8385])).

tff(c_8423,plain,(
    ~ v6_lattices('#skF_12') ),
    inference(splitLeft,[status(thm)],[c_8386])).

tff(c_8426,plain,
    ( ~ v10_lattices('#skF_12')
    | v2_struct_0('#skF_12')
    | ~ l3_lattices('#skF_12') ),
    inference(resolution,[status(thm)],[c_22,c_8423])).

tff(c_8429,plain,(
    v2_struct_0('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_116,c_8426])).

tff(c_8431,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_8429])).

tff(c_8434,plain,(
    ! [B_1096] :
      ( k2_lattices('#skF_12',B_1096,'#skF_4'('#skF_12')) = k2_lattices('#skF_12','#skF_4'('#skF_12'),B_1096)
      | ~ m1_subset_1(B_1096,u1_struct_0('#skF_12')) ) ),
    inference(splitRight,[status(thm)],[c_8386])).

tff(c_8473,plain,(
    ! [B_90] :
      ( k2_lattices('#skF_12',k15_lattice3('#skF_12',B_90),'#skF_4'('#skF_12')) = k2_lattices('#skF_12','#skF_4'('#skF_12'),k15_lattice3('#skF_12',B_90))
      | ~ l3_lattices('#skF_12')
      | v2_struct_0('#skF_12') ) ),
    inference(resolution,[status(thm)],[c_84,c_8434])).

tff(c_8514,plain,(
    ! [B_90] :
      ( k2_lattices('#skF_12',k15_lattice3('#skF_12',B_90),'#skF_4'('#skF_12')) = k2_lattices('#skF_12','#skF_4'('#skF_12'),k15_lattice3('#skF_12',B_90))
      | v2_struct_0('#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_8473])).

tff(c_8520,plain,(
    ! [B_1097] : k2_lattices('#skF_12',k15_lattice3('#skF_12',B_1097),'#skF_4'('#skF_12')) = k2_lattices('#skF_12','#skF_4'('#skF_12'),k15_lattice3('#skF_12',B_1097)) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_8514])).

tff(c_7717,plain,(
    ! [A_89,B_90] :
      ( k2_lattices(A_89,k15_lattice3(A_89,B_90),'#skF_4'(A_89)) = '#skF_4'(A_89)
      | ~ v13_lattices(A_89)
      | ~ l1_lattices(A_89)
      | ~ l3_lattices(A_89)
      | v2_struct_0(A_89) ) ),
    inference(resolution,[status(thm)],[c_84,c_7700])).

tff(c_8526,plain,(
    ! [B_1097] :
      ( k2_lattices('#skF_12','#skF_4'('#skF_12'),k15_lattice3('#skF_12',B_1097)) = '#skF_4'('#skF_12')
      | ~ v13_lattices('#skF_12')
      | ~ l1_lattices('#skF_12')
      | ~ l3_lattices('#skF_12')
      | v2_struct_0('#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8520,c_7717])).

tff(c_8544,plain,(
    ! [B_1097] :
      ( k2_lattices('#skF_12','#skF_4'('#skF_12'),k15_lattice3('#skF_12',B_1097)) = '#skF_4'('#skF_12')
      | v2_struct_0('#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_127,c_7413,c_8526])).

tff(c_8545,plain,(
    ! [B_1097] : k2_lattices('#skF_12','#skF_4'('#skF_12'),k15_lattice3('#skF_12',B_1097)) = '#skF_4'('#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_8544])).

tff(c_8515,plain,(
    ! [B_90] : k2_lattices('#skF_12',k15_lattice3('#skF_12',B_90),'#skF_4'('#skF_12')) = k2_lattices('#skF_12','#skF_4'('#skF_12'),k15_lattice3('#skF_12',B_90)) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_8514])).

tff(c_8556,plain,(
    ! [B_90] : k2_lattices('#skF_12',k15_lattice3('#skF_12',B_90),'#skF_4'('#skF_12')) = '#skF_4'('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8545,c_8515])).

tff(c_7787,plain,(
    ! [A_1006,B_1007,C_1008] :
      ( r2_hidden('#skF_6'(A_1006,B_1007,C_1008),C_1008)
      | r4_lattice3(A_1006,B_1007,C_1008)
      | ~ m1_subset_1(B_1007,u1_struct_0(A_1006))
      | ~ l3_lattices(A_1006)
      | v2_struct_0(A_1006) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_9078,plain,(
    ! [A_1139,B_1140,C_1141,B_1142] :
      ( r2_hidden('#skF_6'(A_1139,B_1140,C_1141),B_1142)
      | ~ r1_tarski(C_1141,B_1142)
      | r4_lattice3(A_1139,B_1140,C_1141)
      | ~ m1_subset_1(B_1140,u1_struct_0(A_1139))
      | ~ l3_lattices(A_1139)
      | v2_struct_0(A_1139) ) ),
    inference(resolution,[status(thm)],[c_7787,c_2])).

tff(c_9110,plain,(
    ! [C_1143,A_1144,B_1145] :
      ( ~ r1_tarski(C_1143,k1_xboole_0)
      | r4_lattice3(A_1144,B_1145,C_1143)
      | ~ m1_subset_1(B_1145,u1_struct_0(A_1144))
      | ~ l3_lattices(A_1144)
      | v2_struct_0(A_1144) ) ),
    inference(resolution,[status(thm)],[c_9078,c_7471])).

tff(c_9112,plain,(
    ! [C_1143] :
      ( ~ r1_tarski(C_1143,k1_xboole_0)
      | r4_lattice3('#skF_12','#skF_4'('#skF_12'),C_1143)
      | ~ l3_lattices('#skF_12')
      | v2_struct_0('#skF_12') ) ),
    inference(resolution,[status(thm)],[c_8327,c_9110])).

tff(c_9135,plain,(
    ! [C_1143] :
      ( ~ r1_tarski(C_1143,k1_xboole_0)
      | r4_lattice3('#skF_12','#skF_4'('#skF_12'),C_1143)
      | v2_struct_0('#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_9112])).

tff(c_9136,plain,(
    ! [C_1143] :
      ( ~ r1_tarski(C_1143,k1_xboole_0)
      | r4_lattice3('#skF_12','#skF_4'('#skF_12'),C_1143) ) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_9135])).

tff(c_10238,plain,(
    ! [A_1281,B_1282,D_1283] :
      ( r1_lattices(A_1281,k15_lattice3(A_1281,B_1282),D_1283)
      | ~ r4_lattice3(A_1281,D_1283,B_1282)
      | ~ m1_subset_1(D_1283,u1_struct_0(A_1281))
      | ~ m1_subset_1(k15_lattice3(A_1281,B_1282),u1_struct_0(A_1281))
      | ~ v4_lattice3(A_1281)
      | ~ v10_lattices(A_1281)
      | ~ l3_lattices(A_1281)
      | v2_struct_0(A_1281) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_10246,plain,(
    ! [A_1284,B_1285,D_1286] :
      ( r1_lattices(A_1284,k15_lattice3(A_1284,B_1285),D_1286)
      | ~ r4_lattice3(A_1284,D_1286,B_1285)
      | ~ m1_subset_1(D_1286,u1_struct_0(A_1284))
      | ~ v4_lattice3(A_1284)
      | ~ v10_lattices(A_1284)
      | ~ l3_lattices(A_1284)
      | v2_struct_0(A_1284) ) ),
    inference(resolution,[status(thm)],[c_84,c_10238])).

tff(c_36193,plain,(
    ! [A_2443,B_2444,D_2445] :
      ( r1_lattices(A_2443,k15_lattice3(A_2443,B_2444),D_2445)
      | ~ r4_lattice3(A_2443,D_2445,a_2_5_lattice3(A_2443,B_2444))
      | ~ m1_subset_1(D_2445,u1_struct_0(A_2443))
      | ~ v4_lattice3(A_2443)
      | ~ v10_lattices(A_2443)
      | ~ l3_lattices(A_2443)
      | v2_struct_0(A_2443)
      | ~ l3_lattices(A_2443)
      | ~ v4_lattice3(A_2443)
      | ~ v10_lattices(A_2443)
      | v2_struct_0(A_2443) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_10246])).

tff(c_36273,plain,(
    ! [B_2444] :
      ( r1_lattices('#skF_12',k15_lattice3('#skF_12',B_2444),'#skF_4'('#skF_12'))
      | ~ m1_subset_1('#skF_4'('#skF_12'),u1_struct_0('#skF_12'))
      | ~ l3_lattices('#skF_12')
      | ~ v4_lattice3('#skF_12')
      | ~ v10_lattices('#skF_12')
      | v2_struct_0('#skF_12')
      | ~ r1_tarski(a_2_5_lattice3('#skF_12',B_2444),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_9136,c_36193])).

tff(c_36306,plain,(
    ! [B_2444] :
      ( r1_lattices('#skF_12',k15_lattice3('#skF_12',B_2444),'#skF_4'('#skF_12'))
      | v2_struct_0('#skF_12')
      | ~ r1_tarski(a_2_5_lattice3('#skF_12',B_2444),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_114,c_112,c_8327,c_36273])).

tff(c_36312,plain,(
    ! [B_2446] :
      ( r1_lattices('#skF_12',k15_lattice3('#skF_12',B_2446),'#skF_4'('#skF_12'))
      | ~ r1_tarski(a_2_5_lattice3('#skF_12',B_2446),k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_36306])).

tff(c_36314,plain,(
    ! [B_2446] :
      ( k2_lattices('#skF_12',k15_lattice3('#skF_12',B_2446),'#skF_4'('#skF_12')) = k15_lattice3('#skF_12',B_2446)
      | ~ m1_subset_1('#skF_4'('#skF_12'),u1_struct_0('#skF_12'))
      | ~ m1_subset_1(k15_lattice3('#skF_12',B_2446),u1_struct_0('#skF_12'))
      | ~ l3_lattices('#skF_12')
      | ~ v9_lattices('#skF_12')
      | ~ v8_lattices('#skF_12')
      | v2_struct_0('#skF_12')
      | ~ r1_tarski(a_2_5_lattice3('#skF_12',B_2446),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_36312,c_46])).

tff(c_36329,plain,(
    ! [B_2446] :
      ( k15_lattice3('#skF_12',B_2446) = '#skF_4'('#skF_12')
      | ~ m1_subset_1(k15_lattice3('#skF_12',B_2446),u1_struct_0('#skF_12'))
      | v2_struct_0('#skF_12')
      | ~ r1_tarski(a_2_5_lattice3('#skF_12',B_2446),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9211,c_9223,c_112,c_8327,c_8556,c_36314])).

tff(c_36392,plain,(
    ! [B_2452] :
      ( k15_lattice3('#skF_12',B_2452) = '#skF_4'('#skF_12')
      | ~ m1_subset_1(k15_lattice3('#skF_12',B_2452),u1_struct_0('#skF_12'))
      | ~ r1_tarski(a_2_5_lattice3('#skF_12',B_2452),k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_36329])).

tff(c_36408,plain,(
    ! [B_90] :
      ( k15_lattice3('#skF_12',B_90) = '#skF_4'('#skF_12')
      | ~ r1_tarski(a_2_5_lattice3('#skF_12',B_90),k1_xboole_0)
      | ~ l3_lattices('#skF_12')
      | v2_struct_0('#skF_12') ) ),
    inference(resolution,[status(thm)],[c_84,c_36392])).

tff(c_36420,plain,(
    ! [B_90] :
      ( k15_lattice3('#skF_12',B_90) = '#skF_4'('#skF_12')
      | ~ r1_tarski(a_2_5_lattice3('#skF_12',B_90),k1_xboole_0)
      | v2_struct_0('#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_36408])).

tff(c_36422,plain,(
    ! [B_2453] :
      ( k15_lattice3('#skF_12',B_2453) = '#skF_4'('#skF_12')
      | ~ r1_tarski(a_2_5_lattice3('#skF_12',B_2453),k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_36420])).

tff(c_36529,plain,
    ( k15_lattice3('#skF_12',k1_xboole_0) = '#skF_4'('#skF_12')
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7984,c_36422])).

tff(c_36605,plain,(
    k15_lattice3('#skF_12',k1_xboole_0) = '#skF_4'('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7469,c_36529])).

tff(c_36607,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8294,c_36605])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:55:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.14/11.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.14/11.37  
% 22.14/11.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.34/11.38  %$ r4_lattice3 > r3_lattices > r1_lattices > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k6_domain_1 > k3_xboole_0 > k16_lattice3 > k15_lattice3 > a_2_6_lattice3 > a_2_5_lattice3 > #nlpp > u1_struct_0 > k5_lattices > k1_xboole_0 > #skF_9 > #skF_4 > #skF_6 > #skF_8 > #skF_3 > #skF_11 > #skF_7 > #skF_2 > #skF_1 > #skF_5 > #skF_12 > #skF_10
% 22.34/11.38  
% 22.34/11.38  %Foreground sorts:
% 22.34/11.38  
% 22.34/11.38  
% 22.34/11.38  %Background operators:
% 22.34/11.38  
% 22.34/11.38  
% 22.34/11.38  %Foreground operators:
% 22.34/11.38  tff(l3_lattices, type, l3_lattices: $i > $o).
% 22.34/11.38  tff('#skF_9', type, '#skF_9': $i > $i).
% 22.34/11.38  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 22.34/11.38  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 22.34/11.38  tff(l2_lattices, type, l2_lattices: $i > $o).
% 22.34/11.38  tff('#skF_4', type, '#skF_4': $i > $i).
% 22.34/11.38  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 22.34/11.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.34/11.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 22.34/11.38  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 22.34/11.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 22.34/11.38  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 22.34/11.38  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 22.34/11.38  tff(l1_lattices, type, l1_lattices: $i > $o).
% 22.34/11.38  tff('#skF_8', type, '#skF_8': $i > $i).
% 22.34/11.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 22.34/11.38  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 22.34/11.38  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 22.34/11.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 22.34/11.38  tff(v4_lattices, type, v4_lattices: $i > $o).
% 22.34/11.38  tff(v6_lattices, type, v6_lattices: $i > $o).
% 22.34/11.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 22.34/11.38  tff(v9_lattices, type, v9_lattices: $i > $o).
% 22.34/11.38  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 22.34/11.38  tff(a_2_5_lattice3, type, a_2_5_lattice3: ($i * $i) > $i).
% 22.34/11.38  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 22.34/11.38  tff(v5_lattices, type, v5_lattices: $i > $o).
% 22.34/11.38  tff('#skF_11', type, '#skF_11': ($i * $i * $i) > $i).
% 22.34/11.38  tff(v10_lattices, type, v10_lattices: $i > $o).
% 22.34/11.38  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 22.34/11.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.34/11.38  tff(v13_lattices, type, v13_lattices: $i > $o).
% 22.34/11.38  tff(v8_lattices, type, v8_lattices: $i > $o).
% 22.34/11.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.34/11.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 22.34/11.38  tff(k5_lattices, type, k5_lattices: $i > $i).
% 22.34/11.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 22.34/11.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 22.34/11.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 22.34/11.38  tff(a_2_6_lattice3, type, a_2_6_lattice3: ($i * $i) > $i).
% 22.34/11.38  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 22.34/11.38  tff('#skF_12', type, '#skF_12': $i).
% 22.34/11.38  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 22.34/11.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 22.34/11.38  tff(v7_lattices, type, v7_lattices: $i > $o).
% 22.34/11.38  
% 22.41/11.41  tff(f_300, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v13_lattices(A)) & l3_lattices(A)) & (k5_lattices(A) = k15_lattice3(A, k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_lattice3)).
% 22.41/11.41  tff(f_106, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 22.41/11.41  tff(f_210, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k15_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 22.41/11.41  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 22.41/11.41  tff(f_233, axiom, (![A, B, C]: ((((~v2_struct_0(B) & v10_lattices(B)) & v4_lattice3(B)) & l3_lattices(B)) => (r2_hidden(A, a_2_5_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r3_lattices(B, D, E)) & r2_hidden(E, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_5_lattice3)).
% 22.41/11.41  tff(f_52, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 22.41/11.41  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 22.41/11.41  tff(f_50, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 22.41/11.41  tff(f_188, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k15_lattice3(A, B)) <=> (r4_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d21_lattice3)).
% 22.41/11.41  tff(f_279, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: ((k15_lattice3(A, B) = k15_lattice3(A, a_2_5_lattice3(A, B))) & (k16_lattice3(A, B) = k16_lattice3(A, a_2_6_lattice3(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_lattice3)).
% 22.41/11.41  tff(f_142, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) <=> (?[B]: (m1_subset_1(B, u1_struct_0(A)) & (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_lattices)).
% 22.41/11.41  tff(f_74, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 22.41/11.41  tff(f_125, axiom, (![A]: ((((~v2_struct_0(A) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k2_lattices(A, B, C) = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_lattices)).
% 22.41/11.41  tff(f_160, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_lattice3)).
% 22.41/11.41  tff(f_100, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => m1_subset_1(k5_lattices(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_lattices)).
% 22.41/11.41  tff(f_203, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v6_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, C) = k2_lattices(A, C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_lattices)).
% 22.41/11.41  tff(f_93, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((B = k5_lattices(A)) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattices)).
% 22.41/11.41  tff(c_112, plain, (l3_lattices('#skF_12')), inference(cnfTransformation, [status(thm)], [f_300])).
% 22.41/11.41  tff(c_123, plain, (![A_116]: (l1_lattices(A_116) | ~l3_lattices(A_116))), inference(cnfTransformation, [status(thm)], [f_106])).
% 22.41/11.41  tff(c_127, plain, (l1_lattices('#skF_12')), inference(resolution, [status(thm)], [c_112, c_123])).
% 22.41/11.41  tff(c_118, plain, (~v2_struct_0('#skF_12')), inference(cnfTransformation, [status(thm)], [f_300])).
% 22.41/11.41  tff(c_84, plain, (![A_89, B_90]: (m1_subset_1(k15_lattice3(A_89, B_90), u1_struct_0(A_89)) | ~l3_lattices(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_210])).
% 22.41/11.41  tff(c_116, plain, (v10_lattices('#skF_12')), inference(cnfTransformation, [status(thm)], [f_300])).
% 22.41/11.41  tff(c_114, plain, (v4_lattice3('#skF_12')), inference(cnfTransformation, [status(thm)], [f_300])).
% 22.41/11.41  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 22.41/11.41  tff(c_598, plain, (![A_225, B_226, C_227]: (r2_hidden('#skF_11'(A_225, B_226, C_227), C_227) | ~r2_hidden(A_225, a_2_5_lattice3(B_226, C_227)) | ~l3_lattices(B_226) | ~v4_lattice3(B_226) | ~v10_lattices(B_226) | v2_struct_0(B_226))), inference(cnfTransformation, [status(thm)], [f_233])).
% 22.41/11.41  tff(c_14, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_52])).
% 22.41/11.41  tff(c_140, plain, (![A_125, B_126, C_127]: (~r1_xboole_0(A_125, B_126) | ~r2_hidden(C_127, k3_xboole_0(A_125, B_126)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 22.41/11.41  tff(c_161, plain, (![A_133, B_134, B_135]: (~r1_xboole_0(A_133, B_134) | r1_tarski(k3_xboole_0(A_133, B_134), B_135))), inference(resolution, [status(thm)], [c_6, c_140])).
% 22.41/11.41  tff(c_12, plain, (![A_11]: (k1_xboole_0=A_11 | ~r1_tarski(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_50])).
% 22.41/11.41  tff(c_167, plain, (![A_136, B_137]: (k3_xboole_0(A_136, B_137)=k1_xboole_0 | ~r1_xboole_0(A_136, B_137))), inference(resolution, [status(thm)], [c_161, c_12])).
% 22.41/11.41  tff(c_172, plain, (![A_138]: (k3_xboole_0(A_138, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_167])).
% 22.41/11.41  tff(c_10, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 22.41/11.41  tff(c_180, plain, (![A_138, C_10]: (~r1_xboole_0(A_138, k1_xboole_0) | ~r2_hidden(C_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_172, c_10])).
% 22.41/11.41  tff(c_187, plain, (![C_10]: (~r2_hidden(C_10, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_180])).
% 22.41/11.41  tff(c_617, plain, (![A_228, B_229]: (~r2_hidden(A_228, a_2_5_lattice3(B_229, k1_xboole_0)) | ~l3_lattices(B_229) | ~v4_lattice3(B_229) | ~v10_lattices(B_229) | v2_struct_0(B_229))), inference(resolution, [status(thm)], [c_598, c_187])).
% 22.41/11.41  tff(c_643, plain, (![B_230, B_231]: (~l3_lattices(B_230) | ~v4_lattice3(B_230) | ~v10_lattices(B_230) | v2_struct_0(B_230) | r1_tarski(a_2_5_lattice3(B_230, k1_xboole_0), B_231))), inference(resolution, [status(thm)], [c_6, c_617])).
% 22.41/11.41  tff(c_663, plain, (![B_232]: (a_2_5_lattice3(B_232, k1_xboole_0)=k1_xboole_0 | ~l3_lattices(B_232) | ~v4_lattice3(B_232) | ~v10_lattices(B_232) | v2_struct_0(B_232))), inference(resolution, [status(thm)], [c_643, c_12])).
% 22.41/11.41  tff(c_666, plain, (a_2_5_lattice3('#skF_12', k1_xboole_0)=k1_xboole_0 | ~l3_lattices('#skF_12') | ~v10_lattices('#skF_12') | v2_struct_0('#skF_12')), inference(resolution, [status(thm)], [c_114, c_663])).
% 22.41/11.41  tff(c_669, plain, (a_2_5_lattice3('#skF_12', k1_xboole_0)=k1_xboole_0 | v2_struct_0('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_112, c_666])).
% 22.41/11.41  tff(c_670, plain, (a_2_5_lattice3('#skF_12', k1_xboole_0)=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_118, c_669])).
% 22.41/11.41  tff(c_875, plain, (![A_266, B_267]: (r4_lattice3(A_266, k15_lattice3(A_266, B_267), B_267) | ~m1_subset_1(k15_lattice3(A_266, B_267), u1_struct_0(A_266)) | ~v4_lattice3(A_266) | ~v10_lattices(A_266) | ~l3_lattices(A_266) | v2_struct_0(A_266))), inference(cnfTransformation, [status(thm)], [f_188])).
% 22.41/11.41  tff(c_882, plain, (![A_89, B_90]: (r4_lattice3(A_89, k15_lattice3(A_89, B_90), B_90) | ~v4_lattice3(A_89) | ~v10_lattices(A_89) | ~l3_lattices(A_89) | v2_struct_0(A_89))), inference(resolution, [status(thm)], [c_84, c_875])).
% 22.41/11.41  tff(c_106, plain, (![A_112, B_114]: (k15_lattice3(A_112, a_2_5_lattice3(A_112, B_114))=k15_lattice3(A_112, B_114) | ~l3_lattices(A_112) | ~v4_lattice3(A_112) | ~v10_lattices(A_112) | v2_struct_0(A_112))), inference(cnfTransformation, [status(thm)], [f_279])).
% 22.41/11.41  tff(c_1685, plain, (![A_404, B_405, D_406]: (r1_lattices(A_404, k15_lattice3(A_404, B_405), D_406) | ~r4_lattice3(A_404, D_406, B_405) | ~m1_subset_1(D_406, u1_struct_0(A_404)) | ~m1_subset_1(k15_lattice3(A_404, B_405), u1_struct_0(A_404)) | ~v4_lattice3(A_404) | ~v10_lattices(A_404) | ~l3_lattices(A_404) | v2_struct_0(A_404))), inference(cnfTransformation, [status(thm)], [f_188])).
% 22.41/11.41  tff(c_1728, plain, (![A_409, B_410, D_411]: (r1_lattices(A_409, k15_lattice3(A_409, B_410), D_411) | ~r4_lattice3(A_409, D_411, B_410) | ~m1_subset_1(D_411, u1_struct_0(A_409)) | ~v4_lattice3(A_409) | ~v10_lattices(A_409) | ~l3_lattices(A_409) | v2_struct_0(A_409))), inference(resolution, [status(thm)], [c_84, c_1685])).
% 22.41/11.41  tff(c_5117, plain, (![A_838, B_839, D_840]: (r1_lattices(A_838, k15_lattice3(A_838, B_839), D_840) | ~r4_lattice3(A_838, D_840, a_2_5_lattice3(A_838, B_839)) | ~m1_subset_1(D_840, u1_struct_0(A_838)) | ~v4_lattice3(A_838) | ~v10_lattices(A_838) | ~l3_lattices(A_838) | v2_struct_0(A_838) | ~l3_lattices(A_838) | ~v4_lattice3(A_838) | ~v10_lattices(A_838) | v2_struct_0(A_838))), inference(superposition, [status(thm), theory('equality')], [c_106, c_1728])).
% 22.41/11.41  tff(c_5310, plain, (![A_856, B_857]: (r1_lattices(A_856, k15_lattice3(A_856, B_857), k15_lattice3(A_856, a_2_5_lattice3(A_856, B_857))) | ~m1_subset_1(k15_lattice3(A_856, a_2_5_lattice3(A_856, B_857)), u1_struct_0(A_856)) | ~v4_lattice3(A_856) | ~v10_lattices(A_856) | ~l3_lattices(A_856) | v2_struct_0(A_856))), inference(resolution, [status(thm)], [c_882, c_5117])).
% 22.41/11.41  tff(c_5330, plain, (r1_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), k15_lattice3('#skF_12', k1_xboole_0)) | ~m1_subset_1(k15_lattice3('#skF_12', a_2_5_lattice3('#skF_12', k1_xboole_0)), u1_struct_0('#skF_12')) | ~v4_lattice3('#skF_12') | ~v10_lattices('#skF_12') | ~l3_lattices('#skF_12') | v2_struct_0('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_670, c_5310])).
% 22.41/11.41  tff(c_5342, plain, (r1_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), k15_lattice3('#skF_12', k1_xboole_0)) | ~m1_subset_1(k15_lattice3('#skF_12', k1_xboole_0), u1_struct_0('#skF_12')) | v2_struct_0('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_116, c_114, c_670, c_5330])).
% 22.41/11.41  tff(c_5343, plain, (r1_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), k15_lattice3('#skF_12', k1_xboole_0)) | ~m1_subset_1(k15_lattice3('#skF_12', k1_xboole_0), u1_struct_0('#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_118, c_5342])).
% 22.41/11.41  tff(c_5344, plain, (~m1_subset_1(k15_lattice3('#skF_12', k1_xboole_0), u1_struct_0('#skF_12'))), inference(splitLeft, [status(thm)], [c_5343])).
% 22.41/11.41  tff(c_5358, plain, (~l3_lattices('#skF_12') | v2_struct_0('#skF_12')), inference(resolution, [status(thm)], [c_84, c_5344])).
% 22.41/11.41  tff(c_5361, plain, (v2_struct_0('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_5358])).
% 22.41/11.41  tff(c_5363, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_5361])).
% 22.41/11.41  tff(c_5365, plain, (m1_subset_1(k15_lattice3('#skF_12', k1_xboole_0), u1_struct_0('#skF_12'))), inference(splitRight, [status(thm)], [c_5343])).
% 22.41/11.41  tff(c_110, plain, (k15_lattice3('#skF_12', k1_xboole_0)!=k5_lattices('#skF_12') | ~l3_lattices('#skF_12') | ~v13_lattices('#skF_12') | ~v10_lattices('#skF_12') | v2_struct_0('#skF_12')), inference(cnfTransformation, [status(thm)], [f_300])).
% 22.41/11.41  tff(c_120, plain, (k15_lattice3('#skF_12', k1_xboole_0)!=k5_lattices('#skF_12') | ~v13_lattices('#skF_12') | v2_struct_0('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_112, c_110])).
% 22.41/11.41  tff(c_121, plain, (k15_lattice3('#skF_12', k1_xboole_0)!=k5_lattices('#skF_12') | ~v13_lattices('#skF_12')), inference(negUnitSimplification, [status(thm)], [c_118, c_120])).
% 22.41/11.41  tff(c_133, plain, (~v13_lattices('#skF_12')), inference(splitLeft, [status(thm)], [c_121])).
% 22.41/11.41  tff(c_50, plain, (![A_33, B_42]: (m1_subset_1('#skF_5'(A_33, B_42), u1_struct_0(A_33)) | v13_lattices(A_33) | ~m1_subset_1(B_42, u1_struct_0(A_33)) | ~l1_lattices(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_142])).
% 22.41/11.41  tff(c_18, plain, (![A_13]: (v8_lattices(A_13) | ~v10_lattices(A_13) | v2_struct_0(A_13) | ~l3_lattices(A_13))), inference(cnfTransformation, [status(thm)], [f_74])).
% 22.41/11.41  tff(c_5364, plain, (r1_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), k15_lattice3('#skF_12', k1_xboole_0))), inference(splitRight, [status(thm)], [c_5343])).
% 22.41/11.41  tff(c_46, plain, (![A_26, B_30, C_32]: (k2_lattices(A_26, B_30, C_32)=B_30 | ~r1_lattices(A_26, B_30, C_32) | ~m1_subset_1(C_32, u1_struct_0(A_26)) | ~m1_subset_1(B_30, u1_struct_0(A_26)) | ~l3_lattices(A_26) | ~v9_lattices(A_26) | ~v8_lattices(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_125])).
% 22.41/11.41  tff(c_5464, plain, (k2_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), k15_lattice3('#skF_12', k1_xboole_0))=k15_lattice3('#skF_12', k1_xboole_0) | ~m1_subset_1(k15_lattice3('#skF_12', k1_xboole_0), u1_struct_0('#skF_12')) | ~l3_lattices('#skF_12') | ~v9_lattices('#skF_12') | ~v8_lattices('#skF_12') | v2_struct_0('#skF_12')), inference(resolution, [status(thm)], [c_5364, c_46])).
% 22.41/11.41  tff(c_5467, plain, (k2_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), k15_lattice3('#skF_12', k1_xboole_0))=k15_lattice3('#skF_12', k1_xboole_0) | ~v9_lattices('#skF_12') | ~v8_lattices('#skF_12') | v2_struct_0('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_5365, c_5464])).
% 22.41/11.41  tff(c_5468, plain, (k2_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), k15_lattice3('#skF_12', k1_xboole_0))=k15_lattice3('#skF_12', k1_xboole_0) | ~v9_lattices('#skF_12') | ~v8_lattices('#skF_12')), inference(negUnitSimplification, [status(thm)], [c_118, c_5467])).
% 22.41/11.41  tff(c_5516, plain, (~v8_lattices('#skF_12')), inference(splitLeft, [status(thm)], [c_5468])).
% 22.41/11.41  tff(c_5519, plain, (~v10_lattices('#skF_12') | v2_struct_0('#skF_12') | ~l3_lattices('#skF_12')), inference(resolution, [status(thm)], [c_18, c_5516])).
% 22.41/11.41  tff(c_5522, plain, (v2_struct_0('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_116, c_5519])).
% 22.41/11.41  tff(c_5524, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_5522])).
% 22.41/11.41  tff(c_5526, plain, (v8_lattices('#skF_12')), inference(splitRight, [status(thm)], [c_5468])).
% 22.41/11.41  tff(c_16, plain, (![A_13]: (v9_lattices(A_13) | ~v10_lattices(A_13) | v2_struct_0(A_13) | ~l3_lattices(A_13))), inference(cnfTransformation, [status(thm)], [f_74])).
% 22.41/11.41  tff(c_5525, plain, (~v9_lattices('#skF_12') | k2_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), k15_lattice3('#skF_12', k1_xboole_0))=k15_lattice3('#skF_12', k1_xboole_0)), inference(splitRight, [status(thm)], [c_5468])).
% 22.41/11.41  tff(c_5527, plain, (~v9_lattices('#skF_12')), inference(splitLeft, [status(thm)], [c_5525])).
% 22.41/11.41  tff(c_5530, plain, (~v10_lattices('#skF_12') | v2_struct_0('#skF_12') | ~l3_lattices('#skF_12')), inference(resolution, [status(thm)], [c_16, c_5527])).
% 22.41/11.41  tff(c_5533, plain, (v2_struct_0('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_116, c_5530])).
% 22.41/11.41  tff(c_5535, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_5533])).
% 22.41/11.41  tff(c_5537, plain, (v9_lattices('#skF_12')), inference(splitRight, [status(thm)], [c_5525])).
% 22.41/11.41  tff(c_145, plain, (![A_125, B_126, B_2]: (~r1_xboole_0(A_125, B_126) | r1_tarski(k3_xboole_0(A_125, B_126), B_2))), inference(resolution, [status(thm)], [c_6, c_140])).
% 22.41/11.41  tff(c_5536, plain, (k2_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), k15_lattice3('#skF_12', k1_xboole_0))=k15_lattice3('#skF_12', k1_xboole_0)), inference(splitRight, [status(thm)], [c_5525])).
% 22.41/11.41  tff(c_734, plain, (![A_238, B_239, A_240, B_241]: (~r1_xboole_0(A_238, B_239) | ~r2_hidden(A_240, a_2_5_lattice3(B_241, k3_xboole_0(A_238, B_239))) | ~l3_lattices(B_241) | ~v4_lattice3(B_241) | ~v10_lattices(B_241) | v2_struct_0(B_241))), inference(resolution, [status(thm)], [c_598, c_10])).
% 22.41/11.41  tff(c_765, plain, (![A_242, B_243, B_244, B_245]: (~r1_xboole_0(A_242, B_243) | ~l3_lattices(B_244) | ~v4_lattice3(B_244) | ~v10_lattices(B_244) | v2_struct_0(B_244) | r1_tarski(a_2_5_lattice3(B_244, k3_xboole_0(A_242, B_243)), B_245))), inference(resolution, [status(thm)], [c_6, c_734])).
% 22.41/11.41  tff(c_794, plain, (![B_246, A_247, B_248]: (a_2_5_lattice3(B_246, k3_xboole_0(A_247, B_248))=k1_xboole_0 | ~r1_xboole_0(A_247, B_248) | ~l3_lattices(B_246) | ~v4_lattice3(B_246) | ~v10_lattices(B_246) | v2_struct_0(B_246))), inference(resolution, [status(thm)], [c_765, c_12])).
% 22.41/11.41  tff(c_809, plain, (![B_246, A_247, B_248]: (k15_lattice3(B_246, k3_xboole_0(A_247, B_248))=k15_lattice3(B_246, k1_xboole_0) | ~l3_lattices(B_246) | ~v4_lattice3(B_246) | ~v10_lattices(B_246) | v2_struct_0(B_246) | ~r1_xboole_0(A_247, B_248) | ~l3_lattices(B_246) | ~v4_lattice3(B_246) | ~v10_lattices(B_246) | v2_struct_0(B_246))), inference(superposition, [status(thm), theory('equality')], [c_794, c_106])).
% 22.41/11.41  tff(c_177, plain, (![A_138, B_2]: (~r1_xboole_0(A_138, k1_xboole_0) | r1_tarski(k1_xboole_0, B_2))), inference(superposition, [status(thm), theory('equality')], [c_172, c_145])).
% 22.41/11.41  tff(c_185, plain, (![B_2]: (r1_tarski(k1_xboole_0, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_177])).
% 22.41/11.41  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 22.41/11.41  tff(c_1394, plain, (![A_359, B_360, C_361, B_362]: (r2_hidden('#skF_11'(A_359, B_360, C_361), B_362) | ~r1_tarski(C_361, B_362) | ~r2_hidden(A_359, a_2_5_lattice3(B_360, C_361)) | ~l3_lattices(B_360) | ~v4_lattice3(B_360) | ~v10_lattices(B_360) | v2_struct_0(B_360))), inference(resolution, [status(thm)], [c_598, c_2])).
% 22.41/11.41  tff(c_1426, plain, (![C_363, A_364, B_365]: (~r1_tarski(C_363, k1_xboole_0) | ~r2_hidden(A_364, a_2_5_lattice3(B_365, C_363)) | ~l3_lattices(B_365) | ~v4_lattice3(B_365) | ~v10_lattices(B_365) | v2_struct_0(B_365))), inference(resolution, [status(thm)], [c_1394, c_187])).
% 22.41/11.41  tff(c_1470, plain, (![C_363, B_365, B_2]: (~r1_tarski(C_363, k1_xboole_0) | ~l3_lattices(B_365) | ~v4_lattice3(B_365) | ~v10_lattices(B_365) | v2_struct_0(B_365) | r1_tarski(a_2_5_lattice3(B_365, C_363), B_2))), inference(resolution, [status(thm)], [c_6, c_1426])).
% 22.41/11.41  tff(c_1472, plain, (![C_369, B_370, B_371]: (~r1_tarski(C_369, k1_xboole_0) | ~l3_lattices(B_370) | ~v4_lattice3(B_370) | ~v10_lattices(B_370) | v2_struct_0(B_370) | r1_tarski(a_2_5_lattice3(B_370, C_369), B_371))), inference(resolution, [status(thm)], [c_6, c_1426])).
% 22.41/11.41  tff(c_1514, plain, (![B_372, C_373]: (a_2_5_lattice3(B_372, C_373)=k1_xboole_0 | ~r1_tarski(C_373, k1_xboole_0) | ~l3_lattices(B_372) | ~v4_lattice3(B_372) | ~v10_lattices(B_372) | v2_struct_0(B_372))), inference(resolution, [status(thm)], [c_1472, c_12])).
% 22.41/11.41  tff(c_1533, plain, (![B_372, B_365, C_363]: (a_2_5_lattice3(B_372, a_2_5_lattice3(B_365, C_363))=k1_xboole_0 | ~l3_lattices(B_372) | ~v4_lattice3(B_372) | ~v10_lattices(B_372) | v2_struct_0(B_372) | ~r1_tarski(C_363, k1_xboole_0) | ~l3_lattices(B_365) | ~v4_lattice3(B_365) | ~v10_lattices(B_365) | v2_struct_0(B_365))), inference(resolution, [status(thm)], [c_1470, c_1514])).
% 22.41/11.41  tff(c_478, plain, (![A_197, B_198, C_199]: (r2_hidden('#skF_6'(A_197, B_198, C_199), C_199) | r4_lattice3(A_197, B_198, C_199) | ~m1_subset_1(B_198, u1_struct_0(A_197)) | ~l3_lattices(A_197) | v2_struct_0(A_197))), inference(cnfTransformation, [status(thm)], [f_160])).
% 22.41/11.41  tff(c_1204, plain, (![A_317, B_318, C_319, B_320]: (r2_hidden('#skF_6'(A_317, B_318, C_319), B_320) | ~r1_tarski(C_319, B_320) | r4_lattice3(A_317, B_318, C_319) | ~m1_subset_1(B_318, u1_struct_0(A_317)) | ~l3_lattices(A_317) | v2_struct_0(A_317))), inference(resolution, [status(thm)], [c_478, c_2])).
% 22.41/11.41  tff(c_1234, plain, (![C_319, A_317, B_318]: (~r1_tarski(C_319, k1_xboole_0) | r4_lattice3(A_317, B_318, C_319) | ~m1_subset_1(B_318, u1_struct_0(A_317)) | ~l3_lattices(A_317) | v2_struct_0(A_317))), inference(resolution, [status(thm)], [c_1204, c_187])).
% 22.41/11.41  tff(c_5383, plain, (![C_319]: (~r1_tarski(C_319, k1_xboole_0) | r4_lattice3('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), C_319) | ~l3_lattices('#skF_12') | v2_struct_0('#skF_12'))), inference(resolution, [status(thm)], [c_5365, c_1234])).
% 22.41/11.41  tff(c_5433, plain, (![C_319]: (~r1_tarski(C_319, k1_xboole_0) | r4_lattice3('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), C_319) | v2_struct_0('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_5383])).
% 22.41/11.41  tff(c_5479, plain, (![C_861]: (~r1_tarski(C_861, k1_xboole_0) | r4_lattice3('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), C_861))), inference(negUnitSimplification, [status(thm)], [c_118, c_5433])).
% 22.41/11.41  tff(c_1740, plain, (![A_112, B_114, D_411]: (r1_lattices(A_112, k15_lattice3(A_112, B_114), D_411) | ~r4_lattice3(A_112, D_411, a_2_5_lattice3(A_112, B_114)) | ~m1_subset_1(D_411, u1_struct_0(A_112)) | ~v4_lattice3(A_112) | ~v10_lattices(A_112) | ~l3_lattices(A_112) | v2_struct_0(A_112) | ~l3_lattices(A_112) | ~v4_lattice3(A_112) | ~v10_lattices(A_112) | v2_struct_0(A_112))), inference(superposition, [status(thm), theory('equality')], [c_106, c_1728])).
% 22.41/11.41  tff(c_5483, plain, (![B_114]: (r1_lattices('#skF_12', k15_lattice3('#skF_12', B_114), k15_lattice3('#skF_12', k1_xboole_0)) | ~m1_subset_1(k15_lattice3('#skF_12', k1_xboole_0), u1_struct_0('#skF_12')) | ~l3_lattices('#skF_12') | ~v4_lattice3('#skF_12') | ~v10_lattices('#skF_12') | v2_struct_0('#skF_12') | ~r1_tarski(a_2_5_lattice3('#skF_12', B_114), k1_xboole_0))), inference(resolution, [status(thm)], [c_5479, c_1740])).
% 22.41/11.41  tff(c_5486, plain, (![B_114]: (r1_lattices('#skF_12', k15_lattice3('#skF_12', B_114), k15_lattice3('#skF_12', k1_xboole_0)) | v2_struct_0('#skF_12') | ~r1_tarski(a_2_5_lattice3('#skF_12', B_114), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_114, c_112, c_5365, c_5483])).
% 22.41/11.41  tff(c_5488, plain, (![B_862]: (r1_lattices('#skF_12', k15_lattice3('#skF_12', B_862), k15_lattice3('#skF_12', k1_xboole_0)) | ~r1_tarski(a_2_5_lattice3('#skF_12', B_862), k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_118, c_5486])).
% 22.41/11.41  tff(c_5502, plain, (![B_114]: (r1_lattices('#skF_12', k15_lattice3('#skF_12', B_114), k15_lattice3('#skF_12', k1_xboole_0)) | ~r1_tarski(a_2_5_lattice3('#skF_12', a_2_5_lattice3('#skF_12', B_114)), k1_xboole_0) | ~l3_lattices('#skF_12') | ~v4_lattice3('#skF_12') | ~v10_lattices('#skF_12') | v2_struct_0('#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_106, c_5488])).
% 22.41/11.41  tff(c_5514, plain, (![B_114]: (r1_lattices('#skF_12', k15_lattice3('#skF_12', B_114), k15_lattice3('#skF_12', k1_xboole_0)) | ~r1_tarski(a_2_5_lattice3('#skF_12', a_2_5_lattice3('#skF_12', B_114)), k1_xboole_0) | v2_struct_0('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_114, c_112, c_5502])).
% 22.41/11.41  tff(c_5552, plain, (![B_866]: (r1_lattices('#skF_12', k15_lattice3('#skF_12', B_866), k15_lattice3('#skF_12', k1_xboole_0)) | ~r1_tarski(a_2_5_lattice3('#skF_12', a_2_5_lattice3('#skF_12', B_866)), k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_118, c_5514])).
% 22.41/11.41  tff(c_5566, plain, (![B_114]: (r1_lattices('#skF_12', k15_lattice3('#skF_12', B_114), k15_lattice3('#skF_12', k1_xboole_0)) | ~r1_tarski(a_2_5_lattice3('#skF_12', a_2_5_lattice3('#skF_12', a_2_5_lattice3('#skF_12', B_114))), k1_xboole_0) | ~l3_lattices('#skF_12') | ~v4_lattice3('#skF_12') | ~v10_lattices('#skF_12') | v2_struct_0('#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_106, c_5552])).
% 22.41/11.41  tff(c_5578, plain, (![B_114]: (r1_lattices('#skF_12', k15_lattice3('#skF_12', B_114), k15_lattice3('#skF_12', k1_xboole_0)) | ~r1_tarski(a_2_5_lattice3('#skF_12', a_2_5_lattice3('#skF_12', a_2_5_lattice3('#skF_12', B_114))), k1_xboole_0) | v2_struct_0('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_114, c_112, c_5566])).
% 22.41/11.41  tff(c_5703, plain, (![B_868]: (r1_lattices('#skF_12', k15_lattice3('#skF_12', B_868), k15_lattice3('#skF_12', k1_xboole_0)) | ~r1_tarski(a_2_5_lattice3('#skF_12', a_2_5_lattice3('#skF_12', a_2_5_lattice3('#skF_12', B_868))), k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_118, c_5578])).
% 22.41/11.41  tff(c_5725, plain, (![C_363]: (r1_lattices('#skF_12', k15_lattice3('#skF_12', C_363), k15_lattice3('#skF_12', k1_xboole_0)) | ~r1_tarski(a_2_5_lattice3('#skF_12', k1_xboole_0), k1_xboole_0) | ~l3_lattices('#skF_12') | ~v4_lattice3('#skF_12') | ~v10_lattices('#skF_12') | v2_struct_0('#skF_12') | ~r1_tarski(C_363, k1_xboole_0) | ~l3_lattices('#skF_12') | ~v4_lattice3('#skF_12') | ~v10_lattices('#skF_12') | v2_struct_0('#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_1533, c_5703])).
% 22.41/11.41  tff(c_5765, plain, (![C_363]: (r1_lattices('#skF_12', k15_lattice3('#skF_12', C_363), k15_lattice3('#skF_12', k1_xboole_0)) | ~r1_tarski(C_363, k1_xboole_0) | v2_struct_0('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_114, c_112, c_116, c_114, c_112, c_185, c_670, c_5725])).
% 22.41/11.41  tff(c_5785, plain, (![C_869]: (r1_lattices('#skF_12', k15_lattice3('#skF_12', C_869), k15_lattice3('#skF_12', k1_xboole_0)) | ~r1_tarski(C_869, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_118, c_5765])).
% 22.41/11.41  tff(c_5787, plain, (![C_869]: (k2_lattices('#skF_12', k15_lattice3('#skF_12', C_869), k15_lattice3('#skF_12', k1_xboole_0))=k15_lattice3('#skF_12', C_869) | ~m1_subset_1(k15_lattice3('#skF_12', k1_xboole_0), u1_struct_0('#skF_12')) | ~m1_subset_1(k15_lattice3('#skF_12', C_869), u1_struct_0('#skF_12')) | ~l3_lattices('#skF_12') | ~v9_lattices('#skF_12') | ~v8_lattices('#skF_12') | v2_struct_0('#skF_12') | ~r1_tarski(C_869, k1_xboole_0))), inference(resolution, [status(thm)], [c_5785, c_46])).
% 22.41/11.41  tff(c_5802, plain, (![C_869]: (k2_lattices('#skF_12', k15_lattice3('#skF_12', C_869), k15_lattice3('#skF_12', k1_xboole_0))=k15_lattice3('#skF_12', C_869) | ~m1_subset_1(k15_lattice3('#skF_12', C_869), u1_struct_0('#skF_12')) | v2_struct_0('#skF_12') | ~r1_tarski(C_869, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_5526, c_5537, c_112, c_5365, c_5787])).
% 22.41/11.41  tff(c_6282, plain, (![C_890]: (k2_lattices('#skF_12', k15_lattice3('#skF_12', C_890), k15_lattice3('#skF_12', k1_xboole_0))=k15_lattice3('#skF_12', C_890) | ~m1_subset_1(k15_lattice3('#skF_12', C_890), u1_struct_0('#skF_12')) | ~r1_tarski(C_890, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_118, c_5802])).
% 22.41/11.41  tff(c_6301, plain, (![B_90]: (k2_lattices('#skF_12', k15_lattice3('#skF_12', B_90), k15_lattice3('#skF_12', k1_xboole_0))=k15_lattice3('#skF_12', B_90) | ~r1_tarski(B_90, k1_xboole_0) | ~l3_lattices('#skF_12') | v2_struct_0('#skF_12'))), inference(resolution, [status(thm)], [c_84, c_6282])).
% 22.41/11.41  tff(c_6316, plain, (![B_90]: (k2_lattices('#skF_12', k15_lattice3('#skF_12', B_90), k15_lattice3('#skF_12', k1_xboole_0))=k15_lattice3('#skF_12', B_90) | ~r1_tarski(B_90, k1_xboole_0) | v2_struct_0('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_6301])).
% 22.41/11.41  tff(c_6318, plain, (![B_891]: (k2_lattices('#skF_12', k15_lattice3('#skF_12', B_891), k15_lattice3('#skF_12', k1_xboole_0))=k15_lattice3('#skF_12', B_891) | ~r1_tarski(B_891, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_118, c_6316])).
% 22.41/11.41  tff(c_6346, plain, (![A_247, B_248]: (k2_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), k15_lattice3('#skF_12', k1_xboole_0))=k15_lattice3('#skF_12', k3_xboole_0(A_247, B_248)) | ~r1_tarski(k3_xboole_0(A_247, B_248), k1_xboole_0) | ~l3_lattices('#skF_12') | ~v4_lattice3('#skF_12') | ~v10_lattices('#skF_12') | v2_struct_0('#skF_12') | ~r1_xboole_0(A_247, B_248) | ~l3_lattices('#skF_12') | ~v4_lattice3('#skF_12') | ~v10_lattices('#skF_12') | v2_struct_0('#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_809, c_6318])).
% 22.41/11.41  tff(c_6378, plain, (![A_247, B_248]: (k15_lattice3('#skF_12', k3_xboole_0(A_247, B_248))=k15_lattice3('#skF_12', k1_xboole_0) | ~r1_tarski(k3_xboole_0(A_247, B_248), k1_xboole_0) | ~r1_xboole_0(A_247, B_248) | v2_struct_0('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_114, c_112, c_116, c_114, c_112, c_5536, c_6346])).
% 22.41/11.41  tff(c_6532, plain, (![A_897, B_898]: (k15_lattice3('#skF_12', k3_xboole_0(A_897, B_898))=k15_lattice3('#skF_12', k1_xboole_0) | ~r1_tarski(k3_xboole_0(A_897, B_898), k1_xboole_0) | ~r1_xboole_0(A_897, B_898))), inference(negUnitSimplification, [status(thm)], [c_118, c_6378])).
% 22.41/11.41  tff(c_6543, plain, (![A_899, B_900]: (k15_lattice3('#skF_12', k3_xboole_0(A_899, B_900))=k15_lattice3('#skF_12', k1_xboole_0) | ~r1_xboole_0(A_899, B_900))), inference(resolution, [status(thm)], [c_145, c_6532])).
% 22.41/11.41  tff(c_764, plain, (![A_238, B_239, B_241, B_2]: (~r1_xboole_0(A_238, B_239) | ~l3_lattices(B_241) | ~v4_lattice3(B_241) | ~v10_lattices(B_241) | v2_struct_0(B_241) | r1_tarski(a_2_5_lattice3(B_241, k3_xboole_0(A_238, B_239)), B_2))), inference(resolution, [status(thm)], [c_6, c_734])).
% 22.41/11.41  tff(c_1310, plain, (![C_342, B_341, A_344, B_343, A_345]: (~r1_xboole_0(A_344, B_343) | ~r1_tarski(C_342, k3_xboole_0(A_344, B_343)) | r4_lattice3(A_345, B_341, C_342) | ~m1_subset_1(B_341, u1_struct_0(A_345)) | ~l3_lattices(A_345) | v2_struct_0(A_345))), inference(resolution, [status(thm)], [c_1204, c_10])).
% 22.41/11.41  tff(c_1328, plain, (![B_341, B_239, A_344, B_343, A_345, B_241, A_238]: (~r1_xboole_0(A_344, B_343) | r4_lattice3(A_345, B_341, a_2_5_lattice3(B_241, k3_xboole_0(A_238, B_239))) | ~m1_subset_1(B_341, u1_struct_0(A_345)) | ~l3_lattices(A_345) | v2_struct_0(A_345) | ~r1_xboole_0(A_238, B_239) | ~l3_lattices(B_241) | ~v4_lattice3(B_241) | ~v10_lattices(B_241) | v2_struct_0(B_241))), inference(resolution, [status(thm)], [c_764, c_1310])).
% 22.41/11.41  tff(c_4167, plain, (![A_344, B_343]: (~r1_xboole_0(A_344, B_343))), inference(splitLeft, [status(thm)], [c_1328])).
% 22.41/11.41  tff(c_4181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4167, c_14])).
% 22.41/11.41  tff(c_4182, plain, (![B_341, B_239, A_345, B_241, A_238]: (r4_lattice3(A_345, B_341, a_2_5_lattice3(B_241, k3_xboole_0(A_238, B_239))) | ~m1_subset_1(B_341, u1_struct_0(A_345)) | ~l3_lattices(A_345) | v2_struct_0(A_345) | ~r1_xboole_0(A_238, B_239) | ~l3_lattices(B_241) | ~v4_lattice3(B_241) | ~v10_lattices(B_241) | v2_struct_0(B_241))), inference(splitRight, [status(thm)], [c_1328])).
% 22.41/11.41  tff(c_5201, plain, (![B_241, A_238, B_239, B_341]: (r1_lattices(B_241, k15_lattice3(B_241, k3_xboole_0(A_238, B_239)), B_341) | ~m1_subset_1(B_341, u1_struct_0(B_241)) | ~r1_xboole_0(A_238, B_239) | ~l3_lattices(B_241) | ~v4_lattice3(B_241) | ~v10_lattices(B_241) | v2_struct_0(B_241))), inference(resolution, [status(thm)], [c_4182, c_5117])).
% 22.41/11.41  tff(c_6576, plain, (![B_341, A_899, B_900]: (r1_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), B_341) | ~m1_subset_1(B_341, u1_struct_0('#skF_12')) | ~r1_xboole_0(A_899, B_900) | ~l3_lattices('#skF_12') | ~v4_lattice3('#skF_12') | ~v10_lattices('#skF_12') | v2_struct_0('#skF_12') | ~r1_xboole_0(A_899, B_900))), inference(superposition, [status(thm), theory('equality')], [c_6543, c_5201])).
% 22.41/11.41  tff(c_6696, plain, (![B_341, A_899, B_900]: (r1_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), B_341) | ~m1_subset_1(B_341, u1_struct_0('#skF_12')) | v2_struct_0('#skF_12') | ~r1_xboole_0(A_899, B_900))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_114, c_112, c_6576])).
% 22.41/11.41  tff(c_6697, plain, (![B_341, A_899, B_900]: (r1_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), B_341) | ~m1_subset_1(B_341, u1_struct_0('#skF_12')) | ~r1_xboole_0(A_899, B_900))), inference(negUnitSimplification, [status(thm)], [c_118, c_6696])).
% 22.41/11.41  tff(c_6846, plain, (![A_899, B_900]: (~r1_xboole_0(A_899, B_900))), inference(splitLeft, [status(thm)], [c_6697])).
% 22.41/11.41  tff(c_6864, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6846, c_14])).
% 22.41/11.41  tff(c_6866, plain, (![B_908]: (r1_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), B_908) | ~m1_subset_1(B_908, u1_struct_0('#skF_12')))), inference(splitRight, [status(thm)], [c_6697])).
% 22.41/11.41  tff(c_6872, plain, (![B_908]: (k2_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), B_908)=k15_lattice3('#skF_12', k1_xboole_0) | ~m1_subset_1(k15_lattice3('#skF_12', k1_xboole_0), u1_struct_0('#skF_12')) | ~l3_lattices('#skF_12') | ~v9_lattices('#skF_12') | ~v8_lattices('#skF_12') | v2_struct_0('#skF_12') | ~m1_subset_1(B_908, u1_struct_0('#skF_12')))), inference(resolution, [status(thm)], [c_6866, c_46])).
% 22.41/11.41  tff(c_6879, plain, (![B_908]: (k2_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), B_908)=k15_lattice3('#skF_12', k1_xboole_0) | v2_struct_0('#skF_12') | ~m1_subset_1(B_908, u1_struct_0('#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_5526, c_5537, c_112, c_5365, c_6872])).
% 22.41/11.41  tff(c_6901, plain, (![B_911]: (k2_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), B_911)=k15_lattice3('#skF_12', k1_xboole_0) | ~m1_subset_1(B_911, u1_struct_0('#skF_12')))), inference(negUnitSimplification, [status(thm)], [c_118, c_6879])).
% 22.41/11.41  tff(c_6928, plain, (![B_42]: (k2_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), '#skF_5'('#skF_12', B_42))=k15_lattice3('#skF_12', k1_xboole_0) | v13_lattices('#skF_12') | ~m1_subset_1(B_42, u1_struct_0('#skF_12')) | ~l1_lattices('#skF_12') | v2_struct_0('#skF_12'))), inference(resolution, [status(thm)], [c_50, c_6901])).
% 22.41/11.41  tff(c_6973, plain, (![B_42]: (k2_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), '#skF_5'('#skF_12', B_42))=k15_lattice3('#skF_12', k1_xboole_0) | v13_lattices('#skF_12') | ~m1_subset_1(B_42, u1_struct_0('#skF_12')) | v2_struct_0('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_6928])).
% 22.41/11.41  tff(c_7384, plain, (![B_920]: (k2_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), '#skF_5'('#skF_12', B_920))=k15_lattice3('#skF_12', k1_xboole_0) | ~m1_subset_1(B_920, u1_struct_0('#skF_12')))), inference(negUnitSimplification, [status(thm)], [c_118, c_133, c_6973])).
% 22.41/11.41  tff(c_22, plain, (![A_13]: (v6_lattices(A_13) | ~v10_lattices(A_13) | v2_struct_0(A_13) | ~l3_lattices(A_13))), inference(cnfTransformation, [status(thm)], [f_74])).
% 22.41/11.41  tff(c_38, plain, (![A_24]: (m1_subset_1(k5_lattices(A_24), u1_struct_0(A_24)) | ~l1_lattices(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_100])).
% 22.41/11.41  tff(c_1032, plain, (![A_286, C_287, B_288]: (k2_lattices(A_286, C_287, B_288)=k2_lattices(A_286, B_288, C_287) | ~m1_subset_1(C_287, u1_struct_0(A_286)) | ~m1_subset_1(B_288, u1_struct_0(A_286)) | ~v6_lattices(A_286) | ~l1_lattices(A_286) | v2_struct_0(A_286))), inference(cnfTransformation, [status(thm)], [f_203])).
% 22.41/11.41  tff(c_1062, plain, (![A_24, B_288]: (k2_lattices(A_24, k5_lattices(A_24), B_288)=k2_lattices(A_24, B_288, k5_lattices(A_24)) | ~m1_subset_1(B_288, u1_struct_0(A_24)) | ~v6_lattices(A_24) | ~l1_lattices(A_24) | v2_struct_0(A_24))), inference(resolution, [status(thm)], [c_38, c_1032])).
% 22.41/11.41  tff(c_5385, plain, (k2_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), k5_lattices('#skF_12'))=k2_lattices('#skF_12', k5_lattices('#skF_12'), k15_lattice3('#skF_12', k1_xboole_0)) | ~v6_lattices('#skF_12') | ~l1_lattices('#skF_12') | v2_struct_0('#skF_12')), inference(resolution, [status(thm)], [c_5365, c_1062])).
% 22.41/11.41  tff(c_5437, plain, (k2_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), k5_lattices('#skF_12'))=k2_lattices('#skF_12', k5_lattices('#skF_12'), k15_lattice3('#skF_12', k1_xboole_0)) | ~v6_lattices('#skF_12') | v2_struct_0('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_5385])).
% 22.41/11.41  tff(c_5438, plain, (k2_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), k5_lattices('#skF_12'))=k2_lattices('#skF_12', k5_lattices('#skF_12'), k15_lattice3('#skF_12', k1_xboole_0)) | ~v6_lattices('#skF_12')), inference(negUnitSimplification, [status(thm)], [c_118, c_5437])).
% 22.41/11.41  tff(c_5580, plain, (~v6_lattices('#skF_12')), inference(splitLeft, [status(thm)], [c_5438])).
% 22.41/11.41  tff(c_5665, plain, (~v10_lattices('#skF_12') | v2_struct_0('#skF_12') | ~l3_lattices('#skF_12')), inference(resolution, [status(thm)], [c_22, c_5580])).
% 22.41/11.41  tff(c_5668, plain, (v2_struct_0('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_116, c_5665])).
% 22.41/11.41  tff(c_5670, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_5668])).
% 22.41/11.41  tff(c_5672, plain, (v6_lattices('#skF_12')), inference(splitRight, [status(thm)], [c_5438])).
% 22.41/11.41  tff(c_76, plain, (![A_78, C_87, B_85]: (k2_lattices(A_78, C_87, B_85)=k2_lattices(A_78, B_85, C_87) | ~m1_subset_1(C_87, u1_struct_0(A_78)) | ~m1_subset_1(B_85, u1_struct_0(A_78)) | ~v6_lattices(A_78) | ~l1_lattices(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_203])).
% 22.41/11.41  tff(c_5387, plain, (![B_85]: (k2_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), B_85)=k2_lattices('#skF_12', B_85, k15_lattice3('#skF_12', k1_xboole_0)) | ~m1_subset_1(B_85, u1_struct_0('#skF_12')) | ~v6_lattices('#skF_12') | ~l1_lattices('#skF_12') | v2_struct_0('#skF_12'))), inference(resolution, [status(thm)], [c_5365, c_76])).
% 22.41/11.41  tff(c_5441, plain, (![B_85]: (k2_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), B_85)=k2_lattices('#skF_12', B_85, k15_lattice3('#skF_12', k1_xboole_0)) | ~m1_subset_1(B_85, u1_struct_0('#skF_12')) | ~v6_lattices('#skF_12') | v2_struct_0('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_5387])).
% 22.41/11.41  tff(c_5442, plain, (![B_85]: (k2_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), B_85)=k2_lattices('#skF_12', B_85, k15_lattice3('#skF_12', k1_xboole_0)) | ~m1_subset_1(B_85, u1_struct_0('#skF_12')) | ~v6_lattices('#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_118, c_5441])).
% 22.41/11.41  tff(c_5875, plain, (![B_877]: (k2_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), B_877)=k2_lattices('#skF_12', B_877, k15_lattice3('#skF_12', k1_xboole_0)) | ~m1_subset_1(B_877, u1_struct_0('#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_5672, c_5442])).
% 22.41/11.41  tff(c_5902, plain, (![B_42]: (k2_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), '#skF_5'('#skF_12', B_42))=k2_lattices('#skF_12', '#skF_5'('#skF_12', B_42), k15_lattice3('#skF_12', k1_xboole_0)) | v13_lattices('#skF_12') | ~m1_subset_1(B_42, u1_struct_0('#skF_12')) | ~l1_lattices('#skF_12') | v2_struct_0('#skF_12'))), inference(resolution, [status(thm)], [c_50, c_5875])).
% 22.41/11.41  tff(c_5947, plain, (![B_42]: (k2_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), '#skF_5'('#skF_12', B_42))=k2_lattices('#skF_12', '#skF_5'('#skF_12', B_42), k15_lattice3('#skF_12', k1_xboole_0)) | v13_lattices('#skF_12') | ~m1_subset_1(B_42, u1_struct_0('#skF_12')) | v2_struct_0('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_5902])).
% 22.41/11.41  tff(c_6201, plain, (![B_888]: (k2_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), '#skF_5'('#skF_12', B_888))=k2_lattices('#skF_12', '#skF_5'('#skF_12', B_888), k15_lattice3('#skF_12', k1_xboole_0)) | ~m1_subset_1(B_888, u1_struct_0('#skF_12')))), inference(negUnitSimplification, [status(thm)], [c_118, c_133, c_5947])).
% 22.41/11.41  tff(c_48, plain, (![A_33, B_42]: (k2_lattices(A_33, '#skF_5'(A_33, B_42), B_42)!=B_42 | k2_lattices(A_33, B_42, '#skF_5'(A_33, B_42))!=B_42 | v13_lattices(A_33) | ~m1_subset_1(B_42, u1_struct_0(A_33)) | ~l1_lattices(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_142])).
% 22.41/11.41  tff(c_6216, plain, (k2_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), '#skF_5'('#skF_12', k15_lattice3('#skF_12', k1_xboole_0)))!=k15_lattice3('#skF_12', k1_xboole_0) | k2_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), '#skF_5'('#skF_12', k15_lattice3('#skF_12', k1_xboole_0)))!=k15_lattice3('#skF_12', k1_xboole_0) | v13_lattices('#skF_12') | ~m1_subset_1(k15_lattice3('#skF_12', k1_xboole_0), u1_struct_0('#skF_12')) | ~l1_lattices('#skF_12') | v2_struct_0('#skF_12') | ~m1_subset_1(k15_lattice3('#skF_12', k1_xboole_0), u1_struct_0('#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_6201, c_48])).
% 22.41/11.41  tff(c_6242, plain, (k2_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), '#skF_5'('#skF_12', k15_lattice3('#skF_12', k1_xboole_0)))!=k15_lattice3('#skF_12', k1_xboole_0) | v13_lattices('#skF_12') | v2_struct_0('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_5365, c_127, c_5365, c_6216])).
% 22.41/11.41  tff(c_6243, plain, (k2_lattices('#skF_12', k15_lattice3('#skF_12', k1_xboole_0), '#skF_5'('#skF_12', k15_lattice3('#skF_12', k1_xboole_0)))!=k15_lattice3('#skF_12', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_118, c_133, c_6242])).
% 22.41/11.41  tff(c_7390, plain, (~m1_subset_1(k15_lattice3('#skF_12', k1_xboole_0), u1_struct_0('#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_7384, c_6243])).
% 22.41/11.41  tff(c_7411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5365, c_7390])).
% 22.41/11.41  tff(c_7413, plain, (v13_lattices('#skF_12')), inference(splitRight, [status(thm)], [c_121])).
% 22.41/11.41  tff(c_52, plain, (![A_33]: (m1_subset_1('#skF_4'(A_33), u1_struct_0(A_33)) | ~v13_lattices(A_33) | ~l1_lattices(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_142])).
% 22.41/11.41  tff(c_8193, plain, (![A_1082, C_1083]: (k2_lattices(A_1082, k5_lattices(A_1082), C_1083)=k5_lattices(A_1082) | ~m1_subset_1(C_1083, u1_struct_0(A_1082)) | ~m1_subset_1(k5_lattices(A_1082), u1_struct_0(A_1082)) | ~v13_lattices(A_1082) | ~l1_lattices(A_1082) | v2_struct_0(A_1082))), inference(cnfTransformation, [status(thm)], [f_93])).
% 22.41/11.41  tff(c_8224, plain, (![A_1084]: (k2_lattices(A_1084, k5_lattices(A_1084), '#skF_4'(A_1084))=k5_lattices(A_1084) | ~m1_subset_1(k5_lattices(A_1084), u1_struct_0(A_1084)) | ~v13_lattices(A_1084) | ~l1_lattices(A_1084) | v2_struct_0(A_1084))), inference(resolution, [status(thm)], [c_52, c_8193])).
% 22.41/11.41  tff(c_8228, plain, (![A_1085]: (k2_lattices(A_1085, k5_lattices(A_1085), '#skF_4'(A_1085))=k5_lattices(A_1085) | ~v13_lattices(A_1085) | ~l1_lattices(A_1085) | v2_struct_0(A_1085))), inference(resolution, [status(thm)], [c_38, c_8224])).
% 22.41/11.41  tff(c_7700, plain, (![A_993, C_994]: (k2_lattices(A_993, C_994, '#skF_4'(A_993))='#skF_4'(A_993) | ~m1_subset_1(C_994, u1_struct_0(A_993)) | ~v13_lattices(A_993) | ~l1_lattices(A_993) | v2_struct_0(A_993))), inference(cnfTransformation, [status(thm)], [f_142])).
% 22.41/11.41  tff(c_7718, plain, (![A_24]: (k2_lattices(A_24, k5_lattices(A_24), '#skF_4'(A_24))='#skF_4'(A_24) | ~v13_lattices(A_24) | ~l1_lattices(A_24) | v2_struct_0(A_24))), inference(resolution, [status(thm)], [c_38, c_7700])).
% 22.41/11.41  tff(c_8234, plain, (![A_1085]: (k5_lattices(A_1085)='#skF_4'(A_1085) | ~v13_lattices(A_1085) | ~l1_lattices(A_1085) | v2_struct_0(A_1085) | ~v13_lattices(A_1085) | ~l1_lattices(A_1085) | v2_struct_0(A_1085))), inference(superposition, [status(thm), theory('equality')], [c_8228, c_7718])).
% 22.41/11.42  tff(c_8287, plain, (![A_1089]: (k5_lattices(A_1089)='#skF_4'(A_1089) | ~v13_lattices(A_1089) | ~l1_lattices(A_1089) | v2_struct_0(A_1089))), inference(factorization, [status(thm), theory('equality')], [c_8234])).
% 22.41/11.42  tff(c_8290, plain, (k5_lattices('#skF_12')='#skF_4'('#skF_12') | ~v13_lattices('#skF_12') | ~l1_lattices('#skF_12')), inference(resolution, [status(thm)], [c_8287, c_118])).
% 22.41/11.42  tff(c_8293, plain, (k5_lattices('#skF_12')='#skF_4'('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_7413, c_8290])).
% 22.41/11.42  tff(c_7412, plain, (k15_lattice3('#skF_12', k1_xboole_0)!=k5_lattices('#skF_12')), inference(splitRight, [status(thm)], [c_121])).
% 22.41/11.42  tff(c_8294, plain, (k15_lattice3('#skF_12', k1_xboole_0)!='#skF_4'('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_8293, c_7412])).
% 22.41/11.42  tff(c_7416, plain, (![A_924, B_925, C_926]: (~r1_xboole_0(A_924, B_925) | ~r2_hidden(C_926, k3_xboole_0(A_924, B_925)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 22.41/11.42  tff(c_7441, plain, (![A_936, B_937, B_938]: (~r1_xboole_0(A_936, B_937) | r1_tarski(k3_xboole_0(A_936, B_937), B_938))), inference(resolution, [status(thm)], [c_6, c_7416])).
% 22.41/11.42  tff(c_7447, plain, (![A_939, B_940]: (k3_xboole_0(A_939, B_940)=k1_xboole_0 | ~r1_xboole_0(A_939, B_940))), inference(resolution, [status(thm)], [c_7441, c_12])).
% 22.41/11.42  tff(c_7456, plain, (![A_944]: (k3_xboole_0(A_944, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_7447])).
% 22.41/11.42  tff(c_7421, plain, (![A_924, B_925, B_2]: (~r1_xboole_0(A_924, B_925) | r1_tarski(k3_xboole_0(A_924, B_925), B_2))), inference(resolution, [status(thm)], [c_6, c_7416])).
% 22.41/11.42  tff(c_7461, plain, (![A_944, B_2]: (~r1_xboole_0(A_944, k1_xboole_0) | r1_tarski(k1_xboole_0, B_2))), inference(superposition, [status(thm), theory('equality')], [c_7456, c_7421])).
% 22.41/11.42  tff(c_7469, plain, (![B_2]: (r1_tarski(k1_xboole_0, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_7461])).
% 22.41/11.42  tff(c_7903, plain, (![A_1036, B_1037, C_1038]: (r2_hidden('#skF_11'(A_1036, B_1037, C_1038), C_1038) | ~r2_hidden(A_1036, a_2_5_lattice3(B_1037, C_1038)) | ~l3_lattices(B_1037) | ~v4_lattice3(B_1037) | ~v10_lattices(B_1037) | v2_struct_0(B_1037))), inference(cnfTransformation, [status(thm)], [f_233])).
% 22.41/11.42  tff(c_7464, plain, (![A_944, C_10]: (~r1_xboole_0(A_944, k1_xboole_0) | ~r2_hidden(C_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_7456, c_10])).
% 22.41/11.42  tff(c_7471, plain, (![C_10]: (~r2_hidden(C_10, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_7464])).
% 22.41/11.42  tff(c_7922, plain, (![A_1039, B_1040]: (~r2_hidden(A_1039, a_2_5_lattice3(B_1040, k1_xboole_0)) | ~l3_lattices(B_1040) | ~v4_lattice3(B_1040) | ~v10_lattices(B_1040) | v2_struct_0(B_1040))), inference(resolution, [status(thm)], [c_7903, c_7471])).
% 22.41/11.42  tff(c_7957, plain, (![B_1043, B_1044]: (~l3_lattices(B_1043) | ~v4_lattice3(B_1043) | ~v10_lattices(B_1043) | v2_struct_0(B_1043) | r1_tarski(a_2_5_lattice3(B_1043, k1_xboole_0), B_1044))), inference(resolution, [status(thm)], [c_6, c_7922])).
% 22.41/11.42  tff(c_7977, plain, (![B_1045]: (a_2_5_lattice3(B_1045, k1_xboole_0)=k1_xboole_0 | ~l3_lattices(B_1045) | ~v4_lattice3(B_1045) | ~v10_lattices(B_1045) | v2_struct_0(B_1045))), inference(resolution, [status(thm)], [c_7957, c_12])).
% 22.41/11.42  tff(c_7980, plain, (a_2_5_lattice3('#skF_12', k1_xboole_0)=k1_xboole_0 | ~l3_lattices('#skF_12') | ~v10_lattices('#skF_12') | v2_struct_0('#skF_12')), inference(resolution, [status(thm)], [c_114, c_7977])).
% 22.41/11.42  tff(c_7983, plain, (a_2_5_lattice3('#skF_12', k1_xboole_0)=k1_xboole_0 | v2_struct_0('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_112, c_7980])).
% 22.41/11.42  tff(c_7984, plain, (a_2_5_lattice3('#skF_12', k1_xboole_0)=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_118, c_7983])).
% 22.41/11.42  tff(c_8310, plain, (m1_subset_1('#skF_4'('#skF_12'), u1_struct_0('#skF_12')) | ~l1_lattices('#skF_12') | v2_struct_0('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_8293, c_38])).
% 22.41/11.42  tff(c_8326, plain, (m1_subset_1('#skF_4'('#skF_12'), u1_struct_0('#skF_12')) | v2_struct_0('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_8310])).
% 22.41/11.42  tff(c_8327, plain, (m1_subset_1('#skF_4'('#skF_12'), u1_struct_0('#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_118, c_8326])).
% 22.41/11.42  tff(c_9155, plain, (![A_1150, B_1151, C_1152]: (r1_lattices(A_1150, B_1151, C_1152) | k2_lattices(A_1150, B_1151, C_1152)!=B_1151 | ~m1_subset_1(C_1152, u1_struct_0(A_1150)) | ~m1_subset_1(B_1151, u1_struct_0(A_1150)) | ~l3_lattices(A_1150) | ~v9_lattices(A_1150) | ~v8_lattices(A_1150) | v2_struct_0(A_1150))), inference(cnfTransformation, [status(thm)], [f_125])).
% 22.41/11.42  tff(c_9157, plain, (![B_1151]: (r1_lattices('#skF_12', B_1151, '#skF_4'('#skF_12')) | k2_lattices('#skF_12', B_1151, '#skF_4'('#skF_12'))!=B_1151 | ~m1_subset_1(B_1151, u1_struct_0('#skF_12')) | ~l3_lattices('#skF_12') | ~v9_lattices('#skF_12') | ~v8_lattices('#skF_12') | v2_struct_0('#skF_12'))), inference(resolution, [status(thm)], [c_8327, c_9155])).
% 22.41/11.42  tff(c_9180, plain, (![B_1151]: (r1_lattices('#skF_12', B_1151, '#skF_4'('#skF_12')) | k2_lattices('#skF_12', B_1151, '#skF_4'('#skF_12'))!=B_1151 | ~m1_subset_1(B_1151, u1_struct_0('#skF_12')) | ~v9_lattices('#skF_12') | ~v8_lattices('#skF_12') | v2_struct_0('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_9157])).
% 22.41/11.42  tff(c_9181, plain, (![B_1151]: (r1_lattices('#skF_12', B_1151, '#skF_4'('#skF_12')) | k2_lattices('#skF_12', B_1151, '#skF_4'('#skF_12'))!=B_1151 | ~m1_subset_1(B_1151, u1_struct_0('#skF_12')) | ~v9_lattices('#skF_12') | ~v8_lattices('#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_118, c_9180])).
% 22.41/11.42  tff(c_9201, plain, (~v8_lattices('#skF_12')), inference(splitLeft, [status(thm)], [c_9181])).
% 22.41/11.42  tff(c_9204, plain, (~v10_lattices('#skF_12') | v2_struct_0('#skF_12') | ~l3_lattices('#skF_12')), inference(resolution, [status(thm)], [c_18, c_9201])).
% 22.41/11.42  tff(c_9207, plain, (v2_struct_0('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_116, c_9204])).
% 22.41/11.42  tff(c_9209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_9207])).
% 22.41/11.42  tff(c_9211, plain, (v8_lattices('#skF_12')), inference(splitRight, [status(thm)], [c_9181])).
% 22.41/11.42  tff(c_9210, plain, (![B_1151]: (~v9_lattices('#skF_12') | r1_lattices('#skF_12', B_1151, '#skF_4'('#skF_12')) | k2_lattices('#skF_12', B_1151, '#skF_4'('#skF_12'))!=B_1151 | ~m1_subset_1(B_1151, u1_struct_0('#skF_12')))), inference(splitRight, [status(thm)], [c_9181])).
% 22.41/11.42  tff(c_9213, plain, (~v9_lattices('#skF_12')), inference(splitLeft, [status(thm)], [c_9210])).
% 22.41/11.42  tff(c_9216, plain, (~v10_lattices('#skF_12') | v2_struct_0('#skF_12') | ~l3_lattices('#skF_12')), inference(resolution, [status(thm)], [c_16, c_9213])).
% 22.41/11.42  tff(c_9219, plain, (v2_struct_0('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_116, c_9216])).
% 22.41/11.42  tff(c_9221, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_9219])).
% 22.41/11.42  tff(c_9223, plain, (v9_lattices('#skF_12')), inference(splitRight, [status(thm)], [c_9210])).
% 22.41/11.42  tff(c_8360, plain, (![A_1090, C_1091, B_1092]: (k2_lattices(A_1090, C_1091, B_1092)=k2_lattices(A_1090, B_1092, C_1091) | ~m1_subset_1(C_1091, u1_struct_0(A_1090)) | ~m1_subset_1(B_1092, u1_struct_0(A_1090)) | ~v6_lattices(A_1090) | ~l1_lattices(A_1090) | v2_struct_0(A_1090))), inference(cnfTransformation, [status(thm)], [f_203])).
% 22.41/11.42  tff(c_8362, plain, (![B_1092]: (k2_lattices('#skF_12', B_1092, '#skF_4'('#skF_12'))=k2_lattices('#skF_12', '#skF_4'('#skF_12'), B_1092) | ~m1_subset_1(B_1092, u1_struct_0('#skF_12')) | ~v6_lattices('#skF_12') | ~l1_lattices('#skF_12') | v2_struct_0('#skF_12'))), inference(resolution, [status(thm)], [c_8327, c_8360])).
% 22.41/11.42  tff(c_8385, plain, (![B_1092]: (k2_lattices('#skF_12', B_1092, '#skF_4'('#skF_12'))=k2_lattices('#skF_12', '#skF_4'('#skF_12'), B_1092) | ~m1_subset_1(B_1092, u1_struct_0('#skF_12')) | ~v6_lattices('#skF_12') | v2_struct_0('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_8362])).
% 22.41/11.42  tff(c_8386, plain, (![B_1092]: (k2_lattices('#skF_12', B_1092, '#skF_4'('#skF_12'))=k2_lattices('#skF_12', '#skF_4'('#skF_12'), B_1092) | ~m1_subset_1(B_1092, u1_struct_0('#skF_12')) | ~v6_lattices('#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_118, c_8385])).
% 22.41/11.42  tff(c_8423, plain, (~v6_lattices('#skF_12')), inference(splitLeft, [status(thm)], [c_8386])).
% 22.41/11.42  tff(c_8426, plain, (~v10_lattices('#skF_12') | v2_struct_0('#skF_12') | ~l3_lattices('#skF_12')), inference(resolution, [status(thm)], [c_22, c_8423])).
% 22.41/11.42  tff(c_8429, plain, (v2_struct_0('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_116, c_8426])).
% 22.41/11.42  tff(c_8431, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_8429])).
% 22.41/11.42  tff(c_8434, plain, (![B_1096]: (k2_lattices('#skF_12', B_1096, '#skF_4'('#skF_12'))=k2_lattices('#skF_12', '#skF_4'('#skF_12'), B_1096) | ~m1_subset_1(B_1096, u1_struct_0('#skF_12')))), inference(splitRight, [status(thm)], [c_8386])).
% 22.41/11.42  tff(c_8473, plain, (![B_90]: (k2_lattices('#skF_12', k15_lattice3('#skF_12', B_90), '#skF_4'('#skF_12'))=k2_lattices('#skF_12', '#skF_4'('#skF_12'), k15_lattice3('#skF_12', B_90)) | ~l3_lattices('#skF_12') | v2_struct_0('#skF_12'))), inference(resolution, [status(thm)], [c_84, c_8434])).
% 22.41/11.42  tff(c_8514, plain, (![B_90]: (k2_lattices('#skF_12', k15_lattice3('#skF_12', B_90), '#skF_4'('#skF_12'))=k2_lattices('#skF_12', '#skF_4'('#skF_12'), k15_lattice3('#skF_12', B_90)) | v2_struct_0('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_8473])).
% 22.41/11.42  tff(c_8520, plain, (![B_1097]: (k2_lattices('#skF_12', k15_lattice3('#skF_12', B_1097), '#skF_4'('#skF_12'))=k2_lattices('#skF_12', '#skF_4'('#skF_12'), k15_lattice3('#skF_12', B_1097)))), inference(negUnitSimplification, [status(thm)], [c_118, c_8514])).
% 22.41/11.42  tff(c_7717, plain, (![A_89, B_90]: (k2_lattices(A_89, k15_lattice3(A_89, B_90), '#skF_4'(A_89))='#skF_4'(A_89) | ~v13_lattices(A_89) | ~l1_lattices(A_89) | ~l3_lattices(A_89) | v2_struct_0(A_89))), inference(resolution, [status(thm)], [c_84, c_7700])).
% 22.41/11.42  tff(c_8526, plain, (![B_1097]: (k2_lattices('#skF_12', '#skF_4'('#skF_12'), k15_lattice3('#skF_12', B_1097))='#skF_4'('#skF_12') | ~v13_lattices('#skF_12') | ~l1_lattices('#skF_12') | ~l3_lattices('#skF_12') | v2_struct_0('#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_8520, c_7717])).
% 22.41/11.42  tff(c_8544, plain, (![B_1097]: (k2_lattices('#skF_12', '#skF_4'('#skF_12'), k15_lattice3('#skF_12', B_1097))='#skF_4'('#skF_12') | v2_struct_0('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_127, c_7413, c_8526])).
% 22.41/11.42  tff(c_8545, plain, (![B_1097]: (k2_lattices('#skF_12', '#skF_4'('#skF_12'), k15_lattice3('#skF_12', B_1097))='#skF_4'('#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_118, c_8544])).
% 22.41/11.42  tff(c_8515, plain, (![B_90]: (k2_lattices('#skF_12', k15_lattice3('#skF_12', B_90), '#skF_4'('#skF_12'))=k2_lattices('#skF_12', '#skF_4'('#skF_12'), k15_lattice3('#skF_12', B_90)))), inference(negUnitSimplification, [status(thm)], [c_118, c_8514])).
% 22.41/11.42  tff(c_8556, plain, (![B_90]: (k2_lattices('#skF_12', k15_lattice3('#skF_12', B_90), '#skF_4'('#skF_12'))='#skF_4'('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_8545, c_8515])).
% 22.41/11.42  tff(c_7787, plain, (![A_1006, B_1007, C_1008]: (r2_hidden('#skF_6'(A_1006, B_1007, C_1008), C_1008) | r4_lattice3(A_1006, B_1007, C_1008) | ~m1_subset_1(B_1007, u1_struct_0(A_1006)) | ~l3_lattices(A_1006) | v2_struct_0(A_1006))), inference(cnfTransformation, [status(thm)], [f_160])).
% 22.41/11.42  tff(c_9078, plain, (![A_1139, B_1140, C_1141, B_1142]: (r2_hidden('#skF_6'(A_1139, B_1140, C_1141), B_1142) | ~r1_tarski(C_1141, B_1142) | r4_lattice3(A_1139, B_1140, C_1141) | ~m1_subset_1(B_1140, u1_struct_0(A_1139)) | ~l3_lattices(A_1139) | v2_struct_0(A_1139))), inference(resolution, [status(thm)], [c_7787, c_2])).
% 22.41/11.42  tff(c_9110, plain, (![C_1143, A_1144, B_1145]: (~r1_tarski(C_1143, k1_xboole_0) | r4_lattice3(A_1144, B_1145, C_1143) | ~m1_subset_1(B_1145, u1_struct_0(A_1144)) | ~l3_lattices(A_1144) | v2_struct_0(A_1144))), inference(resolution, [status(thm)], [c_9078, c_7471])).
% 22.41/11.42  tff(c_9112, plain, (![C_1143]: (~r1_tarski(C_1143, k1_xboole_0) | r4_lattice3('#skF_12', '#skF_4'('#skF_12'), C_1143) | ~l3_lattices('#skF_12') | v2_struct_0('#skF_12'))), inference(resolution, [status(thm)], [c_8327, c_9110])).
% 22.41/11.42  tff(c_9135, plain, (![C_1143]: (~r1_tarski(C_1143, k1_xboole_0) | r4_lattice3('#skF_12', '#skF_4'('#skF_12'), C_1143) | v2_struct_0('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_9112])).
% 22.41/11.42  tff(c_9136, plain, (![C_1143]: (~r1_tarski(C_1143, k1_xboole_0) | r4_lattice3('#skF_12', '#skF_4'('#skF_12'), C_1143))), inference(negUnitSimplification, [status(thm)], [c_118, c_9135])).
% 22.41/11.42  tff(c_10238, plain, (![A_1281, B_1282, D_1283]: (r1_lattices(A_1281, k15_lattice3(A_1281, B_1282), D_1283) | ~r4_lattice3(A_1281, D_1283, B_1282) | ~m1_subset_1(D_1283, u1_struct_0(A_1281)) | ~m1_subset_1(k15_lattice3(A_1281, B_1282), u1_struct_0(A_1281)) | ~v4_lattice3(A_1281) | ~v10_lattices(A_1281) | ~l3_lattices(A_1281) | v2_struct_0(A_1281))), inference(cnfTransformation, [status(thm)], [f_188])).
% 22.41/11.42  tff(c_10246, plain, (![A_1284, B_1285, D_1286]: (r1_lattices(A_1284, k15_lattice3(A_1284, B_1285), D_1286) | ~r4_lattice3(A_1284, D_1286, B_1285) | ~m1_subset_1(D_1286, u1_struct_0(A_1284)) | ~v4_lattice3(A_1284) | ~v10_lattices(A_1284) | ~l3_lattices(A_1284) | v2_struct_0(A_1284))), inference(resolution, [status(thm)], [c_84, c_10238])).
% 22.41/11.42  tff(c_36193, plain, (![A_2443, B_2444, D_2445]: (r1_lattices(A_2443, k15_lattice3(A_2443, B_2444), D_2445) | ~r4_lattice3(A_2443, D_2445, a_2_5_lattice3(A_2443, B_2444)) | ~m1_subset_1(D_2445, u1_struct_0(A_2443)) | ~v4_lattice3(A_2443) | ~v10_lattices(A_2443) | ~l3_lattices(A_2443) | v2_struct_0(A_2443) | ~l3_lattices(A_2443) | ~v4_lattice3(A_2443) | ~v10_lattices(A_2443) | v2_struct_0(A_2443))), inference(superposition, [status(thm), theory('equality')], [c_106, c_10246])).
% 22.41/11.42  tff(c_36273, plain, (![B_2444]: (r1_lattices('#skF_12', k15_lattice3('#skF_12', B_2444), '#skF_4'('#skF_12')) | ~m1_subset_1('#skF_4'('#skF_12'), u1_struct_0('#skF_12')) | ~l3_lattices('#skF_12') | ~v4_lattice3('#skF_12') | ~v10_lattices('#skF_12') | v2_struct_0('#skF_12') | ~r1_tarski(a_2_5_lattice3('#skF_12', B_2444), k1_xboole_0))), inference(resolution, [status(thm)], [c_9136, c_36193])).
% 22.41/11.42  tff(c_36306, plain, (![B_2444]: (r1_lattices('#skF_12', k15_lattice3('#skF_12', B_2444), '#skF_4'('#skF_12')) | v2_struct_0('#skF_12') | ~r1_tarski(a_2_5_lattice3('#skF_12', B_2444), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_114, c_112, c_8327, c_36273])).
% 22.41/11.42  tff(c_36312, plain, (![B_2446]: (r1_lattices('#skF_12', k15_lattice3('#skF_12', B_2446), '#skF_4'('#skF_12')) | ~r1_tarski(a_2_5_lattice3('#skF_12', B_2446), k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_118, c_36306])).
% 22.41/11.42  tff(c_36314, plain, (![B_2446]: (k2_lattices('#skF_12', k15_lattice3('#skF_12', B_2446), '#skF_4'('#skF_12'))=k15_lattice3('#skF_12', B_2446) | ~m1_subset_1('#skF_4'('#skF_12'), u1_struct_0('#skF_12')) | ~m1_subset_1(k15_lattice3('#skF_12', B_2446), u1_struct_0('#skF_12')) | ~l3_lattices('#skF_12') | ~v9_lattices('#skF_12') | ~v8_lattices('#skF_12') | v2_struct_0('#skF_12') | ~r1_tarski(a_2_5_lattice3('#skF_12', B_2446), k1_xboole_0))), inference(resolution, [status(thm)], [c_36312, c_46])).
% 22.41/11.42  tff(c_36329, plain, (![B_2446]: (k15_lattice3('#skF_12', B_2446)='#skF_4'('#skF_12') | ~m1_subset_1(k15_lattice3('#skF_12', B_2446), u1_struct_0('#skF_12')) | v2_struct_0('#skF_12') | ~r1_tarski(a_2_5_lattice3('#skF_12', B_2446), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_9211, c_9223, c_112, c_8327, c_8556, c_36314])).
% 22.41/11.42  tff(c_36392, plain, (![B_2452]: (k15_lattice3('#skF_12', B_2452)='#skF_4'('#skF_12') | ~m1_subset_1(k15_lattice3('#skF_12', B_2452), u1_struct_0('#skF_12')) | ~r1_tarski(a_2_5_lattice3('#skF_12', B_2452), k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_118, c_36329])).
% 22.41/11.42  tff(c_36408, plain, (![B_90]: (k15_lattice3('#skF_12', B_90)='#skF_4'('#skF_12') | ~r1_tarski(a_2_5_lattice3('#skF_12', B_90), k1_xboole_0) | ~l3_lattices('#skF_12') | v2_struct_0('#skF_12'))), inference(resolution, [status(thm)], [c_84, c_36392])).
% 22.41/11.42  tff(c_36420, plain, (![B_90]: (k15_lattice3('#skF_12', B_90)='#skF_4'('#skF_12') | ~r1_tarski(a_2_5_lattice3('#skF_12', B_90), k1_xboole_0) | v2_struct_0('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_36408])).
% 22.41/11.42  tff(c_36422, plain, (![B_2453]: (k15_lattice3('#skF_12', B_2453)='#skF_4'('#skF_12') | ~r1_tarski(a_2_5_lattice3('#skF_12', B_2453), k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_118, c_36420])).
% 22.41/11.42  tff(c_36529, plain, (k15_lattice3('#skF_12', k1_xboole_0)='#skF_4'('#skF_12') | ~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7984, c_36422])).
% 22.41/11.42  tff(c_36605, plain, (k15_lattice3('#skF_12', k1_xboole_0)='#skF_4'('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_7469, c_36529])).
% 22.41/11.42  tff(c_36607, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8294, c_36605])).
% 22.41/11.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.41/11.42  
% 22.41/11.42  Inference rules
% 22.41/11.42  ----------------------
% 22.41/11.42  #Ref     : 0
% 22.41/11.42  #Sup     : 7392
% 22.41/11.42  #Fact    : 4
% 22.41/11.42  #Define  : 0
% 22.41/11.42  #Split   : 78
% 22.41/11.42  #Chain   : 0
% 22.41/11.42  #Close   : 0
% 22.41/11.42  
% 22.41/11.42  Ordering : KBO
% 22.41/11.42  
% 22.41/11.42  Simplification rules
% 22.41/11.42  ----------------------
% 22.41/11.42  #Subsume      : 4063
% 22.41/11.42  #Demod        : 9431
% 22.41/11.42  #Tautology    : 2038
% 22.41/11.42  #SimpNegUnit  : 2891
% 22.41/11.42  #BackRed      : 559
% 22.41/11.42  
% 22.41/11.42  #Partial instantiations: 0
% 22.41/11.42  #Strategies tried      : 1
% 22.41/11.42  
% 22.41/11.42  Timing (in seconds)
% 22.41/11.42  ----------------------
% 22.41/11.42  Preprocessing        : 0.44
% 22.41/11.42  Parsing              : 0.21
% 22.41/11.42  CNF conversion       : 0.04
% 22.41/11.42  Main loop            : 10.16
% 22.41/11.42  Inferencing          : 2.16
% 22.41/11.42  Reduction            : 1.78
% 22.41/11.42  Demodulation         : 1.25
% 22.41/11.42  BG Simplification    : 0.15
% 22.41/11.42  Subsumption          : 5.69
% 22.41/11.42  Abstraction          : 0.26
% 22.41/11.42  MUC search           : 0.00
% 22.41/11.42  Cooper               : 0.00
% 22.41/11.42  Total                : 10.68
% 22.41/11.42  Index Insertion      : 0.00
% 22.41/11.42  Index Deletion       : 0.00
% 22.41/11.42  Index Matching       : 0.00
% 22.41/11.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
