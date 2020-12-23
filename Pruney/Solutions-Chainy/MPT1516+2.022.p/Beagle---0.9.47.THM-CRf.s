%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:54 EST 2020

% Result     : Theorem 15.95s
% Output     : CNFRefutation 16.17s
% Verified   : 
% Statistics : Number of formulae       :  274 (7120 expanded)
%              Number of leaves         :   61 (2532 expanded)
%              Depth                    :   35
%              Number of atoms          :  874 (32850 expanded)
%              Number of equality atoms :  100 (5154 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r1_lattices > r2_hidden > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v1_xboole_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k6_domain_1 > k16_lattice3 > k15_lattice3 > a_2_6_lattice3 > a_2_5_lattice3 > #nlpp > u1_struct_0 > k5_lattices > k1_xboole_0 > #skF_7 > #skF_4 > #skF_11 > #skF_1 > #skF_3 > #skF_9 > #skF_2 > #skF_8 > #skF_5 > #skF_6 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

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

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k16_lattice3,type,(
    k16_lattice3: ( $i * $i ) > $i )).

tff(k15_lattice3,type,(
    k15_lattice3: ( $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

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

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff(a_2_5_lattice3,type,(
    a_2_5_lattice3: ( $i * $i ) > $i )).

tff(v4_lattice3,type,(
    v4_lattice3: $i > $o )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

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

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(a_2_6_lattice3,type,(
    a_2_6_lattice3: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_274,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattice3)).

tff(f_72,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

tff(f_97,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_174,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k15_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_197,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_5_lattice3)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_227,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( k15_lattice3(A,B) = k15_lattice3(A,a_2_5_lattice3(A,B))
          & k16_lattice3(A,B) = k16_lattice3(A,a_2_6_lattice3(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_lattice3)).

tff(f_253,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B,C] :
          ( ! [D] :
              ( m1_subset_1(D,u1_struct_0(A))
             => ~ ( r2_hidden(D,B)
                  & ! [E] :
                      ( m1_subset_1(E,u1_struct_0(A))
                     => ~ ( r3_lattices(A,D,E)
                          & r2_hidden(E,C) ) ) ) )
         => r3_lattices(A,k15_lattice3(A,B),k15_lattice3(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_lattice3)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_lattices(A,B,C)
      <=> r1_lattices(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

tff(f_152,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_lattices)).

tff(f_213,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( k15_lattice3(A,k6_domain_1(u1_struct_0(A),B)) = B
            & k16_lattice3(A,k6_domain_1(u1_struct_0(A),B)) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_lattice3)).

tff(f_135,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).

tff(f_167,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => ( v6_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k2_lattices(A,B,C) = k2_lattices(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattices)).

tff(f_91,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_108,plain,(
    ~ v2_struct_0('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_274])).

tff(c_102,plain,(
    l3_lattices('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_274])).

tff(c_106,plain,(
    v10_lattices('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_274])).

tff(c_26,plain,(
    ! [A_14] :
      ( v6_lattices(A_14)
      | ~ v10_lattices(A_14)
      | v2_struct_0(A_14)
      | ~ l3_lattices(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_118,plain,(
    ! [A_97] :
      ( l1_lattices(A_97)
      | ~ l3_lattices(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_122,plain,(
    l1_lattices('#skF_11') ),
    inference(resolution,[status(thm)],[c_102,c_118])).

tff(c_72,plain,(
    ! [A_58,B_59] :
      ( m1_subset_1(k15_lattice3(A_58,B_59),u1_struct_0(A_58))
      | ~ l3_lattices(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_104,plain,(
    v4_lattice3('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_274])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_535,plain,(
    ! [A_183,B_184,C_185] :
      ( r2_hidden('#skF_9'(A_183,B_184,C_185),C_185)
      | ~ r2_hidden(A_183,a_2_5_lattice3(B_184,C_185))
      | ~ l3_lattices(B_184)
      | ~ v4_lattice3(B_184)
      | ~ v10_lattices(B_184)
      | v2_struct_0(B_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_552,plain,(
    ! [C_186,A_187,B_188] :
      ( ~ v1_xboole_0(C_186)
      | ~ r2_hidden(A_187,a_2_5_lattice3(B_188,C_186))
      | ~ l3_lattices(B_188)
      | ~ v4_lattice3(B_188)
      | ~ v10_lattices(B_188)
      | v2_struct_0(B_188) ) ),
    inference(resolution,[status(thm)],[c_535,c_2])).

tff(c_578,plain,(
    ! [C_189,B_190] :
      ( ~ v1_xboole_0(C_189)
      | ~ l3_lattices(B_190)
      | ~ v4_lattice3(B_190)
      | ~ v10_lattices(B_190)
      | v2_struct_0(B_190)
      | v1_xboole_0(a_2_5_lattice3(B_190,C_189)) ) ),
    inference(resolution,[status(thm)],[c_4,c_552])).

tff(c_149,plain,(
    ! [A_105,B_106] :
      ( r2_hidden('#skF_2'(A_105,B_106),A_105)
      | r1_tarski(A_105,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_158,plain,(
    ! [A_107,B_108] :
      ( ~ v1_xboole_0(A_107)
      | r1_tarski(A_107,B_108) ) ),
    inference(resolution,[status(thm)],[c_149,c_2])).

tff(c_16,plain,(
    ! [A_11] :
      ( k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_168,plain,(
    ! [A_107] :
      ( k1_xboole_0 = A_107
      | ~ v1_xboole_0(A_107) ) ),
    inference(resolution,[status(thm)],[c_158,c_16])).

tff(c_583,plain,(
    ! [B_191,C_192] :
      ( a_2_5_lattice3(B_191,C_192) = k1_xboole_0
      | ~ v1_xboole_0(C_192)
      | ~ l3_lattices(B_191)
      | ~ v4_lattice3(B_191)
      | ~ v10_lattices(B_191)
      | v2_struct_0(B_191) ) ),
    inference(resolution,[status(thm)],[c_578,c_168])).

tff(c_597,plain,(
    ! [B_196] :
      ( a_2_5_lattice3(B_196,k1_xboole_0) = k1_xboole_0
      | ~ l3_lattices(B_196)
      | ~ v4_lattice3(B_196)
      | ~ v10_lattices(B_196)
      | v2_struct_0(B_196) ) ),
    inference(resolution,[status(thm)],[c_12,c_583])).

tff(c_600,plain,
    ( a_2_5_lattice3('#skF_11',k1_xboole_0) = k1_xboole_0
    | ~ l3_lattices('#skF_11')
    | ~ v10_lattices('#skF_11')
    | v2_struct_0('#skF_11') ),
    inference(resolution,[status(thm)],[c_104,c_597])).

tff(c_603,plain,
    ( a_2_5_lattice3('#skF_11',k1_xboole_0) = k1_xboole_0
    | v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_102,c_600])).

tff(c_604,plain,(
    a_2_5_lattice3('#skF_11',k1_xboole_0) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_603])).

tff(c_90,plain,(
    ! [A_76,B_78] :
      ( k15_lattice3(A_76,a_2_5_lattice3(A_76,B_78)) = k15_lattice3(A_76,B_78)
      | ~ l3_lattices(A_76)
      | ~ v4_lattice3(A_76)
      | ~ v10_lattices(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_992,plain,(
    ! [A_227,B_228,C_229] :
      ( r2_hidden('#skF_10'(A_227,B_228,C_229),B_228)
      | r3_lattices(A_227,k15_lattice3(A_227,B_228),k15_lattice3(A_227,C_229))
      | ~ l3_lattices(A_227)
      | ~ v4_lattice3(A_227)
      | ~ v10_lattices(A_227)
      | v2_struct_0(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_76,plain,(
    ! [A_60,B_61,C_62] :
      ( r2_hidden('#skF_9'(A_60,B_61,C_62),C_62)
      | ~ r2_hidden(A_60,a_2_5_lattice3(B_61,C_62))
      | ~ l3_lattices(B_61)
      | ~ v4_lattice3(B_61)
      | ~ v10_lattices(B_61)
      | v2_struct_0(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_551,plain,(
    ! [C_185,A_183,B_184] :
      ( ~ v1_xboole_0(C_185)
      | ~ r2_hidden(A_183,a_2_5_lattice3(B_184,C_185))
      | ~ l3_lattices(B_184)
      | ~ v4_lattice3(B_184)
      | ~ v10_lattices(B_184)
      | v2_struct_0(B_184) ) ),
    inference(resolution,[status(thm)],[c_535,c_2])).

tff(c_611,plain,(
    ! [A_183] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_183,k1_xboole_0)
      | ~ l3_lattices('#skF_11')
      | ~ v4_lattice3('#skF_11')
      | ~ v10_lattices('#skF_11')
      | v2_struct_0('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_604,c_551])).

tff(c_624,plain,(
    ! [A_183] :
      ( ~ r2_hidden(A_183,k1_xboole_0)
      | v2_struct_0('#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_104,c_102,c_12,c_611])).

tff(c_634,plain,(
    ! [A_197] : ~ r2_hidden(A_197,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_624])).

tff(c_655,plain,(
    ! [A_60,B_61] :
      ( ~ r2_hidden(A_60,a_2_5_lattice3(B_61,k1_xboole_0))
      | ~ l3_lattices(B_61)
      | ~ v4_lattice3(B_61)
      | ~ v10_lattices(B_61)
      | v2_struct_0(B_61) ) ),
    inference(resolution,[status(thm)],[c_76,c_634])).

tff(c_1051,plain,(
    ! [B_233,A_234,C_235] :
      ( ~ l3_lattices(B_233)
      | ~ v4_lattice3(B_233)
      | ~ v10_lattices(B_233)
      | v2_struct_0(B_233)
      | r3_lattices(A_234,k15_lattice3(A_234,a_2_5_lattice3(B_233,k1_xboole_0)),k15_lattice3(A_234,C_235))
      | ~ l3_lattices(A_234)
      | ~ v4_lattice3(A_234)
      | ~ v10_lattices(A_234)
      | v2_struct_0(A_234) ) ),
    inference(resolution,[status(thm)],[c_992,c_655])).

tff(c_1054,plain,(
    ! [A_234,C_235] :
      ( ~ l3_lattices('#skF_11')
      | ~ v4_lattice3('#skF_11')
      | ~ v10_lattices('#skF_11')
      | v2_struct_0('#skF_11')
      | r3_lattices(A_234,k15_lattice3(A_234,k1_xboole_0),k15_lattice3(A_234,C_235))
      | ~ l3_lattices(A_234)
      | ~ v4_lattice3(A_234)
      | ~ v10_lattices(A_234)
      | v2_struct_0(A_234) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_604,c_1051])).

tff(c_1066,plain,(
    ! [A_234,C_235] :
      ( v2_struct_0('#skF_11')
      | r3_lattices(A_234,k15_lattice3(A_234,k1_xboole_0),k15_lattice3(A_234,C_235))
      | ~ l3_lattices(A_234)
      | ~ v4_lattice3(A_234)
      | ~ v10_lattices(A_234)
      | v2_struct_0(A_234) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_104,c_102,c_1054])).

tff(c_1067,plain,(
    ! [A_234,C_235] :
      ( r3_lattices(A_234,k15_lattice3(A_234,k1_xboole_0),k15_lattice3(A_234,C_235))
      | ~ l3_lattices(A_234)
      | ~ v4_lattice3(A_234)
      | ~ v10_lattices(A_234)
      | v2_struct_0(A_234) ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_1066])).

tff(c_2590,plain,(
    ! [A_379,B_380,C_381] :
      ( r1_lattices(A_379,B_380,C_381)
      | ~ r3_lattices(A_379,B_380,C_381)
      | ~ m1_subset_1(C_381,u1_struct_0(A_379))
      | ~ m1_subset_1(B_380,u1_struct_0(A_379))
      | ~ l3_lattices(A_379)
      | ~ v9_lattices(A_379)
      | ~ v8_lattices(A_379)
      | ~ v6_lattices(A_379)
      | v2_struct_0(A_379) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2692,plain,(
    ! [A_394,C_395] :
      ( r1_lattices(A_394,k15_lattice3(A_394,k1_xboole_0),k15_lattice3(A_394,C_395))
      | ~ m1_subset_1(k15_lattice3(A_394,C_395),u1_struct_0(A_394))
      | ~ m1_subset_1(k15_lattice3(A_394,k1_xboole_0),u1_struct_0(A_394))
      | ~ v9_lattices(A_394)
      | ~ v8_lattices(A_394)
      | ~ v6_lattices(A_394)
      | ~ l3_lattices(A_394)
      | ~ v4_lattice3(A_394)
      | ~ v10_lattices(A_394)
      | v2_struct_0(A_394) ) ),
    inference(resolution,[status(thm)],[c_1067,c_2590])).

tff(c_4538,plain,(
    ! [A_520,B_521] :
      ( r1_lattices(A_520,k15_lattice3(A_520,k1_xboole_0),k15_lattice3(A_520,B_521))
      | ~ m1_subset_1(k15_lattice3(A_520,a_2_5_lattice3(A_520,B_521)),u1_struct_0(A_520))
      | ~ m1_subset_1(k15_lattice3(A_520,k1_xboole_0),u1_struct_0(A_520))
      | ~ v9_lattices(A_520)
      | ~ v8_lattices(A_520)
      | ~ v6_lattices(A_520)
      | ~ l3_lattices(A_520)
      | ~ v4_lattice3(A_520)
      | ~ v10_lattices(A_520)
      | v2_struct_0(A_520)
      | ~ l3_lattices(A_520)
      | ~ v4_lattice3(A_520)
      | ~ v10_lattices(A_520)
      | v2_struct_0(A_520) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_2692])).

tff(c_4550,plain,
    ( r1_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),k15_lattice3('#skF_11',k1_xboole_0))
    | ~ m1_subset_1(k15_lattice3('#skF_11',k1_xboole_0),u1_struct_0('#skF_11'))
    | ~ m1_subset_1(k15_lattice3('#skF_11',k1_xboole_0),u1_struct_0('#skF_11'))
    | ~ v9_lattices('#skF_11')
    | ~ v8_lattices('#skF_11')
    | ~ v6_lattices('#skF_11')
    | ~ l3_lattices('#skF_11')
    | ~ v4_lattice3('#skF_11')
    | ~ v10_lattices('#skF_11')
    | v2_struct_0('#skF_11')
    | ~ l3_lattices('#skF_11')
    | ~ v4_lattice3('#skF_11')
    | ~ v10_lattices('#skF_11')
    | v2_struct_0('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_604,c_4538])).

tff(c_4559,plain,
    ( r1_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),k15_lattice3('#skF_11',k1_xboole_0))
    | ~ m1_subset_1(k15_lattice3('#skF_11',k1_xboole_0),u1_struct_0('#skF_11'))
    | ~ v9_lattices('#skF_11')
    | ~ v8_lattices('#skF_11')
    | ~ v6_lattices('#skF_11')
    | v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_104,c_102,c_106,c_104,c_102,c_4550])).

tff(c_4560,plain,
    ( r1_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),k15_lattice3('#skF_11',k1_xboole_0))
    | ~ m1_subset_1(k15_lattice3('#skF_11',k1_xboole_0),u1_struct_0('#skF_11'))
    | ~ v9_lattices('#skF_11')
    | ~ v8_lattices('#skF_11')
    | ~ v6_lattices('#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_4559])).

tff(c_4562,plain,(
    ~ v6_lattices('#skF_11') ),
    inference(splitLeft,[status(thm)],[c_4560])).

tff(c_4565,plain,
    ( ~ v10_lattices('#skF_11')
    | v2_struct_0('#skF_11')
    | ~ l3_lattices('#skF_11') ),
    inference(resolution,[status(thm)],[c_26,c_4562])).

tff(c_4568,plain,(
    v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_106,c_4565])).

tff(c_4570,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_4568])).

tff(c_4571,plain,
    ( ~ v8_lattices('#skF_11')
    | ~ v9_lattices('#skF_11')
    | ~ m1_subset_1(k15_lattice3('#skF_11',k1_xboole_0),u1_struct_0('#skF_11'))
    | r1_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),k15_lattice3('#skF_11',k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_4560])).

tff(c_4573,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_11',k1_xboole_0),u1_struct_0('#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_4571])).

tff(c_4576,plain,
    ( ~ l3_lattices('#skF_11')
    | v2_struct_0('#skF_11') ),
    inference(resolution,[status(thm)],[c_72,c_4573])).

tff(c_4579,plain,(
    v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_4576])).

tff(c_4581,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_4579])).

tff(c_4583,plain,(
    m1_subset_1(k15_lattice3('#skF_11',k1_xboole_0),u1_struct_0('#skF_11')) ),
    inference(splitRight,[status(thm)],[c_4571])).

tff(c_100,plain,
    ( k15_lattice3('#skF_11',k1_xboole_0) != k5_lattices('#skF_11')
    | ~ l3_lattices('#skF_11')
    | ~ v13_lattices('#skF_11')
    | ~ v10_lattices('#skF_11')
    | v2_struct_0('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_274])).

tff(c_110,plain,
    ( k15_lattice3('#skF_11',k1_xboole_0) != k5_lattices('#skF_11')
    | ~ v13_lattices('#skF_11')
    | v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_102,c_100])).

tff(c_111,plain,
    ( k15_lattice3('#skF_11',k1_xboole_0) != k5_lattices('#skF_11')
    | ~ v13_lattices('#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_110])).

tff(c_148,plain,(
    ~ v13_lattices('#skF_11') ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_56,plain,(
    ! [A_36,B_45] :
      ( m1_subset_1('#skF_5'(A_36,B_45),u1_struct_0(A_36))
      | v13_lattices(A_36)
      | ~ m1_subset_1(B_45,u1_struct_0(A_36))
      | ~ l1_lattices(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_22,plain,(
    ! [A_14] :
      ( v8_lattices(A_14)
      | ~ v10_lattices(A_14)
      | v2_struct_0(A_14)
      | ~ l3_lattices(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4582,plain,
    ( ~ v9_lattices('#skF_11')
    | ~ v8_lattices('#skF_11')
    | r1_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),k15_lattice3('#skF_11',k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_4571])).

tff(c_4652,plain,(
    ~ v8_lattices('#skF_11') ),
    inference(splitLeft,[status(thm)],[c_4582])).

tff(c_4655,plain,
    ( ~ v10_lattices('#skF_11')
    | v2_struct_0('#skF_11')
    | ~ l3_lattices('#skF_11') ),
    inference(resolution,[status(thm)],[c_22,c_4652])).

tff(c_4658,plain,(
    v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_106,c_4655])).

tff(c_4660,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_4658])).

tff(c_4662,plain,(
    v8_lattices('#skF_11') ),
    inference(splitRight,[status(thm)],[c_4582])).

tff(c_20,plain,(
    ! [A_14] :
      ( v9_lattices(A_14)
      | ~ v10_lattices(A_14)
      | v2_struct_0(A_14)
      | ~ l3_lattices(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4661,plain,
    ( ~ v9_lattices('#skF_11')
    | r1_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),k15_lattice3('#skF_11',k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_4582])).

tff(c_4669,plain,(
    ~ v9_lattices('#skF_11') ),
    inference(splitLeft,[status(thm)],[c_4661])).

tff(c_4703,plain,
    ( ~ v10_lattices('#skF_11')
    | v2_struct_0('#skF_11')
    | ~ l3_lattices('#skF_11') ),
    inference(resolution,[status(thm)],[c_20,c_4669])).

tff(c_4706,plain,(
    v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_106,c_4703])).

tff(c_4708,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_4706])).

tff(c_4710,plain,(
    v9_lattices('#skF_11') ),
    inference(splitRight,[status(thm)],[c_4661])).

tff(c_4572,plain,(
    v6_lattices('#skF_11') ),
    inference(splitRight,[status(thm)],[c_4560])).

tff(c_88,plain,(
    ! [A_73,B_75] :
      ( k15_lattice3(A_73,k6_domain_1(u1_struct_0(A_73),B_75)) = B_75
      | ~ m1_subset_1(B_75,u1_struct_0(A_73))
      | ~ l3_lattices(A_73)
      | ~ v4_lattice3(A_73)
      | ~ v10_lattices(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_625,plain,(
    ! [A_183] : ~ r2_hidden(A_183,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_624])).

tff(c_8728,plain,(
    ! [A_634,B_635,C_636] :
      ( r2_hidden('#skF_10'(A_634,a_2_5_lattice3(A_634,B_635),C_636),a_2_5_lattice3(A_634,B_635))
      | r3_lattices(A_634,k15_lattice3(A_634,B_635),k15_lattice3(A_634,C_636))
      | ~ l3_lattices(A_634)
      | ~ v4_lattice3(A_634)
      | ~ v10_lattices(A_634)
      | v2_struct_0(A_634)
      | ~ l3_lattices(A_634)
      | ~ v4_lattice3(A_634)
      | ~ v10_lattices(A_634)
      | v2_struct_0(A_634) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_992])).

tff(c_8784,plain,(
    ! [C_636] :
      ( r2_hidden('#skF_10'('#skF_11',k1_xboole_0,C_636),a_2_5_lattice3('#skF_11',k1_xboole_0))
      | r3_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),k15_lattice3('#skF_11',C_636))
      | ~ l3_lattices('#skF_11')
      | ~ v4_lattice3('#skF_11')
      | ~ v10_lattices('#skF_11')
      | v2_struct_0('#skF_11')
      | ~ l3_lattices('#skF_11')
      | ~ v4_lattice3('#skF_11')
      | ~ v10_lattices('#skF_11')
      | v2_struct_0('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_604,c_8728])).

tff(c_8803,plain,(
    ! [C_636] :
      ( r2_hidden('#skF_10'('#skF_11',k1_xboole_0,C_636),k1_xboole_0)
      | r3_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),k15_lattice3('#skF_11',C_636))
      | v2_struct_0('#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_104,c_102,c_106,c_104,c_102,c_604,c_8784])).

tff(c_8811,plain,(
    ! [C_637] : r3_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),k15_lattice3('#skF_11',C_637)) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_625,c_8803])).

tff(c_8817,plain,(
    ! [B_75] :
      ( r3_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),B_75)
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_11'))
      | ~ l3_lattices('#skF_11')
      | ~ v4_lattice3('#skF_11')
      | ~ v10_lattices('#skF_11')
      | v2_struct_0('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_8811])).

tff(c_8827,plain,(
    ! [B_75] :
      ( r3_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),B_75)
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_11'))
      | v2_struct_0('#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_104,c_102,c_8817])).

tff(c_8833,plain,(
    ! [B_638] :
      ( r3_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),B_638)
      | ~ m1_subset_1(B_638,u1_struct_0('#skF_11')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_8827])).

tff(c_48,plain,(
    ! [A_26,B_27,C_28] :
      ( r1_lattices(A_26,B_27,C_28)
      | ~ r3_lattices(A_26,B_27,C_28)
      | ~ m1_subset_1(C_28,u1_struct_0(A_26))
      | ~ m1_subset_1(B_27,u1_struct_0(A_26))
      | ~ l3_lattices(A_26)
      | ~ v9_lattices(A_26)
      | ~ v8_lattices(A_26)
      | ~ v6_lattices(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_8841,plain,(
    ! [B_638] :
      ( r1_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),B_638)
      | ~ m1_subset_1(k15_lattice3('#skF_11',k1_xboole_0),u1_struct_0('#skF_11'))
      | ~ l3_lattices('#skF_11')
      | ~ v9_lattices('#skF_11')
      | ~ v8_lattices('#skF_11')
      | ~ v6_lattices('#skF_11')
      | v2_struct_0('#skF_11')
      | ~ m1_subset_1(B_638,u1_struct_0('#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_8833,c_48])).

tff(c_8852,plain,(
    ! [B_638] :
      ( r1_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),B_638)
      | v2_struct_0('#skF_11')
      | ~ m1_subset_1(B_638,u1_struct_0('#skF_11')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4572,c_4662,c_4710,c_102,c_4583,c_8841])).

tff(c_8854,plain,(
    ! [B_639] :
      ( r1_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),B_639)
      | ~ m1_subset_1(B_639,u1_struct_0('#skF_11')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_8852])).

tff(c_52,plain,(
    ! [A_29,B_33,C_35] :
      ( k2_lattices(A_29,B_33,C_35) = B_33
      | ~ r1_lattices(A_29,B_33,C_35)
      | ~ m1_subset_1(C_35,u1_struct_0(A_29))
      | ~ m1_subset_1(B_33,u1_struct_0(A_29))
      | ~ l3_lattices(A_29)
      | ~ v9_lattices(A_29)
      | ~ v8_lattices(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_8856,plain,(
    ! [B_639] :
      ( k2_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),B_639) = k15_lattice3('#skF_11',k1_xboole_0)
      | ~ m1_subset_1(k15_lattice3('#skF_11',k1_xboole_0),u1_struct_0('#skF_11'))
      | ~ l3_lattices('#skF_11')
      | ~ v9_lattices('#skF_11')
      | ~ v8_lattices('#skF_11')
      | v2_struct_0('#skF_11')
      | ~ m1_subset_1(B_639,u1_struct_0('#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_8854,c_52])).

tff(c_8859,plain,(
    ! [B_639] :
      ( k2_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),B_639) = k15_lattice3('#skF_11',k1_xboole_0)
      | v2_struct_0('#skF_11')
      | ~ m1_subset_1(B_639,u1_struct_0('#skF_11')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4662,c_4710,c_102,c_4583,c_8856])).

tff(c_8861,plain,(
    ! [B_640] :
      ( k2_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),B_640) = k15_lattice3('#skF_11',k1_xboole_0)
      | ~ m1_subset_1(B_640,u1_struct_0('#skF_11')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_8859])).

tff(c_8891,plain,(
    ! [B_45] :
      ( k2_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),'#skF_5'('#skF_11',B_45)) = k15_lattice3('#skF_11',k1_xboole_0)
      | v13_lattices('#skF_11')
      | ~ m1_subset_1(B_45,u1_struct_0('#skF_11'))
      | ~ l1_lattices('#skF_11')
      | v2_struct_0('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_56,c_8861])).

tff(c_8933,plain,(
    ! [B_45] :
      ( k2_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),'#skF_5'('#skF_11',B_45)) = k15_lattice3('#skF_11',k1_xboole_0)
      | v13_lattices('#skF_11')
      | ~ m1_subset_1(B_45,u1_struct_0('#skF_11'))
      | v2_struct_0('#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_8891])).

tff(c_9419,plain,(
    ! [B_653] :
      ( k2_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),'#skF_5'('#skF_11',B_653)) = k15_lattice3('#skF_11',k1_xboole_0)
      | ~ m1_subset_1(B_653,u1_struct_0('#skF_11')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_148,c_8933])).

tff(c_1075,plain,(
    ! [A_238,C_239,B_240] :
      ( k2_lattices(A_238,C_239,B_240) = k2_lattices(A_238,B_240,C_239)
      | ~ m1_subset_1(C_239,u1_struct_0(A_238))
      | ~ m1_subset_1(B_240,u1_struct_0(A_238))
      | ~ v6_lattices(A_238)
      | ~ l1_lattices(A_238)
      | v2_struct_0(A_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_4941,plain,(
    ! [A_531,B_532,B_533] :
      ( k2_lattices(A_531,B_532,'#skF_5'(A_531,B_533)) = k2_lattices(A_531,'#skF_5'(A_531,B_533),B_532)
      | ~ m1_subset_1(B_532,u1_struct_0(A_531))
      | ~ v6_lattices(A_531)
      | v13_lattices(A_531)
      | ~ m1_subset_1(B_533,u1_struct_0(A_531))
      | ~ l1_lattices(A_531)
      | v2_struct_0(A_531) ) ),
    inference(resolution,[status(thm)],[c_56,c_1075])).

tff(c_4943,plain,(
    ! [B_533] :
      ( k2_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),'#skF_5'('#skF_11',B_533)) = k2_lattices('#skF_11','#skF_5'('#skF_11',B_533),k15_lattice3('#skF_11',k1_xboole_0))
      | ~ v6_lattices('#skF_11')
      | v13_lattices('#skF_11')
      | ~ m1_subset_1(B_533,u1_struct_0('#skF_11'))
      | ~ l1_lattices('#skF_11')
      | v2_struct_0('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_4583,c_4941])).

tff(c_4962,plain,(
    ! [B_533] :
      ( k2_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),'#skF_5'('#skF_11',B_533)) = k2_lattices('#skF_11','#skF_5'('#skF_11',B_533),k15_lattice3('#skF_11',k1_xboole_0))
      | v13_lattices('#skF_11')
      | ~ m1_subset_1(B_533,u1_struct_0('#skF_11'))
      | v2_struct_0('#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_4572,c_4943])).

tff(c_4972,plain,(
    ! [B_534] :
      ( k2_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),'#skF_5'('#skF_11',B_534)) = k2_lattices('#skF_11','#skF_5'('#skF_11',B_534),k15_lattice3('#skF_11',k1_xboole_0))
      | ~ m1_subset_1(B_534,u1_struct_0('#skF_11')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_148,c_4962])).

tff(c_54,plain,(
    ! [A_36,B_45] :
      ( k2_lattices(A_36,'#skF_5'(A_36,B_45),B_45) != B_45
      | k2_lattices(A_36,B_45,'#skF_5'(A_36,B_45)) != B_45
      | v13_lattices(A_36)
      | ~ m1_subset_1(B_45,u1_struct_0(A_36))
      | ~ l1_lattices(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_4981,plain,
    ( k2_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),'#skF_5'('#skF_11',k15_lattice3('#skF_11',k1_xboole_0))) != k15_lattice3('#skF_11',k1_xboole_0)
    | k2_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),'#skF_5'('#skF_11',k15_lattice3('#skF_11',k1_xboole_0))) != k15_lattice3('#skF_11',k1_xboole_0)
    | v13_lattices('#skF_11')
    | ~ m1_subset_1(k15_lattice3('#skF_11',k1_xboole_0),u1_struct_0('#skF_11'))
    | ~ l1_lattices('#skF_11')
    | v2_struct_0('#skF_11')
    | ~ m1_subset_1(k15_lattice3('#skF_11',k1_xboole_0),u1_struct_0('#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4972,c_54])).

tff(c_4991,plain,
    ( k2_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),'#skF_5'('#skF_11',k15_lattice3('#skF_11',k1_xboole_0))) != k15_lattice3('#skF_11',k1_xboole_0)
    | v13_lattices('#skF_11')
    | v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4583,c_122,c_4583,c_4981])).

tff(c_4992,plain,(
    k2_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),'#skF_5'('#skF_11',k15_lattice3('#skF_11',k1_xboole_0))) != k15_lattice3('#skF_11',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_148,c_4991])).

tff(c_9425,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_11',k1_xboole_0),u1_struct_0('#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9419,c_4992])).

tff(c_9439,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4583,c_9425])).

tff(c_9441,plain,(
    v13_lattices('#skF_11') ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_58,plain,(
    ! [A_36] :
      ( m1_subset_1('#skF_4'(A_36),u1_struct_0(A_36))
      | ~ v13_lattices(A_36)
      | ~ l1_lattices(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_9812,plain,(
    ! [A_728,B_729] :
      ( m1_subset_1('#skF_3'(A_728,B_729),u1_struct_0(A_728))
      | k5_lattices(A_728) = B_729
      | ~ m1_subset_1(B_729,u1_struct_0(A_728))
      | ~ v13_lattices(A_728)
      | ~ l1_lattices(A_728)
      | v2_struct_0(A_728) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_62,plain,(
    ! [A_36,C_44] :
      ( k2_lattices(A_36,'#skF_4'(A_36),C_44) = '#skF_4'(A_36)
      | ~ m1_subset_1(C_44,u1_struct_0(A_36))
      | ~ v13_lattices(A_36)
      | ~ l1_lattices(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_9818,plain,(
    ! [A_728,B_729] :
      ( k2_lattices(A_728,'#skF_4'(A_728),'#skF_3'(A_728,B_729)) = '#skF_4'(A_728)
      | k5_lattices(A_728) = B_729
      | ~ m1_subset_1(B_729,u1_struct_0(A_728))
      | ~ v13_lattices(A_728)
      | ~ l1_lattices(A_728)
      | v2_struct_0(A_728) ) ),
    inference(resolution,[status(thm)],[c_9812,c_62])).

tff(c_60,plain,(
    ! [A_36,C_44] :
      ( k2_lattices(A_36,C_44,'#skF_4'(A_36)) = '#skF_4'(A_36)
      | ~ m1_subset_1(C_44,u1_struct_0(A_36))
      | ~ v13_lattices(A_36)
      | ~ l1_lattices(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_9817,plain,(
    ! [A_728,B_729] :
      ( k2_lattices(A_728,'#skF_3'(A_728,B_729),'#skF_4'(A_728)) = '#skF_4'(A_728)
      | k5_lattices(A_728) = B_729
      | ~ m1_subset_1(B_729,u1_struct_0(A_728))
      | ~ v13_lattices(A_728)
      | ~ l1_lattices(A_728)
      | v2_struct_0(A_728) ) ),
    inference(resolution,[status(thm)],[c_9812,c_60])).

tff(c_12669,plain,(
    ! [A_971,B_972] :
      ( k2_lattices(A_971,'#skF_3'(A_971,B_972),B_972) != B_972
      | k2_lattices(A_971,B_972,'#skF_3'(A_971,B_972)) != B_972
      | k5_lattices(A_971) = B_972
      | ~ m1_subset_1(B_972,u1_struct_0(A_971))
      | ~ v13_lattices(A_971)
      | ~ l1_lattices(A_971)
      | v2_struct_0(A_971) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_12674,plain,(
    ! [A_973] :
      ( k2_lattices(A_973,'#skF_4'(A_973),'#skF_3'(A_973,'#skF_4'(A_973))) != '#skF_4'(A_973)
      | k5_lattices(A_973) = '#skF_4'(A_973)
      | ~ m1_subset_1('#skF_4'(A_973),u1_struct_0(A_973))
      | ~ v13_lattices(A_973)
      | ~ l1_lattices(A_973)
      | v2_struct_0(A_973) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9817,c_12669])).

tff(c_12680,plain,(
    ! [A_974] :
      ( k5_lattices(A_974) = '#skF_4'(A_974)
      | ~ m1_subset_1('#skF_4'(A_974),u1_struct_0(A_974))
      | ~ v13_lattices(A_974)
      | ~ l1_lattices(A_974)
      | v2_struct_0(A_974) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9818,c_12674])).

tff(c_12685,plain,(
    ! [A_975] :
      ( k5_lattices(A_975) = '#skF_4'(A_975)
      | ~ v13_lattices(A_975)
      | ~ l1_lattices(A_975)
      | v2_struct_0(A_975) ) ),
    inference(resolution,[status(thm)],[c_58,c_12680])).

tff(c_12688,plain,
    ( k5_lattices('#skF_11') = '#skF_4'('#skF_11')
    | ~ v13_lattices('#skF_11')
    | ~ l1_lattices('#skF_11') ),
    inference(resolution,[status(thm)],[c_12685,c_108])).

tff(c_12691,plain,(
    k5_lattices('#skF_11') = '#skF_4'('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_9441,c_12688])).

tff(c_9440,plain,(
    k15_lattice3('#skF_11',k1_xboole_0) != k5_lattices('#skF_11') ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_12692,plain,(
    k15_lattice3('#skF_11',k1_xboole_0) != '#skF_4'('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12691,c_9440])).

tff(c_10421,plain,(
    ! [A_795,C_796] :
      ( k2_lattices(A_795,C_796,k5_lattices(A_795)) = k5_lattices(A_795)
      | ~ m1_subset_1(C_796,u1_struct_0(A_795))
      | ~ m1_subset_1(k5_lattices(A_795),u1_struct_0(A_795))
      | ~ v13_lattices(A_795)
      | ~ l1_lattices(A_795)
      | v2_struct_0(A_795) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_10443,plain,(
    ! [A_36] :
      ( k2_lattices(A_36,'#skF_4'(A_36),k5_lattices(A_36)) = k5_lattices(A_36)
      | ~ m1_subset_1(k5_lattices(A_36),u1_struct_0(A_36))
      | ~ v13_lattices(A_36)
      | ~ l1_lattices(A_36)
      | v2_struct_0(A_36) ) ),
    inference(resolution,[status(thm)],[c_58,c_10421])).

tff(c_12703,plain,
    ( k2_lattices('#skF_11','#skF_4'('#skF_11'),k5_lattices('#skF_11')) = k5_lattices('#skF_11')
    | ~ m1_subset_1('#skF_4'('#skF_11'),u1_struct_0('#skF_11'))
    | ~ v13_lattices('#skF_11')
    | ~ l1_lattices('#skF_11')
    | v2_struct_0('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_12691,c_10443])).

tff(c_12725,plain,
    ( k2_lattices('#skF_11','#skF_4'('#skF_11'),'#skF_4'('#skF_11')) = '#skF_4'('#skF_11')
    | ~ m1_subset_1('#skF_4'('#skF_11'),u1_struct_0('#skF_11'))
    | v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_9441,c_12691,c_12691,c_12703])).

tff(c_12726,plain,
    ( k2_lattices('#skF_11','#skF_4'('#skF_11'),'#skF_4'('#skF_11')) = '#skF_4'('#skF_11')
    | ~ m1_subset_1('#skF_4'('#skF_11'),u1_struct_0('#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_12725])).

tff(c_12737,plain,(
    ~ m1_subset_1('#skF_4'('#skF_11'),u1_struct_0('#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_12726])).

tff(c_12740,plain,
    ( ~ v13_lattices('#skF_11')
    | ~ l1_lattices('#skF_11')
    | v2_struct_0('#skF_11') ),
    inference(resolution,[status(thm)],[c_58,c_12737])).

tff(c_12743,plain,(
    v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_9441,c_12740])).

tff(c_12745,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_12743])).

tff(c_12747,plain,(
    m1_subset_1('#skF_4'('#skF_11'),u1_struct_0('#skF_11')) ),
    inference(splitRight,[status(thm)],[c_12726])).

tff(c_10445,plain,(
    ! [A_58,B_59] :
      ( k2_lattices(A_58,k15_lattice3(A_58,B_59),k5_lattices(A_58)) = k5_lattices(A_58)
      | ~ m1_subset_1(k5_lattices(A_58),u1_struct_0(A_58))
      | ~ v13_lattices(A_58)
      | ~ l1_lattices(A_58)
      | ~ l3_lattices(A_58)
      | v2_struct_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_72,c_10421])).

tff(c_12695,plain,(
    ! [B_59] :
      ( k2_lattices('#skF_11',k15_lattice3('#skF_11',B_59),k5_lattices('#skF_11')) = k5_lattices('#skF_11')
      | ~ m1_subset_1('#skF_4'('#skF_11'),u1_struct_0('#skF_11'))
      | ~ v13_lattices('#skF_11')
      | ~ l1_lattices('#skF_11')
      | ~ l3_lattices('#skF_11')
      | v2_struct_0('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12691,c_10445])).

tff(c_12713,plain,(
    ! [B_59] :
      ( k2_lattices('#skF_11',k15_lattice3('#skF_11',B_59),'#skF_4'('#skF_11')) = '#skF_4'('#skF_11')
      | ~ m1_subset_1('#skF_4'('#skF_11'),u1_struct_0('#skF_11'))
      | v2_struct_0('#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_122,c_9441,c_12691,c_12691,c_12695])).

tff(c_12714,plain,(
    ! [B_59] :
      ( k2_lattices('#skF_11',k15_lattice3('#skF_11',B_59),'#skF_4'('#skF_11')) = '#skF_4'('#skF_11')
      | ~ m1_subset_1('#skF_4'('#skF_11'),u1_struct_0('#skF_11')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_12713])).

tff(c_12964,plain,(
    ! [B_59] : k2_lattices('#skF_11',k15_lattice3('#skF_11',B_59),'#skF_4'('#skF_11')) = '#skF_4'('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12747,c_12714])).

tff(c_50,plain,(
    ! [A_29,B_33,C_35] :
      ( r1_lattices(A_29,B_33,C_35)
      | k2_lattices(A_29,B_33,C_35) != B_33
      | ~ m1_subset_1(C_35,u1_struct_0(A_29))
      | ~ m1_subset_1(B_33,u1_struct_0(A_29))
      | ~ l3_lattices(A_29)
      | ~ v9_lattices(A_29)
      | ~ v8_lattices(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_12753,plain,(
    ! [B_33] :
      ( r1_lattices('#skF_11',B_33,'#skF_4'('#skF_11'))
      | k2_lattices('#skF_11',B_33,'#skF_4'('#skF_11')) != B_33
      | ~ m1_subset_1(B_33,u1_struct_0('#skF_11'))
      | ~ l3_lattices('#skF_11')
      | ~ v9_lattices('#skF_11')
      | ~ v8_lattices('#skF_11')
      | v2_struct_0('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_12747,c_50])).

tff(c_12776,plain,(
    ! [B_33] :
      ( r1_lattices('#skF_11',B_33,'#skF_4'('#skF_11'))
      | k2_lattices('#skF_11',B_33,'#skF_4'('#skF_11')) != B_33
      | ~ m1_subset_1(B_33,u1_struct_0('#skF_11'))
      | ~ v9_lattices('#skF_11')
      | ~ v8_lattices('#skF_11')
      | v2_struct_0('#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_12753])).

tff(c_12777,plain,(
    ! [B_33] :
      ( r1_lattices('#skF_11',B_33,'#skF_4'('#skF_11'))
      | k2_lattices('#skF_11',B_33,'#skF_4'('#skF_11')) != B_33
      | ~ m1_subset_1(B_33,u1_struct_0('#skF_11'))
      | ~ v9_lattices('#skF_11')
      | ~ v8_lattices('#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_12776])).

tff(c_13318,plain,(
    ~ v8_lattices('#skF_11') ),
    inference(splitLeft,[status(thm)],[c_12777])).

tff(c_13321,plain,
    ( ~ v10_lattices('#skF_11')
    | v2_struct_0('#skF_11')
    | ~ l3_lattices('#skF_11') ),
    inference(resolution,[status(thm)],[c_22,c_13318])).

tff(c_13324,plain,(
    v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_106,c_13321])).

tff(c_13326,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_13324])).

tff(c_13328,plain,(
    v8_lattices('#skF_11') ),
    inference(splitRight,[status(thm)],[c_12777])).

tff(c_13327,plain,(
    ! [B_33] :
      ( ~ v9_lattices('#skF_11')
      | r1_lattices('#skF_11',B_33,'#skF_4'('#skF_11'))
      | k2_lattices('#skF_11',B_33,'#skF_4'('#skF_11')) != B_33
      | ~ m1_subset_1(B_33,u1_struct_0('#skF_11')) ) ),
    inference(splitRight,[status(thm)],[c_12777])).

tff(c_13343,plain,(
    ~ v9_lattices('#skF_11') ),
    inference(splitLeft,[status(thm)],[c_13327])).

tff(c_13346,plain,
    ( ~ v10_lattices('#skF_11')
    | v2_struct_0('#skF_11')
    | ~ l3_lattices('#skF_11') ),
    inference(resolution,[status(thm)],[c_20,c_13343])).

tff(c_13349,plain,(
    v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_106,c_13346])).

tff(c_13351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_13349])).

tff(c_13353,plain,(
    v9_lattices('#skF_11') ),
    inference(splitRight,[status(thm)],[c_13327])).

tff(c_70,plain,(
    ! [A_47] :
      ( m1_subset_1('#skF_6'(A_47),u1_struct_0(A_47))
      | v6_lattices(A_47)
      | ~ l1_lattices(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_10310,plain,(
    ! [A_779,C_780] :
      ( k2_lattices(A_779,k5_lattices(A_779),C_780) = k5_lattices(A_779)
      | ~ m1_subset_1(C_780,u1_struct_0(A_779))
      | ~ m1_subset_1(k5_lattices(A_779),u1_struct_0(A_779))
      | ~ v13_lattices(A_779)
      | ~ l1_lattices(A_779)
      | v2_struct_0(A_779) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_10334,plain,(
    ! [A_58,B_59] :
      ( k2_lattices(A_58,k5_lattices(A_58),k15_lattice3(A_58,B_59)) = k5_lattices(A_58)
      | ~ m1_subset_1(k5_lattices(A_58),u1_struct_0(A_58))
      | ~ v13_lattices(A_58)
      | ~ l1_lattices(A_58)
      | ~ l3_lattices(A_58)
      | v2_struct_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_72,c_10310])).

tff(c_12697,plain,(
    ! [B_59] :
      ( k2_lattices('#skF_11',k5_lattices('#skF_11'),k15_lattice3('#skF_11',B_59)) = k5_lattices('#skF_11')
      | ~ m1_subset_1('#skF_4'('#skF_11'),u1_struct_0('#skF_11'))
      | ~ v13_lattices('#skF_11')
      | ~ l1_lattices('#skF_11')
      | ~ l3_lattices('#skF_11')
      | v2_struct_0('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12691,c_10334])).

tff(c_12716,plain,(
    ! [B_59] :
      ( k2_lattices('#skF_11','#skF_4'('#skF_11'),k15_lattice3('#skF_11',B_59)) = '#skF_4'('#skF_11')
      | ~ m1_subset_1('#skF_4'('#skF_11'),u1_struct_0('#skF_11'))
      | v2_struct_0('#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_122,c_9441,c_12691,c_12691,c_12697])).

tff(c_12717,plain,(
    ! [B_59] :
      ( k2_lattices('#skF_11','#skF_4'('#skF_11'),k15_lattice3('#skF_11',B_59)) = '#skF_4'('#skF_11')
      | ~ m1_subset_1('#skF_4'('#skF_11'),u1_struct_0('#skF_11')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_12716])).

tff(c_12854,plain,(
    ! [B_980] : k2_lattices('#skF_11','#skF_4'('#skF_11'),k15_lattice3('#skF_11',B_980)) = '#skF_4'('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12747,c_12717])).

tff(c_12865,plain,(
    ! [B_75] :
      ( k2_lattices('#skF_11','#skF_4'('#skF_11'),B_75) = '#skF_4'('#skF_11')
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_11'))
      | ~ l3_lattices('#skF_11')
      | ~ v4_lattice3('#skF_11')
      | ~ v10_lattices('#skF_11')
      | v2_struct_0('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_12854])).

tff(c_12881,plain,(
    ! [B_75] :
      ( k2_lattices('#skF_11','#skF_4'('#skF_11'),B_75) = '#skF_4'('#skF_11')
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_11'))
      | v2_struct_0('#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_104,c_102,c_12865])).

tff(c_12890,plain,(
    ! [B_981] :
      ( k2_lattices('#skF_11','#skF_4'('#skF_11'),B_981) = '#skF_4'('#skF_11')
      | ~ m1_subset_1(B_981,u1_struct_0('#skF_11')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_12881])).

tff(c_12913,plain,
    ( k2_lattices('#skF_11','#skF_4'('#skF_11'),'#skF_6'('#skF_11')) = '#skF_4'('#skF_11')
    | v6_lattices('#skF_11')
    | ~ l1_lattices('#skF_11')
    | v2_struct_0('#skF_11') ),
    inference(resolution,[status(thm)],[c_70,c_12890])).

tff(c_12946,plain,
    ( k2_lattices('#skF_11','#skF_4'('#skF_11'),'#skF_6'('#skF_11')) = '#skF_4'('#skF_11')
    | v6_lattices('#skF_11')
    | v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_12913])).

tff(c_12947,plain,
    ( k2_lattices('#skF_11','#skF_4'('#skF_11'),'#skF_6'('#skF_11')) = '#skF_4'('#skF_11')
    | v6_lattices('#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_12946])).

tff(c_12960,plain,(
    v6_lattices('#skF_11') ),
    inference(splitLeft,[status(thm)],[c_12947])).

tff(c_14,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_9819,plain,(
    ! [A_730,B_731,C_732] :
      ( r2_hidden('#skF_9'(A_730,B_731,C_732),C_732)
      | ~ r2_hidden(A_730,a_2_5_lattice3(B_731,C_732))
      | ~ l3_lattices(B_731)
      | ~ v4_lattice3(B_731)
      | ~ v10_lattices(B_731)
      | v2_struct_0(B_731) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_9836,plain,(
    ! [C_733,A_734,B_735] :
      ( ~ v1_xboole_0(C_733)
      | ~ r2_hidden(A_734,a_2_5_lattice3(B_735,C_733))
      | ~ l3_lattices(B_735)
      | ~ v4_lattice3(B_735)
      | ~ v10_lattices(B_735)
      | v2_struct_0(B_735) ) ),
    inference(resolution,[status(thm)],[c_9819,c_2])).

tff(c_9862,plain,(
    ! [C_736,B_737] :
      ( ~ v1_xboole_0(C_736)
      | ~ l3_lattices(B_737)
      | ~ v4_lattice3(B_737)
      | ~ v10_lattices(B_737)
      | v2_struct_0(B_737)
      | v1_xboole_0(a_2_5_lattice3(B_737,C_736)) ) ),
    inference(resolution,[status(thm)],[c_4,c_9836])).

tff(c_9448,plain,(
    ! [A_661,B_662] :
      ( r2_hidden('#skF_2'(A_661,B_662),A_661)
      | r1_tarski(A_661,B_662) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_9470,plain,(
    ! [A_665,B_666] :
      ( ~ v1_xboole_0(A_665)
      | r1_tarski(A_665,B_666) ) ),
    inference(resolution,[status(thm)],[c_9448,c_2])).

tff(c_9480,plain,(
    ! [A_665] :
      ( k1_xboole_0 = A_665
      | ~ v1_xboole_0(A_665) ) ),
    inference(resolution,[status(thm)],[c_9470,c_16])).

tff(c_9867,plain,(
    ! [B_738,C_739] :
      ( a_2_5_lattice3(B_738,C_739) = k1_xboole_0
      | ~ v1_xboole_0(C_739)
      | ~ l3_lattices(B_738)
      | ~ v4_lattice3(B_738)
      | ~ v10_lattices(B_738)
      | v2_struct_0(B_738) ) ),
    inference(resolution,[status(thm)],[c_9862,c_9480])).

tff(c_9883,plain,(
    ! [B_742] :
      ( a_2_5_lattice3(B_742,k1_xboole_0) = k1_xboole_0
      | ~ l3_lattices(B_742)
      | ~ v4_lattice3(B_742)
      | ~ v10_lattices(B_742)
      | v2_struct_0(B_742) ) ),
    inference(resolution,[status(thm)],[c_12,c_9867])).

tff(c_9886,plain,
    ( a_2_5_lattice3('#skF_11',k1_xboole_0) = k1_xboole_0
    | ~ l3_lattices('#skF_11')
    | ~ v10_lattices('#skF_11')
    | v2_struct_0('#skF_11') ),
    inference(resolution,[status(thm)],[c_104,c_9883])).

tff(c_9889,plain,
    ( a_2_5_lattice3('#skF_11',k1_xboole_0) = k1_xboole_0
    | v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_102,c_9886])).

tff(c_9890,plain,(
    a_2_5_lattice3('#skF_11',k1_xboole_0) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_9889])).

tff(c_10335,plain,(
    ! [A_781,B_782,C_783] :
      ( r2_hidden('#skF_10'(A_781,B_782,C_783),B_782)
      | r3_lattices(A_781,k15_lattice3(A_781,B_782),k15_lattice3(A_781,C_783))
      | ~ l3_lattices(A_781)
      | ~ v4_lattice3(A_781)
      | ~ v10_lattices(A_781)
      | v2_struct_0(A_781) ) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_21146,plain,(
    ! [A_1300,B_1301,B_1302] :
      ( r2_hidden('#skF_10'(A_1300,B_1301,a_2_5_lattice3(A_1300,B_1302)),B_1301)
      | r3_lattices(A_1300,k15_lattice3(A_1300,B_1301),k15_lattice3(A_1300,B_1302))
      | ~ l3_lattices(A_1300)
      | ~ v4_lattice3(A_1300)
      | ~ v10_lattices(A_1300)
      | v2_struct_0(A_1300)
      | ~ l3_lattices(A_1300)
      | ~ v4_lattice3(A_1300)
      | ~ v10_lattices(A_1300)
      | v2_struct_0(A_1300) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_10335])).

tff(c_21200,plain,(
    ! [B_1301] :
      ( r2_hidden('#skF_10'('#skF_11',B_1301,k1_xboole_0),B_1301)
      | r3_lattices('#skF_11',k15_lattice3('#skF_11',B_1301),k15_lattice3('#skF_11',k1_xboole_0))
      | ~ l3_lattices('#skF_11')
      | ~ v4_lattice3('#skF_11')
      | ~ v10_lattices('#skF_11')
      | v2_struct_0('#skF_11')
      | ~ l3_lattices('#skF_11')
      | ~ v4_lattice3('#skF_11')
      | ~ v10_lattices('#skF_11')
      | v2_struct_0('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9890,c_21146])).

tff(c_21222,plain,(
    ! [B_1301] :
      ( r2_hidden('#skF_10'('#skF_11',B_1301,k1_xboole_0),B_1301)
      | r3_lattices('#skF_11',k15_lattice3('#skF_11',B_1301),k15_lattice3('#skF_11',k1_xboole_0))
      | v2_struct_0('#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_104,c_102,c_106,c_104,c_102,c_21200])).

tff(c_21224,plain,(
    ! [B_1303] :
      ( r2_hidden('#skF_10'('#skF_11',B_1303,k1_xboole_0),B_1303)
      | r3_lattices('#skF_11',k15_lattice3('#skF_11',B_1303),k15_lattice3('#skF_11',k1_xboole_0)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_21222])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( ~ r1_tarski(B_13,A_12)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_21353,plain,(
    ! [B_1307] :
      ( ~ r1_tarski(B_1307,'#skF_10'('#skF_11',B_1307,k1_xboole_0))
      | r3_lattices('#skF_11',k15_lattice3('#skF_11',B_1307),k15_lattice3('#skF_11',k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_21224,c_18])).

tff(c_21425,plain,(
    r3_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),k15_lattice3('#skF_11',k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_14,c_21353])).

tff(c_21427,plain,
    ( r1_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),k15_lattice3('#skF_11',k1_xboole_0))
    | ~ m1_subset_1(k15_lattice3('#skF_11',k1_xboole_0),u1_struct_0('#skF_11'))
    | ~ l3_lattices('#skF_11')
    | ~ v9_lattices('#skF_11')
    | ~ v8_lattices('#skF_11')
    | ~ v6_lattices('#skF_11')
    | v2_struct_0('#skF_11') ),
    inference(resolution,[status(thm)],[c_21425,c_48])).

tff(c_21430,plain,
    ( r1_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),k15_lattice3('#skF_11',k1_xboole_0))
    | ~ m1_subset_1(k15_lattice3('#skF_11',k1_xboole_0),u1_struct_0('#skF_11'))
    | v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12960,c_13328,c_13353,c_102,c_21427])).

tff(c_21431,plain,
    ( r1_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),k15_lattice3('#skF_11',k1_xboole_0))
    | ~ m1_subset_1(k15_lattice3('#skF_11',k1_xboole_0),u1_struct_0('#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_21430])).

tff(c_21432,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_11',k1_xboole_0),u1_struct_0('#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_21431])).

tff(c_21435,plain,
    ( ~ l3_lattices('#skF_11')
    | v2_struct_0('#skF_11') ),
    inference(resolution,[status(thm)],[c_72,c_21432])).

tff(c_21438,plain,(
    v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_21435])).

tff(c_21440,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_21438])).

tff(c_21442,plain,(
    m1_subset_1(k15_lattice3('#skF_11',k1_xboole_0),u1_struct_0('#skF_11')) ),
    inference(splitRight,[status(thm)],[c_21431])).

tff(c_9835,plain,(
    ! [C_732,A_730,B_731] :
      ( ~ v1_xboole_0(C_732)
      | ~ r2_hidden(A_730,a_2_5_lattice3(B_731,C_732))
      | ~ l3_lattices(B_731)
      | ~ v4_lattice3(B_731)
      | ~ v10_lattices(B_731)
      | v2_struct_0(B_731) ) ),
    inference(resolution,[status(thm)],[c_9819,c_2])).

tff(c_9897,plain,(
    ! [A_730] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_730,k1_xboole_0)
      | ~ l3_lattices('#skF_11')
      | ~ v4_lattice3('#skF_11')
      | ~ v10_lattices('#skF_11')
      | v2_struct_0('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9890,c_9835])).

tff(c_9910,plain,(
    ! [A_730] :
      ( ~ r2_hidden(A_730,k1_xboole_0)
      | v2_struct_0('#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_104,c_102,c_12,c_9897])).

tff(c_9911,plain,(
    ! [A_730] : ~ r2_hidden(A_730,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_9910])).

tff(c_23066,plain,(
    ! [A_1348,B_1349,C_1350] :
      ( r2_hidden('#skF_10'(A_1348,a_2_5_lattice3(A_1348,B_1349),C_1350),a_2_5_lattice3(A_1348,B_1349))
      | r3_lattices(A_1348,k15_lattice3(A_1348,B_1349),k15_lattice3(A_1348,C_1350))
      | ~ l3_lattices(A_1348)
      | ~ v4_lattice3(A_1348)
      | ~ v10_lattices(A_1348)
      | v2_struct_0(A_1348)
      | ~ l3_lattices(A_1348)
      | ~ v4_lattice3(A_1348)
      | ~ v10_lattices(A_1348)
      | v2_struct_0(A_1348) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_10335])).

tff(c_23122,plain,(
    ! [C_1350] :
      ( r2_hidden('#skF_10'('#skF_11',k1_xboole_0,C_1350),a_2_5_lattice3('#skF_11',k1_xboole_0))
      | r3_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),k15_lattice3('#skF_11',C_1350))
      | ~ l3_lattices('#skF_11')
      | ~ v4_lattice3('#skF_11')
      | ~ v10_lattices('#skF_11')
      | v2_struct_0('#skF_11')
      | ~ l3_lattices('#skF_11')
      | ~ v4_lattice3('#skF_11')
      | ~ v10_lattices('#skF_11')
      | v2_struct_0('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9890,c_23066])).

tff(c_23141,plain,(
    ! [C_1350] :
      ( r2_hidden('#skF_10'('#skF_11',k1_xboole_0,C_1350),k1_xboole_0)
      | r3_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),k15_lattice3('#skF_11',C_1350))
      | v2_struct_0('#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_104,c_102,c_106,c_104,c_102,c_9890,c_23122])).

tff(c_23149,plain,(
    ! [C_1351] : r3_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),k15_lattice3('#skF_11',C_1351)) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_9911,c_23141])).

tff(c_23155,plain,(
    ! [B_75] :
      ( r3_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),B_75)
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_11'))
      | ~ l3_lattices('#skF_11')
      | ~ v4_lattice3('#skF_11')
      | ~ v10_lattices('#skF_11')
      | v2_struct_0('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_23149])).

tff(c_23165,plain,(
    ! [B_75] :
      ( r3_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),B_75)
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_11'))
      | v2_struct_0('#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_104,c_102,c_23155])).

tff(c_23171,plain,(
    ! [B_1352] :
      ( r3_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),B_1352)
      | ~ m1_subset_1(B_1352,u1_struct_0('#skF_11')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_23165])).

tff(c_23179,plain,(
    ! [B_1352] :
      ( r1_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),B_1352)
      | ~ m1_subset_1(k15_lattice3('#skF_11',k1_xboole_0),u1_struct_0('#skF_11'))
      | ~ l3_lattices('#skF_11')
      | ~ v9_lattices('#skF_11')
      | ~ v8_lattices('#skF_11')
      | ~ v6_lattices('#skF_11')
      | v2_struct_0('#skF_11')
      | ~ m1_subset_1(B_1352,u1_struct_0('#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_23171,c_48])).

tff(c_23190,plain,(
    ! [B_1352] :
      ( r1_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),B_1352)
      | v2_struct_0('#skF_11')
      | ~ m1_subset_1(B_1352,u1_struct_0('#skF_11')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12960,c_13328,c_13353,c_102,c_21442,c_23179])).

tff(c_23192,plain,(
    ! [B_1353] :
      ( r1_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),B_1353)
      | ~ m1_subset_1(B_1353,u1_struct_0('#skF_11')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_23190])).

tff(c_23194,plain,(
    ! [B_1353] :
      ( k2_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),B_1353) = k15_lattice3('#skF_11',k1_xboole_0)
      | ~ m1_subset_1(k15_lattice3('#skF_11',k1_xboole_0),u1_struct_0('#skF_11'))
      | ~ l3_lattices('#skF_11')
      | ~ v9_lattices('#skF_11')
      | ~ v8_lattices('#skF_11')
      | v2_struct_0('#skF_11')
      | ~ m1_subset_1(B_1353,u1_struct_0('#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_23192,c_52])).

tff(c_23197,plain,(
    ! [B_1353] :
      ( k2_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),B_1353) = k15_lattice3('#skF_11',k1_xboole_0)
      | v2_struct_0('#skF_11')
      | ~ m1_subset_1(B_1353,u1_struct_0('#skF_11')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13328,c_13353,c_102,c_21442,c_23194])).

tff(c_23199,plain,(
    ! [B_1354] :
      ( k2_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),B_1354) = k15_lattice3('#skF_11',k1_xboole_0)
      | ~ m1_subset_1(B_1354,u1_struct_0('#skF_11')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_23197])).

tff(c_23216,plain,(
    k2_lattices('#skF_11',k15_lattice3('#skF_11',k1_xboole_0),'#skF_4'('#skF_11')) = k15_lattice3('#skF_11',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12747,c_23199])).

tff(c_23261,plain,(
    k15_lattice3('#skF_11',k1_xboole_0) = '#skF_4'('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12964,c_23216])).

tff(c_23263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12692,c_23261])).

tff(c_23265,plain,(
    ~ v6_lattices('#skF_11') ),
    inference(splitRight,[status(thm)],[c_12947])).

tff(c_23268,plain,
    ( ~ v10_lattices('#skF_11')
    | v2_struct_0('#skF_11')
    | ~ l3_lattices('#skF_11') ),
    inference(resolution,[status(thm)],[c_26,c_23265])).

tff(c_23271,plain,(
    v2_struct_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_106,c_23268])).

tff(c_23273,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_23271])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:26:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.95/7.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.95/7.70  
% 15.95/7.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.95/7.71  %$ r3_lattices > r1_lattices > r2_hidden > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v1_xboole_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k6_domain_1 > k16_lattice3 > k15_lattice3 > a_2_6_lattice3 > a_2_5_lattice3 > #nlpp > u1_struct_0 > k5_lattices > k1_xboole_0 > #skF_7 > #skF_4 > #skF_11 > #skF_1 > #skF_3 > #skF_9 > #skF_2 > #skF_8 > #skF_5 > #skF_6 > #skF_10
% 15.95/7.71  
% 15.95/7.71  %Foreground sorts:
% 15.95/7.71  
% 15.95/7.71  
% 15.95/7.71  %Background operators:
% 15.95/7.71  
% 15.95/7.71  
% 15.95/7.71  %Foreground operators:
% 15.95/7.71  tff(l3_lattices, type, l3_lattices: $i > $o).
% 15.95/7.71  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 15.95/7.71  tff('#skF_7', type, '#skF_7': $i > $i).
% 15.95/7.71  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 15.95/7.71  tff(l2_lattices, type, l2_lattices: $i > $o).
% 15.95/7.71  tff('#skF_4', type, '#skF_4': $i > $i).
% 15.95/7.71  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 15.95/7.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.95/7.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.95/7.71  tff('#skF_11', type, '#skF_11': $i).
% 15.95/7.71  tff('#skF_1', type, '#skF_1': $i > $i).
% 15.95/7.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.95/7.71  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 15.95/7.71  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 15.95/7.71  tff(l1_lattices, type, l1_lattices: $i > $o).
% 15.95/7.71  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 15.95/7.71  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 15.95/7.71  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 15.95/7.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.95/7.71  tff(v4_lattices, type, v4_lattices: $i > $o).
% 15.95/7.71  tff(v6_lattices, type, v6_lattices: $i > $o).
% 15.95/7.71  tff(v9_lattices, type, v9_lattices: $i > $o).
% 15.95/7.71  tff(a_2_5_lattice3, type, a_2_5_lattice3: ($i * $i) > $i).
% 15.95/7.71  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 15.95/7.71  tff(v5_lattices, type, v5_lattices: $i > $o).
% 15.95/7.71  tff(v10_lattices, type, v10_lattices: $i > $o).
% 15.95/7.71  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 15.95/7.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.95/7.71  tff(v13_lattices, type, v13_lattices: $i > $o).
% 15.95/7.71  tff(v8_lattices, type, v8_lattices: $i > $o).
% 15.95/7.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.95/7.71  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 15.95/7.71  tff(k5_lattices, type, k5_lattices: $i > $i).
% 15.95/7.71  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 15.95/7.71  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 15.95/7.71  tff(a_2_6_lattice3, type, a_2_6_lattice3: ($i * $i) > $i).
% 15.95/7.71  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 15.95/7.71  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 15.95/7.71  tff('#skF_6', type, '#skF_6': $i > $i).
% 15.95/7.71  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 15.95/7.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.95/7.71  tff(v7_lattices, type, v7_lattices: $i > $o).
% 15.95/7.71  
% 16.17/7.74  tff(f_274, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v13_lattices(A)) & l3_lattices(A)) & (k5_lattices(A) = k15_lattice3(A, k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_lattice3)).
% 16.17/7.74  tff(f_72, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 16.17/7.74  tff(f_97, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 16.17/7.74  tff(f_174, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k15_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 16.17/7.74  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 16.17/7.74  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 16.17/7.74  tff(f_197, axiom, (![A, B, C]: ((((~v2_struct_0(B) & v10_lattices(B)) & v4_lattice3(B)) & l3_lattices(B)) => (r2_hidden(A, a_2_5_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r3_lattices(B, D, E)) & r2_hidden(E, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_5_lattice3)).
% 16.17/7.74  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 16.17/7.74  tff(f_45, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 16.17/7.74  tff(f_227, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: ((k15_lattice3(A, B) = k15_lattice3(A, a_2_5_lattice3(A, B))) & (k16_lattice3(A, B) = k16_lattice3(A, a_2_6_lattice3(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_lattice3)).
% 16.17/7.74  tff(f_253, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: ((![D]: (m1_subset_1(D, u1_struct_0(A)) => ~(r2_hidden(D, B) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ~(r3_lattices(A, D, E) & r2_hidden(E, C))))))) => r3_lattices(A, k15_lattice3(A, B), k15_lattice3(A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_lattice3)).
% 16.17/7.74  tff(f_116, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 16.17/7.74  tff(f_152, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) <=> (?[B]: (m1_subset_1(B, u1_struct_0(A)) & (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_lattices)).
% 16.17/7.74  tff(f_213, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((k15_lattice3(A, k6_domain_1(u1_struct_0(A), B)) = B) & (k16_lattice3(A, k6_domain_1(u1_struct_0(A), B)) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_lattice3)).
% 16.17/7.74  tff(f_135, axiom, (![A]: ((((~v2_struct_0(A) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k2_lattices(A, B, C) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 16.17/7.74  tff(f_167, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v6_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, C) = k2_lattices(A, C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_lattices)).
% 16.17/7.74  tff(f_91, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((B = k5_lattices(A)) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattices)).
% 16.17/7.74  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 16.17/7.74  tff(f_50, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 16.17/7.74  tff(c_108, plain, (~v2_struct_0('#skF_11')), inference(cnfTransformation, [status(thm)], [f_274])).
% 16.17/7.74  tff(c_102, plain, (l3_lattices('#skF_11')), inference(cnfTransformation, [status(thm)], [f_274])).
% 16.17/7.74  tff(c_106, plain, (v10_lattices('#skF_11')), inference(cnfTransformation, [status(thm)], [f_274])).
% 16.17/7.74  tff(c_26, plain, (![A_14]: (v6_lattices(A_14) | ~v10_lattices(A_14) | v2_struct_0(A_14) | ~l3_lattices(A_14))), inference(cnfTransformation, [status(thm)], [f_72])).
% 16.17/7.74  tff(c_118, plain, (![A_97]: (l1_lattices(A_97) | ~l3_lattices(A_97))), inference(cnfTransformation, [status(thm)], [f_97])).
% 16.17/7.74  tff(c_122, plain, (l1_lattices('#skF_11')), inference(resolution, [status(thm)], [c_102, c_118])).
% 16.17/7.74  tff(c_72, plain, (![A_58, B_59]: (m1_subset_1(k15_lattice3(A_58, B_59), u1_struct_0(A_58)) | ~l3_lattices(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_174])).
% 16.17/7.74  tff(c_104, plain, (v4_lattice3('#skF_11')), inference(cnfTransformation, [status(thm)], [f_274])).
% 16.17/7.74  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 16.17/7.74  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.17/7.74  tff(c_535, plain, (![A_183, B_184, C_185]: (r2_hidden('#skF_9'(A_183, B_184, C_185), C_185) | ~r2_hidden(A_183, a_2_5_lattice3(B_184, C_185)) | ~l3_lattices(B_184) | ~v4_lattice3(B_184) | ~v10_lattices(B_184) | v2_struct_0(B_184))), inference(cnfTransformation, [status(thm)], [f_197])).
% 16.17/7.74  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.17/7.74  tff(c_552, plain, (![C_186, A_187, B_188]: (~v1_xboole_0(C_186) | ~r2_hidden(A_187, a_2_5_lattice3(B_188, C_186)) | ~l3_lattices(B_188) | ~v4_lattice3(B_188) | ~v10_lattices(B_188) | v2_struct_0(B_188))), inference(resolution, [status(thm)], [c_535, c_2])).
% 16.17/7.74  tff(c_578, plain, (![C_189, B_190]: (~v1_xboole_0(C_189) | ~l3_lattices(B_190) | ~v4_lattice3(B_190) | ~v10_lattices(B_190) | v2_struct_0(B_190) | v1_xboole_0(a_2_5_lattice3(B_190, C_189)))), inference(resolution, [status(thm)], [c_4, c_552])).
% 16.17/7.74  tff(c_149, plain, (![A_105, B_106]: (r2_hidden('#skF_2'(A_105, B_106), A_105) | r1_tarski(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_38])).
% 16.17/7.74  tff(c_158, plain, (![A_107, B_108]: (~v1_xboole_0(A_107) | r1_tarski(A_107, B_108))), inference(resolution, [status(thm)], [c_149, c_2])).
% 16.17/7.74  tff(c_16, plain, (![A_11]: (k1_xboole_0=A_11 | ~r1_tarski(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 16.17/7.74  tff(c_168, plain, (![A_107]: (k1_xboole_0=A_107 | ~v1_xboole_0(A_107))), inference(resolution, [status(thm)], [c_158, c_16])).
% 16.17/7.74  tff(c_583, plain, (![B_191, C_192]: (a_2_5_lattice3(B_191, C_192)=k1_xboole_0 | ~v1_xboole_0(C_192) | ~l3_lattices(B_191) | ~v4_lattice3(B_191) | ~v10_lattices(B_191) | v2_struct_0(B_191))), inference(resolution, [status(thm)], [c_578, c_168])).
% 16.17/7.74  tff(c_597, plain, (![B_196]: (a_2_5_lattice3(B_196, k1_xboole_0)=k1_xboole_0 | ~l3_lattices(B_196) | ~v4_lattice3(B_196) | ~v10_lattices(B_196) | v2_struct_0(B_196))), inference(resolution, [status(thm)], [c_12, c_583])).
% 16.17/7.74  tff(c_600, plain, (a_2_5_lattice3('#skF_11', k1_xboole_0)=k1_xboole_0 | ~l3_lattices('#skF_11') | ~v10_lattices('#skF_11') | v2_struct_0('#skF_11')), inference(resolution, [status(thm)], [c_104, c_597])).
% 16.17/7.74  tff(c_603, plain, (a_2_5_lattice3('#skF_11', k1_xboole_0)=k1_xboole_0 | v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_102, c_600])).
% 16.17/7.74  tff(c_604, plain, (a_2_5_lattice3('#skF_11', k1_xboole_0)=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_108, c_603])).
% 16.17/7.74  tff(c_90, plain, (![A_76, B_78]: (k15_lattice3(A_76, a_2_5_lattice3(A_76, B_78))=k15_lattice3(A_76, B_78) | ~l3_lattices(A_76) | ~v4_lattice3(A_76) | ~v10_lattices(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_227])).
% 16.17/7.74  tff(c_992, plain, (![A_227, B_228, C_229]: (r2_hidden('#skF_10'(A_227, B_228, C_229), B_228) | r3_lattices(A_227, k15_lattice3(A_227, B_228), k15_lattice3(A_227, C_229)) | ~l3_lattices(A_227) | ~v4_lattice3(A_227) | ~v10_lattices(A_227) | v2_struct_0(A_227))), inference(cnfTransformation, [status(thm)], [f_253])).
% 16.17/7.74  tff(c_76, plain, (![A_60, B_61, C_62]: (r2_hidden('#skF_9'(A_60, B_61, C_62), C_62) | ~r2_hidden(A_60, a_2_5_lattice3(B_61, C_62)) | ~l3_lattices(B_61) | ~v4_lattice3(B_61) | ~v10_lattices(B_61) | v2_struct_0(B_61))), inference(cnfTransformation, [status(thm)], [f_197])).
% 16.17/7.74  tff(c_551, plain, (![C_185, A_183, B_184]: (~v1_xboole_0(C_185) | ~r2_hidden(A_183, a_2_5_lattice3(B_184, C_185)) | ~l3_lattices(B_184) | ~v4_lattice3(B_184) | ~v10_lattices(B_184) | v2_struct_0(B_184))), inference(resolution, [status(thm)], [c_535, c_2])).
% 16.17/7.74  tff(c_611, plain, (![A_183]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_183, k1_xboole_0) | ~l3_lattices('#skF_11') | ~v4_lattice3('#skF_11') | ~v10_lattices('#skF_11') | v2_struct_0('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_604, c_551])).
% 16.17/7.74  tff(c_624, plain, (![A_183]: (~r2_hidden(A_183, k1_xboole_0) | v2_struct_0('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_104, c_102, c_12, c_611])).
% 16.17/7.74  tff(c_634, plain, (![A_197]: (~r2_hidden(A_197, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_108, c_624])).
% 16.17/7.74  tff(c_655, plain, (![A_60, B_61]: (~r2_hidden(A_60, a_2_5_lattice3(B_61, k1_xboole_0)) | ~l3_lattices(B_61) | ~v4_lattice3(B_61) | ~v10_lattices(B_61) | v2_struct_0(B_61))), inference(resolution, [status(thm)], [c_76, c_634])).
% 16.17/7.74  tff(c_1051, plain, (![B_233, A_234, C_235]: (~l3_lattices(B_233) | ~v4_lattice3(B_233) | ~v10_lattices(B_233) | v2_struct_0(B_233) | r3_lattices(A_234, k15_lattice3(A_234, a_2_5_lattice3(B_233, k1_xboole_0)), k15_lattice3(A_234, C_235)) | ~l3_lattices(A_234) | ~v4_lattice3(A_234) | ~v10_lattices(A_234) | v2_struct_0(A_234))), inference(resolution, [status(thm)], [c_992, c_655])).
% 16.17/7.74  tff(c_1054, plain, (![A_234, C_235]: (~l3_lattices('#skF_11') | ~v4_lattice3('#skF_11') | ~v10_lattices('#skF_11') | v2_struct_0('#skF_11') | r3_lattices(A_234, k15_lattice3(A_234, k1_xboole_0), k15_lattice3(A_234, C_235)) | ~l3_lattices(A_234) | ~v4_lattice3(A_234) | ~v10_lattices(A_234) | v2_struct_0(A_234))), inference(superposition, [status(thm), theory('equality')], [c_604, c_1051])).
% 16.17/7.74  tff(c_1066, plain, (![A_234, C_235]: (v2_struct_0('#skF_11') | r3_lattices(A_234, k15_lattice3(A_234, k1_xboole_0), k15_lattice3(A_234, C_235)) | ~l3_lattices(A_234) | ~v4_lattice3(A_234) | ~v10_lattices(A_234) | v2_struct_0(A_234))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_104, c_102, c_1054])).
% 16.17/7.74  tff(c_1067, plain, (![A_234, C_235]: (r3_lattices(A_234, k15_lattice3(A_234, k1_xboole_0), k15_lattice3(A_234, C_235)) | ~l3_lattices(A_234) | ~v4_lattice3(A_234) | ~v10_lattices(A_234) | v2_struct_0(A_234))), inference(negUnitSimplification, [status(thm)], [c_108, c_1066])).
% 16.17/7.74  tff(c_2590, plain, (![A_379, B_380, C_381]: (r1_lattices(A_379, B_380, C_381) | ~r3_lattices(A_379, B_380, C_381) | ~m1_subset_1(C_381, u1_struct_0(A_379)) | ~m1_subset_1(B_380, u1_struct_0(A_379)) | ~l3_lattices(A_379) | ~v9_lattices(A_379) | ~v8_lattices(A_379) | ~v6_lattices(A_379) | v2_struct_0(A_379))), inference(cnfTransformation, [status(thm)], [f_116])).
% 16.17/7.74  tff(c_2692, plain, (![A_394, C_395]: (r1_lattices(A_394, k15_lattice3(A_394, k1_xboole_0), k15_lattice3(A_394, C_395)) | ~m1_subset_1(k15_lattice3(A_394, C_395), u1_struct_0(A_394)) | ~m1_subset_1(k15_lattice3(A_394, k1_xboole_0), u1_struct_0(A_394)) | ~v9_lattices(A_394) | ~v8_lattices(A_394) | ~v6_lattices(A_394) | ~l3_lattices(A_394) | ~v4_lattice3(A_394) | ~v10_lattices(A_394) | v2_struct_0(A_394))), inference(resolution, [status(thm)], [c_1067, c_2590])).
% 16.17/7.74  tff(c_4538, plain, (![A_520, B_521]: (r1_lattices(A_520, k15_lattice3(A_520, k1_xboole_0), k15_lattice3(A_520, B_521)) | ~m1_subset_1(k15_lattice3(A_520, a_2_5_lattice3(A_520, B_521)), u1_struct_0(A_520)) | ~m1_subset_1(k15_lattice3(A_520, k1_xboole_0), u1_struct_0(A_520)) | ~v9_lattices(A_520) | ~v8_lattices(A_520) | ~v6_lattices(A_520) | ~l3_lattices(A_520) | ~v4_lattice3(A_520) | ~v10_lattices(A_520) | v2_struct_0(A_520) | ~l3_lattices(A_520) | ~v4_lattice3(A_520) | ~v10_lattices(A_520) | v2_struct_0(A_520))), inference(superposition, [status(thm), theory('equality')], [c_90, c_2692])).
% 16.17/7.74  tff(c_4550, plain, (r1_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), k15_lattice3('#skF_11', k1_xboole_0)) | ~m1_subset_1(k15_lattice3('#skF_11', k1_xboole_0), u1_struct_0('#skF_11')) | ~m1_subset_1(k15_lattice3('#skF_11', k1_xboole_0), u1_struct_0('#skF_11')) | ~v9_lattices('#skF_11') | ~v8_lattices('#skF_11') | ~v6_lattices('#skF_11') | ~l3_lattices('#skF_11') | ~v4_lattice3('#skF_11') | ~v10_lattices('#skF_11') | v2_struct_0('#skF_11') | ~l3_lattices('#skF_11') | ~v4_lattice3('#skF_11') | ~v10_lattices('#skF_11') | v2_struct_0('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_604, c_4538])).
% 16.17/7.74  tff(c_4559, plain, (r1_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), k15_lattice3('#skF_11', k1_xboole_0)) | ~m1_subset_1(k15_lattice3('#skF_11', k1_xboole_0), u1_struct_0('#skF_11')) | ~v9_lattices('#skF_11') | ~v8_lattices('#skF_11') | ~v6_lattices('#skF_11') | v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_104, c_102, c_106, c_104, c_102, c_4550])).
% 16.17/7.74  tff(c_4560, plain, (r1_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), k15_lattice3('#skF_11', k1_xboole_0)) | ~m1_subset_1(k15_lattice3('#skF_11', k1_xboole_0), u1_struct_0('#skF_11')) | ~v9_lattices('#skF_11') | ~v8_lattices('#skF_11') | ~v6_lattices('#skF_11')), inference(negUnitSimplification, [status(thm)], [c_108, c_4559])).
% 16.17/7.74  tff(c_4562, plain, (~v6_lattices('#skF_11')), inference(splitLeft, [status(thm)], [c_4560])).
% 16.17/7.74  tff(c_4565, plain, (~v10_lattices('#skF_11') | v2_struct_0('#skF_11') | ~l3_lattices('#skF_11')), inference(resolution, [status(thm)], [c_26, c_4562])).
% 16.17/7.74  tff(c_4568, plain, (v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_106, c_4565])).
% 16.17/7.74  tff(c_4570, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_4568])).
% 16.17/7.74  tff(c_4571, plain, (~v8_lattices('#skF_11') | ~v9_lattices('#skF_11') | ~m1_subset_1(k15_lattice3('#skF_11', k1_xboole_0), u1_struct_0('#skF_11')) | r1_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), k15_lattice3('#skF_11', k1_xboole_0))), inference(splitRight, [status(thm)], [c_4560])).
% 16.17/7.74  tff(c_4573, plain, (~m1_subset_1(k15_lattice3('#skF_11', k1_xboole_0), u1_struct_0('#skF_11'))), inference(splitLeft, [status(thm)], [c_4571])).
% 16.17/7.74  tff(c_4576, plain, (~l3_lattices('#skF_11') | v2_struct_0('#skF_11')), inference(resolution, [status(thm)], [c_72, c_4573])).
% 16.17/7.74  tff(c_4579, plain, (v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_4576])).
% 16.17/7.74  tff(c_4581, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_4579])).
% 16.17/7.74  tff(c_4583, plain, (m1_subset_1(k15_lattice3('#skF_11', k1_xboole_0), u1_struct_0('#skF_11'))), inference(splitRight, [status(thm)], [c_4571])).
% 16.17/7.74  tff(c_100, plain, (k15_lattice3('#skF_11', k1_xboole_0)!=k5_lattices('#skF_11') | ~l3_lattices('#skF_11') | ~v13_lattices('#skF_11') | ~v10_lattices('#skF_11') | v2_struct_0('#skF_11')), inference(cnfTransformation, [status(thm)], [f_274])).
% 16.17/7.74  tff(c_110, plain, (k15_lattice3('#skF_11', k1_xboole_0)!=k5_lattices('#skF_11') | ~v13_lattices('#skF_11') | v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_102, c_100])).
% 16.17/7.74  tff(c_111, plain, (k15_lattice3('#skF_11', k1_xboole_0)!=k5_lattices('#skF_11') | ~v13_lattices('#skF_11')), inference(negUnitSimplification, [status(thm)], [c_108, c_110])).
% 16.17/7.74  tff(c_148, plain, (~v13_lattices('#skF_11')), inference(splitLeft, [status(thm)], [c_111])).
% 16.17/7.74  tff(c_56, plain, (![A_36, B_45]: (m1_subset_1('#skF_5'(A_36, B_45), u1_struct_0(A_36)) | v13_lattices(A_36) | ~m1_subset_1(B_45, u1_struct_0(A_36)) | ~l1_lattices(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_152])).
% 16.17/7.74  tff(c_22, plain, (![A_14]: (v8_lattices(A_14) | ~v10_lattices(A_14) | v2_struct_0(A_14) | ~l3_lattices(A_14))), inference(cnfTransformation, [status(thm)], [f_72])).
% 16.17/7.74  tff(c_4582, plain, (~v9_lattices('#skF_11') | ~v8_lattices('#skF_11') | r1_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), k15_lattice3('#skF_11', k1_xboole_0))), inference(splitRight, [status(thm)], [c_4571])).
% 16.17/7.74  tff(c_4652, plain, (~v8_lattices('#skF_11')), inference(splitLeft, [status(thm)], [c_4582])).
% 16.17/7.74  tff(c_4655, plain, (~v10_lattices('#skF_11') | v2_struct_0('#skF_11') | ~l3_lattices('#skF_11')), inference(resolution, [status(thm)], [c_22, c_4652])).
% 16.17/7.74  tff(c_4658, plain, (v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_106, c_4655])).
% 16.17/7.74  tff(c_4660, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_4658])).
% 16.17/7.74  tff(c_4662, plain, (v8_lattices('#skF_11')), inference(splitRight, [status(thm)], [c_4582])).
% 16.17/7.74  tff(c_20, plain, (![A_14]: (v9_lattices(A_14) | ~v10_lattices(A_14) | v2_struct_0(A_14) | ~l3_lattices(A_14))), inference(cnfTransformation, [status(thm)], [f_72])).
% 16.17/7.74  tff(c_4661, plain, (~v9_lattices('#skF_11') | r1_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), k15_lattice3('#skF_11', k1_xboole_0))), inference(splitRight, [status(thm)], [c_4582])).
% 16.17/7.74  tff(c_4669, plain, (~v9_lattices('#skF_11')), inference(splitLeft, [status(thm)], [c_4661])).
% 16.17/7.74  tff(c_4703, plain, (~v10_lattices('#skF_11') | v2_struct_0('#skF_11') | ~l3_lattices('#skF_11')), inference(resolution, [status(thm)], [c_20, c_4669])).
% 16.17/7.74  tff(c_4706, plain, (v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_106, c_4703])).
% 16.17/7.74  tff(c_4708, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_4706])).
% 16.17/7.74  tff(c_4710, plain, (v9_lattices('#skF_11')), inference(splitRight, [status(thm)], [c_4661])).
% 16.17/7.74  tff(c_4572, plain, (v6_lattices('#skF_11')), inference(splitRight, [status(thm)], [c_4560])).
% 16.17/7.74  tff(c_88, plain, (![A_73, B_75]: (k15_lattice3(A_73, k6_domain_1(u1_struct_0(A_73), B_75))=B_75 | ~m1_subset_1(B_75, u1_struct_0(A_73)) | ~l3_lattices(A_73) | ~v4_lattice3(A_73) | ~v10_lattices(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_213])).
% 16.17/7.74  tff(c_625, plain, (![A_183]: (~r2_hidden(A_183, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_108, c_624])).
% 16.17/7.74  tff(c_8728, plain, (![A_634, B_635, C_636]: (r2_hidden('#skF_10'(A_634, a_2_5_lattice3(A_634, B_635), C_636), a_2_5_lattice3(A_634, B_635)) | r3_lattices(A_634, k15_lattice3(A_634, B_635), k15_lattice3(A_634, C_636)) | ~l3_lattices(A_634) | ~v4_lattice3(A_634) | ~v10_lattices(A_634) | v2_struct_0(A_634) | ~l3_lattices(A_634) | ~v4_lattice3(A_634) | ~v10_lattices(A_634) | v2_struct_0(A_634))), inference(superposition, [status(thm), theory('equality')], [c_90, c_992])).
% 16.17/7.74  tff(c_8784, plain, (![C_636]: (r2_hidden('#skF_10'('#skF_11', k1_xboole_0, C_636), a_2_5_lattice3('#skF_11', k1_xboole_0)) | r3_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), k15_lattice3('#skF_11', C_636)) | ~l3_lattices('#skF_11') | ~v4_lattice3('#skF_11') | ~v10_lattices('#skF_11') | v2_struct_0('#skF_11') | ~l3_lattices('#skF_11') | ~v4_lattice3('#skF_11') | ~v10_lattices('#skF_11') | v2_struct_0('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_604, c_8728])).
% 16.17/7.74  tff(c_8803, plain, (![C_636]: (r2_hidden('#skF_10'('#skF_11', k1_xboole_0, C_636), k1_xboole_0) | r3_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), k15_lattice3('#skF_11', C_636)) | v2_struct_0('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_104, c_102, c_106, c_104, c_102, c_604, c_8784])).
% 16.17/7.74  tff(c_8811, plain, (![C_637]: (r3_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), k15_lattice3('#skF_11', C_637)))), inference(negUnitSimplification, [status(thm)], [c_108, c_625, c_8803])).
% 16.17/7.74  tff(c_8817, plain, (![B_75]: (r3_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), B_75) | ~m1_subset_1(B_75, u1_struct_0('#skF_11')) | ~l3_lattices('#skF_11') | ~v4_lattice3('#skF_11') | ~v10_lattices('#skF_11') | v2_struct_0('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_8811])).
% 16.17/7.74  tff(c_8827, plain, (![B_75]: (r3_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), B_75) | ~m1_subset_1(B_75, u1_struct_0('#skF_11')) | v2_struct_0('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_104, c_102, c_8817])).
% 16.17/7.74  tff(c_8833, plain, (![B_638]: (r3_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), B_638) | ~m1_subset_1(B_638, u1_struct_0('#skF_11')))), inference(negUnitSimplification, [status(thm)], [c_108, c_8827])).
% 16.17/7.74  tff(c_48, plain, (![A_26, B_27, C_28]: (r1_lattices(A_26, B_27, C_28) | ~r3_lattices(A_26, B_27, C_28) | ~m1_subset_1(C_28, u1_struct_0(A_26)) | ~m1_subset_1(B_27, u1_struct_0(A_26)) | ~l3_lattices(A_26) | ~v9_lattices(A_26) | ~v8_lattices(A_26) | ~v6_lattices(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_116])).
% 16.17/7.74  tff(c_8841, plain, (![B_638]: (r1_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), B_638) | ~m1_subset_1(k15_lattice3('#skF_11', k1_xboole_0), u1_struct_0('#skF_11')) | ~l3_lattices('#skF_11') | ~v9_lattices('#skF_11') | ~v8_lattices('#skF_11') | ~v6_lattices('#skF_11') | v2_struct_0('#skF_11') | ~m1_subset_1(B_638, u1_struct_0('#skF_11')))), inference(resolution, [status(thm)], [c_8833, c_48])).
% 16.17/7.74  tff(c_8852, plain, (![B_638]: (r1_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), B_638) | v2_struct_0('#skF_11') | ~m1_subset_1(B_638, u1_struct_0('#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_4572, c_4662, c_4710, c_102, c_4583, c_8841])).
% 16.17/7.74  tff(c_8854, plain, (![B_639]: (r1_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), B_639) | ~m1_subset_1(B_639, u1_struct_0('#skF_11')))), inference(negUnitSimplification, [status(thm)], [c_108, c_8852])).
% 16.17/7.74  tff(c_52, plain, (![A_29, B_33, C_35]: (k2_lattices(A_29, B_33, C_35)=B_33 | ~r1_lattices(A_29, B_33, C_35) | ~m1_subset_1(C_35, u1_struct_0(A_29)) | ~m1_subset_1(B_33, u1_struct_0(A_29)) | ~l3_lattices(A_29) | ~v9_lattices(A_29) | ~v8_lattices(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_135])).
% 16.17/7.74  tff(c_8856, plain, (![B_639]: (k2_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), B_639)=k15_lattice3('#skF_11', k1_xboole_0) | ~m1_subset_1(k15_lattice3('#skF_11', k1_xboole_0), u1_struct_0('#skF_11')) | ~l3_lattices('#skF_11') | ~v9_lattices('#skF_11') | ~v8_lattices('#skF_11') | v2_struct_0('#skF_11') | ~m1_subset_1(B_639, u1_struct_0('#skF_11')))), inference(resolution, [status(thm)], [c_8854, c_52])).
% 16.17/7.74  tff(c_8859, plain, (![B_639]: (k2_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), B_639)=k15_lattice3('#skF_11', k1_xboole_0) | v2_struct_0('#skF_11') | ~m1_subset_1(B_639, u1_struct_0('#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_4662, c_4710, c_102, c_4583, c_8856])).
% 16.17/7.74  tff(c_8861, plain, (![B_640]: (k2_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), B_640)=k15_lattice3('#skF_11', k1_xboole_0) | ~m1_subset_1(B_640, u1_struct_0('#skF_11')))), inference(negUnitSimplification, [status(thm)], [c_108, c_8859])).
% 16.17/7.74  tff(c_8891, plain, (![B_45]: (k2_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), '#skF_5'('#skF_11', B_45))=k15_lattice3('#skF_11', k1_xboole_0) | v13_lattices('#skF_11') | ~m1_subset_1(B_45, u1_struct_0('#skF_11')) | ~l1_lattices('#skF_11') | v2_struct_0('#skF_11'))), inference(resolution, [status(thm)], [c_56, c_8861])).
% 16.17/7.74  tff(c_8933, plain, (![B_45]: (k2_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), '#skF_5'('#skF_11', B_45))=k15_lattice3('#skF_11', k1_xboole_0) | v13_lattices('#skF_11') | ~m1_subset_1(B_45, u1_struct_0('#skF_11')) | v2_struct_0('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_8891])).
% 16.17/7.74  tff(c_9419, plain, (![B_653]: (k2_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), '#skF_5'('#skF_11', B_653))=k15_lattice3('#skF_11', k1_xboole_0) | ~m1_subset_1(B_653, u1_struct_0('#skF_11')))), inference(negUnitSimplification, [status(thm)], [c_108, c_148, c_8933])).
% 16.17/7.74  tff(c_1075, plain, (![A_238, C_239, B_240]: (k2_lattices(A_238, C_239, B_240)=k2_lattices(A_238, B_240, C_239) | ~m1_subset_1(C_239, u1_struct_0(A_238)) | ~m1_subset_1(B_240, u1_struct_0(A_238)) | ~v6_lattices(A_238) | ~l1_lattices(A_238) | v2_struct_0(A_238))), inference(cnfTransformation, [status(thm)], [f_167])).
% 16.17/7.74  tff(c_4941, plain, (![A_531, B_532, B_533]: (k2_lattices(A_531, B_532, '#skF_5'(A_531, B_533))=k2_lattices(A_531, '#skF_5'(A_531, B_533), B_532) | ~m1_subset_1(B_532, u1_struct_0(A_531)) | ~v6_lattices(A_531) | v13_lattices(A_531) | ~m1_subset_1(B_533, u1_struct_0(A_531)) | ~l1_lattices(A_531) | v2_struct_0(A_531))), inference(resolution, [status(thm)], [c_56, c_1075])).
% 16.17/7.74  tff(c_4943, plain, (![B_533]: (k2_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), '#skF_5'('#skF_11', B_533))=k2_lattices('#skF_11', '#skF_5'('#skF_11', B_533), k15_lattice3('#skF_11', k1_xboole_0)) | ~v6_lattices('#skF_11') | v13_lattices('#skF_11') | ~m1_subset_1(B_533, u1_struct_0('#skF_11')) | ~l1_lattices('#skF_11') | v2_struct_0('#skF_11'))), inference(resolution, [status(thm)], [c_4583, c_4941])).
% 16.17/7.74  tff(c_4962, plain, (![B_533]: (k2_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), '#skF_5'('#skF_11', B_533))=k2_lattices('#skF_11', '#skF_5'('#skF_11', B_533), k15_lattice3('#skF_11', k1_xboole_0)) | v13_lattices('#skF_11') | ~m1_subset_1(B_533, u1_struct_0('#skF_11')) | v2_struct_0('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_4572, c_4943])).
% 16.17/7.74  tff(c_4972, plain, (![B_534]: (k2_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), '#skF_5'('#skF_11', B_534))=k2_lattices('#skF_11', '#skF_5'('#skF_11', B_534), k15_lattice3('#skF_11', k1_xboole_0)) | ~m1_subset_1(B_534, u1_struct_0('#skF_11')))), inference(negUnitSimplification, [status(thm)], [c_108, c_148, c_4962])).
% 16.17/7.74  tff(c_54, plain, (![A_36, B_45]: (k2_lattices(A_36, '#skF_5'(A_36, B_45), B_45)!=B_45 | k2_lattices(A_36, B_45, '#skF_5'(A_36, B_45))!=B_45 | v13_lattices(A_36) | ~m1_subset_1(B_45, u1_struct_0(A_36)) | ~l1_lattices(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_152])).
% 16.17/7.74  tff(c_4981, plain, (k2_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), '#skF_5'('#skF_11', k15_lattice3('#skF_11', k1_xboole_0)))!=k15_lattice3('#skF_11', k1_xboole_0) | k2_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), '#skF_5'('#skF_11', k15_lattice3('#skF_11', k1_xboole_0)))!=k15_lattice3('#skF_11', k1_xboole_0) | v13_lattices('#skF_11') | ~m1_subset_1(k15_lattice3('#skF_11', k1_xboole_0), u1_struct_0('#skF_11')) | ~l1_lattices('#skF_11') | v2_struct_0('#skF_11') | ~m1_subset_1(k15_lattice3('#skF_11', k1_xboole_0), u1_struct_0('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_4972, c_54])).
% 16.17/7.74  tff(c_4991, plain, (k2_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), '#skF_5'('#skF_11', k15_lattice3('#skF_11', k1_xboole_0)))!=k15_lattice3('#skF_11', k1_xboole_0) | v13_lattices('#skF_11') | v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_4583, c_122, c_4583, c_4981])).
% 16.17/7.74  tff(c_4992, plain, (k2_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), '#skF_5'('#skF_11', k15_lattice3('#skF_11', k1_xboole_0)))!=k15_lattice3('#skF_11', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_108, c_148, c_4991])).
% 16.17/7.74  tff(c_9425, plain, (~m1_subset_1(k15_lattice3('#skF_11', k1_xboole_0), u1_struct_0('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_9419, c_4992])).
% 16.17/7.74  tff(c_9439, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4583, c_9425])).
% 16.17/7.74  tff(c_9441, plain, (v13_lattices('#skF_11')), inference(splitRight, [status(thm)], [c_111])).
% 16.17/7.74  tff(c_58, plain, (![A_36]: (m1_subset_1('#skF_4'(A_36), u1_struct_0(A_36)) | ~v13_lattices(A_36) | ~l1_lattices(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_152])).
% 16.17/7.74  tff(c_9812, plain, (![A_728, B_729]: (m1_subset_1('#skF_3'(A_728, B_729), u1_struct_0(A_728)) | k5_lattices(A_728)=B_729 | ~m1_subset_1(B_729, u1_struct_0(A_728)) | ~v13_lattices(A_728) | ~l1_lattices(A_728) | v2_struct_0(A_728))), inference(cnfTransformation, [status(thm)], [f_91])).
% 16.17/7.74  tff(c_62, plain, (![A_36, C_44]: (k2_lattices(A_36, '#skF_4'(A_36), C_44)='#skF_4'(A_36) | ~m1_subset_1(C_44, u1_struct_0(A_36)) | ~v13_lattices(A_36) | ~l1_lattices(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_152])).
% 16.17/7.74  tff(c_9818, plain, (![A_728, B_729]: (k2_lattices(A_728, '#skF_4'(A_728), '#skF_3'(A_728, B_729))='#skF_4'(A_728) | k5_lattices(A_728)=B_729 | ~m1_subset_1(B_729, u1_struct_0(A_728)) | ~v13_lattices(A_728) | ~l1_lattices(A_728) | v2_struct_0(A_728))), inference(resolution, [status(thm)], [c_9812, c_62])).
% 16.17/7.74  tff(c_60, plain, (![A_36, C_44]: (k2_lattices(A_36, C_44, '#skF_4'(A_36))='#skF_4'(A_36) | ~m1_subset_1(C_44, u1_struct_0(A_36)) | ~v13_lattices(A_36) | ~l1_lattices(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_152])).
% 16.17/7.74  tff(c_9817, plain, (![A_728, B_729]: (k2_lattices(A_728, '#skF_3'(A_728, B_729), '#skF_4'(A_728))='#skF_4'(A_728) | k5_lattices(A_728)=B_729 | ~m1_subset_1(B_729, u1_struct_0(A_728)) | ~v13_lattices(A_728) | ~l1_lattices(A_728) | v2_struct_0(A_728))), inference(resolution, [status(thm)], [c_9812, c_60])).
% 16.17/7.74  tff(c_12669, plain, (![A_971, B_972]: (k2_lattices(A_971, '#skF_3'(A_971, B_972), B_972)!=B_972 | k2_lattices(A_971, B_972, '#skF_3'(A_971, B_972))!=B_972 | k5_lattices(A_971)=B_972 | ~m1_subset_1(B_972, u1_struct_0(A_971)) | ~v13_lattices(A_971) | ~l1_lattices(A_971) | v2_struct_0(A_971))), inference(cnfTransformation, [status(thm)], [f_91])).
% 16.17/7.74  tff(c_12674, plain, (![A_973]: (k2_lattices(A_973, '#skF_4'(A_973), '#skF_3'(A_973, '#skF_4'(A_973)))!='#skF_4'(A_973) | k5_lattices(A_973)='#skF_4'(A_973) | ~m1_subset_1('#skF_4'(A_973), u1_struct_0(A_973)) | ~v13_lattices(A_973) | ~l1_lattices(A_973) | v2_struct_0(A_973))), inference(superposition, [status(thm), theory('equality')], [c_9817, c_12669])).
% 16.17/7.74  tff(c_12680, plain, (![A_974]: (k5_lattices(A_974)='#skF_4'(A_974) | ~m1_subset_1('#skF_4'(A_974), u1_struct_0(A_974)) | ~v13_lattices(A_974) | ~l1_lattices(A_974) | v2_struct_0(A_974))), inference(superposition, [status(thm), theory('equality')], [c_9818, c_12674])).
% 16.17/7.74  tff(c_12685, plain, (![A_975]: (k5_lattices(A_975)='#skF_4'(A_975) | ~v13_lattices(A_975) | ~l1_lattices(A_975) | v2_struct_0(A_975))), inference(resolution, [status(thm)], [c_58, c_12680])).
% 16.17/7.74  tff(c_12688, plain, (k5_lattices('#skF_11')='#skF_4'('#skF_11') | ~v13_lattices('#skF_11') | ~l1_lattices('#skF_11')), inference(resolution, [status(thm)], [c_12685, c_108])).
% 16.17/7.74  tff(c_12691, plain, (k5_lattices('#skF_11')='#skF_4'('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_9441, c_12688])).
% 16.17/7.74  tff(c_9440, plain, (k15_lattice3('#skF_11', k1_xboole_0)!=k5_lattices('#skF_11')), inference(splitRight, [status(thm)], [c_111])).
% 16.17/7.74  tff(c_12692, plain, (k15_lattice3('#skF_11', k1_xboole_0)!='#skF_4'('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_12691, c_9440])).
% 16.17/7.74  tff(c_10421, plain, (![A_795, C_796]: (k2_lattices(A_795, C_796, k5_lattices(A_795))=k5_lattices(A_795) | ~m1_subset_1(C_796, u1_struct_0(A_795)) | ~m1_subset_1(k5_lattices(A_795), u1_struct_0(A_795)) | ~v13_lattices(A_795) | ~l1_lattices(A_795) | v2_struct_0(A_795))), inference(cnfTransformation, [status(thm)], [f_91])).
% 16.17/7.74  tff(c_10443, plain, (![A_36]: (k2_lattices(A_36, '#skF_4'(A_36), k5_lattices(A_36))=k5_lattices(A_36) | ~m1_subset_1(k5_lattices(A_36), u1_struct_0(A_36)) | ~v13_lattices(A_36) | ~l1_lattices(A_36) | v2_struct_0(A_36))), inference(resolution, [status(thm)], [c_58, c_10421])).
% 16.17/7.74  tff(c_12703, plain, (k2_lattices('#skF_11', '#skF_4'('#skF_11'), k5_lattices('#skF_11'))=k5_lattices('#skF_11') | ~m1_subset_1('#skF_4'('#skF_11'), u1_struct_0('#skF_11')) | ~v13_lattices('#skF_11') | ~l1_lattices('#skF_11') | v2_struct_0('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_12691, c_10443])).
% 16.17/7.74  tff(c_12725, plain, (k2_lattices('#skF_11', '#skF_4'('#skF_11'), '#skF_4'('#skF_11'))='#skF_4'('#skF_11') | ~m1_subset_1('#skF_4'('#skF_11'), u1_struct_0('#skF_11')) | v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_9441, c_12691, c_12691, c_12703])).
% 16.17/7.74  tff(c_12726, plain, (k2_lattices('#skF_11', '#skF_4'('#skF_11'), '#skF_4'('#skF_11'))='#skF_4'('#skF_11') | ~m1_subset_1('#skF_4'('#skF_11'), u1_struct_0('#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_108, c_12725])).
% 16.17/7.74  tff(c_12737, plain, (~m1_subset_1('#skF_4'('#skF_11'), u1_struct_0('#skF_11'))), inference(splitLeft, [status(thm)], [c_12726])).
% 16.17/7.74  tff(c_12740, plain, (~v13_lattices('#skF_11') | ~l1_lattices('#skF_11') | v2_struct_0('#skF_11')), inference(resolution, [status(thm)], [c_58, c_12737])).
% 16.17/7.74  tff(c_12743, plain, (v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_9441, c_12740])).
% 16.17/7.74  tff(c_12745, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_12743])).
% 16.17/7.74  tff(c_12747, plain, (m1_subset_1('#skF_4'('#skF_11'), u1_struct_0('#skF_11'))), inference(splitRight, [status(thm)], [c_12726])).
% 16.17/7.74  tff(c_10445, plain, (![A_58, B_59]: (k2_lattices(A_58, k15_lattice3(A_58, B_59), k5_lattices(A_58))=k5_lattices(A_58) | ~m1_subset_1(k5_lattices(A_58), u1_struct_0(A_58)) | ~v13_lattices(A_58) | ~l1_lattices(A_58) | ~l3_lattices(A_58) | v2_struct_0(A_58))), inference(resolution, [status(thm)], [c_72, c_10421])).
% 16.17/7.74  tff(c_12695, plain, (![B_59]: (k2_lattices('#skF_11', k15_lattice3('#skF_11', B_59), k5_lattices('#skF_11'))=k5_lattices('#skF_11') | ~m1_subset_1('#skF_4'('#skF_11'), u1_struct_0('#skF_11')) | ~v13_lattices('#skF_11') | ~l1_lattices('#skF_11') | ~l3_lattices('#skF_11') | v2_struct_0('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_12691, c_10445])).
% 16.17/7.74  tff(c_12713, plain, (![B_59]: (k2_lattices('#skF_11', k15_lattice3('#skF_11', B_59), '#skF_4'('#skF_11'))='#skF_4'('#skF_11') | ~m1_subset_1('#skF_4'('#skF_11'), u1_struct_0('#skF_11')) | v2_struct_0('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_122, c_9441, c_12691, c_12691, c_12695])).
% 16.17/7.74  tff(c_12714, plain, (![B_59]: (k2_lattices('#skF_11', k15_lattice3('#skF_11', B_59), '#skF_4'('#skF_11'))='#skF_4'('#skF_11') | ~m1_subset_1('#skF_4'('#skF_11'), u1_struct_0('#skF_11')))), inference(negUnitSimplification, [status(thm)], [c_108, c_12713])).
% 16.17/7.74  tff(c_12964, plain, (![B_59]: (k2_lattices('#skF_11', k15_lattice3('#skF_11', B_59), '#skF_4'('#skF_11'))='#skF_4'('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_12747, c_12714])).
% 16.17/7.74  tff(c_50, plain, (![A_29, B_33, C_35]: (r1_lattices(A_29, B_33, C_35) | k2_lattices(A_29, B_33, C_35)!=B_33 | ~m1_subset_1(C_35, u1_struct_0(A_29)) | ~m1_subset_1(B_33, u1_struct_0(A_29)) | ~l3_lattices(A_29) | ~v9_lattices(A_29) | ~v8_lattices(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_135])).
% 16.17/7.74  tff(c_12753, plain, (![B_33]: (r1_lattices('#skF_11', B_33, '#skF_4'('#skF_11')) | k2_lattices('#skF_11', B_33, '#skF_4'('#skF_11'))!=B_33 | ~m1_subset_1(B_33, u1_struct_0('#skF_11')) | ~l3_lattices('#skF_11') | ~v9_lattices('#skF_11') | ~v8_lattices('#skF_11') | v2_struct_0('#skF_11'))), inference(resolution, [status(thm)], [c_12747, c_50])).
% 16.17/7.74  tff(c_12776, plain, (![B_33]: (r1_lattices('#skF_11', B_33, '#skF_4'('#skF_11')) | k2_lattices('#skF_11', B_33, '#skF_4'('#skF_11'))!=B_33 | ~m1_subset_1(B_33, u1_struct_0('#skF_11')) | ~v9_lattices('#skF_11') | ~v8_lattices('#skF_11') | v2_struct_0('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_12753])).
% 16.17/7.74  tff(c_12777, plain, (![B_33]: (r1_lattices('#skF_11', B_33, '#skF_4'('#skF_11')) | k2_lattices('#skF_11', B_33, '#skF_4'('#skF_11'))!=B_33 | ~m1_subset_1(B_33, u1_struct_0('#skF_11')) | ~v9_lattices('#skF_11') | ~v8_lattices('#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_108, c_12776])).
% 16.17/7.74  tff(c_13318, plain, (~v8_lattices('#skF_11')), inference(splitLeft, [status(thm)], [c_12777])).
% 16.17/7.74  tff(c_13321, plain, (~v10_lattices('#skF_11') | v2_struct_0('#skF_11') | ~l3_lattices('#skF_11')), inference(resolution, [status(thm)], [c_22, c_13318])).
% 16.17/7.74  tff(c_13324, plain, (v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_106, c_13321])).
% 16.17/7.74  tff(c_13326, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_13324])).
% 16.17/7.74  tff(c_13328, plain, (v8_lattices('#skF_11')), inference(splitRight, [status(thm)], [c_12777])).
% 16.17/7.74  tff(c_13327, plain, (![B_33]: (~v9_lattices('#skF_11') | r1_lattices('#skF_11', B_33, '#skF_4'('#skF_11')) | k2_lattices('#skF_11', B_33, '#skF_4'('#skF_11'))!=B_33 | ~m1_subset_1(B_33, u1_struct_0('#skF_11')))), inference(splitRight, [status(thm)], [c_12777])).
% 16.17/7.74  tff(c_13343, plain, (~v9_lattices('#skF_11')), inference(splitLeft, [status(thm)], [c_13327])).
% 16.17/7.74  tff(c_13346, plain, (~v10_lattices('#skF_11') | v2_struct_0('#skF_11') | ~l3_lattices('#skF_11')), inference(resolution, [status(thm)], [c_20, c_13343])).
% 16.17/7.74  tff(c_13349, plain, (v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_106, c_13346])).
% 16.17/7.74  tff(c_13351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_13349])).
% 16.17/7.74  tff(c_13353, plain, (v9_lattices('#skF_11')), inference(splitRight, [status(thm)], [c_13327])).
% 16.17/7.74  tff(c_70, plain, (![A_47]: (m1_subset_1('#skF_6'(A_47), u1_struct_0(A_47)) | v6_lattices(A_47) | ~l1_lattices(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_167])).
% 16.17/7.74  tff(c_10310, plain, (![A_779, C_780]: (k2_lattices(A_779, k5_lattices(A_779), C_780)=k5_lattices(A_779) | ~m1_subset_1(C_780, u1_struct_0(A_779)) | ~m1_subset_1(k5_lattices(A_779), u1_struct_0(A_779)) | ~v13_lattices(A_779) | ~l1_lattices(A_779) | v2_struct_0(A_779))), inference(cnfTransformation, [status(thm)], [f_91])).
% 16.17/7.74  tff(c_10334, plain, (![A_58, B_59]: (k2_lattices(A_58, k5_lattices(A_58), k15_lattice3(A_58, B_59))=k5_lattices(A_58) | ~m1_subset_1(k5_lattices(A_58), u1_struct_0(A_58)) | ~v13_lattices(A_58) | ~l1_lattices(A_58) | ~l3_lattices(A_58) | v2_struct_0(A_58))), inference(resolution, [status(thm)], [c_72, c_10310])).
% 16.17/7.74  tff(c_12697, plain, (![B_59]: (k2_lattices('#skF_11', k5_lattices('#skF_11'), k15_lattice3('#skF_11', B_59))=k5_lattices('#skF_11') | ~m1_subset_1('#skF_4'('#skF_11'), u1_struct_0('#skF_11')) | ~v13_lattices('#skF_11') | ~l1_lattices('#skF_11') | ~l3_lattices('#skF_11') | v2_struct_0('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_12691, c_10334])).
% 16.17/7.74  tff(c_12716, plain, (![B_59]: (k2_lattices('#skF_11', '#skF_4'('#skF_11'), k15_lattice3('#skF_11', B_59))='#skF_4'('#skF_11') | ~m1_subset_1('#skF_4'('#skF_11'), u1_struct_0('#skF_11')) | v2_struct_0('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_122, c_9441, c_12691, c_12691, c_12697])).
% 16.17/7.74  tff(c_12717, plain, (![B_59]: (k2_lattices('#skF_11', '#skF_4'('#skF_11'), k15_lattice3('#skF_11', B_59))='#skF_4'('#skF_11') | ~m1_subset_1('#skF_4'('#skF_11'), u1_struct_0('#skF_11')))), inference(negUnitSimplification, [status(thm)], [c_108, c_12716])).
% 16.17/7.74  tff(c_12854, plain, (![B_980]: (k2_lattices('#skF_11', '#skF_4'('#skF_11'), k15_lattice3('#skF_11', B_980))='#skF_4'('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_12747, c_12717])).
% 16.17/7.74  tff(c_12865, plain, (![B_75]: (k2_lattices('#skF_11', '#skF_4'('#skF_11'), B_75)='#skF_4'('#skF_11') | ~m1_subset_1(B_75, u1_struct_0('#skF_11')) | ~l3_lattices('#skF_11') | ~v4_lattice3('#skF_11') | ~v10_lattices('#skF_11') | v2_struct_0('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_12854])).
% 16.17/7.74  tff(c_12881, plain, (![B_75]: (k2_lattices('#skF_11', '#skF_4'('#skF_11'), B_75)='#skF_4'('#skF_11') | ~m1_subset_1(B_75, u1_struct_0('#skF_11')) | v2_struct_0('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_104, c_102, c_12865])).
% 16.17/7.74  tff(c_12890, plain, (![B_981]: (k2_lattices('#skF_11', '#skF_4'('#skF_11'), B_981)='#skF_4'('#skF_11') | ~m1_subset_1(B_981, u1_struct_0('#skF_11')))), inference(negUnitSimplification, [status(thm)], [c_108, c_12881])).
% 16.17/7.74  tff(c_12913, plain, (k2_lattices('#skF_11', '#skF_4'('#skF_11'), '#skF_6'('#skF_11'))='#skF_4'('#skF_11') | v6_lattices('#skF_11') | ~l1_lattices('#skF_11') | v2_struct_0('#skF_11')), inference(resolution, [status(thm)], [c_70, c_12890])).
% 16.17/7.74  tff(c_12946, plain, (k2_lattices('#skF_11', '#skF_4'('#skF_11'), '#skF_6'('#skF_11'))='#skF_4'('#skF_11') | v6_lattices('#skF_11') | v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_12913])).
% 16.17/7.74  tff(c_12947, plain, (k2_lattices('#skF_11', '#skF_4'('#skF_11'), '#skF_6'('#skF_11'))='#skF_4'('#skF_11') | v6_lattices('#skF_11')), inference(negUnitSimplification, [status(thm)], [c_108, c_12946])).
% 16.17/7.74  tff(c_12960, plain, (v6_lattices('#skF_11')), inference(splitLeft, [status(thm)], [c_12947])).
% 16.17/7.74  tff(c_14, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 16.17/7.74  tff(c_9819, plain, (![A_730, B_731, C_732]: (r2_hidden('#skF_9'(A_730, B_731, C_732), C_732) | ~r2_hidden(A_730, a_2_5_lattice3(B_731, C_732)) | ~l3_lattices(B_731) | ~v4_lattice3(B_731) | ~v10_lattices(B_731) | v2_struct_0(B_731))), inference(cnfTransformation, [status(thm)], [f_197])).
% 16.17/7.74  tff(c_9836, plain, (![C_733, A_734, B_735]: (~v1_xboole_0(C_733) | ~r2_hidden(A_734, a_2_5_lattice3(B_735, C_733)) | ~l3_lattices(B_735) | ~v4_lattice3(B_735) | ~v10_lattices(B_735) | v2_struct_0(B_735))), inference(resolution, [status(thm)], [c_9819, c_2])).
% 16.17/7.74  tff(c_9862, plain, (![C_736, B_737]: (~v1_xboole_0(C_736) | ~l3_lattices(B_737) | ~v4_lattice3(B_737) | ~v10_lattices(B_737) | v2_struct_0(B_737) | v1_xboole_0(a_2_5_lattice3(B_737, C_736)))), inference(resolution, [status(thm)], [c_4, c_9836])).
% 16.17/7.74  tff(c_9448, plain, (![A_661, B_662]: (r2_hidden('#skF_2'(A_661, B_662), A_661) | r1_tarski(A_661, B_662))), inference(cnfTransformation, [status(thm)], [f_38])).
% 16.17/7.74  tff(c_9470, plain, (![A_665, B_666]: (~v1_xboole_0(A_665) | r1_tarski(A_665, B_666))), inference(resolution, [status(thm)], [c_9448, c_2])).
% 16.17/7.74  tff(c_9480, plain, (![A_665]: (k1_xboole_0=A_665 | ~v1_xboole_0(A_665))), inference(resolution, [status(thm)], [c_9470, c_16])).
% 16.17/7.74  tff(c_9867, plain, (![B_738, C_739]: (a_2_5_lattice3(B_738, C_739)=k1_xboole_0 | ~v1_xboole_0(C_739) | ~l3_lattices(B_738) | ~v4_lattice3(B_738) | ~v10_lattices(B_738) | v2_struct_0(B_738))), inference(resolution, [status(thm)], [c_9862, c_9480])).
% 16.17/7.74  tff(c_9883, plain, (![B_742]: (a_2_5_lattice3(B_742, k1_xboole_0)=k1_xboole_0 | ~l3_lattices(B_742) | ~v4_lattice3(B_742) | ~v10_lattices(B_742) | v2_struct_0(B_742))), inference(resolution, [status(thm)], [c_12, c_9867])).
% 16.17/7.74  tff(c_9886, plain, (a_2_5_lattice3('#skF_11', k1_xboole_0)=k1_xboole_0 | ~l3_lattices('#skF_11') | ~v10_lattices('#skF_11') | v2_struct_0('#skF_11')), inference(resolution, [status(thm)], [c_104, c_9883])).
% 16.17/7.74  tff(c_9889, plain, (a_2_5_lattice3('#skF_11', k1_xboole_0)=k1_xboole_0 | v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_102, c_9886])).
% 16.17/7.74  tff(c_9890, plain, (a_2_5_lattice3('#skF_11', k1_xboole_0)=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_108, c_9889])).
% 16.17/7.74  tff(c_10335, plain, (![A_781, B_782, C_783]: (r2_hidden('#skF_10'(A_781, B_782, C_783), B_782) | r3_lattices(A_781, k15_lattice3(A_781, B_782), k15_lattice3(A_781, C_783)) | ~l3_lattices(A_781) | ~v4_lattice3(A_781) | ~v10_lattices(A_781) | v2_struct_0(A_781))), inference(cnfTransformation, [status(thm)], [f_253])).
% 16.17/7.74  tff(c_21146, plain, (![A_1300, B_1301, B_1302]: (r2_hidden('#skF_10'(A_1300, B_1301, a_2_5_lattice3(A_1300, B_1302)), B_1301) | r3_lattices(A_1300, k15_lattice3(A_1300, B_1301), k15_lattice3(A_1300, B_1302)) | ~l3_lattices(A_1300) | ~v4_lattice3(A_1300) | ~v10_lattices(A_1300) | v2_struct_0(A_1300) | ~l3_lattices(A_1300) | ~v4_lattice3(A_1300) | ~v10_lattices(A_1300) | v2_struct_0(A_1300))), inference(superposition, [status(thm), theory('equality')], [c_90, c_10335])).
% 16.17/7.74  tff(c_21200, plain, (![B_1301]: (r2_hidden('#skF_10'('#skF_11', B_1301, k1_xboole_0), B_1301) | r3_lattices('#skF_11', k15_lattice3('#skF_11', B_1301), k15_lattice3('#skF_11', k1_xboole_0)) | ~l3_lattices('#skF_11') | ~v4_lattice3('#skF_11') | ~v10_lattices('#skF_11') | v2_struct_0('#skF_11') | ~l3_lattices('#skF_11') | ~v4_lattice3('#skF_11') | ~v10_lattices('#skF_11') | v2_struct_0('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_9890, c_21146])).
% 16.17/7.74  tff(c_21222, plain, (![B_1301]: (r2_hidden('#skF_10'('#skF_11', B_1301, k1_xboole_0), B_1301) | r3_lattices('#skF_11', k15_lattice3('#skF_11', B_1301), k15_lattice3('#skF_11', k1_xboole_0)) | v2_struct_0('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_104, c_102, c_106, c_104, c_102, c_21200])).
% 16.17/7.74  tff(c_21224, plain, (![B_1303]: (r2_hidden('#skF_10'('#skF_11', B_1303, k1_xboole_0), B_1303) | r3_lattices('#skF_11', k15_lattice3('#skF_11', B_1303), k15_lattice3('#skF_11', k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_108, c_21222])).
% 16.17/7.74  tff(c_18, plain, (![B_13, A_12]: (~r1_tarski(B_13, A_12) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 16.17/7.74  tff(c_21353, plain, (![B_1307]: (~r1_tarski(B_1307, '#skF_10'('#skF_11', B_1307, k1_xboole_0)) | r3_lattices('#skF_11', k15_lattice3('#skF_11', B_1307), k15_lattice3('#skF_11', k1_xboole_0)))), inference(resolution, [status(thm)], [c_21224, c_18])).
% 16.17/7.74  tff(c_21425, plain, (r3_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), k15_lattice3('#skF_11', k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_21353])).
% 16.17/7.74  tff(c_21427, plain, (r1_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), k15_lattice3('#skF_11', k1_xboole_0)) | ~m1_subset_1(k15_lattice3('#skF_11', k1_xboole_0), u1_struct_0('#skF_11')) | ~l3_lattices('#skF_11') | ~v9_lattices('#skF_11') | ~v8_lattices('#skF_11') | ~v6_lattices('#skF_11') | v2_struct_0('#skF_11')), inference(resolution, [status(thm)], [c_21425, c_48])).
% 16.17/7.74  tff(c_21430, plain, (r1_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), k15_lattice3('#skF_11', k1_xboole_0)) | ~m1_subset_1(k15_lattice3('#skF_11', k1_xboole_0), u1_struct_0('#skF_11')) | v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_12960, c_13328, c_13353, c_102, c_21427])).
% 16.17/7.74  tff(c_21431, plain, (r1_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), k15_lattice3('#skF_11', k1_xboole_0)) | ~m1_subset_1(k15_lattice3('#skF_11', k1_xboole_0), u1_struct_0('#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_108, c_21430])).
% 16.17/7.74  tff(c_21432, plain, (~m1_subset_1(k15_lattice3('#skF_11', k1_xboole_0), u1_struct_0('#skF_11'))), inference(splitLeft, [status(thm)], [c_21431])).
% 16.17/7.74  tff(c_21435, plain, (~l3_lattices('#skF_11') | v2_struct_0('#skF_11')), inference(resolution, [status(thm)], [c_72, c_21432])).
% 16.17/7.74  tff(c_21438, plain, (v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_21435])).
% 16.17/7.74  tff(c_21440, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_21438])).
% 16.17/7.74  tff(c_21442, plain, (m1_subset_1(k15_lattice3('#skF_11', k1_xboole_0), u1_struct_0('#skF_11'))), inference(splitRight, [status(thm)], [c_21431])).
% 16.17/7.74  tff(c_9835, plain, (![C_732, A_730, B_731]: (~v1_xboole_0(C_732) | ~r2_hidden(A_730, a_2_5_lattice3(B_731, C_732)) | ~l3_lattices(B_731) | ~v4_lattice3(B_731) | ~v10_lattices(B_731) | v2_struct_0(B_731))), inference(resolution, [status(thm)], [c_9819, c_2])).
% 16.17/7.74  tff(c_9897, plain, (![A_730]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_730, k1_xboole_0) | ~l3_lattices('#skF_11') | ~v4_lattice3('#skF_11') | ~v10_lattices('#skF_11') | v2_struct_0('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_9890, c_9835])).
% 16.17/7.74  tff(c_9910, plain, (![A_730]: (~r2_hidden(A_730, k1_xboole_0) | v2_struct_0('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_104, c_102, c_12, c_9897])).
% 16.17/7.74  tff(c_9911, plain, (![A_730]: (~r2_hidden(A_730, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_108, c_9910])).
% 16.17/7.74  tff(c_23066, plain, (![A_1348, B_1349, C_1350]: (r2_hidden('#skF_10'(A_1348, a_2_5_lattice3(A_1348, B_1349), C_1350), a_2_5_lattice3(A_1348, B_1349)) | r3_lattices(A_1348, k15_lattice3(A_1348, B_1349), k15_lattice3(A_1348, C_1350)) | ~l3_lattices(A_1348) | ~v4_lattice3(A_1348) | ~v10_lattices(A_1348) | v2_struct_0(A_1348) | ~l3_lattices(A_1348) | ~v4_lattice3(A_1348) | ~v10_lattices(A_1348) | v2_struct_0(A_1348))), inference(superposition, [status(thm), theory('equality')], [c_90, c_10335])).
% 16.17/7.74  tff(c_23122, plain, (![C_1350]: (r2_hidden('#skF_10'('#skF_11', k1_xboole_0, C_1350), a_2_5_lattice3('#skF_11', k1_xboole_0)) | r3_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), k15_lattice3('#skF_11', C_1350)) | ~l3_lattices('#skF_11') | ~v4_lattice3('#skF_11') | ~v10_lattices('#skF_11') | v2_struct_0('#skF_11') | ~l3_lattices('#skF_11') | ~v4_lattice3('#skF_11') | ~v10_lattices('#skF_11') | v2_struct_0('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_9890, c_23066])).
% 16.17/7.74  tff(c_23141, plain, (![C_1350]: (r2_hidden('#skF_10'('#skF_11', k1_xboole_0, C_1350), k1_xboole_0) | r3_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), k15_lattice3('#skF_11', C_1350)) | v2_struct_0('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_104, c_102, c_106, c_104, c_102, c_9890, c_23122])).
% 16.17/7.74  tff(c_23149, plain, (![C_1351]: (r3_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), k15_lattice3('#skF_11', C_1351)))), inference(negUnitSimplification, [status(thm)], [c_108, c_9911, c_23141])).
% 16.17/7.74  tff(c_23155, plain, (![B_75]: (r3_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), B_75) | ~m1_subset_1(B_75, u1_struct_0('#skF_11')) | ~l3_lattices('#skF_11') | ~v4_lattice3('#skF_11') | ~v10_lattices('#skF_11') | v2_struct_0('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_23149])).
% 16.17/7.74  tff(c_23165, plain, (![B_75]: (r3_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), B_75) | ~m1_subset_1(B_75, u1_struct_0('#skF_11')) | v2_struct_0('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_104, c_102, c_23155])).
% 16.17/7.74  tff(c_23171, plain, (![B_1352]: (r3_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), B_1352) | ~m1_subset_1(B_1352, u1_struct_0('#skF_11')))), inference(negUnitSimplification, [status(thm)], [c_108, c_23165])).
% 16.17/7.74  tff(c_23179, plain, (![B_1352]: (r1_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), B_1352) | ~m1_subset_1(k15_lattice3('#skF_11', k1_xboole_0), u1_struct_0('#skF_11')) | ~l3_lattices('#skF_11') | ~v9_lattices('#skF_11') | ~v8_lattices('#skF_11') | ~v6_lattices('#skF_11') | v2_struct_0('#skF_11') | ~m1_subset_1(B_1352, u1_struct_0('#skF_11')))), inference(resolution, [status(thm)], [c_23171, c_48])).
% 16.17/7.74  tff(c_23190, plain, (![B_1352]: (r1_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), B_1352) | v2_struct_0('#skF_11') | ~m1_subset_1(B_1352, u1_struct_0('#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_12960, c_13328, c_13353, c_102, c_21442, c_23179])).
% 16.17/7.74  tff(c_23192, plain, (![B_1353]: (r1_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), B_1353) | ~m1_subset_1(B_1353, u1_struct_0('#skF_11')))), inference(negUnitSimplification, [status(thm)], [c_108, c_23190])).
% 16.17/7.74  tff(c_23194, plain, (![B_1353]: (k2_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), B_1353)=k15_lattice3('#skF_11', k1_xboole_0) | ~m1_subset_1(k15_lattice3('#skF_11', k1_xboole_0), u1_struct_0('#skF_11')) | ~l3_lattices('#skF_11') | ~v9_lattices('#skF_11') | ~v8_lattices('#skF_11') | v2_struct_0('#skF_11') | ~m1_subset_1(B_1353, u1_struct_0('#skF_11')))), inference(resolution, [status(thm)], [c_23192, c_52])).
% 16.17/7.74  tff(c_23197, plain, (![B_1353]: (k2_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), B_1353)=k15_lattice3('#skF_11', k1_xboole_0) | v2_struct_0('#skF_11') | ~m1_subset_1(B_1353, u1_struct_0('#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_13328, c_13353, c_102, c_21442, c_23194])).
% 16.17/7.74  tff(c_23199, plain, (![B_1354]: (k2_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), B_1354)=k15_lattice3('#skF_11', k1_xboole_0) | ~m1_subset_1(B_1354, u1_struct_0('#skF_11')))), inference(negUnitSimplification, [status(thm)], [c_108, c_23197])).
% 16.17/7.74  tff(c_23216, plain, (k2_lattices('#skF_11', k15_lattice3('#skF_11', k1_xboole_0), '#skF_4'('#skF_11'))=k15_lattice3('#skF_11', k1_xboole_0)), inference(resolution, [status(thm)], [c_12747, c_23199])).
% 16.17/7.74  tff(c_23261, plain, (k15_lattice3('#skF_11', k1_xboole_0)='#skF_4'('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_12964, c_23216])).
% 16.17/7.74  tff(c_23263, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12692, c_23261])).
% 16.17/7.74  tff(c_23265, plain, (~v6_lattices('#skF_11')), inference(splitRight, [status(thm)], [c_12947])).
% 16.17/7.74  tff(c_23268, plain, (~v10_lattices('#skF_11') | v2_struct_0('#skF_11') | ~l3_lattices('#skF_11')), inference(resolution, [status(thm)], [c_26, c_23265])).
% 16.17/7.74  tff(c_23271, plain, (v2_struct_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_106, c_23268])).
% 16.17/7.74  tff(c_23273, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_23271])).
% 16.17/7.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.17/7.74  
% 16.17/7.74  Inference rules
% 16.17/7.74  ----------------------
% 16.17/7.74  #Ref     : 0
% 16.17/7.74  #Sup     : 4834
% 16.17/7.74  #Fact    : 0
% 16.17/7.74  #Define  : 0
% 16.17/7.74  #Split   : 25
% 16.17/7.74  #Chain   : 0
% 16.17/7.74  #Close   : 0
% 16.17/7.74  
% 16.17/7.74  Ordering : KBO
% 16.17/7.74  
% 16.17/7.74  Simplification rules
% 16.17/7.74  ----------------------
% 16.17/7.74  #Subsume      : 1954
% 16.17/7.74  #Demod        : 5047
% 16.17/7.74  #Tautology    : 1105
% 16.17/7.74  #SimpNegUnit  : 1191
% 16.17/7.74  #BackRed      : 6
% 16.17/7.74  
% 16.17/7.74  #Partial instantiations: 0
% 16.17/7.74  #Strategies tried      : 1
% 16.17/7.74  
% 16.17/7.74  Timing (in seconds)
% 16.17/7.74  ----------------------
% 16.17/7.75  Preprocessing        : 0.39
% 16.17/7.75  Parsing              : 0.19
% 16.17/7.75  CNF conversion       : 0.04
% 16.17/7.75  Main loop            : 6.53
% 16.17/7.75  Inferencing          : 1.14
% 16.17/7.75  Reduction            : 1.03
% 16.17/7.75  Demodulation         : 0.71
% 16.17/7.75  BG Simplification    : 0.10
% 16.17/7.75  Subsumption          : 4.03
% 16.17/7.75  Abstraction          : 0.16
% 16.17/7.75  MUC search           : 0.00
% 16.17/7.75  Cooper               : 0.00
% 16.17/7.75  Total                : 6.99
% 16.17/7.75  Index Insertion      : 0.00
% 16.17/7.75  Index Deletion       : 0.00
% 16.17/7.75  Index Matching       : 0.00
% 16.17/7.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
