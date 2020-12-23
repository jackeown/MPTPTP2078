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
% DateTime   : Thu Dec  3 10:24:53 EST 2020

% Result     : Theorem 29.46s
% Output     : CNFRefutation 29.46s
% Verified   : 
% Statistics : Number of formulae       :  158 (1429 expanded)
%              Number of leaves         :   54 ( 521 expanded)
%              Depth                    :   19
%              Number of atoms          :  580 (6875 expanded)
%              Number of equality atoms :   65 (1296 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r1_lattices > r2_hidden > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k16_lattice3 > k15_lattice3 > a_2_6_lattice3 > a_2_5_lattice3 > #nlpp > u1_struct_0 > k5_lattices > k1_xboole_0 > #skF_7 > #skF_2 > #skF_4 > #skF_3 > #skF_10 > #skF_5 > #skF_9 > #skF_8 > #skF_1 > #skF_6

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

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k16_lattice3,type,(
    k16_lattice3: ( $i * $i ) > $i )).

tff(k15_lattice3,type,(
    k15_lattice3: ( $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff(k5_lattices,type,(
    k5_lattices: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(a_2_6_lattice3,type,(
    a_2_6_lattice3: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_241,negated_conjecture,(
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

tff(f_79,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_54,axiom,(
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

tff(f_183,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k15_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

tff(f_115,axiom,(
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

tff(f_133,axiom,(
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

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_206,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_220,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( k15_lattice3(A,B) = k15_lattice3(A,a_2_5_lattice3(A,B))
          & k16_lattice3(A,B) = k16_lattice3(A,a_2_6_lattice3(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_lattice3)).

tff(f_161,axiom,(
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

tff(f_98,axiom,(
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

tff(f_176,axiom,(
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

tff(f_73,axiom,(
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

tff(c_98,plain,(
    ~ v2_struct_0('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_92,plain,(
    l3_lattices('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_103,plain,(
    ! [A_98] :
      ( l1_lattices(A_98)
      | ~ l3_lattices(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_107,plain,(
    l1_lattices('#skF_10') ),
    inference(resolution,[status(thm)],[c_92,c_103])).

tff(c_96,plain,(
    v10_lattices('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_90,plain,
    ( k15_lattice3('#skF_10',k1_xboole_0) != k5_lattices('#skF_10')
    | ~ l3_lattices('#skF_10')
    | ~ v13_lattices('#skF_10')
    | ~ v10_lattices('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_100,plain,
    ( k15_lattice3('#skF_10',k1_xboole_0) != k5_lattices('#skF_10')
    | ~ v13_lattices('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_92,c_90])).

tff(c_101,plain,
    ( k15_lattice3('#skF_10',k1_xboole_0) != k5_lattices('#skF_10')
    | ~ v13_lattices('#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_100])).

tff(c_113,plain,(
    ~ v13_lattices('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_94,plain,(
    v4_lattice3('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_12,plain,(
    ! [A_4] :
      ( v6_lattices(A_4)
      | ~ v10_lattices(A_4)
      | v2_struct_0(A_4)
      | ~ l3_lattices(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [A_4] :
      ( v8_lattices(A_4)
      | ~ v10_lattices(A_4)
      | v2_struct_0(A_4)
      | ~ l3_lattices(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [A_4] :
      ( v9_lattices(A_4)
      | ~ v10_lattices(A_4)
      | v2_struct_0(A_4)
      | ~ l3_lattices(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_72,plain,(
    ! [A_79,B_80] :
      ( m1_subset_1(k15_lattice3(A_79,B_80),u1_struct_0(A_79))
      | ~ l3_lattices(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_38,plain,(
    ! [A_23,B_32] :
      ( m1_subset_1('#skF_3'(A_23,B_32),u1_struct_0(A_23))
      | v13_lattices(A_23)
      | ~ m1_subset_1(B_32,u1_struct_0(A_23))
      | ~ l1_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_50,plain,(
    ! [A_34,B_46,C_52] :
      ( r2_hidden('#skF_4'(A_34,B_46,C_52),C_52)
      | r4_lattice3(A_34,B_46,C_52)
      | ~ m1_subset_1(B_46,u1_struct_0(A_34))
      | ~ l3_lattices(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_287,plain,(
    ! [A_144,B_145,C_146] :
      ( r2_hidden('#skF_9'(A_144,B_145,C_146),C_146)
      | ~ r2_hidden(A_144,a_2_5_lattice3(B_145,C_146))
      | ~ l3_lattices(B_145)
      | ~ v4_lattice3(B_145)
      | ~ v10_lattices(B_145)
      | v2_struct_0(B_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( ~ r1_tarski(B_3,A_2)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_328,plain,(
    ! [C_162,A_163,B_164] :
      ( ~ r1_tarski(C_162,'#skF_9'(A_163,B_164,C_162))
      | ~ r2_hidden(A_163,a_2_5_lattice3(B_164,C_162))
      | ~ l3_lattices(B_164)
      | ~ v4_lattice3(B_164)
      | ~ v10_lattices(B_164)
      | v2_struct_0(B_164) ) ),
    inference(resolution,[status(thm)],[c_287,c_4])).

tff(c_344,plain,(
    ! [A_168,B_169] :
      ( ~ r2_hidden(A_168,a_2_5_lattice3(B_169,k1_xboole_0))
      | ~ l3_lattices(B_169)
      | ~ v4_lattice3(B_169)
      | ~ v10_lattices(B_169)
      | v2_struct_0(B_169) ) ),
    inference(resolution,[status(thm)],[c_2,c_328])).

tff(c_354,plain,(
    ! [B_169,A_34,B_46] :
      ( ~ l3_lattices(B_169)
      | ~ v4_lattice3(B_169)
      | ~ v10_lattices(B_169)
      | v2_struct_0(B_169)
      | r4_lattice3(A_34,B_46,a_2_5_lattice3(B_169,k1_xboole_0))
      | ~ m1_subset_1(B_46,u1_struct_0(A_34))
      | ~ l3_lattices(A_34)
      | v2_struct_0(A_34) ) ),
    inference(resolution,[status(thm)],[c_50,c_344])).

tff(c_86,plain,(
    ! [A_94,B_96] :
      ( k15_lattice3(A_94,a_2_5_lattice3(A_94,B_96)) = k15_lattice3(A_94,B_96)
      | ~ l3_lattices(A_94)
      | ~ v4_lattice3(A_94)
      | ~ v10_lattices(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_759,plain,(
    ! [A_268,B_269,D_270] :
      ( r1_lattices(A_268,k15_lattice3(A_268,B_269),D_270)
      | ~ r4_lattice3(A_268,D_270,B_269)
      | ~ m1_subset_1(D_270,u1_struct_0(A_268))
      | ~ m1_subset_1(k15_lattice3(A_268,B_269),u1_struct_0(A_268))
      | ~ v4_lattice3(A_268)
      | ~ v10_lattices(A_268)
      | ~ l3_lattices(A_268)
      | v2_struct_0(A_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_765,plain,(
    ! [A_271,B_272,D_273] :
      ( r1_lattices(A_271,k15_lattice3(A_271,B_272),D_273)
      | ~ r4_lattice3(A_271,D_273,B_272)
      | ~ m1_subset_1(D_273,u1_struct_0(A_271))
      | ~ v4_lattice3(A_271)
      | ~ v10_lattices(A_271)
      | ~ l3_lattices(A_271)
      | v2_struct_0(A_271) ) ),
    inference(resolution,[status(thm)],[c_72,c_759])).

tff(c_967,plain,(
    ! [A_329,B_330,D_331] :
      ( r1_lattices(A_329,k15_lattice3(A_329,B_330),D_331)
      | ~ r4_lattice3(A_329,D_331,a_2_5_lattice3(A_329,B_330))
      | ~ m1_subset_1(D_331,u1_struct_0(A_329))
      | ~ v4_lattice3(A_329)
      | ~ v10_lattices(A_329)
      | ~ l3_lattices(A_329)
      | v2_struct_0(A_329)
      | ~ l3_lattices(A_329)
      | ~ v4_lattice3(A_329)
      | ~ v10_lattices(A_329)
      | v2_struct_0(A_329) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_765])).

tff(c_987,plain,(
    ! [B_332,B_333] :
      ( r1_lattices(B_332,k15_lattice3(B_332,k1_xboole_0),B_333)
      | ~ v4_lattice3(B_332)
      | ~ v10_lattices(B_332)
      | ~ m1_subset_1(B_333,u1_struct_0(B_332))
      | ~ l3_lattices(B_332)
      | v2_struct_0(B_332) ) ),
    inference(resolution,[status(thm)],[c_354,c_967])).

tff(c_34,plain,(
    ! [A_16,B_20,C_22] :
      ( k2_lattices(A_16,B_20,C_22) = B_20
      | ~ r1_lattices(A_16,B_20,C_22)
      | ~ m1_subset_1(C_22,u1_struct_0(A_16))
      | ~ m1_subset_1(B_20,u1_struct_0(A_16))
      | ~ l3_lattices(A_16)
      | ~ v9_lattices(A_16)
      | ~ v8_lattices(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1046,plain,(
    ! [B_345,B_346] :
      ( k2_lattices(B_345,k15_lattice3(B_345,k1_xboole_0),B_346) = k15_lattice3(B_345,k1_xboole_0)
      | ~ m1_subset_1(k15_lattice3(B_345,k1_xboole_0),u1_struct_0(B_345))
      | ~ v9_lattices(B_345)
      | ~ v8_lattices(B_345)
      | ~ v4_lattice3(B_345)
      | ~ v10_lattices(B_345)
      | ~ m1_subset_1(B_346,u1_struct_0(B_345))
      | ~ l3_lattices(B_345)
      | v2_struct_0(B_345) ) ),
    inference(resolution,[status(thm)],[c_987,c_34])).

tff(c_1051,plain,(
    ! [A_347,B_348] :
      ( k2_lattices(A_347,k15_lattice3(A_347,k1_xboole_0),B_348) = k15_lattice3(A_347,k1_xboole_0)
      | ~ v9_lattices(A_347)
      | ~ v8_lattices(A_347)
      | ~ v4_lattice3(A_347)
      | ~ v10_lattices(A_347)
      | ~ m1_subset_1(B_348,u1_struct_0(A_347))
      | ~ l3_lattices(A_347)
      | v2_struct_0(A_347) ) ),
    inference(resolution,[status(thm)],[c_72,c_1046])).

tff(c_1077,plain,(
    ! [A_23,B_32] :
      ( k2_lattices(A_23,k15_lattice3(A_23,k1_xboole_0),'#skF_3'(A_23,B_32)) = k15_lattice3(A_23,k1_xboole_0)
      | ~ v9_lattices(A_23)
      | ~ v8_lattices(A_23)
      | ~ v4_lattice3(A_23)
      | ~ v10_lattices(A_23)
      | ~ l3_lattices(A_23)
      | v13_lattices(A_23)
      | ~ m1_subset_1(B_32,u1_struct_0(A_23))
      | ~ l1_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(resolution,[status(thm)],[c_38,c_1051])).

tff(c_1208,plain,(
    ! [A_365,B_366] :
      ( k2_lattices(A_365,k15_lattice3(A_365,k1_xboole_0),'#skF_3'(A_365,B_366)) = k15_lattice3(A_365,k1_xboole_0)
      | ~ v9_lattices(A_365)
      | ~ v8_lattices(A_365)
      | ~ v4_lattice3(A_365)
      | ~ v10_lattices(A_365)
      | ~ l3_lattices(A_365)
      | v13_lattices(A_365)
      | ~ m1_subset_1(B_366,u1_struct_0(A_365))
      | ~ l1_lattices(A_365)
      | v2_struct_0(A_365) ) ),
    inference(resolution,[status(thm)],[c_38,c_1051])).

tff(c_408,plain,(
    ! [A_189,C_190,B_191] :
      ( k2_lattices(A_189,C_190,B_191) = k2_lattices(A_189,B_191,C_190)
      | ~ m1_subset_1(C_190,u1_struct_0(A_189))
      | ~ m1_subset_1(B_191,u1_struct_0(A_189))
      | ~ v6_lattices(A_189)
      | ~ l1_lattices(A_189)
      | v2_struct_0(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_542,plain,(
    ! [A_226,B_227,B_228] :
      ( k2_lattices(A_226,k15_lattice3(A_226,B_227),B_228) = k2_lattices(A_226,B_228,k15_lattice3(A_226,B_227))
      | ~ m1_subset_1(B_228,u1_struct_0(A_226))
      | ~ v6_lattices(A_226)
      | ~ l1_lattices(A_226)
      | ~ l3_lattices(A_226)
      | v2_struct_0(A_226) ) ),
    inference(resolution,[status(thm)],[c_72,c_408])).

tff(c_565,plain,(
    ! [A_23,B_227,B_32] :
      ( k2_lattices(A_23,k15_lattice3(A_23,B_227),'#skF_3'(A_23,B_32)) = k2_lattices(A_23,'#skF_3'(A_23,B_32),k15_lattice3(A_23,B_227))
      | ~ v6_lattices(A_23)
      | ~ l3_lattices(A_23)
      | v13_lattices(A_23)
      | ~ m1_subset_1(B_32,u1_struct_0(A_23))
      | ~ l1_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(resolution,[status(thm)],[c_38,c_542])).

tff(c_22686,plain,(
    ! [A_1199,B_1200] :
      ( k2_lattices(A_1199,'#skF_3'(A_1199,B_1200),k15_lattice3(A_1199,k1_xboole_0)) = k15_lattice3(A_1199,k1_xboole_0)
      | ~ v6_lattices(A_1199)
      | ~ l3_lattices(A_1199)
      | v13_lattices(A_1199)
      | ~ m1_subset_1(B_1200,u1_struct_0(A_1199))
      | ~ l1_lattices(A_1199)
      | v2_struct_0(A_1199)
      | ~ v9_lattices(A_1199)
      | ~ v8_lattices(A_1199)
      | ~ v4_lattice3(A_1199)
      | ~ v10_lattices(A_1199)
      | ~ l3_lattices(A_1199)
      | v13_lattices(A_1199)
      | ~ m1_subset_1(B_1200,u1_struct_0(A_1199))
      | ~ l1_lattices(A_1199)
      | v2_struct_0(A_1199) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1208,c_565])).

tff(c_36,plain,(
    ! [A_23,B_32] :
      ( k2_lattices(A_23,'#skF_3'(A_23,B_32),B_32) != B_32
      | k2_lattices(A_23,B_32,'#skF_3'(A_23,B_32)) != B_32
      | v13_lattices(A_23)
      | ~ m1_subset_1(B_32,u1_struct_0(A_23))
      | ~ l1_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_22706,plain,(
    ! [A_1201] :
      ( k2_lattices(A_1201,k15_lattice3(A_1201,k1_xboole_0),'#skF_3'(A_1201,k15_lattice3(A_1201,k1_xboole_0))) != k15_lattice3(A_1201,k1_xboole_0)
      | ~ v6_lattices(A_1201)
      | ~ v9_lattices(A_1201)
      | ~ v8_lattices(A_1201)
      | ~ v4_lattice3(A_1201)
      | ~ v10_lattices(A_1201)
      | ~ l3_lattices(A_1201)
      | v13_lattices(A_1201)
      | ~ m1_subset_1(k15_lattice3(A_1201,k1_xboole_0),u1_struct_0(A_1201))
      | ~ l1_lattices(A_1201)
      | v2_struct_0(A_1201) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22686,c_36])).

tff(c_22738,plain,(
    ! [A_1207] :
      ( ~ v6_lattices(A_1207)
      | ~ v9_lattices(A_1207)
      | ~ v8_lattices(A_1207)
      | ~ v4_lattice3(A_1207)
      | ~ v10_lattices(A_1207)
      | ~ l3_lattices(A_1207)
      | v13_lattices(A_1207)
      | ~ m1_subset_1(k15_lattice3(A_1207,k1_xboole_0),u1_struct_0(A_1207))
      | ~ l1_lattices(A_1207)
      | v2_struct_0(A_1207) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1077,c_22706])).

tff(c_22744,plain,(
    ! [A_1208] :
      ( ~ v6_lattices(A_1208)
      | ~ v9_lattices(A_1208)
      | ~ v8_lattices(A_1208)
      | ~ v4_lattice3(A_1208)
      | ~ v10_lattices(A_1208)
      | v13_lattices(A_1208)
      | ~ l1_lattices(A_1208)
      | ~ l3_lattices(A_1208)
      | v2_struct_0(A_1208) ) ),
    inference(resolution,[status(thm)],[c_72,c_22738])).

tff(c_22749,plain,(
    ! [A_1209] :
      ( ~ v6_lattices(A_1209)
      | ~ v8_lattices(A_1209)
      | ~ v4_lattice3(A_1209)
      | v13_lattices(A_1209)
      | ~ l1_lattices(A_1209)
      | ~ v10_lattices(A_1209)
      | v2_struct_0(A_1209)
      | ~ l3_lattices(A_1209) ) ),
    inference(resolution,[status(thm)],[c_6,c_22744])).

tff(c_22754,plain,(
    ! [A_1210] :
      ( ~ v6_lattices(A_1210)
      | ~ v4_lattice3(A_1210)
      | v13_lattices(A_1210)
      | ~ l1_lattices(A_1210)
      | ~ v10_lattices(A_1210)
      | v2_struct_0(A_1210)
      | ~ l3_lattices(A_1210) ) ),
    inference(resolution,[status(thm)],[c_8,c_22749])).

tff(c_22759,plain,(
    ! [A_1211] :
      ( ~ v4_lattice3(A_1211)
      | v13_lattices(A_1211)
      | ~ l1_lattices(A_1211)
      | ~ v10_lattices(A_1211)
      | v2_struct_0(A_1211)
      | ~ l3_lattices(A_1211) ) ),
    inference(resolution,[status(thm)],[c_12,c_22754])).

tff(c_22762,plain,
    ( v13_lattices('#skF_10')
    | ~ l1_lattices('#skF_10')
    | ~ v10_lattices('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l3_lattices('#skF_10') ),
    inference(resolution,[status(thm)],[c_94,c_22759])).

tff(c_22765,plain,
    ( v13_lattices('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_96,c_107,c_22762])).

tff(c_22767,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_113,c_22765])).

tff(c_22769,plain,(
    v13_lattices('#skF_10') ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_40,plain,(
    ! [A_23] :
      ( m1_subset_1('#skF_2'(A_23),u1_struct_0(A_23))
      | ~ v13_lattices(A_23)
      | ~ l1_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_22916,plain,(
    ! [A_1251,B_1252] :
      ( m1_subset_1('#skF_1'(A_1251,B_1252),u1_struct_0(A_1251))
      | k5_lattices(A_1251) = B_1252
      | ~ m1_subset_1(B_1252,u1_struct_0(A_1251))
      | ~ v13_lattices(A_1251)
      | ~ l1_lattices(A_1251)
      | v2_struct_0(A_1251) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_44,plain,(
    ! [A_23,C_31] :
      ( k2_lattices(A_23,'#skF_2'(A_23),C_31) = '#skF_2'(A_23)
      | ~ m1_subset_1(C_31,u1_struct_0(A_23))
      | ~ v13_lattices(A_23)
      | ~ l1_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_22922,plain,(
    ! [A_1251,B_1252] :
      ( k2_lattices(A_1251,'#skF_2'(A_1251),'#skF_1'(A_1251,B_1252)) = '#skF_2'(A_1251)
      | k5_lattices(A_1251) = B_1252
      | ~ m1_subset_1(B_1252,u1_struct_0(A_1251))
      | ~ v13_lattices(A_1251)
      | ~ l1_lattices(A_1251)
      | v2_struct_0(A_1251) ) ),
    inference(resolution,[status(thm)],[c_22916,c_44])).

tff(c_42,plain,(
    ! [A_23,C_31] :
      ( k2_lattices(A_23,C_31,'#skF_2'(A_23)) = '#skF_2'(A_23)
      | ~ m1_subset_1(C_31,u1_struct_0(A_23))
      | ~ v13_lattices(A_23)
      | ~ l1_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_22921,plain,(
    ! [A_1251,B_1252] :
      ( k2_lattices(A_1251,'#skF_1'(A_1251,B_1252),'#skF_2'(A_1251)) = '#skF_2'(A_1251)
      | k5_lattices(A_1251) = B_1252
      | ~ m1_subset_1(B_1252,u1_struct_0(A_1251))
      | ~ v13_lattices(A_1251)
      | ~ l1_lattices(A_1251)
      | v2_struct_0(A_1251) ) ),
    inference(resolution,[status(thm)],[c_22916,c_42])).

tff(c_23353,plain,(
    ! [A_1366,B_1367] :
      ( k2_lattices(A_1366,'#skF_1'(A_1366,B_1367),B_1367) != B_1367
      | k2_lattices(A_1366,B_1367,'#skF_1'(A_1366,B_1367)) != B_1367
      | k5_lattices(A_1366) = B_1367
      | ~ m1_subset_1(B_1367,u1_struct_0(A_1366))
      | ~ v13_lattices(A_1366)
      | ~ l1_lattices(A_1366)
      | v2_struct_0(A_1366) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_23358,plain,(
    ! [A_1368] :
      ( k2_lattices(A_1368,'#skF_2'(A_1368),'#skF_1'(A_1368,'#skF_2'(A_1368))) != '#skF_2'(A_1368)
      | k5_lattices(A_1368) = '#skF_2'(A_1368)
      | ~ m1_subset_1('#skF_2'(A_1368),u1_struct_0(A_1368))
      | ~ v13_lattices(A_1368)
      | ~ l1_lattices(A_1368)
      | v2_struct_0(A_1368) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22921,c_23353])).

tff(c_23364,plain,(
    ! [A_1369] :
      ( k5_lattices(A_1369) = '#skF_2'(A_1369)
      | ~ m1_subset_1('#skF_2'(A_1369),u1_struct_0(A_1369))
      | ~ v13_lattices(A_1369)
      | ~ l1_lattices(A_1369)
      | v2_struct_0(A_1369) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22922,c_23358])).

tff(c_23369,plain,(
    ! [A_1370] :
      ( k5_lattices(A_1370) = '#skF_2'(A_1370)
      | ~ v13_lattices(A_1370)
      | ~ l1_lattices(A_1370)
      | v2_struct_0(A_1370) ) ),
    inference(resolution,[status(thm)],[c_40,c_23364])).

tff(c_23372,plain,
    ( k5_lattices('#skF_10') = '#skF_2'('#skF_10')
    | ~ v13_lattices('#skF_10')
    | ~ l1_lattices('#skF_10') ),
    inference(resolution,[status(thm)],[c_23369,c_98])).

tff(c_23375,plain,(
    k5_lattices('#skF_10') = '#skF_2'('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_22769,c_23372])).

tff(c_22768,plain,(
    k15_lattice3('#skF_10',k1_xboole_0) != k5_lattices('#skF_10') ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_23376,plain,(
    k15_lattice3('#skF_10',k1_xboole_0) != '#skF_2'('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23375,c_22768])).

tff(c_23035,plain,(
    ! [A_1298,C_1299] :
      ( k2_lattices(A_1298,C_1299,k5_lattices(A_1298)) = k5_lattices(A_1298)
      | ~ m1_subset_1(C_1299,u1_struct_0(A_1298))
      | ~ m1_subset_1(k5_lattices(A_1298),u1_struct_0(A_1298))
      | ~ v13_lattices(A_1298)
      | ~ l1_lattices(A_1298)
      | v2_struct_0(A_1298) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_23061,plain,(
    ! [A_23] :
      ( k2_lattices(A_23,'#skF_2'(A_23),k5_lattices(A_23)) = k5_lattices(A_23)
      | ~ m1_subset_1(k5_lattices(A_23),u1_struct_0(A_23))
      | ~ v13_lattices(A_23)
      | ~ l1_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(resolution,[status(thm)],[c_40,c_23035])).

tff(c_23393,plain,
    ( k2_lattices('#skF_10','#skF_2'('#skF_10'),k5_lattices('#skF_10')) = k5_lattices('#skF_10')
    | ~ m1_subset_1('#skF_2'('#skF_10'),u1_struct_0('#skF_10'))
    | ~ v13_lattices('#skF_10')
    | ~ l1_lattices('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_23375,c_23061])).

tff(c_23418,plain,
    ( k2_lattices('#skF_10','#skF_2'('#skF_10'),'#skF_2'('#skF_10')) = '#skF_2'('#skF_10')
    | ~ m1_subset_1('#skF_2'('#skF_10'),u1_struct_0('#skF_10'))
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_22769,c_23375,c_23375,c_23393])).

tff(c_23419,plain,
    ( k2_lattices('#skF_10','#skF_2'('#skF_10'),'#skF_2'('#skF_10')) = '#skF_2'('#skF_10')
    | ~ m1_subset_1('#skF_2'('#skF_10'),u1_struct_0('#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_23418])).

tff(c_23450,plain,(
    ~ m1_subset_1('#skF_2'('#skF_10'),u1_struct_0('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_23419])).

tff(c_23453,plain,
    ( ~ v13_lattices('#skF_10')
    | ~ l1_lattices('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_40,c_23450])).

tff(c_23456,plain,(
    v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_22769,c_23453])).

tff(c_23458,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_23456])).

tff(c_23460,plain,(
    m1_subset_1('#skF_2'('#skF_10'),u1_struct_0('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_23419])).

tff(c_32,plain,(
    ! [A_16,B_20,C_22] :
      ( r1_lattices(A_16,B_20,C_22)
      | k2_lattices(A_16,B_20,C_22) != B_20
      | ~ m1_subset_1(C_22,u1_struct_0(A_16))
      | ~ m1_subset_1(B_20,u1_struct_0(A_16))
      | ~ l3_lattices(A_16)
      | ~ v9_lattices(A_16)
      | ~ v8_lattices(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_23525,plain,(
    ! [B_20] :
      ( r1_lattices('#skF_10',B_20,'#skF_2'('#skF_10'))
      | k2_lattices('#skF_10',B_20,'#skF_2'('#skF_10')) != B_20
      | ~ m1_subset_1(B_20,u1_struct_0('#skF_10'))
      | ~ l3_lattices('#skF_10')
      | ~ v9_lattices('#skF_10')
      | ~ v8_lattices('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_23460,c_32])).

tff(c_23547,plain,(
    ! [B_20] :
      ( r1_lattices('#skF_10',B_20,'#skF_2'('#skF_10'))
      | k2_lattices('#skF_10',B_20,'#skF_2'('#skF_10')) != B_20
      | ~ m1_subset_1(B_20,u1_struct_0('#skF_10'))
      | ~ v9_lattices('#skF_10')
      | ~ v8_lattices('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_23525])).

tff(c_23548,plain,(
    ! [B_20] :
      ( r1_lattices('#skF_10',B_20,'#skF_2'('#skF_10'))
      | k2_lattices('#skF_10',B_20,'#skF_2'('#skF_10')) != B_20
      | ~ m1_subset_1(B_20,u1_struct_0('#skF_10'))
      | ~ v9_lattices('#skF_10')
      | ~ v8_lattices('#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_23547])).

tff(c_23802,plain,(
    ~ v8_lattices('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_23548])).

tff(c_23805,plain,
    ( ~ v10_lattices('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l3_lattices('#skF_10') ),
    inference(resolution,[status(thm)],[c_8,c_23802])).

tff(c_23808,plain,(
    v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_96,c_23805])).

tff(c_23810,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_23808])).

tff(c_23812,plain,(
    v8_lattices('#skF_10') ),
    inference(splitRight,[status(thm)],[c_23548])).

tff(c_23811,plain,(
    ! [B_20] :
      ( ~ v9_lattices('#skF_10')
      | r1_lattices('#skF_10',B_20,'#skF_2'('#skF_10'))
      | k2_lattices('#skF_10',B_20,'#skF_2'('#skF_10')) != B_20
      | ~ m1_subset_1(B_20,u1_struct_0('#skF_10')) ) ),
    inference(splitRight,[status(thm)],[c_23548])).

tff(c_23830,plain,(
    ~ v9_lattices('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_23811])).

tff(c_23833,plain,
    ( ~ v10_lattices('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l3_lattices('#skF_10') ),
    inference(resolution,[status(thm)],[c_6,c_23830])).

tff(c_23836,plain,(
    v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_96,c_23833])).

tff(c_23838,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_23836])).

tff(c_23840,plain,(
    v9_lattices('#skF_10') ),
    inference(splitRight,[status(thm)],[c_23811])).

tff(c_23062,plain,(
    ! [A_79,B_80] :
      ( k2_lattices(A_79,k15_lattice3(A_79,B_80),k5_lattices(A_79)) = k5_lattices(A_79)
      | ~ m1_subset_1(k5_lattices(A_79),u1_struct_0(A_79))
      | ~ v13_lattices(A_79)
      | ~ l1_lattices(A_79)
      | ~ l3_lattices(A_79)
      | v2_struct_0(A_79) ) ),
    inference(resolution,[status(thm)],[c_72,c_23035])).

tff(c_23379,plain,(
    ! [B_80] :
      ( k2_lattices('#skF_10',k15_lattice3('#skF_10',B_80),k5_lattices('#skF_10')) = k5_lattices('#skF_10')
      | ~ m1_subset_1('#skF_2'('#skF_10'),u1_struct_0('#skF_10'))
      | ~ v13_lattices('#skF_10')
      | ~ l1_lattices('#skF_10')
      | ~ l3_lattices('#skF_10')
      | v2_struct_0('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23375,c_23062])).

tff(c_23397,plain,(
    ! [B_80] :
      ( k2_lattices('#skF_10',k15_lattice3('#skF_10',B_80),'#skF_2'('#skF_10')) = '#skF_2'('#skF_10')
      | ~ m1_subset_1('#skF_2'('#skF_10'),u1_struct_0('#skF_10'))
      | v2_struct_0('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_107,c_22769,c_23375,c_23375,c_23379])).

tff(c_23398,plain,(
    ! [B_80] :
      ( k2_lattices('#skF_10',k15_lattice3('#skF_10',B_80),'#skF_2'('#skF_10')) = '#skF_2'('#skF_10')
      | ~ m1_subset_1('#skF_2'('#skF_10'),u1_struct_0('#skF_10')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_23397])).

tff(c_23604,plain,(
    ! [B_80] : k2_lattices('#skF_10',k15_lattice3('#skF_10',B_80),'#skF_2'('#skF_10')) = '#skF_2'('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23460,c_23398])).

tff(c_22974,plain,(
    ! [A_1271,B_1272,C_1273] :
      ( r2_hidden('#skF_9'(A_1271,B_1272,C_1273),C_1273)
      | ~ r2_hidden(A_1271,a_2_5_lattice3(B_1272,C_1273))
      | ~ l3_lattices(B_1272)
      | ~ v4_lattice3(B_1272)
      | ~ v10_lattices(B_1272)
      | v2_struct_0(B_1272) ) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_22984,plain,(
    ! [C_1274,A_1275,B_1276] :
      ( ~ r1_tarski(C_1274,'#skF_9'(A_1275,B_1276,C_1274))
      | ~ r2_hidden(A_1275,a_2_5_lattice3(B_1276,C_1274))
      | ~ l3_lattices(B_1276)
      | ~ v4_lattice3(B_1276)
      | ~ v10_lattices(B_1276)
      | v2_struct_0(B_1276) ) ),
    inference(resolution,[status(thm)],[c_22974,c_4])).

tff(c_22989,plain,(
    ! [A_1277,B_1278] :
      ( ~ r2_hidden(A_1277,a_2_5_lattice3(B_1278,k1_xboole_0))
      | ~ l3_lattices(B_1278)
      | ~ v4_lattice3(B_1278)
      | ~ v10_lattices(B_1278)
      | v2_struct_0(B_1278) ) ),
    inference(resolution,[status(thm)],[c_2,c_22984])).

tff(c_22999,plain,(
    ! [B_1278,A_34,B_46] :
      ( ~ l3_lattices(B_1278)
      | ~ v4_lattice3(B_1278)
      | ~ v10_lattices(B_1278)
      | v2_struct_0(B_1278)
      | r4_lattice3(A_34,B_46,a_2_5_lattice3(B_1278,k1_xboole_0))
      | ~ m1_subset_1(B_46,u1_struct_0(A_34))
      | ~ l3_lattices(A_34)
      | v2_struct_0(A_34) ) ),
    inference(resolution,[status(thm)],[c_50,c_22989])).

tff(c_23708,plain,(
    ! [A_1383,B_1384,D_1385] :
      ( r1_lattices(A_1383,k15_lattice3(A_1383,B_1384),D_1385)
      | ~ r4_lattice3(A_1383,D_1385,B_1384)
      | ~ m1_subset_1(D_1385,u1_struct_0(A_1383))
      | ~ m1_subset_1(k15_lattice3(A_1383,B_1384),u1_struct_0(A_1383))
      | ~ v4_lattice3(A_1383)
      | ~ v10_lattices(A_1383)
      | ~ l3_lattices(A_1383)
      | v2_struct_0(A_1383) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_23856,plain,(
    ! [A_1390,B_1391,D_1392] :
      ( r1_lattices(A_1390,k15_lattice3(A_1390,B_1391),D_1392)
      | ~ r4_lattice3(A_1390,D_1392,B_1391)
      | ~ m1_subset_1(D_1392,u1_struct_0(A_1390))
      | ~ v4_lattice3(A_1390)
      | ~ v10_lattices(A_1390)
      | ~ l3_lattices(A_1390)
      | v2_struct_0(A_1390) ) ),
    inference(resolution,[status(thm)],[c_72,c_23708])).

tff(c_24710,plain,(
    ! [A_1477,B_1478,D_1479] :
      ( r1_lattices(A_1477,k15_lattice3(A_1477,B_1478),D_1479)
      | ~ r4_lattice3(A_1477,D_1479,a_2_5_lattice3(A_1477,B_1478))
      | ~ m1_subset_1(D_1479,u1_struct_0(A_1477))
      | ~ v4_lattice3(A_1477)
      | ~ v10_lattices(A_1477)
      | ~ l3_lattices(A_1477)
      | v2_struct_0(A_1477)
      | ~ l3_lattices(A_1477)
      | ~ v4_lattice3(A_1477)
      | ~ v10_lattices(A_1477)
      | v2_struct_0(A_1477) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_23856])).

tff(c_24752,plain,(
    ! [B_1481,B_1482] :
      ( r1_lattices(B_1481,k15_lattice3(B_1481,k1_xboole_0),B_1482)
      | ~ v4_lattice3(B_1481)
      | ~ v10_lattices(B_1481)
      | ~ m1_subset_1(B_1482,u1_struct_0(B_1481))
      | ~ l3_lattices(B_1481)
      | v2_struct_0(B_1481) ) ),
    inference(resolution,[status(thm)],[c_22999,c_24710])).

tff(c_24829,plain,(
    ! [B_1497,B_1498] :
      ( k2_lattices(B_1497,k15_lattice3(B_1497,k1_xboole_0),B_1498) = k15_lattice3(B_1497,k1_xboole_0)
      | ~ m1_subset_1(k15_lattice3(B_1497,k1_xboole_0),u1_struct_0(B_1497))
      | ~ v9_lattices(B_1497)
      | ~ v8_lattices(B_1497)
      | ~ v4_lattice3(B_1497)
      | ~ v10_lattices(B_1497)
      | ~ m1_subset_1(B_1498,u1_struct_0(B_1497))
      | ~ l3_lattices(B_1497)
      | v2_struct_0(B_1497) ) ),
    inference(resolution,[status(thm)],[c_24752,c_34])).

tff(c_24871,plain,(
    ! [A_1503,B_1504] :
      ( k2_lattices(A_1503,k15_lattice3(A_1503,k1_xboole_0),B_1504) = k15_lattice3(A_1503,k1_xboole_0)
      | ~ v9_lattices(A_1503)
      | ~ v8_lattices(A_1503)
      | ~ v4_lattice3(A_1503)
      | ~ v10_lattices(A_1503)
      | ~ m1_subset_1(B_1504,u1_struct_0(A_1503))
      | ~ l3_lattices(A_1503)
      | v2_struct_0(A_1503) ) ),
    inference(resolution,[status(thm)],[c_72,c_24829])).

tff(c_24873,plain,
    ( k2_lattices('#skF_10',k15_lattice3('#skF_10',k1_xboole_0),'#skF_2'('#skF_10')) = k15_lattice3('#skF_10',k1_xboole_0)
    | ~ v9_lattices('#skF_10')
    | ~ v8_lattices('#skF_10')
    | ~ v4_lattice3('#skF_10')
    | ~ v10_lattices('#skF_10')
    | ~ l3_lattices('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_23460,c_24871])).

tff(c_24896,plain,
    ( k15_lattice3('#skF_10',k1_xboole_0) = '#skF_2'('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_96,c_94,c_23812,c_23840,c_23604,c_24873])).

tff(c_24898,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_23376,c_24896])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:15:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 29.46/19.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.46/19.52  
% 29.46/19.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.46/19.52  %$ r4_lattice3 > r3_lattices > r1_lattices > r2_hidden > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k16_lattice3 > k15_lattice3 > a_2_6_lattice3 > a_2_5_lattice3 > #nlpp > u1_struct_0 > k5_lattices > k1_xboole_0 > #skF_7 > #skF_2 > #skF_4 > #skF_3 > #skF_10 > #skF_5 > #skF_9 > #skF_8 > #skF_1 > #skF_6
% 29.46/19.52  
% 29.46/19.52  %Foreground sorts:
% 29.46/19.52  
% 29.46/19.52  
% 29.46/19.52  %Background operators:
% 29.46/19.52  
% 29.46/19.52  
% 29.46/19.52  %Foreground operators:
% 29.46/19.52  tff(l3_lattices, type, l3_lattices: $i > $o).
% 29.46/19.52  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 29.46/19.52  tff('#skF_7', type, '#skF_7': $i > $i).
% 29.46/19.52  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 29.46/19.52  tff(l2_lattices, type, l2_lattices: $i > $o).
% 29.46/19.52  tff('#skF_2', type, '#skF_2': $i > $i).
% 29.46/19.52  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 29.46/19.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 29.46/19.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 29.46/19.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 29.46/19.52  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 29.46/19.52  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 29.46/19.52  tff(l1_lattices, type, l1_lattices: $i > $o).
% 29.46/19.52  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 29.46/19.52  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 29.46/19.52  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 29.46/19.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 29.46/19.52  tff('#skF_10', type, '#skF_10': $i).
% 29.46/19.52  tff(v4_lattices, type, v4_lattices: $i > $o).
% 29.46/19.52  tff(v6_lattices, type, v6_lattices: $i > $o).
% 29.46/19.52  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 29.46/19.52  tff(v9_lattices, type, v9_lattices: $i > $o).
% 29.46/19.52  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 29.46/19.52  tff(a_2_5_lattice3, type, a_2_5_lattice3: ($i * $i) > $i).
% 29.46/19.52  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 29.46/19.52  tff(v5_lattices, type, v5_lattices: $i > $o).
% 29.46/19.52  tff(v10_lattices, type, v10_lattices: $i > $o).
% 29.46/19.52  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 29.46/19.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 29.46/19.52  tff(v13_lattices, type, v13_lattices: $i > $o).
% 29.46/19.52  tff(v8_lattices, type, v8_lattices: $i > $o).
% 29.46/19.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 29.46/19.52  tff(k5_lattices, type, k5_lattices: $i > $i).
% 29.46/19.52  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 29.46/19.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 29.46/19.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 29.46/19.52  tff(a_2_6_lattice3, type, a_2_6_lattice3: ($i * $i) > $i).
% 29.46/19.52  tff('#skF_6', type, '#skF_6': $i > $i).
% 29.46/19.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 29.46/19.52  tff(v7_lattices, type, v7_lattices: $i > $o).
% 29.46/19.52  
% 29.46/19.55  tff(f_241, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v13_lattices(A)) & l3_lattices(A)) & (k5_lattices(A) = k15_lattice3(A, k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_lattice3)).
% 29.46/19.55  tff(f_79, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 29.46/19.55  tff(f_54, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 29.46/19.55  tff(f_183, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k15_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 29.46/19.55  tff(f_115, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) <=> (?[B]: (m1_subset_1(B, u1_struct_0(A)) & (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_lattices)).
% 29.46/19.55  tff(f_133, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_lattice3)).
% 29.46/19.55  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 29.46/19.55  tff(f_206, axiom, (![A, B, C]: ((((~v2_struct_0(B) & v10_lattices(B)) & v4_lattice3(B)) & l3_lattices(B)) => (r2_hidden(A, a_2_5_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r3_lattices(B, D, E)) & r2_hidden(E, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_5_lattice3)).
% 29.46/19.55  tff(f_32, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 29.46/19.55  tff(f_220, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: ((k15_lattice3(A, B) = k15_lattice3(A, a_2_5_lattice3(A, B))) & (k16_lattice3(A, B) = k16_lattice3(A, a_2_6_lattice3(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_lattice3)).
% 29.46/19.55  tff(f_161, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k15_lattice3(A, B)) <=> (r4_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d21_lattice3)).
% 29.46/19.55  tff(f_98, axiom, (![A]: ((((~v2_struct_0(A) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k2_lattices(A, B, C) = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_lattices)).
% 29.46/19.55  tff(f_176, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v6_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, C) = k2_lattices(A, C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_lattices)).
% 29.46/19.55  tff(f_73, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((B = k5_lattices(A)) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattices)).
% 29.46/19.55  tff(c_98, plain, (~v2_struct_0('#skF_10')), inference(cnfTransformation, [status(thm)], [f_241])).
% 29.46/19.55  tff(c_92, plain, (l3_lattices('#skF_10')), inference(cnfTransformation, [status(thm)], [f_241])).
% 29.46/19.55  tff(c_103, plain, (![A_98]: (l1_lattices(A_98) | ~l3_lattices(A_98))), inference(cnfTransformation, [status(thm)], [f_79])).
% 29.46/19.55  tff(c_107, plain, (l1_lattices('#skF_10')), inference(resolution, [status(thm)], [c_92, c_103])).
% 29.46/19.55  tff(c_96, plain, (v10_lattices('#skF_10')), inference(cnfTransformation, [status(thm)], [f_241])).
% 29.46/19.55  tff(c_90, plain, (k15_lattice3('#skF_10', k1_xboole_0)!=k5_lattices('#skF_10') | ~l3_lattices('#skF_10') | ~v13_lattices('#skF_10') | ~v10_lattices('#skF_10') | v2_struct_0('#skF_10')), inference(cnfTransformation, [status(thm)], [f_241])).
% 29.46/19.55  tff(c_100, plain, (k15_lattice3('#skF_10', k1_xboole_0)!=k5_lattices('#skF_10') | ~v13_lattices('#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_92, c_90])).
% 29.46/19.55  tff(c_101, plain, (k15_lattice3('#skF_10', k1_xboole_0)!=k5_lattices('#skF_10') | ~v13_lattices('#skF_10')), inference(negUnitSimplification, [status(thm)], [c_98, c_100])).
% 29.46/19.55  tff(c_113, plain, (~v13_lattices('#skF_10')), inference(splitLeft, [status(thm)], [c_101])).
% 29.46/19.55  tff(c_94, plain, (v4_lattice3('#skF_10')), inference(cnfTransformation, [status(thm)], [f_241])).
% 29.46/19.55  tff(c_12, plain, (![A_4]: (v6_lattices(A_4) | ~v10_lattices(A_4) | v2_struct_0(A_4) | ~l3_lattices(A_4))), inference(cnfTransformation, [status(thm)], [f_54])).
% 29.46/19.55  tff(c_8, plain, (![A_4]: (v8_lattices(A_4) | ~v10_lattices(A_4) | v2_struct_0(A_4) | ~l3_lattices(A_4))), inference(cnfTransformation, [status(thm)], [f_54])).
% 29.46/19.55  tff(c_6, plain, (![A_4]: (v9_lattices(A_4) | ~v10_lattices(A_4) | v2_struct_0(A_4) | ~l3_lattices(A_4))), inference(cnfTransformation, [status(thm)], [f_54])).
% 29.46/19.55  tff(c_72, plain, (![A_79, B_80]: (m1_subset_1(k15_lattice3(A_79, B_80), u1_struct_0(A_79)) | ~l3_lattices(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_183])).
% 29.46/19.55  tff(c_38, plain, (![A_23, B_32]: (m1_subset_1('#skF_3'(A_23, B_32), u1_struct_0(A_23)) | v13_lattices(A_23) | ~m1_subset_1(B_32, u1_struct_0(A_23)) | ~l1_lattices(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_115])).
% 29.46/19.55  tff(c_50, plain, (![A_34, B_46, C_52]: (r2_hidden('#skF_4'(A_34, B_46, C_52), C_52) | r4_lattice3(A_34, B_46, C_52) | ~m1_subset_1(B_46, u1_struct_0(A_34)) | ~l3_lattices(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_133])).
% 29.46/19.55  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 29.46/19.55  tff(c_287, plain, (![A_144, B_145, C_146]: (r2_hidden('#skF_9'(A_144, B_145, C_146), C_146) | ~r2_hidden(A_144, a_2_5_lattice3(B_145, C_146)) | ~l3_lattices(B_145) | ~v4_lattice3(B_145) | ~v10_lattices(B_145) | v2_struct_0(B_145))), inference(cnfTransformation, [status(thm)], [f_206])).
% 29.46/19.55  tff(c_4, plain, (![B_3, A_2]: (~r1_tarski(B_3, A_2) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 29.46/19.55  tff(c_328, plain, (![C_162, A_163, B_164]: (~r1_tarski(C_162, '#skF_9'(A_163, B_164, C_162)) | ~r2_hidden(A_163, a_2_5_lattice3(B_164, C_162)) | ~l3_lattices(B_164) | ~v4_lattice3(B_164) | ~v10_lattices(B_164) | v2_struct_0(B_164))), inference(resolution, [status(thm)], [c_287, c_4])).
% 29.46/19.55  tff(c_344, plain, (![A_168, B_169]: (~r2_hidden(A_168, a_2_5_lattice3(B_169, k1_xboole_0)) | ~l3_lattices(B_169) | ~v4_lattice3(B_169) | ~v10_lattices(B_169) | v2_struct_0(B_169))), inference(resolution, [status(thm)], [c_2, c_328])).
% 29.46/19.55  tff(c_354, plain, (![B_169, A_34, B_46]: (~l3_lattices(B_169) | ~v4_lattice3(B_169) | ~v10_lattices(B_169) | v2_struct_0(B_169) | r4_lattice3(A_34, B_46, a_2_5_lattice3(B_169, k1_xboole_0)) | ~m1_subset_1(B_46, u1_struct_0(A_34)) | ~l3_lattices(A_34) | v2_struct_0(A_34))), inference(resolution, [status(thm)], [c_50, c_344])).
% 29.46/19.55  tff(c_86, plain, (![A_94, B_96]: (k15_lattice3(A_94, a_2_5_lattice3(A_94, B_96))=k15_lattice3(A_94, B_96) | ~l3_lattices(A_94) | ~v4_lattice3(A_94) | ~v10_lattices(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_220])).
% 29.46/19.55  tff(c_759, plain, (![A_268, B_269, D_270]: (r1_lattices(A_268, k15_lattice3(A_268, B_269), D_270) | ~r4_lattice3(A_268, D_270, B_269) | ~m1_subset_1(D_270, u1_struct_0(A_268)) | ~m1_subset_1(k15_lattice3(A_268, B_269), u1_struct_0(A_268)) | ~v4_lattice3(A_268) | ~v10_lattices(A_268) | ~l3_lattices(A_268) | v2_struct_0(A_268))), inference(cnfTransformation, [status(thm)], [f_161])).
% 29.46/19.55  tff(c_765, plain, (![A_271, B_272, D_273]: (r1_lattices(A_271, k15_lattice3(A_271, B_272), D_273) | ~r4_lattice3(A_271, D_273, B_272) | ~m1_subset_1(D_273, u1_struct_0(A_271)) | ~v4_lattice3(A_271) | ~v10_lattices(A_271) | ~l3_lattices(A_271) | v2_struct_0(A_271))), inference(resolution, [status(thm)], [c_72, c_759])).
% 29.46/19.55  tff(c_967, plain, (![A_329, B_330, D_331]: (r1_lattices(A_329, k15_lattice3(A_329, B_330), D_331) | ~r4_lattice3(A_329, D_331, a_2_5_lattice3(A_329, B_330)) | ~m1_subset_1(D_331, u1_struct_0(A_329)) | ~v4_lattice3(A_329) | ~v10_lattices(A_329) | ~l3_lattices(A_329) | v2_struct_0(A_329) | ~l3_lattices(A_329) | ~v4_lattice3(A_329) | ~v10_lattices(A_329) | v2_struct_0(A_329))), inference(superposition, [status(thm), theory('equality')], [c_86, c_765])).
% 29.46/19.55  tff(c_987, plain, (![B_332, B_333]: (r1_lattices(B_332, k15_lattice3(B_332, k1_xboole_0), B_333) | ~v4_lattice3(B_332) | ~v10_lattices(B_332) | ~m1_subset_1(B_333, u1_struct_0(B_332)) | ~l3_lattices(B_332) | v2_struct_0(B_332))), inference(resolution, [status(thm)], [c_354, c_967])).
% 29.46/19.55  tff(c_34, plain, (![A_16, B_20, C_22]: (k2_lattices(A_16, B_20, C_22)=B_20 | ~r1_lattices(A_16, B_20, C_22) | ~m1_subset_1(C_22, u1_struct_0(A_16)) | ~m1_subset_1(B_20, u1_struct_0(A_16)) | ~l3_lattices(A_16) | ~v9_lattices(A_16) | ~v8_lattices(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_98])).
% 29.46/19.55  tff(c_1046, plain, (![B_345, B_346]: (k2_lattices(B_345, k15_lattice3(B_345, k1_xboole_0), B_346)=k15_lattice3(B_345, k1_xboole_0) | ~m1_subset_1(k15_lattice3(B_345, k1_xboole_0), u1_struct_0(B_345)) | ~v9_lattices(B_345) | ~v8_lattices(B_345) | ~v4_lattice3(B_345) | ~v10_lattices(B_345) | ~m1_subset_1(B_346, u1_struct_0(B_345)) | ~l3_lattices(B_345) | v2_struct_0(B_345))), inference(resolution, [status(thm)], [c_987, c_34])).
% 29.46/19.55  tff(c_1051, plain, (![A_347, B_348]: (k2_lattices(A_347, k15_lattice3(A_347, k1_xboole_0), B_348)=k15_lattice3(A_347, k1_xboole_0) | ~v9_lattices(A_347) | ~v8_lattices(A_347) | ~v4_lattice3(A_347) | ~v10_lattices(A_347) | ~m1_subset_1(B_348, u1_struct_0(A_347)) | ~l3_lattices(A_347) | v2_struct_0(A_347))), inference(resolution, [status(thm)], [c_72, c_1046])).
% 29.46/19.55  tff(c_1077, plain, (![A_23, B_32]: (k2_lattices(A_23, k15_lattice3(A_23, k1_xboole_0), '#skF_3'(A_23, B_32))=k15_lattice3(A_23, k1_xboole_0) | ~v9_lattices(A_23) | ~v8_lattices(A_23) | ~v4_lattice3(A_23) | ~v10_lattices(A_23) | ~l3_lattices(A_23) | v13_lattices(A_23) | ~m1_subset_1(B_32, u1_struct_0(A_23)) | ~l1_lattices(A_23) | v2_struct_0(A_23))), inference(resolution, [status(thm)], [c_38, c_1051])).
% 29.46/19.55  tff(c_1208, plain, (![A_365, B_366]: (k2_lattices(A_365, k15_lattice3(A_365, k1_xboole_0), '#skF_3'(A_365, B_366))=k15_lattice3(A_365, k1_xboole_0) | ~v9_lattices(A_365) | ~v8_lattices(A_365) | ~v4_lattice3(A_365) | ~v10_lattices(A_365) | ~l3_lattices(A_365) | v13_lattices(A_365) | ~m1_subset_1(B_366, u1_struct_0(A_365)) | ~l1_lattices(A_365) | v2_struct_0(A_365))), inference(resolution, [status(thm)], [c_38, c_1051])).
% 29.46/19.55  tff(c_408, plain, (![A_189, C_190, B_191]: (k2_lattices(A_189, C_190, B_191)=k2_lattices(A_189, B_191, C_190) | ~m1_subset_1(C_190, u1_struct_0(A_189)) | ~m1_subset_1(B_191, u1_struct_0(A_189)) | ~v6_lattices(A_189) | ~l1_lattices(A_189) | v2_struct_0(A_189))), inference(cnfTransformation, [status(thm)], [f_176])).
% 29.46/19.55  tff(c_542, plain, (![A_226, B_227, B_228]: (k2_lattices(A_226, k15_lattice3(A_226, B_227), B_228)=k2_lattices(A_226, B_228, k15_lattice3(A_226, B_227)) | ~m1_subset_1(B_228, u1_struct_0(A_226)) | ~v6_lattices(A_226) | ~l1_lattices(A_226) | ~l3_lattices(A_226) | v2_struct_0(A_226))), inference(resolution, [status(thm)], [c_72, c_408])).
% 29.46/19.55  tff(c_565, plain, (![A_23, B_227, B_32]: (k2_lattices(A_23, k15_lattice3(A_23, B_227), '#skF_3'(A_23, B_32))=k2_lattices(A_23, '#skF_3'(A_23, B_32), k15_lattice3(A_23, B_227)) | ~v6_lattices(A_23) | ~l3_lattices(A_23) | v13_lattices(A_23) | ~m1_subset_1(B_32, u1_struct_0(A_23)) | ~l1_lattices(A_23) | v2_struct_0(A_23))), inference(resolution, [status(thm)], [c_38, c_542])).
% 29.46/19.55  tff(c_22686, plain, (![A_1199, B_1200]: (k2_lattices(A_1199, '#skF_3'(A_1199, B_1200), k15_lattice3(A_1199, k1_xboole_0))=k15_lattice3(A_1199, k1_xboole_0) | ~v6_lattices(A_1199) | ~l3_lattices(A_1199) | v13_lattices(A_1199) | ~m1_subset_1(B_1200, u1_struct_0(A_1199)) | ~l1_lattices(A_1199) | v2_struct_0(A_1199) | ~v9_lattices(A_1199) | ~v8_lattices(A_1199) | ~v4_lattice3(A_1199) | ~v10_lattices(A_1199) | ~l3_lattices(A_1199) | v13_lattices(A_1199) | ~m1_subset_1(B_1200, u1_struct_0(A_1199)) | ~l1_lattices(A_1199) | v2_struct_0(A_1199))), inference(superposition, [status(thm), theory('equality')], [c_1208, c_565])).
% 29.46/19.55  tff(c_36, plain, (![A_23, B_32]: (k2_lattices(A_23, '#skF_3'(A_23, B_32), B_32)!=B_32 | k2_lattices(A_23, B_32, '#skF_3'(A_23, B_32))!=B_32 | v13_lattices(A_23) | ~m1_subset_1(B_32, u1_struct_0(A_23)) | ~l1_lattices(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_115])).
% 29.46/19.55  tff(c_22706, plain, (![A_1201]: (k2_lattices(A_1201, k15_lattice3(A_1201, k1_xboole_0), '#skF_3'(A_1201, k15_lattice3(A_1201, k1_xboole_0)))!=k15_lattice3(A_1201, k1_xboole_0) | ~v6_lattices(A_1201) | ~v9_lattices(A_1201) | ~v8_lattices(A_1201) | ~v4_lattice3(A_1201) | ~v10_lattices(A_1201) | ~l3_lattices(A_1201) | v13_lattices(A_1201) | ~m1_subset_1(k15_lattice3(A_1201, k1_xboole_0), u1_struct_0(A_1201)) | ~l1_lattices(A_1201) | v2_struct_0(A_1201))), inference(superposition, [status(thm), theory('equality')], [c_22686, c_36])).
% 29.46/19.55  tff(c_22738, plain, (![A_1207]: (~v6_lattices(A_1207) | ~v9_lattices(A_1207) | ~v8_lattices(A_1207) | ~v4_lattice3(A_1207) | ~v10_lattices(A_1207) | ~l3_lattices(A_1207) | v13_lattices(A_1207) | ~m1_subset_1(k15_lattice3(A_1207, k1_xboole_0), u1_struct_0(A_1207)) | ~l1_lattices(A_1207) | v2_struct_0(A_1207))), inference(superposition, [status(thm), theory('equality')], [c_1077, c_22706])).
% 29.46/19.55  tff(c_22744, plain, (![A_1208]: (~v6_lattices(A_1208) | ~v9_lattices(A_1208) | ~v8_lattices(A_1208) | ~v4_lattice3(A_1208) | ~v10_lattices(A_1208) | v13_lattices(A_1208) | ~l1_lattices(A_1208) | ~l3_lattices(A_1208) | v2_struct_0(A_1208))), inference(resolution, [status(thm)], [c_72, c_22738])).
% 29.46/19.55  tff(c_22749, plain, (![A_1209]: (~v6_lattices(A_1209) | ~v8_lattices(A_1209) | ~v4_lattice3(A_1209) | v13_lattices(A_1209) | ~l1_lattices(A_1209) | ~v10_lattices(A_1209) | v2_struct_0(A_1209) | ~l3_lattices(A_1209))), inference(resolution, [status(thm)], [c_6, c_22744])).
% 29.46/19.55  tff(c_22754, plain, (![A_1210]: (~v6_lattices(A_1210) | ~v4_lattice3(A_1210) | v13_lattices(A_1210) | ~l1_lattices(A_1210) | ~v10_lattices(A_1210) | v2_struct_0(A_1210) | ~l3_lattices(A_1210))), inference(resolution, [status(thm)], [c_8, c_22749])).
% 29.46/19.55  tff(c_22759, plain, (![A_1211]: (~v4_lattice3(A_1211) | v13_lattices(A_1211) | ~l1_lattices(A_1211) | ~v10_lattices(A_1211) | v2_struct_0(A_1211) | ~l3_lattices(A_1211))), inference(resolution, [status(thm)], [c_12, c_22754])).
% 29.46/19.55  tff(c_22762, plain, (v13_lattices('#skF_10') | ~l1_lattices('#skF_10') | ~v10_lattices('#skF_10') | v2_struct_0('#skF_10') | ~l3_lattices('#skF_10')), inference(resolution, [status(thm)], [c_94, c_22759])).
% 29.46/19.55  tff(c_22765, plain, (v13_lattices('#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_96, c_107, c_22762])).
% 29.46/19.55  tff(c_22767, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_113, c_22765])).
% 29.46/19.55  tff(c_22769, plain, (v13_lattices('#skF_10')), inference(splitRight, [status(thm)], [c_101])).
% 29.46/19.55  tff(c_40, plain, (![A_23]: (m1_subset_1('#skF_2'(A_23), u1_struct_0(A_23)) | ~v13_lattices(A_23) | ~l1_lattices(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_115])).
% 29.46/19.55  tff(c_22916, plain, (![A_1251, B_1252]: (m1_subset_1('#skF_1'(A_1251, B_1252), u1_struct_0(A_1251)) | k5_lattices(A_1251)=B_1252 | ~m1_subset_1(B_1252, u1_struct_0(A_1251)) | ~v13_lattices(A_1251) | ~l1_lattices(A_1251) | v2_struct_0(A_1251))), inference(cnfTransformation, [status(thm)], [f_73])).
% 29.46/19.55  tff(c_44, plain, (![A_23, C_31]: (k2_lattices(A_23, '#skF_2'(A_23), C_31)='#skF_2'(A_23) | ~m1_subset_1(C_31, u1_struct_0(A_23)) | ~v13_lattices(A_23) | ~l1_lattices(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_115])).
% 29.46/19.55  tff(c_22922, plain, (![A_1251, B_1252]: (k2_lattices(A_1251, '#skF_2'(A_1251), '#skF_1'(A_1251, B_1252))='#skF_2'(A_1251) | k5_lattices(A_1251)=B_1252 | ~m1_subset_1(B_1252, u1_struct_0(A_1251)) | ~v13_lattices(A_1251) | ~l1_lattices(A_1251) | v2_struct_0(A_1251))), inference(resolution, [status(thm)], [c_22916, c_44])).
% 29.46/19.55  tff(c_42, plain, (![A_23, C_31]: (k2_lattices(A_23, C_31, '#skF_2'(A_23))='#skF_2'(A_23) | ~m1_subset_1(C_31, u1_struct_0(A_23)) | ~v13_lattices(A_23) | ~l1_lattices(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_115])).
% 29.46/19.55  tff(c_22921, plain, (![A_1251, B_1252]: (k2_lattices(A_1251, '#skF_1'(A_1251, B_1252), '#skF_2'(A_1251))='#skF_2'(A_1251) | k5_lattices(A_1251)=B_1252 | ~m1_subset_1(B_1252, u1_struct_0(A_1251)) | ~v13_lattices(A_1251) | ~l1_lattices(A_1251) | v2_struct_0(A_1251))), inference(resolution, [status(thm)], [c_22916, c_42])).
% 29.46/19.55  tff(c_23353, plain, (![A_1366, B_1367]: (k2_lattices(A_1366, '#skF_1'(A_1366, B_1367), B_1367)!=B_1367 | k2_lattices(A_1366, B_1367, '#skF_1'(A_1366, B_1367))!=B_1367 | k5_lattices(A_1366)=B_1367 | ~m1_subset_1(B_1367, u1_struct_0(A_1366)) | ~v13_lattices(A_1366) | ~l1_lattices(A_1366) | v2_struct_0(A_1366))), inference(cnfTransformation, [status(thm)], [f_73])).
% 29.46/19.55  tff(c_23358, plain, (![A_1368]: (k2_lattices(A_1368, '#skF_2'(A_1368), '#skF_1'(A_1368, '#skF_2'(A_1368)))!='#skF_2'(A_1368) | k5_lattices(A_1368)='#skF_2'(A_1368) | ~m1_subset_1('#skF_2'(A_1368), u1_struct_0(A_1368)) | ~v13_lattices(A_1368) | ~l1_lattices(A_1368) | v2_struct_0(A_1368))), inference(superposition, [status(thm), theory('equality')], [c_22921, c_23353])).
% 29.46/19.55  tff(c_23364, plain, (![A_1369]: (k5_lattices(A_1369)='#skF_2'(A_1369) | ~m1_subset_1('#skF_2'(A_1369), u1_struct_0(A_1369)) | ~v13_lattices(A_1369) | ~l1_lattices(A_1369) | v2_struct_0(A_1369))), inference(superposition, [status(thm), theory('equality')], [c_22922, c_23358])).
% 29.46/19.55  tff(c_23369, plain, (![A_1370]: (k5_lattices(A_1370)='#skF_2'(A_1370) | ~v13_lattices(A_1370) | ~l1_lattices(A_1370) | v2_struct_0(A_1370))), inference(resolution, [status(thm)], [c_40, c_23364])).
% 29.46/19.55  tff(c_23372, plain, (k5_lattices('#skF_10')='#skF_2'('#skF_10') | ~v13_lattices('#skF_10') | ~l1_lattices('#skF_10')), inference(resolution, [status(thm)], [c_23369, c_98])).
% 29.46/19.55  tff(c_23375, plain, (k5_lattices('#skF_10')='#skF_2'('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_22769, c_23372])).
% 29.46/19.55  tff(c_22768, plain, (k15_lattice3('#skF_10', k1_xboole_0)!=k5_lattices('#skF_10')), inference(splitRight, [status(thm)], [c_101])).
% 29.46/19.55  tff(c_23376, plain, (k15_lattice3('#skF_10', k1_xboole_0)!='#skF_2'('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_23375, c_22768])).
% 29.46/19.55  tff(c_23035, plain, (![A_1298, C_1299]: (k2_lattices(A_1298, C_1299, k5_lattices(A_1298))=k5_lattices(A_1298) | ~m1_subset_1(C_1299, u1_struct_0(A_1298)) | ~m1_subset_1(k5_lattices(A_1298), u1_struct_0(A_1298)) | ~v13_lattices(A_1298) | ~l1_lattices(A_1298) | v2_struct_0(A_1298))), inference(cnfTransformation, [status(thm)], [f_73])).
% 29.46/19.55  tff(c_23061, plain, (![A_23]: (k2_lattices(A_23, '#skF_2'(A_23), k5_lattices(A_23))=k5_lattices(A_23) | ~m1_subset_1(k5_lattices(A_23), u1_struct_0(A_23)) | ~v13_lattices(A_23) | ~l1_lattices(A_23) | v2_struct_0(A_23))), inference(resolution, [status(thm)], [c_40, c_23035])).
% 29.46/19.55  tff(c_23393, plain, (k2_lattices('#skF_10', '#skF_2'('#skF_10'), k5_lattices('#skF_10'))=k5_lattices('#skF_10') | ~m1_subset_1('#skF_2'('#skF_10'), u1_struct_0('#skF_10')) | ~v13_lattices('#skF_10') | ~l1_lattices('#skF_10') | v2_struct_0('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_23375, c_23061])).
% 29.46/19.55  tff(c_23418, plain, (k2_lattices('#skF_10', '#skF_2'('#skF_10'), '#skF_2'('#skF_10'))='#skF_2'('#skF_10') | ~m1_subset_1('#skF_2'('#skF_10'), u1_struct_0('#skF_10')) | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_22769, c_23375, c_23375, c_23393])).
% 29.46/19.55  tff(c_23419, plain, (k2_lattices('#skF_10', '#skF_2'('#skF_10'), '#skF_2'('#skF_10'))='#skF_2'('#skF_10') | ~m1_subset_1('#skF_2'('#skF_10'), u1_struct_0('#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_98, c_23418])).
% 29.46/19.55  tff(c_23450, plain, (~m1_subset_1('#skF_2'('#skF_10'), u1_struct_0('#skF_10'))), inference(splitLeft, [status(thm)], [c_23419])).
% 29.46/19.55  tff(c_23453, plain, (~v13_lattices('#skF_10') | ~l1_lattices('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_40, c_23450])).
% 29.46/19.55  tff(c_23456, plain, (v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_22769, c_23453])).
% 29.46/19.55  tff(c_23458, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_23456])).
% 29.46/19.55  tff(c_23460, plain, (m1_subset_1('#skF_2'('#skF_10'), u1_struct_0('#skF_10'))), inference(splitRight, [status(thm)], [c_23419])).
% 29.46/19.55  tff(c_32, plain, (![A_16, B_20, C_22]: (r1_lattices(A_16, B_20, C_22) | k2_lattices(A_16, B_20, C_22)!=B_20 | ~m1_subset_1(C_22, u1_struct_0(A_16)) | ~m1_subset_1(B_20, u1_struct_0(A_16)) | ~l3_lattices(A_16) | ~v9_lattices(A_16) | ~v8_lattices(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_98])).
% 29.46/19.55  tff(c_23525, plain, (![B_20]: (r1_lattices('#skF_10', B_20, '#skF_2'('#skF_10')) | k2_lattices('#skF_10', B_20, '#skF_2'('#skF_10'))!=B_20 | ~m1_subset_1(B_20, u1_struct_0('#skF_10')) | ~l3_lattices('#skF_10') | ~v9_lattices('#skF_10') | ~v8_lattices('#skF_10') | v2_struct_0('#skF_10'))), inference(resolution, [status(thm)], [c_23460, c_32])).
% 29.46/19.55  tff(c_23547, plain, (![B_20]: (r1_lattices('#skF_10', B_20, '#skF_2'('#skF_10')) | k2_lattices('#skF_10', B_20, '#skF_2'('#skF_10'))!=B_20 | ~m1_subset_1(B_20, u1_struct_0('#skF_10')) | ~v9_lattices('#skF_10') | ~v8_lattices('#skF_10') | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_23525])).
% 29.46/19.55  tff(c_23548, plain, (![B_20]: (r1_lattices('#skF_10', B_20, '#skF_2'('#skF_10')) | k2_lattices('#skF_10', B_20, '#skF_2'('#skF_10'))!=B_20 | ~m1_subset_1(B_20, u1_struct_0('#skF_10')) | ~v9_lattices('#skF_10') | ~v8_lattices('#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_98, c_23547])).
% 29.46/19.55  tff(c_23802, plain, (~v8_lattices('#skF_10')), inference(splitLeft, [status(thm)], [c_23548])).
% 29.46/19.55  tff(c_23805, plain, (~v10_lattices('#skF_10') | v2_struct_0('#skF_10') | ~l3_lattices('#skF_10')), inference(resolution, [status(thm)], [c_8, c_23802])).
% 29.46/19.55  tff(c_23808, plain, (v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_96, c_23805])).
% 29.46/19.55  tff(c_23810, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_23808])).
% 29.46/19.55  tff(c_23812, plain, (v8_lattices('#skF_10')), inference(splitRight, [status(thm)], [c_23548])).
% 29.46/19.55  tff(c_23811, plain, (![B_20]: (~v9_lattices('#skF_10') | r1_lattices('#skF_10', B_20, '#skF_2'('#skF_10')) | k2_lattices('#skF_10', B_20, '#skF_2'('#skF_10'))!=B_20 | ~m1_subset_1(B_20, u1_struct_0('#skF_10')))), inference(splitRight, [status(thm)], [c_23548])).
% 29.46/19.55  tff(c_23830, plain, (~v9_lattices('#skF_10')), inference(splitLeft, [status(thm)], [c_23811])).
% 29.46/19.55  tff(c_23833, plain, (~v10_lattices('#skF_10') | v2_struct_0('#skF_10') | ~l3_lattices('#skF_10')), inference(resolution, [status(thm)], [c_6, c_23830])).
% 29.46/19.55  tff(c_23836, plain, (v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_96, c_23833])).
% 29.46/19.55  tff(c_23838, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_23836])).
% 29.46/19.55  tff(c_23840, plain, (v9_lattices('#skF_10')), inference(splitRight, [status(thm)], [c_23811])).
% 29.46/19.55  tff(c_23062, plain, (![A_79, B_80]: (k2_lattices(A_79, k15_lattice3(A_79, B_80), k5_lattices(A_79))=k5_lattices(A_79) | ~m1_subset_1(k5_lattices(A_79), u1_struct_0(A_79)) | ~v13_lattices(A_79) | ~l1_lattices(A_79) | ~l3_lattices(A_79) | v2_struct_0(A_79))), inference(resolution, [status(thm)], [c_72, c_23035])).
% 29.46/19.55  tff(c_23379, plain, (![B_80]: (k2_lattices('#skF_10', k15_lattice3('#skF_10', B_80), k5_lattices('#skF_10'))=k5_lattices('#skF_10') | ~m1_subset_1('#skF_2'('#skF_10'), u1_struct_0('#skF_10')) | ~v13_lattices('#skF_10') | ~l1_lattices('#skF_10') | ~l3_lattices('#skF_10') | v2_struct_0('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_23375, c_23062])).
% 29.46/19.55  tff(c_23397, plain, (![B_80]: (k2_lattices('#skF_10', k15_lattice3('#skF_10', B_80), '#skF_2'('#skF_10'))='#skF_2'('#skF_10') | ~m1_subset_1('#skF_2'('#skF_10'), u1_struct_0('#skF_10')) | v2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_107, c_22769, c_23375, c_23375, c_23379])).
% 29.46/19.55  tff(c_23398, plain, (![B_80]: (k2_lattices('#skF_10', k15_lattice3('#skF_10', B_80), '#skF_2'('#skF_10'))='#skF_2'('#skF_10') | ~m1_subset_1('#skF_2'('#skF_10'), u1_struct_0('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_98, c_23397])).
% 29.46/19.55  tff(c_23604, plain, (![B_80]: (k2_lattices('#skF_10', k15_lattice3('#skF_10', B_80), '#skF_2'('#skF_10'))='#skF_2'('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_23460, c_23398])).
% 29.46/19.55  tff(c_22974, plain, (![A_1271, B_1272, C_1273]: (r2_hidden('#skF_9'(A_1271, B_1272, C_1273), C_1273) | ~r2_hidden(A_1271, a_2_5_lattice3(B_1272, C_1273)) | ~l3_lattices(B_1272) | ~v4_lattice3(B_1272) | ~v10_lattices(B_1272) | v2_struct_0(B_1272))), inference(cnfTransformation, [status(thm)], [f_206])).
% 29.46/19.55  tff(c_22984, plain, (![C_1274, A_1275, B_1276]: (~r1_tarski(C_1274, '#skF_9'(A_1275, B_1276, C_1274)) | ~r2_hidden(A_1275, a_2_5_lattice3(B_1276, C_1274)) | ~l3_lattices(B_1276) | ~v4_lattice3(B_1276) | ~v10_lattices(B_1276) | v2_struct_0(B_1276))), inference(resolution, [status(thm)], [c_22974, c_4])).
% 29.46/19.55  tff(c_22989, plain, (![A_1277, B_1278]: (~r2_hidden(A_1277, a_2_5_lattice3(B_1278, k1_xboole_0)) | ~l3_lattices(B_1278) | ~v4_lattice3(B_1278) | ~v10_lattices(B_1278) | v2_struct_0(B_1278))), inference(resolution, [status(thm)], [c_2, c_22984])).
% 29.46/19.55  tff(c_22999, plain, (![B_1278, A_34, B_46]: (~l3_lattices(B_1278) | ~v4_lattice3(B_1278) | ~v10_lattices(B_1278) | v2_struct_0(B_1278) | r4_lattice3(A_34, B_46, a_2_5_lattice3(B_1278, k1_xboole_0)) | ~m1_subset_1(B_46, u1_struct_0(A_34)) | ~l3_lattices(A_34) | v2_struct_0(A_34))), inference(resolution, [status(thm)], [c_50, c_22989])).
% 29.46/19.55  tff(c_23708, plain, (![A_1383, B_1384, D_1385]: (r1_lattices(A_1383, k15_lattice3(A_1383, B_1384), D_1385) | ~r4_lattice3(A_1383, D_1385, B_1384) | ~m1_subset_1(D_1385, u1_struct_0(A_1383)) | ~m1_subset_1(k15_lattice3(A_1383, B_1384), u1_struct_0(A_1383)) | ~v4_lattice3(A_1383) | ~v10_lattices(A_1383) | ~l3_lattices(A_1383) | v2_struct_0(A_1383))), inference(cnfTransformation, [status(thm)], [f_161])).
% 29.46/19.55  tff(c_23856, plain, (![A_1390, B_1391, D_1392]: (r1_lattices(A_1390, k15_lattice3(A_1390, B_1391), D_1392) | ~r4_lattice3(A_1390, D_1392, B_1391) | ~m1_subset_1(D_1392, u1_struct_0(A_1390)) | ~v4_lattice3(A_1390) | ~v10_lattices(A_1390) | ~l3_lattices(A_1390) | v2_struct_0(A_1390))), inference(resolution, [status(thm)], [c_72, c_23708])).
% 29.46/19.55  tff(c_24710, plain, (![A_1477, B_1478, D_1479]: (r1_lattices(A_1477, k15_lattice3(A_1477, B_1478), D_1479) | ~r4_lattice3(A_1477, D_1479, a_2_5_lattice3(A_1477, B_1478)) | ~m1_subset_1(D_1479, u1_struct_0(A_1477)) | ~v4_lattice3(A_1477) | ~v10_lattices(A_1477) | ~l3_lattices(A_1477) | v2_struct_0(A_1477) | ~l3_lattices(A_1477) | ~v4_lattice3(A_1477) | ~v10_lattices(A_1477) | v2_struct_0(A_1477))), inference(superposition, [status(thm), theory('equality')], [c_86, c_23856])).
% 29.46/19.55  tff(c_24752, plain, (![B_1481, B_1482]: (r1_lattices(B_1481, k15_lattice3(B_1481, k1_xboole_0), B_1482) | ~v4_lattice3(B_1481) | ~v10_lattices(B_1481) | ~m1_subset_1(B_1482, u1_struct_0(B_1481)) | ~l3_lattices(B_1481) | v2_struct_0(B_1481))), inference(resolution, [status(thm)], [c_22999, c_24710])).
% 29.46/19.55  tff(c_24829, plain, (![B_1497, B_1498]: (k2_lattices(B_1497, k15_lattice3(B_1497, k1_xboole_0), B_1498)=k15_lattice3(B_1497, k1_xboole_0) | ~m1_subset_1(k15_lattice3(B_1497, k1_xboole_0), u1_struct_0(B_1497)) | ~v9_lattices(B_1497) | ~v8_lattices(B_1497) | ~v4_lattice3(B_1497) | ~v10_lattices(B_1497) | ~m1_subset_1(B_1498, u1_struct_0(B_1497)) | ~l3_lattices(B_1497) | v2_struct_0(B_1497))), inference(resolution, [status(thm)], [c_24752, c_34])).
% 29.46/19.55  tff(c_24871, plain, (![A_1503, B_1504]: (k2_lattices(A_1503, k15_lattice3(A_1503, k1_xboole_0), B_1504)=k15_lattice3(A_1503, k1_xboole_0) | ~v9_lattices(A_1503) | ~v8_lattices(A_1503) | ~v4_lattice3(A_1503) | ~v10_lattices(A_1503) | ~m1_subset_1(B_1504, u1_struct_0(A_1503)) | ~l3_lattices(A_1503) | v2_struct_0(A_1503))), inference(resolution, [status(thm)], [c_72, c_24829])).
% 29.46/19.55  tff(c_24873, plain, (k2_lattices('#skF_10', k15_lattice3('#skF_10', k1_xboole_0), '#skF_2'('#skF_10'))=k15_lattice3('#skF_10', k1_xboole_0) | ~v9_lattices('#skF_10') | ~v8_lattices('#skF_10') | ~v4_lattice3('#skF_10') | ~v10_lattices('#skF_10') | ~l3_lattices('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_23460, c_24871])).
% 29.46/19.55  tff(c_24896, plain, (k15_lattice3('#skF_10', k1_xboole_0)='#skF_2'('#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_96, c_94, c_23812, c_23840, c_23604, c_24873])).
% 29.46/19.55  tff(c_24898, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_23376, c_24896])).
% 29.46/19.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.46/19.55  
% 29.46/19.55  Inference rules
% 29.46/19.55  ----------------------
% 29.46/19.55  #Ref     : 0
% 29.46/19.55  #Sup     : 6742
% 29.46/19.55  #Fact    : 0
% 29.46/19.55  #Define  : 0
% 29.46/19.55  #Split   : 7
% 29.46/19.55  #Chain   : 0
% 29.46/19.55  #Close   : 0
% 29.46/19.55  
% 29.46/19.55  Ordering : KBO
% 29.46/19.55  
% 29.46/19.55  Simplification rules
% 29.46/19.55  ----------------------
% 29.46/19.55  #Subsume      : 2079
% 29.46/19.55  #Demod        : 468
% 29.46/19.55  #Tautology    : 1019
% 29.46/19.55  #SimpNegUnit  : 119
% 29.46/19.55  #BackRed      : 1
% 29.46/19.55  
% 29.46/19.55  #Partial instantiations: 0
% 29.46/19.55  #Strategies tried      : 1
% 29.46/19.55  
% 29.46/19.55  Timing (in seconds)
% 29.46/19.55  ----------------------
% 29.46/19.55  Preprocessing        : 0.42
% 29.46/19.55  Parsing              : 0.21
% 29.46/19.55  CNF conversion       : 0.03
% 29.46/19.55  Main loop            : 18.28
% 29.46/19.55  Inferencing          : 2.89
% 29.46/19.55  Reduction            : 1.49
% 29.46/19.55  Demodulation         : 1.02
% 29.46/19.55  BG Simplification    : 0.31
% 29.46/19.56  Subsumption          : 13.23
% 29.46/19.56  Abstraction          : 0.33
% 29.46/19.56  MUC search           : 0.00
% 29.46/19.56  Cooper               : 0.00
% 29.46/19.56  Total                : 18.75
% 29.46/19.56  Index Insertion      : 0.00
% 29.46/19.56  Index Deletion       : 0.00
% 29.46/19.56  Index Matching       : 0.00
% 29.46/19.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
