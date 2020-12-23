%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:51 EST 2020

% Result     : Theorem 47.82s
% Output     : CNFRefutation 48.15s
% Verified   : 
% Statistics : Number of formulae       :  335 (7712 expanded)
%              Number of leaves         :   71 (2545 expanded)
%              Depth                    :   55
%              Number of atoms          :  933 (21538 expanded)
%              Number of equality atoms :  169 (3515 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r1_lattices > r2_hidden > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k1_lattices > k16_lattice3 > k15_lattice3 > a_2_6_lattice3 > a_2_5_lattice3 > a_2_4_lattice3 > a_2_3_lattice3 > #nlpp > u1_struct_0 > k5_lattices > k1_zfmisc_1 > k1_xboole_0 > #skF_13 > #skF_9 > #skF_5 > #skF_6 > #skF_4 > #skF_12 > #skF_14 > #skF_10 > #skF_11 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff('#skF_13',type,(
    '#skF_13': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k2_lattices,type,(
    k2_lattices: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff(k1_lattices,type,(
    k1_lattices: ( $i * $i * $i ) > $i )).

tff(k15_lattice3,type,(
    k15_lattice3: ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff(a_2_4_lattice3,type,(
    a_2_4_lattice3: ( $i * $i ) > $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff('#skF_10',type,(
    '#skF_10': $i > $i )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff(r4_lattice3,type,(
    r4_lattice3: ( $i * $i * $i ) > $o )).

tff(a_2_3_lattice3,type,(
    a_2_3_lattice3: ( $i * $i ) > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v13_lattices,type,(
    v13_lattices: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(a_2_6_lattice3,type,(
    a_2_6_lattice3: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_361,negated_conjecture,(
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

tff(f_251,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k15_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

tff(f_147,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_294,axiom,(
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

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_340,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( k15_lattice3(A,B) = k15_lattice3(A,a_2_5_lattice3(A,B))
          & k16_lattice3(A,B) = k16_lattice3(A,a_2_6_lattice3(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_lattice3)).

tff(f_183,axiom,(
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

tff(f_310,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( B = k15_lattice3(A,a_2_3_lattice3(A,B))
            & B = k16_lattice3(A,a_2_4_lattice3(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_lattice3)).

tff(f_201,axiom,(
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

tff(f_85,axiom,(
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

tff(f_229,axiom,(
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

tff(f_119,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_lattices(A,B,C)
              <=> k1_lattices(A,B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).

tff(f_134,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v9_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k2_lattices(A,B,k1_lattices(A,B,C)) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).

tff(f_141,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => m1_subset_1(k5_lattices(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

tff(f_244,axiom,(
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

tff(f_104,axiom,(
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

tff(c_148,plain,(
    ~ v2_struct_0('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_361])).

tff(c_142,plain,(
    l3_lattices('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_361])).

tff(c_106,plain,(
    ! [A_113,B_114] :
      ( m1_subset_1(k15_lattice3(A_113,B_114),u1_struct_0(A_113))
      | ~ l3_lattices(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_160,plain,(
    ! [A_148] :
      ( l1_lattices(A_148)
      | ~ l3_lattices(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_164,plain,(
    l1_lattices('#skF_14') ),
    inference(resolution,[status(thm)],[c_142,c_160])).

tff(c_146,plain,(
    v10_lattices('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_361])).

tff(c_144,plain,(
    v4_lattice3('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_361])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_201,plain,(
    ! [A_165,B_166] :
      ( r2_hidden('#skF_1'(A_165,B_166),A_165)
      | r1_tarski(A_165,B_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,B_14)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_219,plain,(
    ! [A_170,B_171] :
      ( m1_subset_1('#skF_1'(A_170,B_171),A_170)
      | r1_tarski(A_170,B_171) ) ),
    inference(resolution,[status(thm)],[c_201,c_20])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_256,plain,(
    ! [B_185,B_186] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(B_185),B_186),B_185)
      | r1_tarski(k1_zfmisc_1(B_185),B_186) ) ),
    inference(resolution,[status(thm)],[c_219,c_22])).

tff(c_18,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_272,plain,(
    ! [B_187] :
      ( '#skF_1'(k1_zfmisc_1(k1_xboole_0),B_187) = k1_xboole_0
      | r1_tarski(k1_zfmisc_1(k1_xboole_0),B_187) ) ),
    inference(resolution,[status(thm)],[c_256,c_18])).

tff(c_292,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | '#skF_1'(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_272,c_18])).

tff(c_294,plain,(
    '#skF_1'(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_292])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_307,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_6])).

tff(c_317,plain,(
    r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_307])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_323,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_317,c_8])).

tff(c_331,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_323])).

tff(c_24,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_401,plain,(
    ! [A_194] :
      ( m1_subset_1(A_194,k1_xboole_0)
      | ~ r1_tarski(A_194,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_24])).

tff(c_420,plain,(
    m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_401])).

tff(c_224,plain,(
    ! [B_16,B_171] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(B_16),B_171),B_16)
      | r1_tarski(k1_zfmisc_1(B_16),B_171) ) ),
    inference(resolution,[status(thm)],[c_219,c_22])).

tff(c_377,plain,(
    ! [A_191] :
      ( r1_tarski(A_191,k1_xboole_0)
      | ~ m1_subset_1(A_191,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_22])).

tff(c_14,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(A_8,C_10)
      | ~ r1_tarski(B_9,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_486,plain,(
    ! [A_204,A_205] :
      ( r1_tarski(A_204,k1_xboole_0)
      | ~ r1_tarski(A_204,A_205)
      | ~ m1_subset_1(A_205,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_377,c_14])).

tff(c_903,plain,(
    ! [B_238,B_239] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(B_238),B_239),k1_xboole_0)
      | ~ m1_subset_1(B_238,k1_xboole_0)
      | r1_tarski(k1_zfmisc_1(B_238),B_239) ) ),
    inference(resolution,[status(thm)],[c_224,c_486])).

tff(c_237,plain,(
    ! [A_178,C_179,B_180] :
      ( r1_tarski(A_178,C_179)
      | ~ r1_tarski(B_180,C_179)
      | ~ r1_tarski(A_178,B_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_243,plain,(
    ! [A_178,A_11] :
      ( r1_tarski(A_178,A_11)
      | ~ r1_tarski(A_178,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_237])).

tff(c_429,plain,(
    ! [A_196,A_197] :
      ( r1_tarski(A_196,A_197)
      | ~ m1_subset_1(A_196,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_377,c_243])).

tff(c_453,plain,(
    ! [A_197,A_196] :
      ( A_197 = A_196
      | ~ r1_tarski(A_197,A_196)
      | ~ m1_subset_1(A_196,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_429,c_8])).

tff(c_908,plain,(
    ! [B_238,B_239] :
      ( '#skF_1'(k1_zfmisc_1(B_238),B_239) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_xboole_0)
      | ~ m1_subset_1(B_238,k1_xboole_0)
      | r1_tarski(k1_zfmisc_1(B_238),B_239) ) ),
    inference(resolution,[status(thm)],[c_903,c_453])).

tff(c_942,plain,(
    ! [B_240,B_241] :
      ( '#skF_1'(k1_zfmisc_1(B_240),B_241) = k1_xboole_0
      | ~ m1_subset_1(B_240,k1_xboole_0)
      | r1_tarski(k1_zfmisc_1(B_240),B_241) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_908])).

tff(c_347,plain,(
    ! [A_15] :
      ( m1_subset_1(A_15,k1_xboole_0)
      | ~ r1_tarski(A_15,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_24])).

tff(c_982,plain,(
    ! [B_240] :
      ( m1_subset_1(k1_zfmisc_1(B_240),k1_xboole_0)
      | '#skF_1'(k1_zfmisc_1(B_240),k1_xboole_0) = k1_xboole_0
      | ~ m1_subset_1(B_240,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_942,c_347])).

tff(c_387,plain,(
    ! [A_191,A_11] :
      ( r1_tarski(A_191,A_11)
      | ~ m1_subset_1(A_191,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_377,c_243])).

tff(c_1509,plain,(
    ! [A_277,B_278,C_279] :
      ( r2_hidden('#skF_13'(A_277,B_278,C_279),C_279)
      | ~ r2_hidden(A_277,a_2_5_lattice3(B_278,C_279))
      | ~ l3_lattices(B_278)
      | ~ v4_lattice3(B_278)
      | ~ v10_lattices(B_278)
      | v2_struct_0(B_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_294])).

tff(c_26,plain,(
    ! [B_18,A_17] :
      ( ~ r1_tarski(B_18,A_17)
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_11035,plain,(
    ! [C_645,A_646,B_647] :
      ( ~ r1_tarski(C_645,'#skF_13'(A_646,B_647,C_645))
      | ~ r2_hidden(A_646,a_2_5_lattice3(B_647,C_645))
      | ~ l3_lattices(B_647)
      | ~ v4_lattice3(B_647)
      | ~ v10_lattices(B_647)
      | v2_struct_0(B_647) ) ),
    inference(resolution,[status(thm)],[c_1509,c_26])).

tff(c_14795,plain,(
    ! [A_710,B_711,A_712] :
      ( ~ r2_hidden(A_710,a_2_5_lattice3(B_711,A_712))
      | ~ l3_lattices(B_711)
      | ~ v4_lattice3(B_711)
      | ~ v10_lattices(B_711)
      | v2_struct_0(B_711)
      | ~ m1_subset_1(A_712,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_387,c_11035])).

tff(c_14827,plain,(
    ! [B_713,A_714,B_715] :
      ( ~ l3_lattices(B_713)
      | ~ v4_lattice3(B_713)
      | ~ v10_lattices(B_713)
      | v2_struct_0(B_713)
      | ~ m1_subset_1(A_714,k1_xboole_0)
      | r1_tarski(a_2_5_lattice3(B_713,A_714),B_715) ) ),
    inference(resolution,[status(thm)],[c_6,c_14795])).

tff(c_15005,plain,(
    ! [B_716,A_717] :
      ( a_2_5_lattice3(B_716,A_717) = k1_xboole_0
      | ~ l3_lattices(B_716)
      | ~ v4_lattice3(B_716)
      | ~ v10_lattices(B_716)
      | v2_struct_0(B_716)
      | ~ m1_subset_1(A_717,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14827,c_18])).

tff(c_15007,plain,(
    ! [A_717] :
      ( a_2_5_lattice3('#skF_14',A_717) = k1_xboole_0
      | ~ l3_lattices('#skF_14')
      | ~ v10_lattices('#skF_14')
      | v2_struct_0('#skF_14')
      | ~ m1_subset_1(A_717,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_144,c_15005])).

tff(c_15010,plain,(
    ! [A_717] :
      ( a_2_5_lattice3('#skF_14',A_717) = k1_xboole_0
      | v2_struct_0('#skF_14')
      | ~ m1_subset_1(A_717,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_142,c_15007])).

tff(c_15012,plain,(
    ! [A_718] :
      ( a_2_5_lattice3('#skF_14',A_718) = k1_xboole_0
      | ~ m1_subset_1(A_718,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_15010])).

tff(c_15098,plain,(
    ! [B_721] :
      ( a_2_5_lattice3('#skF_14',k1_zfmisc_1(B_721)) = k1_xboole_0
      | '#skF_1'(k1_zfmisc_1(B_721),k1_xboole_0) = k1_xboole_0
      | ~ m1_subset_1(B_721,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_982,c_15012])).

tff(c_136,plain,(
    ! [A_142,B_144] :
      ( k15_lattice3(A_142,a_2_5_lattice3(A_142,B_144)) = k15_lattice3(A_142,B_144)
      | ~ l3_lattices(A_142)
      | ~ v4_lattice3(A_142)
      | ~ v10_lattices(A_142)
      | v2_struct_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_340])).

tff(c_15115,plain,(
    ! [B_721] :
      ( k15_lattice3('#skF_14',k1_zfmisc_1(B_721)) = k15_lattice3('#skF_14',k1_xboole_0)
      | ~ l3_lattices('#skF_14')
      | ~ v4_lattice3('#skF_14')
      | ~ v10_lattices('#skF_14')
      | v2_struct_0('#skF_14')
      | '#skF_1'(k1_zfmisc_1(B_721),k1_xboole_0) = k1_xboole_0
      | ~ m1_subset_1(B_721,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15098,c_136])).

tff(c_15139,plain,(
    ! [B_721] :
      ( k15_lattice3('#skF_14',k1_zfmisc_1(B_721)) = k15_lattice3('#skF_14',k1_xboole_0)
      | v2_struct_0('#skF_14')
      | '#skF_1'(k1_zfmisc_1(B_721),k1_xboole_0) = k1_xboole_0
      | ~ m1_subset_1(B_721,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_144,c_142,c_15115])).

tff(c_15201,plain,(
    ! [B_723] :
      ( k15_lattice3('#skF_14',k1_zfmisc_1(B_723)) = k15_lattice3('#skF_14',k1_xboole_0)
      | '#skF_1'(k1_zfmisc_1(B_723),k1_xboole_0) = k1_xboole_0
      | ~ m1_subset_1(B_723,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_15139])).

tff(c_15236,plain,(
    ! [B_723] :
      ( m1_subset_1(k15_lattice3('#skF_14',k1_xboole_0),u1_struct_0('#skF_14'))
      | ~ l3_lattices('#skF_14')
      | v2_struct_0('#skF_14')
      | '#skF_1'(k1_zfmisc_1(B_723),k1_xboole_0) = k1_xboole_0
      | ~ m1_subset_1(B_723,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15201,c_106])).

tff(c_15278,plain,(
    ! [B_723] :
      ( m1_subset_1(k15_lattice3('#skF_14',k1_xboole_0),u1_struct_0('#skF_14'))
      | v2_struct_0('#skF_14')
      | '#skF_1'(k1_zfmisc_1(B_723),k1_xboole_0) = k1_xboole_0
      | ~ m1_subset_1(B_723,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_15236])).

tff(c_15279,plain,(
    ! [B_723] :
      ( m1_subset_1(k15_lattice3('#skF_14',k1_xboole_0),u1_struct_0('#skF_14'))
      | '#skF_1'(k1_zfmisc_1(B_723),k1_xboole_0) = k1_xboole_0
      | ~ m1_subset_1(B_723,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_15278])).

tff(c_15528,plain,(
    m1_subset_1(k15_lattice3('#skF_14',k1_xboole_0),u1_struct_0('#skF_14')) ),
    inference(splitLeft,[status(thm)],[c_15279])).

tff(c_140,plain,
    ( k15_lattice3('#skF_14',k1_xboole_0) != k5_lattices('#skF_14')
    | ~ l3_lattices('#skF_14')
    | ~ v13_lattices('#skF_14')
    | ~ v10_lattices('#skF_14')
    | v2_struct_0('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_361])).

tff(c_150,plain,
    ( k15_lattice3('#skF_14',k1_xboole_0) != k5_lattices('#skF_14')
    | ~ v13_lattices('#skF_14')
    | v2_struct_0('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_142,c_140])).

tff(c_151,plain,
    ( k15_lattice3('#skF_14',k1_xboole_0) != k5_lattices('#skF_14')
    | ~ v13_lattices('#skF_14') ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_150])).

tff(c_180,plain,(
    ~ v13_lattices('#skF_14') ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_72,plain,(
    ! [A_57,B_66] :
      ( m1_subset_1('#skF_6'(A_57,B_66),u1_struct_0(A_57))
      | v13_lattices(A_57)
      | ~ m1_subset_1(B_66,u1_struct_0(A_57))
      | ~ l1_lattices(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_1316,plain,(
    ! [A_265,B_266] :
      ( k15_lattice3(A_265,a_2_3_lattice3(A_265,B_266)) = B_266
      | ~ m1_subset_1(B_266,u1_struct_0(A_265))
      | ~ l3_lattices(A_265)
      | ~ v4_lattice3(A_265)
      | ~ v10_lattices(A_265)
      | v2_struct_0(A_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_1340,plain,(
    ! [A_57,B_66] :
      ( k15_lattice3(A_57,a_2_3_lattice3(A_57,'#skF_6'(A_57,B_66))) = '#skF_6'(A_57,B_66)
      | ~ l3_lattices(A_57)
      | ~ v4_lattice3(A_57)
      | ~ v10_lattices(A_57)
      | v13_lattices(A_57)
      | ~ m1_subset_1(B_66,u1_struct_0(A_57))
      | ~ l1_lattices(A_57)
      | v2_struct_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_72,c_1316])).

tff(c_1231,plain,(
    ! [A_257,B_258,C_259] :
      ( r2_hidden('#skF_7'(A_257,B_258,C_259),C_259)
      | r4_lattice3(A_257,B_258,C_259)
      | ~ m1_subset_1(B_258,u1_struct_0(A_257))
      | ~ l3_lattices(A_257)
      | v2_struct_0(A_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18247,plain,(
    ! [A_764,B_765,C_766,B_767] :
      ( r2_hidden('#skF_7'(A_764,B_765,C_766),B_767)
      | ~ r1_tarski(C_766,B_767)
      | r4_lattice3(A_764,B_765,C_766)
      | ~ m1_subset_1(B_765,u1_struct_0(A_764))
      | ~ l3_lattices(A_764)
      | v2_struct_0(A_764) ) ),
    inference(resolution,[status(thm)],[c_1231,c_2])).

tff(c_11088,plain,(
    ! [A_648,B_649] :
      ( ~ r2_hidden(A_648,a_2_5_lattice3(B_649,k1_xboole_0))
      | ~ l3_lattices(B_649)
      | ~ v4_lattice3(B_649)
      | ~ v10_lattices(B_649)
      | v2_struct_0(B_649) ) ),
    inference(resolution,[status(thm)],[c_16,c_11035])).

tff(c_11114,plain,(
    ! [B_650,B_651] :
      ( ~ l3_lattices(B_650)
      | ~ v4_lattice3(B_650)
      | ~ v10_lattices(B_650)
      | v2_struct_0(B_650)
      | r1_tarski(a_2_5_lattice3(B_650,k1_xboole_0),B_651) ) ),
    inference(resolution,[status(thm)],[c_6,c_11088])).

tff(c_11275,plain,(
    ! [B_652] :
      ( a_2_5_lattice3(B_652,k1_xboole_0) = k1_xboole_0
      | ~ l3_lattices(B_652)
      | ~ v4_lattice3(B_652)
      | ~ v10_lattices(B_652)
      | v2_struct_0(B_652) ) ),
    inference(resolution,[status(thm)],[c_11114,c_18])).

tff(c_11278,plain,
    ( a_2_5_lattice3('#skF_14',k1_xboole_0) = k1_xboole_0
    | ~ l3_lattices('#skF_14')
    | ~ v10_lattices('#skF_14')
    | v2_struct_0('#skF_14') ),
    inference(resolution,[status(thm)],[c_144,c_11275])).

tff(c_11281,plain,
    ( a_2_5_lattice3('#skF_14',k1_xboole_0) = k1_xboole_0
    | v2_struct_0('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_142,c_11278])).

tff(c_11282,plain,(
    a_2_5_lattice3('#skF_14',k1_xboole_0) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_11281])).

tff(c_11087,plain,(
    ! [A_646,B_647] :
      ( ~ r2_hidden(A_646,a_2_5_lattice3(B_647,k1_xboole_0))
      | ~ l3_lattices(B_647)
      | ~ v4_lattice3(B_647)
      | ~ v10_lattices(B_647)
      | v2_struct_0(B_647) ) ),
    inference(resolution,[status(thm)],[c_16,c_11035])).

tff(c_11289,plain,(
    ! [A_646] :
      ( ~ r2_hidden(A_646,k1_xboole_0)
      | ~ l3_lattices('#skF_14')
      | ~ v4_lattice3('#skF_14')
      | ~ v10_lattices('#skF_14')
      | v2_struct_0('#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11282,c_11087])).

tff(c_11302,plain,(
    ! [A_646] :
      ( ~ r2_hidden(A_646,k1_xboole_0)
      | v2_struct_0('#skF_14') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_144,c_142,c_11289])).

tff(c_11303,plain,(
    ! [A_646] : ~ r2_hidden(A_646,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_11302])).

tff(c_18304,plain,(
    ! [C_768,A_769,B_770] :
      ( ~ r1_tarski(C_768,k1_xboole_0)
      | r4_lattice3(A_769,B_770,C_768)
      | ~ m1_subset_1(B_770,u1_struct_0(A_769))
      | ~ l3_lattices(A_769)
      | v2_struct_0(A_769) ) ),
    inference(resolution,[status(thm)],[c_18247,c_11303])).

tff(c_18366,plain,(
    ! [C_768,A_113,B_114] :
      ( ~ r1_tarski(C_768,k1_xboole_0)
      | r4_lattice3(A_113,k15_lattice3(A_113,B_114),C_768)
      | ~ l3_lattices(A_113)
      | v2_struct_0(A_113) ) ),
    inference(resolution,[status(thm)],[c_106,c_18304])).

tff(c_28,plain,(
    ! [A_19] :
      ( v9_lattices(A_19)
      | ~ v10_lattices(A_19)
      | v2_struct_0(A_19)
      | ~ l3_lattices(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_9020,plain,(
    ! [C_561,A_562,B_563] :
      ( ~ r1_tarski(C_561,'#skF_7'(A_562,B_563,C_561))
      | r4_lattice3(A_562,B_563,C_561)
      | ~ m1_subset_1(B_563,u1_struct_0(A_562))
      | ~ l3_lattices(A_562)
      | v2_struct_0(A_562) ) ),
    inference(resolution,[status(thm)],[c_1231,c_26])).

tff(c_9076,plain,(
    ! [A_564,B_565] :
      ( r4_lattice3(A_564,B_565,k1_xboole_0)
      | ~ m1_subset_1(B_565,u1_struct_0(A_564))
      | ~ l3_lattices(A_564)
      | v2_struct_0(A_564) ) ),
    inference(resolution,[status(thm)],[c_16,c_9020])).

tff(c_9140,plain,(
    ! [A_113,B_114] :
      ( r4_lattice3(A_113,k15_lattice3(A_113,B_114),k1_xboole_0)
      | ~ l3_lattices(A_113)
      | v2_struct_0(A_113) ) ),
    inference(resolution,[status(thm)],[c_106,c_9076])).

tff(c_15216,plain,(
    ! [B_723] :
      ( r4_lattice3('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),k1_xboole_0)
      | ~ l3_lattices('#skF_14')
      | v2_struct_0('#skF_14')
      | '#skF_1'(k1_zfmisc_1(B_723),k1_xboole_0) = k1_xboole_0
      | ~ m1_subset_1(B_723,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15201,c_9140])).

tff(c_15257,plain,(
    ! [B_723] :
      ( r4_lattice3('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),k1_xboole_0)
      | v2_struct_0('#skF_14')
      | '#skF_1'(k1_zfmisc_1(B_723),k1_xboole_0) = k1_xboole_0
      | ~ m1_subset_1(B_723,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_15216])).

tff(c_15258,plain,(
    ! [B_723] :
      ( r4_lattice3('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),k1_xboole_0)
      | '#skF_1'(k1_zfmisc_1(B_723),k1_xboole_0) = k1_xboole_0
      | ~ m1_subset_1(B_723,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_15257])).

tff(c_15467,plain,(
    r4_lattice3('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_15258])).

tff(c_155,plain,(
    ! [A_147] :
      ( l2_lattices(A_147)
      | ~ l3_lattices(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_159,plain,(
    l2_lattices('#skF_14') ),
    inference(resolution,[status(thm)],[c_142,c_155])).

tff(c_94,plain,(
    ! [A_90,B_97,D_101] :
      ( r1_lattices(A_90,k15_lattice3(A_90,B_97),D_101)
      | ~ r4_lattice3(A_90,D_101,B_97)
      | ~ m1_subset_1(D_101,u1_struct_0(A_90))
      | ~ m1_subset_1(k15_lattice3(A_90,B_97),u1_struct_0(A_90))
      | ~ v4_lattice3(A_90)
      | ~ v10_lattices(A_90)
      | ~ l3_lattices(A_90)
      | v2_struct_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_15537,plain,(
    ! [D_101] :
      ( r1_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),D_101)
      | ~ r4_lattice3('#skF_14',D_101,k1_xboole_0)
      | ~ m1_subset_1(D_101,u1_struct_0('#skF_14'))
      | ~ v4_lattice3('#skF_14')
      | ~ v10_lattices('#skF_14')
      | ~ l3_lattices('#skF_14')
      | v2_struct_0('#skF_14') ) ),
    inference(resolution,[status(thm)],[c_15528,c_94])).

tff(c_15570,plain,(
    ! [D_101] :
      ( r1_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),D_101)
      | ~ r4_lattice3('#skF_14',D_101,k1_xboole_0)
      | ~ m1_subset_1(D_101,u1_struct_0('#skF_14'))
      | v2_struct_0('#skF_14') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_146,c_144,c_15537])).

tff(c_15723,plain,(
    ! [D_731] :
      ( r1_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),D_731)
      | ~ r4_lattice3('#skF_14',D_731,k1_xboole_0)
      | ~ m1_subset_1(D_731,u1_struct_0('#skF_14')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_15570])).

tff(c_52,plain,(
    ! [A_30,B_34,C_36] :
      ( k1_lattices(A_30,B_34,C_36) = C_36
      | ~ r1_lattices(A_30,B_34,C_36)
      | ~ m1_subset_1(C_36,u1_struct_0(A_30))
      | ~ m1_subset_1(B_34,u1_struct_0(A_30))
      | ~ l2_lattices(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_15731,plain,(
    ! [D_731] :
      ( k1_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),D_731) = D_731
      | ~ m1_subset_1(k15_lattice3('#skF_14',k1_xboole_0),u1_struct_0('#skF_14'))
      | ~ l2_lattices('#skF_14')
      | v2_struct_0('#skF_14')
      | ~ r4_lattice3('#skF_14',D_731,k1_xboole_0)
      | ~ m1_subset_1(D_731,u1_struct_0('#skF_14')) ) ),
    inference(resolution,[status(thm)],[c_15723,c_52])).

tff(c_15742,plain,(
    ! [D_731] :
      ( k1_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),D_731) = D_731
      | v2_struct_0('#skF_14')
      | ~ r4_lattice3('#skF_14',D_731,k1_xboole_0)
      | ~ m1_subset_1(D_731,u1_struct_0('#skF_14')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_15528,c_15731])).

tff(c_15872,plain,(
    ! [D_736] :
      ( k1_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),D_736) = D_736
      | ~ r4_lattice3('#skF_14',D_736,k1_xboole_0)
      | ~ m1_subset_1(D_736,u1_struct_0('#skF_14')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_15742])).

tff(c_15875,plain,
    ( k1_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),k15_lattice3('#skF_14',k1_xboole_0)) = k15_lattice3('#skF_14',k1_xboole_0)
    | ~ r4_lattice3('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_15528,c_15872])).

tff(c_15950,plain,(
    k1_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),k15_lattice3('#skF_14',k1_xboole_0)) = k15_lattice3('#skF_14',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15467,c_15875])).

tff(c_4509,plain,(
    ! [A_406,B_407,C_408] :
      ( k2_lattices(A_406,B_407,k1_lattices(A_406,B_407,C_408)) = B_407
      | ~ m1_subset_1(C_408,u1_struct_0(A_406))
      | ~ m1_subset_1(B_407,u1_struct_0(A_406))
      | ~ v9_lattices(A_406)
      | ~ l3_lattices(A_406)
      | v2_struct_0(A_406) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_17259,plain,(
    ! [A_751,B_752,B_753] :
      ( k2_lattices(A_751,B_752,k1_lattices(A_751,B_752,k15_lattice3(A_751,B_753))) = B_752
      | ~ m1_subset_1(B_752,u1_struct_0(A_751))
      | ~ v9_lattices(A_751)
      | ~ l3_lattices(A_751)
      | v2_struct_0(A_751) ) ),
    inference(resolution,[status(thm)],[c_106,c_4509])).

tff(c_17277,plain,
    ( k2_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),k15_lattice3('#skF_14',k1_xboole_0)) = k15_lattice3('#skF_14',k1_xboole_0)
    | ~ m1_subset_1(k15_lattice3('#skF_14',k1_xboole_0),u1_struct_0('#skF_14'))
    | ~ v9_lattices('#skF_14')
    | ~ l3_lattices('#skF_14')
    | v2_struct_0('#skF_14') ),
    inference(superposition,[status(thm),theory(equality)],[c_15950,c_17259])).

tff(c_17305,plain,
    ( k2_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),k15_lattice3('#skF_14',k1_xboole_0)) = k15_lattice3('#skF_14',k1_xboole_0)
    | ~ v9_lattices('#skF_14')
    | v2_struct_0('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_15528,c_17277])).

tff(c_17306,plain,
    ( k2_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),k15_lattice3('#skF_14',k1_xboole_0)) = k15_lattice3('#skF_14',k1_xboole_0)
    | ~ v9_lattices('#skF_14') ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_17305])).

tff(c_17316,plain,(
    ~ v9_lattices('#skF_14') ),
    inference(splitLeft,[status(thm)],[c_17306])).

tff(c_17319,plain,
    ( ~ v10_lattices('#skF_14')
    | v2_struct_0('#skF_14')
    | ~ l3_lattices('#skF_14') ),
    inference(resolution,[status(thm)],[c_28,c_17316])).

tff(c_17322,plain,(
    v2_struct_0('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_146,c_17319])).

tff(c_17324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_17322])).

tff(c_17326,plain,(
    v9_lattices('#skF_14') ),
    inference(splitRight,[status(thm)],[c_17306])).

tff(c_15939,plain,(
    ! [B_114] :
      ( k1_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),k15_lattice3('#skF_14',B_114)) = k15_lattice3('#skF_14',B_114)
      | ~ r4_lattice3('#skF_14',k15_lattice3('#skF_14',B_114),k1_xboole_0)
      | ~ l3_lattices('#skF_14')
      | v2_struct_0('#skF_14') ) ),
    inference(resolution,[status(thm)],[c_106,c_15872])).

tff(c_16004,plain,(
    ! [B_114] :
      ( k1_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),k15_lattice3('#skF_14',B_114)) = k15_lattice3('#skF_14',B_114)
      | ~ r4_lattice3('#skF_14',k15_lattice3('#skF_14',B_114),k1_xboole_0)
      | v2_struct_0('#skF_14') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_15939])).

tff(c_19228,plain,(
    ! [B_804] :
      ( k1_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),k15_lattice3('#skF_14',B_804)) = k15_lattice3('#skF_14',B_804)
      | ~ r4_lattice3('#skF_14',k15_lattice3('#skF_14',B_804),k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_16004])).

tff(c_4551,plain,(
    ! [A_113,B_407,B_114] :
      ( k2_lattices(A_113,B_407,k1_lattices(A_113,B_407,k15_lattice3(A_113,B_114))) = B_407
      | ~ m1_subset_1(B_407,u1_struct_0(A_113))
      | ~ v9_lattices(A_113)
      | ~ l3_lattices(A_113)
      | v2_struct_0(A_113) ) ),
    inference(resolution,[status(thm)],[c_106,c_4509])).

tff(c_19238,plain,(
    ! [B_804] :
      ( k2_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),k15_lattice3('#skF_14',B_804)) = k15_lattice3('#skF_14',k1_xboole_0)
      | ~ m1_subset_1(k15_lattice3('#skF_14',k1_xboole_0),u1_struct_0('#skF_14'))
      | ~ v9_lattices('#skF_14')
      | ~ l3_lattices('#skF_14')
      | v2_struct_0('#skF_14')
      | ~ r4_lattice3('#skF_14',k15_lattice3('#skF_14',B_804),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19228,c_4551])).

tff(c_19283,plain,(
    ! [B_804] :
      ( k2_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),k15_lattice3('#skF_14',B_804)) = k15_lattice3('#skF_14',k1_xboole_0)
      | v2_struct_0('#skF_14')
      | ~ r4_lattice3('#skF_14',k15_lattice3('#skF_14',B_804),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_17326,c_15528,c_19238])).

tff(c_21314,plain,(
    ! [B_856] :
      ( k2_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),k15_lattice3('#skF_14',B_856)) = k15_lattice3('#skF_14',k1_xboole_0)
      | ~ r4_lattice3('#skF_14',k15_lattice3('#skF_14',B_856),k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_19283])).

tff(c_21357,plain,(
    ! [B_144] :
      ( k2_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),k15_lattice3('#skF_14',B_144)) = k15_lattice3('#skF_14',k1_xboole_0)
      | ~ r4_lattice3('#skF_14',k15_lattice3('#skF_14',a_2_5_lattice3('#skF_14',B_144)),k1_xboole_0)
      | ~ l3_lattices('#skF_14')
      | ~ v4_lattice3('#skF_14')
      | ~ v10_lattices('#skF_14')
      | v2_struct_0('#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_21314])).

tff(c_21382,plain,(
    ! [B_144] :
      ( k2_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),k15_lattice3('#skF_14',B_144)) = k15_lattice3('#skF_14',k1_xboole_0)
      | ~ r4_lattice3('#skF_14',k15_lattice3('#skF_14',a_2_5_lattice3('#skF_14',B_144)),k1_xboole_0)
      | v2_struct_0('#skF_14') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_144,c_142,c_21357])).

tff(c_136946,plain,(
    ! [B_1581] :
      ( k2_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),k15_lattice3('#skF_14',B_1581)) = k15_lattice3('#skF_14',k1_xboole_0)
      | ~ r4_lattice3('#skF_14',k15_lattice3('#skF_14',a_2_5_lattice3('#skF_14',B_1581)),k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_21382])).

tff(c_136972,plain,(
    ! [B_1581] :
      ( k2_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),k15_lattice3('#skF_14',B_1581)) = k15_lattice3('#skF_14',k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ l3_lattices('#skF_14')
      | v2_struct_0('#skF_14') ) ),
    inference(resolution,[status(thm)],[c_18366,c_136946])).

tff(c_137032,plain,(
    ! [B_1581] :
      ( k2_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),k15_lattice3('#skF_14',B_1581)) = k15_lattice3('#skF_14',k1_xboole_0)
      | v2_struct_0('#skF_14') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_12,c_136972])).

tff(c_137079,plain,(
    ! [B_1582] : k2_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),k15_lattice3('#skF_14',B_1582)) = k15_lattice3('#skF_14',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_137032])).

tff(c_137143,plain,(
    ! [B_66] :
      ( k2_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),'#skF_6'('#skF_14',B_66)) = k15_lattice3('#skF_14',k1_xboole_0)
      | ~ l3_lattices('#skF_14')
      | ~ v4_lattice3('#skF_14')
      | ~ v10_lattices('#skF_14')
      | v13_lattices('#skF_14')
      | ~ m1_subset_1(B_66,u1_struct_0('#skF_14'))
      | ~ l1_lattices('#skF_14')
      | v2_struct_0('#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1340,c_137079])).

tff(c_137240,plain,(
    ! [B_66] :
      ( k2_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),'#skF_6'('#skF_14',B_66)) = k15_lattice3('#skF_14',k1_xboole_0)
      | v13_lattices('#skF_14')
      | ~ m1_subset_1(B_66,u1_struct_0('#skF_14'))
      | v2_struct_0('#skF_14') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_146,c_144,c_142,c_137143])).

tff(c_137241,plain,(
    ! [B_66] :
      ( k2_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),'#skF_6'('#skF_14',B_66)) = k15_lattice3('#skF_14',k1_xboole_0)
      | ~ m1_subset_1(B_66,u1_struct_0('#skF_14')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_180,c_137240])).

tff(c_137033,plain,(
    ! [B_1581] : k2_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),k15_lattice3('#skF_14',B_1581)) = k15_lattice3('#skF_14',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_137032])).

tff(c_34,plain,(
    ! [A_19] :
      ( v6_lattices(A_19)
      | ~ v10_lattices(A_19)
      | v2_struct_0(A_19)
      | ~ l3_lattices(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_62,plain,(
    ! [A_48] :
      ( m1_subset_1(k5_lattices(A_48),u1_struct_0(A_48))
      | ~ l1_lattices(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_4191,plain,(
    ! [A_397,C_398,B_399] :
      ( k2_lattices(A_397,C_398,B_399) = k2_lattices(A_397,B_399,C_398)
      | ~ m1_subset_1(C_398,u1_struct_0(A_397))
      | ~ m1_subset_1(B_399,u1_struct_0(A_397))
      | ~ v6_lattices(A_397)
      | ~ l1_lattices(A_397)
      | v2_struct_0(A_397) ) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_4234,plain,(
    ! [A_48,B_399] :
      ( k2_lattices(A_48,k5_lattices(A_48),B_399) = k2_lattices(A_48,B_399,k5_lattices(A_48))
      | ~ m1_subset_1(B_399,u1_struct_0(A_48))
      | ~ v6_lattices(A_48)
      | ~ l1_lattices(A_48)
      | v2_struct_0(A_48) ) ),
    inference(resolution,[status(thm)],[c_62,c_4191])).

tff(c_15530,plain,
    ( k2_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),k5_lattices('#skF_14')) = k2_lattices('#skF_14',k5_lattices('#skF_14'),k15_lattice3('#skF_14',k1_xboole_0))
    | ~ v6_lattices('#skF_14')
    | ~ l1_lattices('#skF_14')
    | v2_struct_0('#skF_14') ),
    inference(resolution,[status(thm)],[c_15528,c_4234])).

tff(c_15558,plain,
    ( k2_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),k5_lattices('#skF_14')) = k2_lattices('#skF_14',k5_lattices('#skF_14'),k15_lattice3('#skF_14',k1_xboole_0))
    | ~ v6_lattices('#skF_14')
    | v2_struct_0('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_15530])).

tff(c_15559,plain,
    ( k2_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),k5_lattices('#skF_14')) = k2_lattices('#skF_14',k5_lattices('#skF_14'),k15_lattice3('#skF_14',k1_xboole_0))
    | ~ v6_lattices('#skF_14') ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_15558])).

tff(c_17431,plain,(
    ~ v6_lattices('#skF_14') ),
    inference(splitLeft,[status(thm)],[c_15559])).

tff(c_17434,plain,
    ( ~ v10_lattices('#skF_14')
    | v2_struct_0('#skF_14')
    | ~ l3_lattices('#skF_14') ),
    inference(resolution,[status(thm)],[c_34,c_17431])).

tff(c_17437,plain,(
    v2_struct_0('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_146,c_17434])).

tff(c_17439,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_17437])).

tff(c_17441,plain,(
    v6_lattices('#skF_14') ),
    inference(splitRight,[status(thm)],[c_15559])).

tff(c_30655,plain,(
    ! [A_1015,B_1016,B_1017] :
      ( k2_lattices(A_1015,k15_lattice3(A_1015,B_1016),B_1017) = k2_lattices(A_1015,B_1017,k15_lattice3(A_1015,B_1016))
      | ~ m1_subset_1(B_1017,u1_struct_0(A_1015))
      | ~ v6_lattices(A_1015)
      | ~ l1_lattices(A_1015)
      | ~ l3_lattices(A_1015)
      | v2_struct_0(A_1015) ) ),
    inference(resolution,[status(thm)],[c_106,c_4191])).

tff(c_30659,plain,(
    ! [B_1016] :
      ( k2_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),k15_lattice3('#skF_14',B_1016)) = k2_lattices('#skF_14',k15_lattice3('#skF_14',B_1016),k15_lattice3('#skF_14',k1_xboole_0))
      | ~ v6_lattices('#skF_14')
      | ~ l1_lattices('#skF_14')
      | ~ l3_lattices('#skF_14')
      | v2_struct_0('#skF_14') ) ),
    inference(resolution,[status(thm)],[c_15528,c_30655])).

tff(c_30706,plain,(
    ! [B_1016] :
      ( k2_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),k15_lattice3('#skF_14',B_1016)) = k2_lattices('#skF_14',k15_lattice3('#skF_14',B_1016),k15_lattice3('#skF_14',k1_xboole_0))
      | v2_struct_0('#skF_14') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_164,c_17441,c_30659])).

tff(c_32096,plain,(
    ! [B_1025] : k2_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),k15_lattice3('#skF_14',B_1025)) = k2_lattices('#skF_14',k15_lattice3('#skF_14',B_1025),k15_lattice3('#skF_14',k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_30706])).

tff(c_32154,plain,(
    ! [B_144] :
      ( k2_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),k15_lattice3('#skF_14',a_2_5_lattice3('#skF_14',B_144))) = k2_lattices('#skF_14',k15_lattice3('#skF_14',B_144),k15_lattice3('#skF_14',k1_xboole_0))
      | ~ l3_lattices('#skF_14')
      | ~ v4_lattice3('#skF_14')
      | ~ v10_lattices('#skF_14')
      | v2_struct_0('#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_32096])).

tff(c_32177,plain,(
    ! [B_144] :
      ( k2_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),k15_lattice3('#skF_14',a_2_5_lattice3('#skF_14',B_144))) = k2_lattices('#skF_14',k15_lattice3('#skF_14',B_144),k15_lattice3('#skF_14',k1_xboole_0))
      | v2_struct_0('#skF_14') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_144,c_142,c_32154])).

tff(c_32178,plain,(
    ! [B_144] : k2_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),k15_lattice3('#skF_14',a_2_5_lattice3('#skF_14',B_144))) = k2_lattices('#skF_14',k15_lattice3('#skF_14',B_144),k15_lattice3('#skF_14',k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_32177])).

tff(c_137285,plain,(
    ! [B_1583] : k2_lattices('#skF_14',k15_lattice3('#skF_14',B_1583),k15_lattice3('#skF_14',k1_xboole_0)) = k15_lattice3('#skF_14',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137033,c_32178])).

tff(c_137319,plain,(
    ! [B_66] :
      ( k2_lattices('#skF_14','#skF_6'('#skF_14',B_66),k15_lattice3('#skF_14',k1_xboole_0)) = k15_lattice3('#skF_14',k1_xboole_0)
      | ~ l3_lattices('#skF_14')
      | ~ v4_lattice3('#skF_14')
      | ~ v10_lattices('#skF_14')
      | v13_lattices('#skF_14')
      | ~ m1_subset_1(B_66,u1_struct_0('#skF_14'))
      | ~ l1_lattices('#skF_14')
      | v2_struct_0('#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1340,c_137285])).

tff(c_137387,plain,(
    ! [B_66] :
      ( k2_lattices('#skF_14','#skF_6'('#skF_14',B_66),k15_lattice3('#skF_14',k1_xboole_0)) = k15_lattice3('#skF_14',k1_xboole_0)
      | v13_lattices('#skF_14')
      | ~ m1_subset_1(B_66,u1_struct_0('#skF_14'))
      | v2_struct_0('#skF_14') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_146,c_144,c_142,c_137319])).

tff(c_137593,plain,(
    ! [B_1588] :
      ( k2_lattices('#skF_14','#skF_6'('#skF_14',B_1588),k15_lattice3('#skF_14',k1_xboole_0)) = k15_lattice3('#skF_14',k1_xboole_0)
      | ~ m1_subset_1(B_1588,u1_struct_0('#skF_14')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_180,c_137387])).

tff(c_70,plain,(
    ! [A_57,B_66] :
      ( k2_lattices(A_57,'#skF_6'(A_57,B_66),B_66) != B_66
      | k2_lattices(A_57,B_66,'#skF_6'(A_57,B_66)) != B_66
      | v13_lattices(A_57)
      | ~ m1_subset_1(B_66,u1_struct_0(A_57))
      | ~ l1_lattices(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_137599,plain,
    ( k2_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),'#skF_6'('#skF_14',k15_lattice3('#skF_14',k1_xboole_0))) != k15_lattice3('#skF_14',k1_xboole_0)
    | v13_lattices('#skF_14')
    | ~ l1_lattices('#skF_14')
    | v2_struct_0('#skF_14')
    | ~ m1_subset_1(k15_lattice3('#skF_14',k1_xboole_0),u1_struct_0('#skF_14')) ),
    inference(superposition,[status(thm),theory(equality)],[c_137593,c_70])).

tff(c_137606,plain,
    ( k2_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),'#skF_6'('#skF_14',k15_lattice3('#skF_14',k1_xboole_0))) != k15_lattice3('#skF_14',k1_xboole_0)
    | v13_lattices('#skF_14')
    | v2_struct_0('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15528,c_164,c_137599])).

tff(c_137607,plain,(
    k2_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),'#skF_6'('#skF_14',k15_lattice3('#skF_14',k1_xboole_0))) != k15_lattice3('#skF_14',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_180,c_137606])).

tff(c_137611,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_14',k1_xboole_0),u1_struct_0('#skF_14')) ),
    inference(superposition,[status(thm),theory(equality)],[c_137241,c_137607])).

tff(c_137615,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15528,c_137611])).

tff(c_137617,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_14',k1_xboole_0),u1_struct_0('#skF_14')) ),
    inference(splitRight,[status(thm)],[c_15279])).

tff(c_137713,plain,
    ( ~ l3_lattices('#skF_14')
    | v2_struct_0('#skF_14') ),
    inference(resolution,[status(thm)],[c_106,c_137617])).

tff(c_137716,plain,(
    v2_struct_0('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_137713])).

tff(c_137718,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_137716])).

tff(c_137720,plain,(
    v13_lattices('#skF_14') ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_74,plain,(
    ! [A_57] :
      ( m1_subset_1('#skF_5'(A_57),u1_struct_0(A_57))
      | ~ v13_lattices(A_57)
      | ~ l1_lattices(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_142059,plain,(
    ! [A_1845,C_1846] :
      ( k2_lattices(A_1845,C_1846,k5_lattices(A_1845)) = k5_lattices(A_1845)
      | ~ m1_subset_1(C_1846,u1_struct_0(A_1845))
      | ~ m1_subset_1(k5_lattices(A_1845),u1_struct_0(A_1845))
      | ~ v13_lattices(A_1845)
      | ~ l1_lattices(A_1845)
      | v2_struct_0(A_1845) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_147531,plain,(
    ! [A_2052] :
      ( k2_lattices(A_2052,'#skF_5'(A_2052),k5_lattices(A_2052)) = k5_lattices(A_2052)
      | ~ m1_subset_1(k5_lattices(A_2052),u1_struct_0(A_2052))
      | ~ v13_lattices(A_2052)
      | ~ l1_lattices(A_2052)
      | v2_struct_0(A_2052) ) ),
    inference(resolution,[status(thm)],[c_74,c_142059])).

tff(c_147535,plain,(
    ! [A_2053] :
      ( k2_lattices(A_2053,'#skF_5'(A_2053),k5_lattices(A_2053)) = k5_lattices(A_2053)
      | ~ v13_lattices(A_2053)
      | ~ l1_lattices(A_2053)
      | v2_struct_0(A_2053) ) ),
    inference(resolution,[status(thm)],[c_62,c_147531])).

tff(c_138410,plain,(
    ! [A_1672,C_1673] :
      ( k2_lattices(A_1672,'#skF_5'(A_1672),C_1673) = '#skF_5'(A_1672)
      | ~ m1_subset_1(C_1673,u1_struct_0(A_1672))
      | ~ v13_lattices(A_1672)
      | ~ l1_lattices(A_1672)
      | v2_struct_0(A_1672) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_138441,plain,(
    ! [A_48] :
      ( k2_lattices(A_48,'#skF_5'(A_48),k5_lattices(A_48)) = '#skF_5'(A_48)
      | ~ v13_lattices(A_48)
      | ~ l1_lattices(A_48)
      | v2_struct_0(A_48) ) ),
    inference(resolution,[status(thm)],[c_62,c_138410])).

tff(c_147541,plain,(
    ! [A_2053] :
      ( k5_lattices(A_2053) = '#skF_5'(A_2053)
      | ~ v13_lattices(A_2053)
      | ~ l1_lattices(A_2053)
      | v2_struct_0(A_2053)
      | ~ v13_lattices(A_2053)
      | ~ l1_lattices(A_2053)
      | v2_struct_0(A_2053) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147535,c_138441])).

tff(c_147565,plain,(
    ! [A_2059] :
      ( k5_lattices(A_2059) = '#skF_5'(A_2059)
      | ~ v13_lattices(A_2059)
      | ~ l1_lattices(A_2059)
      | v2_struct_0(A_2059) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_147541])).

tff(c_147568,plain,
    ( k5_lattices('#skF_14') = '#skF_5'('#skF_14')
    | ~ v13_lattices('#skF_14')
    | ~ l1_lattices('#skF_14') ),
    inference(resolution,[status(thm)],[c_147565,c_148])).

tff(c_147571,plain,(
    k5_lattices('#skF_14') = '#skF_5'('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_137720,c_147568])).

tff(c_137719,plain,(
    k15_lattice3('#skF_14',k1_xboole_0) != k5_lattices('#skF_14') ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_147572,plain,(
    k15_lattice3('#skF_14',k1_xboole_0) != '#skF_5'('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_147571,c_137719])).

tff(c_137742,plain,(
    ! [A_1602,B_1603] :
      ( r2_hidden('#skF_1'(A_1602,B_1603),A_1602)
      | r1_tarski(A_1602,B_1603) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_137770,plain,(
    ! [A_1611,B_1612] :
      ( m1_subset_1('#skF_1'(A_1611,B_1612),A_1611)
      | r1_tarski(A_1611,B_1612) ) ),
    inference(resolution,[status(thm)],[c_137742,c_20])).

tff(c_137775,plain,(
    ! [B_16,B_1612] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(B_16),B_1612),B_16)
      | r1_tarski(k1_zfmisc_1(B_16),B_1612) ) ),
    inference(resolution,[status(thm)],[c_137770,c_22])).

tff(c_137796,plain,(
    ! [B_1621,B_1622] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(B_1621),B_1622),B_1621)
      | r1_tarski(k1_zfmisc_1(B_1621),B_1622) ) ),
    inference(resolution,[status(thm)],[c_137770,c_22])).

tff(c_137812,plain,(
    ! [B_1623] :
      ( '#skF_1'(k1_zfmisc_1(k1_xboole_0),B_1623) = k1_xboole_0
      | r1_tarski(k1_zfmisc_1(k1_xboole_0),B_1623) ) ),
    inference(resolution,[status(thm)],[c_137796,c_18])).

tff(c_137832,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | '#skF_1'(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_137812,c_18])).

tff(c_137833,plain,(
    '#skF_1'(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_137832])).

tff(c_137846,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_137833,c_6])).

tff(c_137856,plain,(
    r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_137846])).

tff(c_137863,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_137856,c_8])).

tff(c_137871,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_137863])).

tff(c_137917,plain,(
    ! [A_1627] :
      ( r1_tarski(A_1627,k1_xboole_0)
      | ~ m1_subset_1(A_1627,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137871,c_22])).

tff(c_137776,plain,(
    ! [A_1613,C_1614,B_1615] :
      ( r1_tarski(A_1613,C_1614)
      | ~ r1_tarski(B_1615,C_1614)
      | ~ r1_tarski(A_1613,B_1615) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_137782,plain,(
    ! [A_1613,A_11] :
      ( r1_tarski(A_1613,A_11)
      | ~ r1_tarski(A_1613,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_137776])).

tff(c_137968,plain,(
    ! [A_1631,A_1632] :
      ( r1_tarski(A_1631,A_1632)
      | ~ m1_subset_1(A_1631,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_137917,c_137782])).

tff(c_137997,plain,(
    ! [A_1635,A_1634] :
      ( A_1635 = A_1634
      | ~ r1_tarski(A_1634,A_1635)
      | ~ m1_subset_1(A_1635,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_137968,c_8])).

tff(c_138193,plain,(
    ! [B_1661,B_1662] :
      ( '#skF_1'(k1_zfmisc_1(B_1661),B_1662) = B_1661
      | ~ m1_subset_1(B_1661,k1_xboole_0)
      | r1_tarski(k1_zfmisc_1(B_1661),B_1662) ) ),
    inference(resolution,[status(thm)],[c_137775,c_137997])).

tff(c_137887,plain,(
    ! [A_15] :
      ( m1_subset_1(A_15,k1_xboole_0)
      | ~ r1_tarski(A_15,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137871,c_24])).

tff(c_138228,plain,(
    ! [B_1661] :
      ( m1_subset_1(k1_zfmisc_1(B_1661),k1_xboole_0)
      | '#skF_1'(k1_zfmisc_1(B_1661),k1_xboole_0) = B_1661
      | ~ m1_subset_1(B_1661,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_138193,c_137887])).

tff(c_137927,plain,(
    ! [A_1627,A_11] :
      ( r1_tarski(A_1627,A_11)
      | ~ m1_subset_1(A_1627,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_137917,c_137782])).

tff(c_139361,plain,(
    ! [A_1739,B_1740,C_1741] :
      ( r2_hidden('#skF_13'(A_1739,B_1740,C_1741),C_1741)
      | ~ r2_hidden(A_1739,a_2_5_lattice3(B_1740,C_1741))
      | ~ l3_lattices(B_1740)
      | ~ v4_lattice3(B_1740)
      | ~ v10_lattices(B_1740)
      | v2_struct_0(B_1740) ) ),
    inference(cnfTransformation,[status(thm)],[f_294])).

tff(c_147822,plain,(
    ! [C_2061,A_2062,B_2063] :
      ( ~ r1_tarski(C_2061,'#skF_13'(A_2062,B_2063,C_2061))
      | ~ r2_hidden(A_2062,a_2_5_lattice3(B_2063,C_2061))
      | ~ l3_lattices(B_2063)
      | ~ v4_lattice3(B_2063)
      | ~ v10_lattices(B_2063)
      | v2_struct_0(B_2063) ) ),
    inference(resolution,[status(thm)],[c_139361,c_26])).

tff(c_149197,plain,(
    ! [A_2107,B_2108,A_2109] :
      ( ~ r2_hidden(A_2107,a_2_5_lattice3(B_2108,A_2109))
      | ~ l3_lattices(B_2108)
      | ~ v4_lattice3(B_2108)
      | ~ v10_lattices(B_2108)
      | v2_struct_0(B_2108)
      | ~ m1_subset_1(A_2109,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_137927,c_147822])).

tff(c_149248,plain,(
    ! [B_2114,A_2115,B_2116] :
      ( ~ l3_lattices(B_2114)
      | ~ v4_lattice3(B_2114)
      | ~ v10_lattices(B_2114)
      | v2_struct_0(B_2114)
      | ~ m1_subset_1(A_2115,k1_xboole_0)
      | r1_tarski(a_2_5_lattice3(B_2114,A_2115),B_2116) ) ),
    inference(resolution,[status(thm)],[c_6,c_149197])).

tff(c_149466,plain,(
    ! [B_2119,A_2120] :
      ( a_2_5_lattice3(B_2119,A_2120) = k1_xboole_0
      | ~ l3_lattices(B_2119)
      | ~ v4_lattice3(B_2119)
      | ~ v10_lattices(B_2119)
      | v2_struct_0(B_2119)
      | ~ m1_subset_1(A_2120,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_149248,c_18])).

tff(c_149468,plain,(
    ! [A_2120] :
      ( a_2_5_lattice3('#skF_14',A_2120) = k1_xboole_0
      | ~ l3_lattices('#skF_14')
      | ~ v10_lattices('#skF_14')
      | v2_struct_0('#skF_14')
      | ~ m1_subset_1(A_2120,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_144,c_149466])).

tff(c_149471,plain,(
    ! [A_2120] :
      ( a_2_5_lattice3('#skF_14',A_2120) = k1_xboole_0
      | v2_struct_0('#skF_14')
      | ~ m1_subset_1(A_2120,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_142,c_149468])).

tff(c_149473,plain,(
    ! [A_2121] :
      ( a_2_5_lattice3('#skF_14',A_2121) = k1_xboole_0
      | ~ m1_subset_1(A_2121,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_149471])).

tff(c_149575,plain,(
    ! [B_2123] :
      ( a_2_5_lattice3('#skF_14',k1_zfmisc_1(B_2123)) = k1_xboole_0
      | '#skF_1'(k1_zfmisc_1(B_2123),k1_xboole_0) = B_2123
      | ~ m1_subset_1(B_2123,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_138228,c_149473])).

tff(c_149601,plain,(
    ! [B_2123] :
      ( k15_lattice3('#skF_14',k1_zfmisc_1(B_2123)) = k15_lattice3('#skF_14',k1_xboole_0)
      | ~ l3_lattices('#skF_14')
      | ~ v4_lattice3('#skF_14')
      | ~ v10_lattices('#skF_14')
      | v2_struct_0('#skF_14')
      | '#skF_1'(k1_zfmisc_1(B_2123),k1_xboole_0) = B_2123
      | ~ m1_subset_1(B_2123,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149575,c_136])).

tff(c_149631,plain,(
    ! [B_2123] :
      ( k15_lattice3('#skF_14',k1_zfmisc_1(B_2123)) = k15_lattice3('#skF_14',k1_xboole_0)
      | v2_struct_0('#skF_14')
      | '#skF_1'(k1_zfmisc_1(B_2123),k1_xboole_0) = B_2123
      | ~ m1_subset_1(B_2123,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_144,c_142,c_149601])).

tff(c_149817,plain,(
    ! [B_2128] :
      ( k15_lattice3('#skF_14',k1_zfmisc_1(B_2128)) = k15_lattice3('#skF_14',k1_xboole_0)
      | '#skF_1'(k1_zfmisc_1(B_2128),k1_xboole_0) = B_2128
      | ~ m1_subset_1(B_2128,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_149631])).

tff(c_149877,plain,(
    ! [B_2128] :
      ( m1_subset_1(k15_lattice3('#skF_14',k1_xboole_0),u1_struct_0('#skF_14'))
      | ~ l3_lattices('#skF_14')
      | v2_struct_0('#skF_14')
      | '#skF_1'(k1_zfmisc_1(B_2128),k1_xboole_0) = B_2128
      | ~ m1_subset_1(B_2128,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149817,c_106])).

tff(c_149929,plain,(
    ! [B_2128] :
      ( m1_subset_1(k15_lattice3('#skF_14',k1_xboole_0),u1_struct_0('#skF_14'))
      | v2_struct_0('#skF_14')
      | '#skF_1'(k1_zfmisc_1(B_2128),k1_xboole_0) = B_2128
      | ~ m1_subset_1(B_2128,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_149877])).

tff(c_149930,plain,(
    ! [B_2128] :
      ( m1_subset_1(k15_lattice3('#skF_14',k1_xboole_0),u1_struct_0('#skF_14'))
      | '#skF_1'(k1_zfmisc_1(B_2128),k1_xboole_0) = B_2128
      | ~ m1_subset_1(B_2128,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_149929])).

tff(c_149937,plain,(
    m1_subset_1(k15_lattice3('#skF_14',k1_xboole_0),u1_struct_0('#skF_14')) ),
    inference(splitLeft,[status(thm)],[c_149930])).

tff(c_147603,plain,
    ( m1_subset_1('#skF_5'('#skF_14'),u1_struct_0('#skF_14'))
    | ~ l1_lattices('#skF_14')
    | v2_struct_0('#skF_14') ),
    inference(superposition,[status(thm),theory(equality)],[c_147571,c_62])).

tff(c_147634,plain,
    ( m1_subset_1('#skF_5'('#skF_14'),u1_struct_0('#skF_14'))
    | v2_struct_0('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_147603])).

tff(c_147635,plain,(
    m1_subset_1('#skF_5'('#skF_14'),u1_struct_0('#skF_14')) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_147634])).

tff(c_98,plain,(
    ! [A_102,C_111,B_109] :
      ( k2_lattices(A_102,C_111,B_109) = k2_lattices(A_102,B_109,C_111)
      | ~ m1_subset_1(C_111,u1_struct_0(A_102))
      | ~ m1_subset_1(B_109,u1_struct_0(A_102))
      | ~ v6_lattices(A_102)
      | ~ l1_lattices(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_147647,plain,(
    ! [B_109] :
      ( k2_lattices('#skF_14',B_109,'#skF_5'('#skF_14')) = k2_lattices('#skF_14','#skF_5'('#skF_14'),B_109)
      | ~ m1_subset_1(B_109,u1_struct_0('#skF_14'))
      | ~ v6_lattices('#skF_14')
      | ~ l1_lattices('#skF_14')
      | v2_struct_0('#skF_14') ) ),
    inference(resolution,[status(thm)],[c_147635,c_98])).

tff(c_147678,plain,(
    ! [B_109] :
      ( k2_lattices('#skF_14',B_109,'#skF_5'('#skF_14')) = k2_lattices('#skF_14','#skF_5'('#skF_14'),B_109)
      | ~ m1_subset_1(B_109,u1_struct_0('#skF_14'))
      | ~ v6_lattices('#skF_14')
      | v2_struct_0('#skF_14') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_147647])).

tff(c_147679,plain,(
    ! [B_109] :
      ( k2_lattices('#skF_14',B_109,'#skF_5'('#skF_14')) = k2_lattices('#skF_14','#skF_5'('#skF_14'),B_109)
      | ~ m1_subset_1(B_109,u1_struct_0('#skF_14'))
      | ~ v6_lattices('#skF_14') ) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_147678])).

tff(c_148710,plain,(
    ~ v6_lattices('#skF_14') ),
    inference(splitLeft,[status(thm)],[c_147679])).

tff(c_148713,plain,
    ( ~ v10_lattices('#skF_14')
    | v2_struct_0('#skF_14')
    | ~ l3_lattices('#skF_14') ),
    inference(resolution,[status(thm)],[c_34,c_148710])).

tff(c_148716,plain,(
    v2_struct_0('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_146,c_148713])).

tff(c_148718,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_148716])).

tff(c_148721,plain,(
    ! [B_2101] :
      ( k2_lattices('#skF_14',B_2101,'#skF_5'('#skF_14')) = k2_lattices('#skF_14','#skF_5'('#skF_14'),B_2101)
      | ~ m1_subset_1(B_2101,u1_struct_0('#skF_14')) ) ),
    inference(splitRight,[status(thm)],[c_147679])).

tff(c_148784,plain,(
    ! [B_114] :
      ( k2_lattices('#skF_14',k15_lattice3('#skF_14',B_114),'#skF_5'('#skF_14')) = k2_lattices('#skF_14','#skF_5'('#skF_14'),k15_lattice3('#skF_14',B_114))
      | ~ l3_lattices('#skF_14')
      | v2_struct_0('#skF_14') ) ),
    inference(resolution,[status(thm)],[c_106,c_148721])).

tff(c_148847,plain,(
    ! [B_114] :
      ( k2_lattices('#skF_14',k15_lattice3('#skF_14',B_114),'#skF_5'('#skF_14')) = k2_lattices('#skF_14','#skF_5'('#skF_14'),k15_lattice3('#skF_14',B_114))
      | v2_struct_0('#skF_14') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_148784])).

tff(c_148854,plain,(
    ! [B_2102] : k2_lattices('#skF_14',k15_lattice3('#skF_14',B_2102),'#skF_5'('#skF_14')) = k2_lattices('#skF_14','#skF_5'('#skF_14'),k15_lattice3('#skF_14',B_2102)) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_148847])).

tff(c_138277,plain,(
    ! [A_1664,C_1665] :
      ( k2_lattices(A_1664,C_1665,'#skF_5'(A_1664)) = '#skF_5'(A_1664)
      | ~ m1_subset_1(C_1665,u1_struct_0(A_1664))
      | ~ v13_lattices(A_1664)
      | ~ l1_lattices(A_1664)
      | v2_struct_0(A_1664) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_138307,plain,(
    ! [A_113,B_114] :
      ( k2_lattices(A_113,k15_lattice3(A_113,B_114),'#skF_5'(A_113)) = '#skF_5'(A_113)
      | ~ v13_lattices(A_113)
      | ~ l1_lattices(A_113)
      | ~ l3_lattices(A_113)
      | v2_struct_0(A_113) ) ),
    inference(resolution,[status(thm)],[c_106,c_138277])).

tff(c_148860,plain,(
    ! [B_2102] :
      ( k2_lattices('#skF_14','#skF_5'('#skF_14'),k15_lattice3('#skF_14',B_2102)) = '#skF_5'('#skF_14')
      | ~ v13_lattices('#skF_14')
      | ~ l1_lattices('#skF_14')
      | ~ l3_lattices('#skF_14')
      | v2_struct_0('#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148854,c_138307])).

tff(c_148885,plain,(
    ! [B_2102] :
      ( k2_lattices('#skF_14','#skF_5'('#skF_14'),k15_lattice3('#skF_14',B_2102)) = '#skF_5'('#skF_14')
      | v2_struct_0('#skF_14') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_164,c_137720,c_148860])).

tff(c_148886,plain,(
    ! [B_2102] : k2_lattices('#skF_14','#skF_5'('#skF_14'),k15_lattice3('#skF_14',B_2102)) = '#skF_5'('#skF_14') ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_148885])).

tff(c_148848,plain,(
    ! [B_114] : k2_lattices('#skF_14',k15_lattice3('#skF_14',B_114),'#skF_5'('#skF_14')) = k2_lattices('#skF_14','#skF_5'('#skF_14'),k15_lattice3('#skF_14',B_114)) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_148847])).

tff(c_148995,plain,(
    ! [B_114] : k2_lattices('#skF_14',k15_lattice3('#skF_14',B_114),'#skF_5'('#skF_14')) = '#skF_5'('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148886,c_148848])).

tff(c_138866,plain,(
    ! [A_1699,B_1700,C_1701] :
      ( r2_hidden('#skF_7'(A_1699,B_1700,C_1701),C_1701)
      | r4_lattice3(A_1699,B_1700,C_1701)
      | ~ m1_subset_1(B_1700,u1_struct_0(A_1699))
      | ~ l3_lattices(A_1699)
      | v2_struct_0(A_1699) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_147306,plain,(
    ! [C_2025,A_2026,B_2027] :
      ( ~ r1_tarski(C_2025,'#skF_7'(A_2026,B_2027,C_2025))
      | r4_lattice3(A_2026,B_2027,C_2025)
      | ~ m1_subset_1(B_2027,u1_struct_0(A_2026))
      | ~ l3_lattices(A_2026)
      | v2_struct_0(A_2026) ) ),
    inference(resolution,[status(thm)],[c_138866,c_26])).

tff(c_147362,plain,(
    ! [A_2028,B_2029] :
      ( r4_lattice3(A_2028,B_2029,k1_xboole_0)
      | ~ m1_subset_1(B_2029,u1_struct_0(A_2028))
      | ~ l3_lattices(A_2028)
      | v2_struct_0(A_2028) ) ),
    inference(resolution,[status(thm)],[c_16,c_147306])).

tff(c_147432,plain,(
    ! [A_48] :
      ( r4_lattice3(A_48,k5_lattices(A_48),k1_xboole_0)
      | ~ l3_lattices(A_48)
      | ~ l1_lattices(A_48)
      | v2_struct_0(A_48) ) ),
    inference(resolution,[status(thm)],[c_62,c_147362])).

tff(c_147588,plain,
    ( r4_lattice3('#skF_14','#skF_5'('#skF_14'),k1_xboole_0)
    | ~ l3_lattices('#skF_14')
    | ~ l1_lattices('#skF_14')
    | v2_struct_0('#skF_14') ),
    inference(superposition,[status(thm),theory(equality)],[c_147571,c_147432])).

tff(c_147619,plain,
    ( r4_lattice3('#skF_14','#skF_5'('#skF_14'),k1_xboole_0)
    | v2_struct_0('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_142,c_147588])).

tff(c_147620,plain,(
    r4_lattice3('#skF_14','#skF_5'('#skF_14'),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_147619])).

tff(c_149949,plain,(
    ! [D_101] :
      ( r1_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),D_101)
      | ~ r4_lattice3('#skF_14',D_101,k1_xboole_0)
      | ~ m1_subset_1(D_101,u1_struct_0('#skF_14'))
      | ~ v4_lattice3('#skF_14')
      | ~ v10_lattices('#skF_14')
      | ~ l3_lattices('#skF_14')
      | v2_struct_0('#skF_14') ) ),
    inference(resolution,[status(thm)],[c_149937,c_94])).

tff(c_149984,plain,(
    ! [D_101] :
      ( r1_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),D_101)
      | ~ r4_lattice3('#skF_14',D_101,k1_xboole_0)
      | ~ m1_subset_1(D_101,u1_struct_0('#skF_14'))
      | v2_struct_0('#skF_14') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_146,c_144,c_149949])).

tff(c_150248,plain,(
    ! [D_2134] :
      ( r1_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),D_2134)
      | ~ r4_lattice3('#skF_14',D_2134,k1_xboole_0)
      | ~ m1_subset_1(D_2134,u1_struct_0('#skF_14')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_149984])).

tff(c_150256,plain,(
    ! [D_2134] :
      ( k1_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),D_2134) = D_2134
      | ~ m1_subset_1(k15_lattice3('#skF_14',k1_xboole_0),u1_struct_0('#skF_14'))
      | ~ l2_lattices('#skF_14')
      | v2_struct_0('#skF_14')
      | ~ r4_lattice3('#skF_14',D_2134,k1_xboole_0)
      | ~ m1_subset_1(D_2134,u1_struct_0('#skF_14')) ) ),
    inference(resolution,[status(thm)],[c_150248,c_52])).

tff(c_150267,plain,(
    ! [D_2134] :
      ( k1_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),D_2134) = D_2134
      | v2_struct_0('#skF_14')
      | ~ r4_lattice3('#skF_14',D_2134,k1_xboole_0)
      | ~ m1_subset_1(D_2134,u1_struct_0('#skF_14')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_149937,c_150256])).

tff(c_150753,plain,(
    ! [D_2158] :
      ( k1_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),D_2158) = D_2158
      | ~ r4_lattice3('#skF_14',D_2158,k1_xboole_0)
      | ~ m1_subset_1(D_2158,u1_struct_0('#skF_14')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_150267])).

tff(c_150815,plain,
    ( k1_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),'#skF_5'('#skF_14')) = '#skF_5'('#skF_14')
    | ~ r4_lattice3('#skF_14','#skF_5'('#skF_14'),k1_xboole_0)
    | ~ v13_lattices('#skF_14')
    | ~ l1_lattices('#skF_14')
    | v2_struct_0('#skF_14') ),
    inference(resolution,[status(thm)],[c_74,c_150753])).

tff(c_150882,plain,
    ( k1_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),'#skF_5'('#skF_14')) = '#skF_5'('#skF_14')
    | v2_struct_0('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_137720,c_147620,c_150815])).

tff(c_150883,plain,(
    k1_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),'#skF_5'('#skF_14')) = '#skF_5'('#skF_14') ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_150882])).

tff(c_54,plain,(
    ! [A_37,B_44,C_46] :
      ( k2_lattices(A_37,B_44,k1_lattices(A_37,B_44,C_46)) = B_44
      | ~ m1_subset_1(C_46,u1_struct_0(A_37))
      | ~ m1_subset_1(B_44,u1_struct_0(A_37))
      | ~ v9_lattices(A_37)
      | ~ l3_lattices(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_147645,plain,(
    ! [B_44] :
      ( k2_lattices('#skF_14',B_44,k1_lattices('#skF_14',B_44,'#skF_5'('#skF_14'))) = B_44
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_14'))
      | ~ v9_lattices('#skF_14')
      | ~ l3_lattices('#skF_14')
      | v2_struct_0('#skF_14') ) ),
    inference(resolution,[status(thm)],[c_147635,c_54])).

tff(c_147674,plain,(
    ! [B_44] :
      ( k2_lattices('#skF_14',B_44,k1_lattices('#skF_14',B_44,'#skF_5'('#skF_14'))) = B_44
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_14'))
      | ~ v9_lattices('#skF_14')
      | v2_struct_0('#skF_14') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_147645])).

tff(c_147675,plain,(
    ! [B_44] :
      ( k2_lattices('#skF_14',B_44,k1_lattices('#skF_14',B_44,'#skF_5'('#skF_14'))) = B_44
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_14'))
      | ~ v9_lattices('#skF_14') ) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_147674])).

tff(c_148289,plain,(
    ~ v9_lattices('#skF_14') ),
    inference(splitLeft,[status(thm)],[c_147675])).

tff(c_148292,plain,
    ( ~ v10_lattices('#skF_14')
    | v2_struct_0('#skF_14')
    | ~ l3_lattices('#skF_14') ),
    inference(resolution,[status(thm)],[c_28,c_148289])).

tff(c_148295,plain,(
    v2_struct_0('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_146,c_148292])).

tff(c_148297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_148295])).

tff(c_148298,plain,(
    ! [B_44] :
      ( k2_lattices('#skF_14',B_44,k1_lattices('#skF_14',B_44,'#skF_5'('#skF_14'))) = B_44
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_14')) ) ),
    inference(splitRight,[status(thm)],[c_147675])).

tff(c_150896,plain,
    ( k2_lattices('#skF_14',k15_lattice3('#skF_14',k1_xboole_0),'#skF_5'('#skF_14')) = k15_lattice3('#skF_14',k1_xboole_0)
    | ~ m1_subset_1(k15_lattice3('#skF_14',k1_xboole_0),u1_struct_0('#skF_14')) ),
    inference(superposition,[status(thm),theory(equality)],[c_150883,c_148298])).

tff(c_150900,plain,(
    k15_lattice3('#skF_14',k1_xboole_0) = '#skF_5'('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149937,c_148995,c_150896])).

tff(c_150902,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147572,c_150900])).

tff(c_150904,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_14',k1_xboole_0),u1_struct_0('#skF_14')) ),
    inference(splitRight,[status(thm)],[c_149930])).

tff(c_150907,plain,
    ( ~ l3_lattices('#skF_14')
    | v2_struct_0('#skF_14') ),
    inference(resolution,[status(thm)],[c_106,c_150904])).

tff(c_150910,plain,(
    v2_struct_0('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_150907])).

tff(c_150912,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_150910])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:24:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 47.82/36.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 47.82/37.01  
% 47.82/37.01  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 47.82/37.01  %$ r4_lattice3 > r3_lattices > r1_lattices > r2_hidden > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k1_lattices > k16_lattice3 > k15_lattice3 > a_2_6_lattice3 > a_2_5_lattice3 > a_2_4_lattice3 > a_2_3_lattice3 > #nlpp > u1_struct_0 > k5_lattices > k1_zfmisc_1 > k1_xboole_0 > #skF_13 > #skF_9 > #skF_5 > #skF_6 > #skF_4 > #skF_12 > #skF_14 > #skF_10 > #skF_11 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_1
% 47.82/37.01  
% 47.82/37.01  %Foreground sorts:
% 47.82/37.01  
% 47.82/37.01  
% 47.82/37.01  %Background operators:
% 47.82/37.01  
% 47.82/37.01  
% 47.82/37.01  %Foreground operators:
% 47.82/37.01  tff(l3_lattices, type, l3_lattices: $i > $o).
% 47.82/37.01  tff('#skF_13', type, '#skF_13': ($i * $i * $i) > $i).
% 47.82/37.01  tff('#skF_9', type, '#skF_9': $i > $i).
% 47.82/37.01  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 47.82/37.01  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 47.82/37.01  tff('#skF_5', type, '#skF_5': $i > $i).
% 47.82/37.01  tff(l2_lattices, type, l2_lattices: $i > $o).
% 47.82/37.01  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 47.82/37.01  tff('#skF_4', type, '#skF_4': $i > $i).
% 47.82/37.01  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 47.82/37.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 47.82/37.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 47.82/37.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 47.82/37.01  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 47.82/37.01  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 47.82/37.01  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 47.82/37.01  tff('#skF_12', type, '#skF_12': ($i * $i * $i) > $i).
% 47.82/37.01  tff(l1_lattices, type, l1_lattices: $i > $o).
% 47.82/37.01  tff(a_2_4_lattice3, type, a_2_4_lattice3: ($i * $i) > $i).
% 47.82/37.01  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 47.82/37.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 47.82/37.01  tff('#skF_14', type, '#skF_14': $i).
% 47.82/37.01  tff(v4_lattices, type, v4_lattices: $i > $o).
% 47.82/37.01  tff('#skF_10', type, '#skF_10': $i > $i).
% 47.82/37.01  tff(v6_lattices, type, v6_lattices: $i > $o).
% 47.82/37.01  tff(v9_lattices, type, v9_lattices: $i > $o).
% 47.82/37.01  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 47.82/37.01  tff(a_2_3_lattice3, type, a_2_3_lattice3: ($i * $i) > $i).
% 47.82/37.01  tff(a_2_5_lattice3, type, a_2_5_lattice3: ($i * $i) > $i).
% 47.82/37.01  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 47.82/37.01  tff(v5_lattices, type, v5_lattices: $i > $o).
% 47.82/37.01  tff('#skF_11', type, '#skF_11': ($i * $i * $i) > $i).
% 47.82/37.01  tff(v10_lattices, type, v10_lattices: $i > $o).
% 47.82/37.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 47.82/37.01  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 47.82/37.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 47.82/37.01  tff(v13_lattices, type, v13_lattices: $i > $o).
% 47.82/37.01  tff('#skF_3', type, '#skF_3': $i > $i).
% 47.82/37.01  tff(v8_lattices, type, v8_lattices: $i > $o).
% 47.82/37.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 47.82/37.01  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 47.82/37.01  tff(k5_lattices, type, k5_lattices: $i > $i).
% 47.82/37.01  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 47.82/37.01  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 47.82/37.01  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 47.82/37.01  tff(a_2_6_lattice3, type, a_2_6_lattice3: ($i * $i) > $i).
% 47.82/37.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 47.82/37.01  tff(v7_lattices, type, v7_lattices: $i > $o).
% 47.82/37.01  
% 48.15/37.05  tff(f_361, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v13_lattices(A)) & l3_lattices(A)) & (k5_lattices(A) = k15_lattice3(A, k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_lattice3)).
% 48.15/37.05  tff(f_251, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k15_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 48.15/37.05  tff(f_147, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 48.15/37.05  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 48.15/37.05  tff(f_46, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 48.15/37.05  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 48.15/37.05  tff(f_54, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 48.15/37.05  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 48.15/37.05  tff(f_50, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 48.15/37.05  tff(f_44, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 48.15/37.05  tff(f_294, axiom, (![A, B, C]: ((((~v2_struct_0(B) & v10_lattices(B)) & v4_lattice3(B)) & l3_lattices(B)) => (r2_hidden(A, a_2_5_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r3_lattices(B, D, E)) & r2_hidden(E, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_5_lattice3)).
% 48.15/37.05  tff(f_63, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 48.15/37.05  tff(f_340, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: ((k15_lattice3(A, B) = k15_lattice3(A, a_2_5_lattice3(A, B))) & (k16_lattice3(A, B) = k16_lattice3(A, a_2_6_lattice3(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_lattice3)).
% 48.15/37.05  tff(f_183, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) <=> (?[B]: (m1_subset_1(B, u1_struct_0(A)) & (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_lattices)).
% 48.15/37.05  tff(f_310, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((B = k15_lattice3(A, a_2_3_lattice3(A, B))) & (B = k16_lattice3(A, a_2_4_lattice3(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_lattice3)).
% 48.15/37.05  tff(f_201, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_lattice3)).
% 48.15/37.05  tff(f_85, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 48.15/37.05  tff(f_229, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k15_lattice3(A, B)) <=> (r4_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d21_lattice3)).
% 48.15/37.05  tff(f_119, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k1_lattices(A, B, C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_lattices)).
% 48.15/37.05  tff(f_134, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v9_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, k1_lattices(A, B, C)) = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattices)).
% 48.15/37.05  tff(f_141, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => m1_subset_1(k5_lattices(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_lattices)).
% 48.15/37.05  tff(f_244, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v6_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, C) = k2_lattices(A, C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_lattices)).
% 48.15/37.05  tff(f_104, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((B = k5_lattices(A)) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattices)).
% 48.15/37.05  tff(c_148, plain, (~v2_struct_0('#skF_14')), inference(cnfTransformation, [status(thm)], [f_361])).
% 48.15/37.05  tff(c_142, plain, (l3_lattices('#skF_14')), inference(cnfTransformation, [status(thm)], [f_361])).
% 48.15/37.05  tff(c_106, plain, (![A_113, B_114]: (m1_subset_1(k15_lattice3(A_113, B_114), u1_struct_0(A_113)) | ~l3_lattices(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_251])).
% 48.15/37.05  tff(c_160, plain, (![A_148]: (l1_lattices(A_148) | ~l3_lattices(A_148))), inference(cnfTransformation, [status(thm)], [f_147])).
% 48.15/37.05  tff(c_164, plain, (l1_lattices('#skF_14')), inference(resolution, [status(thm)], [c_142, c_160])).
% 48.15/37.05  tff(c_146, plain, (v10_lattices('#skF_14')), inference(cnfTransformation, [status(thm)], [f_361])).
% 48.15/37.05  tff(c_144, plain, (v4_lattice3('#skF_14')), inference(cnfTransformation, [status(thm)], [f_361])).
% 48.15/37.05  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 48.15/37.05  tff(c_16, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 48.15/37.05  tff(c_201, plain, (![A_165, B_166]: (r2_hidden('#skF_1'(A_165, B_166), A_165) | r1_tarski(A_165, B_166))), inference(cnfTransformation, [status(thm)], [f_32])).
% 48.15/37.05  tff(c_20, plain, (![A_13, B_14]: (m1_subset_1(A_13, B_14) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 48.15/37.05  tff(c_219, plain, (![A_170, B_171]: (m1_subset_1('#skF_1'(A_170, B_171), A_170) | r1_tarski(A_170, B_171))), inference(resolution, [status(thm)], [c_201, c_20])).
% 48.15/37.05  tff(c_22, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 48.15/37.05  tff(c_256, plain, (![B_185, B_186]: (r1_tarski('#skF_1'(k1_zfmisc_1(B_185), B_186), B_185) | r1_tarski(k1_zfmisc_1(B_185), B_186))), inference(resolution, [status(thm)], [c_219, c_22])).
% 48.15/37.05  tff(c_18, plain, (![A_12]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_50])).
% 48.15/37.05  tff(c_272, plain, (![B_187]: ('#skF_1'(k1_zfmisc_1(k1_xboole_0), B_187)=k1_xboole_0 | r1_tarski(k1_zfmisc_1(k1_xboole_0), B_187))), inference(resolution, [status(thm)], [c_256, c_18])).
% 48.15/37.05  tff(c_292, plain, (k1_zfmisc_1(k1_xboole_0)=k1_xboole_0 | '#skF_1'(k1_zfmisc_1(k1_xboole_0), k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_272, c_18])).
% 48.15/37.05  tff(c_294, plain, ('#skF_1'(k1_zfmisc_1(k1_xboole_0), k1_xboole_0)=k1_xboole_0), inference(splitLeft, [status(thm)], [c_292])).
% 48.15/37.05  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 48.15/37.05  tff(c_307, plain, (r2_hidden(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)) | r1_tarski(k1_zfmisc_1(k1_xboole_0), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_294, c_6])).
% 48.15/37.05  tff(c_317, plain, (r1_tarski(k1_zfmisc_1(k1_xboole_0), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_307])).
% 48.15/37.05  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 48.15/37.05  tff(c_323, plain, (k1_zfmisc_1(k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_317, c_8])).
% 48.15/37.05  tff(c_331, plain, (k1_zfmisc_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_323])).
% 48.15/37.05  tff(c_24, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 48.15/37.05  tff(c_401, plain, (![A_194]: (m1_subset_1(A_194, k1_xboole_0) | ~r1_tarski(A_194, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_331, c_24])).
% 48.15/37.05  tff(c_420, plain, (m1_subset_1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_401])).
% 48.15/37.05  tff(c_224, plain, (![B_16, B_171]: (r1_tarski('#skF_1'(k1_zfmisc_1(B_16), B_171), B_16) | r1_tarski(k1_zfmisc_1(B_16), B_171))), inference(resolution, [status(thm)], [c_219, c_22])).
% 48.15/37.05  tff(c_377, plain, (![A_191]: (r1_tarski(A_191, k1_xboole_0) | ~m1_subset_1(A_191, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_331, c_22])).
% 48.15/37.05  tff(c_14, plain, (![A_8, C_10, B_9]: (r1_tarski(A_8, C_10) | ~r1_tarski(B_9, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 48.15/37.05  tff(c_486, plain, (![A_204, A_205]: (r1_tarski(A_204, k1_xboole_0) | ~r1_tarski(A_204, A_205) | ~m1_subset_1(A_205, k1_xboole_0))), inference(resolution, [status(thm)], [c_377, c_14])).
% 48.15/37.05  tff(c_903, plain, (![B_238, B_239]: (r1_tarski('#skF_1'(k1_zfmisc_1(B_238), B_239), k1_xboole_0) | ~m1_subset_1(B_238, k1_xboole_0) | r1_tarski(k1_zfmisc_1(B_238), B_239))), inference(resolution, [status(thm)], [c_224, c_486])).
% 48.15/37.05  tff(c_237, plain, (![A_178, C_179, B_180]: (r1_tarski(A_178, C_179) | ~r1_tarski(B_180, C_179) | ~r1_tarski(A_178, B_180))), inference(cnfTransformation, [status(thm)], [f_44])).
% 48.15/37.05  tff(c_243, plain, (![A_178, A_11]: (r1_tarski(A_178, A_11) | ~r1_tarski(A_178, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_237])).
% 48.15/37.05  tff(c_429, plain, (![A_196, A_197]: (r1_tarski(A_196, A_197) | ~m1_subset_1(A_196, k1_xboole_0))), inference(resolution, [status(thm)], [c_377, c_243])).
% 48.15/37.05  tff(c_453, plain, (![A_197, A_196]: (A_197=A_196 | ~r1_tarski(A_197, A_196) | ~m1_subset_1(A_196, k1_xboole_0))), inference(resolution, [status(thm)], [c_429, c_8])).
% 48.15/37.05  tff(c_908, plain, (![B_238, B_239]: ('#skF_1'(k1_zfmisc_1(B_238), B_239)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_xboole_0) | ~m1_subset_1(B_238, k1_xboole_0) | r1_tarski(k1_zfmisc_1(B_238), B_239))), inference(resolution, [status(thm)], [c_903, c_453])).
% 48.15/37.05  tff(c_942, plain, (![B_240, B_241]: ('#skF_1'(k1_zfmisc_1(B_240), B_241)=k1_xboole_0 | ~m1_subset_1(B_240, k1_xboole_0) | r1_tarski(k1_zfmisc_1(B_240), B_241))), inference(demodulation, [status(thm), theory('equality')], [c_420, c_908])).
% 48.15/37.05  tff(c_347, plain, (![A_15]: (m1_subset_1(A_15, k1_xboole_0) | ~r1_tarski(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_331, c_24])).
% 48.15/37.05  tff(c_982, plain, (![B_240]: (m1_subset_1(k1_zfmisc_1(B_240), k1_xboole_0) | '#skF_1'(k1_zfmisc_1(B_240), k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(B_240, k1_xboole_0))), inference(resolution, [status(thm)], [c_942, c_347])).
% 48.15/37.05  tff(c_387, plain, (![A_191, A_11]: (r1_tarski(A_191, A_11) | ~m1_subset_1(A_191, k1_xboole_0))), inference(resolution, [status(thm)], [c_377, c_243])).
% 48.15/37.05  tff(c_1509, plain, (![A_277, B_278, C_279]: (r2_hidden('#skF_13'(A_277, B_278, C_279), C_279) | ~r2_hidden(A_277, a_2_5_lattice3(B_278, C_279)) | ~l3_lattices(B_278) | ~v4_lattice3(B_278) | ~v10_lattices(B_278) | v2_struct_0(B_278))), inference(cnfTransformation, [status(thm)], [f_294])).
% 48.15/37.05  tff(c_26, plain, (![B_18, A_17]: (~r1_tarski(B_18, A_17) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 48.15/37.05  tff(c_11035, plain, (![C_645, A_646, B_647]: (~r1_tarski(C_645, '#skF_13'(A_646, B_647, C_645)) | ~r2_hidden(A_646, a_2_5_lattice3(B_647, C_645)) | ~l3_lattices(B_647) | ~v4_lattice3(B_647) | ~v10_lattices(B_647) | v2_struct_0(B_647))), inference(resolution, [status(thm)], [c_1509, c_26])).
% 48.15/37.05  tff(c_14795, plain, (![A_710, B_711, A_712]: (~r2_hidden(A_710, a_2_5_lattice3(B_711, A_712)) | ~l3_lattices(B_711) | ~v4_lattice3(B_711) | ~v10_lattices(B_711) | v2_struct_0(B_711) | ~m1_subset_1(A_712, k1_xboole_0))), inference(resolution, [status(thm)], [c_387, c_11035])).
% 48.15/37.05  tff(c_14827, plain, (![B_713, A_714, B_715]: (~l3_lattices(B_713) | ~v4_lattice3(B_713) | ~v10_lattices(B_713) | v2_struct_0(B_713) | ~m1_subset_1(A_714, k1_xboole_0) | r1_tarski(a_2_5_lattice3(B_713, A_714), B_715))), inference(resolution, [status(thm)], [c_6, c_14795])).
% 48.15/37.05  tff(c_15005, plain, (![B_716, A_717]: (a_2_5_lattice3(B_716, A_717)=k1_xboole_0 | ~l3_lattices(B_716) | ~v4_lattice3(B_716) | ~v10_lattices(B_716) | v2_struct_0(B_716) | ~m1_subset_1(A_717, k1_xboole_0))), inference(resolution, [status(thm)], [c_14827, c_18])).
% 48.15/37.05  tff(c_15007, plain, (![A_717]: (a_2_5_lattice3('#skF_14', A_717)=k1_xboole_0 | ~l3_lattices('#skF_14') | ~v10_lattices('#skF_14') | v2_struct_0('#skF_14') | ~m1_subset_1(A_717, k1_xboole_0))), inference(resolution, [status(thm)], [c_144, c_15005])).
% 48.15/37.05  tff(c_15010, plain, (![A_717]: (a_2_5_lattice3('#skF_14', A_717)=k1_xboole_0 | v2_struct_0('#skF_14') | ~m1_subset_1(A_717, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_142, c_15007])).
% 48.15/37.05  tff(c_15012, plain, (![A_718]: (a_2_5_lattice3('#skF_14', A_718)=k1_xboole_0 | ~m1_subset_1(A_718, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_148, c_15010])).
% 48.15/37.05  tff(c_15098, plain, (![B_721]: (a_2_5_lattice3('#skF_14', k1_zfmisc_1(B_721))=k1_xboole_0 | '#skF_1'(k1_zfmisc_1(B_721), k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(B_721, k1_xboole_0))), inference(resolution, [status(thm)], [c_982, c_15012])).
% 48.15/37.05  tff(c_136, plain, (![A_142, B_144]: (k15_lattice3(A_142, a_2_5_lattice3(A_142, B_144))=k15_lattice3(A_142, B_144) | ~l3_lattices(A_142) | ~v4_lattice3(A_142) | ~v10_lattices(A_142) | v2_struct_0(A_142))), inference(cnfTransformation, [status(thm)], [f_340])).
% 48.15/37.05  tff(c_15115, plain, (![B_721]: (k15_lattice3('#skF_14', k1_zfmisc_1(B_721))=k15_lattice3('#skF_14', k1_xboole_0) | ~l3_lattices('#skF_14') | ~v4_lattice3('#skF_14') | ~v10_lattices('#skF_14') | v2_struct_0('#skF_14') | '#skF_1'(k1_zfmisc_1(B_721), k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(B_721, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_15098, c_136])).
% 48.15/37.05  tff(c_15139, plain, (![B_721]: (k15_lattice3('#skF_14', k1_zfmisc_1(B_721))=k15_lattice3('#skF_14', k1_xboole_0) | v2_struct_0('#skF_14') | '#skF_1'(k1_zfmisc_1(B_721), k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(B_721, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_144, c_142, c_15115])).
% 48.15/37.05  tff(c_15201, plain, (![B_723]: (k15_lattice3('#skF_14', k1_zfmisc_1(B_723))=k15_lattice3('#skF_14', k1_xboole_0) | '#skF_1'(k1_zfmisc_1(B_723), k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(B_723, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_148, c_15139])).
% 48.15/37.05  tff(c_15236, plain, (![B_723]: (m1_subset_1(k15_lattice3('#skF_14', k1_xboole_0), u1_struct_0('#skF_14')) | ~l3_lattices('#skF_14') | v2_struct_0('#skF_14') | '#skF_1'(k1_zfmisc_1(B_723), k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(B_723, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_15201, c_106])).
% 48.15/37.05  tff(c_15278, plain, (![B_723]: (m1_subset_1(k15_lattice3('#skF_14', k1_xboole_0), u1_struct_0('#skF_14')) | v2_struct_0('#skF_14') | '#skF_1'(k1_zfmisc_1(B_723), k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(B_723, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_15236])).
% 48.15/37.05  tff(c_15279, plain, (![B_723]: (m1_subset_1(k15_lattice3('#skF_14', k1_xboole_0), u1_struct_0('#skF_14')) | '#skF_1'(k1_zfmisc_1(B_723), k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(B_723, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_148, c_15278])).
% 48.15/37.05  tff(c_15528, plain, (m1_subset_1(k15_lattice3('#skF_14', k1_xboole_0), u1_struct_0('#skF_14'))), inference(splitLeft, [status(thm)], [c_15279])).
% 48.15/37.05  tff(c_140, plain, (k15_lattice3('#skF_14', k1_xboole_0)!=k5_lattices('#skF_14') | ~l3_lattices('#skF_14') | ~v13_lattices('#skF_14') | ~v10_lattices('#skF_14') | v2_struct_0('#skF_14')), inference(cnfTransformation, [status(thm)], [f_361])).
% 48.15/37.05  tff(c_150, plain, (k15_lattice3('#skF_14', k1_xboole_0)!=k5_lattices('#skF_14') | ~v13_lattices('#skF_14') | v2_struct_0('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_146, c_142, c_140])).
% 48.15/37.05  tff(c_151, plain, (k15_lattice3('#skF_14', k1_xboole_0)!=k5_lattices('#skF_14') | ~v13_lattices('#skF_14')), inference(negUnitSimplification, [status(thm)], [c_148, c_150])).
% 48.15/37.05  tff(c_180, plain, (~v13_lattices('#skF_14')), inference(splitLeft, [status(thm)], [c_151])).
% 48.15/37.05  tff(c_72, plain, (![A_57, B_66]: (m1_subset_1('#skF_6'(A_57, B_66), u1_struct_0(A_57)) | v13_lattices(A_57) | ~m1_subset_1(B_66, u1_struct_0(A_57)) | ~l1_lattices(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_183])).
% 48.15/37.05  tff(c_1316, plain, (![A_265, B_266]: (k15_lattice3(A_265, a_2_3_lattice3(A_265, B_266))=B_266 | ~m1_subset_1(B_266, u1_struct_0(A_265)) | ~l3_lattices(A_265) | ~v4_lattice3(A_265) | ~v10_lattices(A_265) | v2_struct_0(A_265))), inference(cnfTransformation, [status(thm)], [f_310])).
% 48.15/37.05  tff(c_1340, plain, (![A_57, B_66]: (k15_lattice3(A_57, a_2_3_lattice3(A_57, '#skF_6'(A_57, B_66)))='#skF_6'(A_57, B_66) | ~l3_lattices(A_57) | ~v4_lattice3(A_57) | ~v10_lattices(A_57) | v13_lattices(A_57) | ~m1_subset_1(B_66, u1_struct_0(A_57)) | ~l1_lattices(A_57) | v2_struct_0(A_57))), inference(resolution, [status(thm)], [c_72, c_1316])).
% 48.15/37.05  tff(c_1231, plain, (![A_257, B_258, C_259]: (r2_hidden('#skF_7'(A_257, B_258, C_259), C_259) | r4_lattice3(A_257, B_258, C_259) | ~m1_subset_1(B_258, u1_struct_0(A_257)) | ~l3_lattices(A_257) | v2_struct_0(A_257))), inference(cnfTransformation, [status(thm)], [f_201])).
% 48.15/37.05  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 48.15/37.05  tff(c_18247, plain, (![A_764, B_765, C_766, B_767]: (r2_hidden('#skF_7'(A_764, B_765, C_766), B_767) | ~r1_tarski(C_766, B_767) | r4_lattice3(A_764, B_765, C_766) | ~m1_subset_1(B_765, u1_struct_0(A_764)) | ~l3_lattices(A_764) | v2_struct_0(A_764))), inference(resolution, [status(thm)], [c_1231, c_2])).
% 48.15/37.05  tff(c_11088, plain, (![A_648, B_649]: (~r2_hidden(A_648, a_2_5_lattice3(B_649, k1_xboole_0)) | ~l3_lattices(B_649) | ~v4_lattice3(B_649) | ~v10_lattices(B_649) | v2_struct_0(B_649))), inference(resolution, [status(thm)], [c_16, c_11035])).
% 48.15/37.05  tff(c_11114, plain, (![B_650, B_651]: (~l3_lattices(B_650) | ~v4_lattice3(B_650) | ~v10_lattices(B_650) | v2_struct_0(B_650) | r1_tarski(a_2_5_lattice3(B_650, k1_xboole_0), B_651))), inference(resolution, [status(thm)], [c_6, c_11088])).
% 48.15/37.05  tff(c_11275, plain, (![B_652]: (a_2_5_lattice3(B_652, k1_xboole_0)=k1_xboole_0 | ~l3_lattices(B_652) | ~v4_lattice3(B_652) | ~v10_lattices(B_652) | v2_struct_0(B_652))), inference(resolution, [status(thm)], [c_11114, c_18])).
% 48.15/37.05  tff(c_11278, plain, (a_2_5_lattice3('#skF_14', k1_xboole_0)=k1_xboole_0 | ~l3_lattices('#skF_14') | ~v10_lattices('#skF_14') | v2_struct_0('#skF_14')), inference(resolution, [status(thm)], [c_144, c_11275])).
% 48.15/37.05  tff(c_11281, plain, (a_2_5_lattice3('#skF_14', k1_xboole_0)=k1_xboole_0 | v2_struct_0('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_146, c_142, c_11278])).
% 48.15/37.05  tff(c_11282, plain, (a_2_5_lattice3('#skF_14', k1_xboole_0)=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_148, c_11281])).
% 48.15/37.05  tff(c_11087, plain, (![A_646, B_647]: (~r2_hidden(A_646, a_2_5_lattice3(B_647, k1_xboole_0)) | ~l3_lattices(B_647) | ~v4_lattice3(B_647) | ~v10_lattices(B_647) | v2_struct_0(B_647))), inference(resolution, [status(thm)], [c_16, c_11035])).
% 48.15/37.05  tff(c_11289, plain, (![A_646]: (~r2_hidden(A_646, k1_xboole_0) | ~l3_lattices('#skF_14') | ~v4_lattice3('#skF_14') | ~v10_lattices('#skF_14') | v2_struct_0('#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_11282, c_11087])).
% 48.15/37.05  tff(c_11302, plain, (![A_646]: (~r2_hidden(A_646, k1_xboole_0) | v2_struct_0('#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_144, c_142, c_11289])).
% 48.15/37.05  tff(c_11303, plain, (![A_646]: (~r2_hidden(A_646, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_148, c_11302])).
% 48.15/37.05  tff(c_18304, plain, (![C_768, A_769, B_770]: (~r1_tarski(C_768, k1_xboole_0) | r4_lattice3(A_769, B_770, C_768) | ~m1_subset_1(B_770, u1_struct_0(A_769)) | ~l3_lattices(A_769) | v2_struct_0(A_769))), inference(resolution, [status(thm)], [c_18247, c_11303])).
% 48.15/37.05  tff(c_18366, plain, (![C_768, A_113, B_114]: (~r1_tarski(C_768, k1_xboole_0) | r4_lattice3(A_113, k15_lattice3(A_113, B_114), C_768) | ~l3_lattices(A_113) | v2_struct_0(A_113))), inference(resolution, [status(thm)], [c_106, c_18304])).
% 48.15/37.05  tff(c_28, plain, (![A_19]: (v9_lattices(A_19) | ~v10_lattices(A_19) | v2_struct_0(A_19) | ~l3_lattices(A_19))), inference(cnfTransformation, [status(thm)], [f_85])).
% 48.15/37.05  tff(c_9020, plain, (![C_561, A_562, B_563]: (~r1_tarski(C_561, '#skF_7'(A_562, B_563, C_561)) | r4_lattice3(A_562, B_563, C_561) | ~m1_subset_1(B_563, u1_struct_0(A_562)) | ~l3_lattices(A_562) | v2_struct_0(A_562))), inference(resolution, [status(thm)], [c_1231, c_26])).
% 48.15/37.05  tff(c_9076, plain, (![A_564, B_565]: (r4_lattice3(A_564, B_565, k1_xboole_0) | ~m1_subset_1(B_565, u1_struct_0(A_564)) | ~l3_lattices(A_564) | v2_struct_0(A_564))), inference(resolution, [status(thm)], [c_16, c_9020])).
% 48.15/37.05  tff(c_9140, plain, (![A_113, B_114]: (r4_lattice3(A_113, k15_lattice3(A_113, B_114), k1_xboole_0) | ~l3_lattices(A_113) | v2_struct_0(A_113))), inference(resolution, [status(thm)], [c_106, c_9076])).
% 48.15/37.05  tff(c_15216, plain, (![B_723]: (r4_lattice3('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), k1_xboole_0) | ~l3_lattices('#skF_14') | v2_struct_0('#skF_14') | '#skF_1'(k1_zfmisc_1(B_723), k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(B_723, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_15201, c_9140])).
% 48.15/37.05  tff(c_15257, plain, (![B_723]: (r4_lattice3('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), k1_xboole_0) | v2_struct_0('#skF_14') | '#skF_1'(k1_zfmisc_1(B_723), k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(B_723, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_15216])).
% 48.15/37.05  tff(c_15258, plain, (![B_723]: (r4_lattice3('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), k1_xboole_0) | '#skF_1'(k1_zfmisc_1(B_723), k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(B_723, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_148, c_15257])).
% 48.15/37.05  tff(c_15467, plain, (r4_lattice3('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_15258])).
% 48.15/37.05  tff(c_155, plain, (![A_147]: (l2_lattices(A_147) | ~l3_lattices(A_147))), inference(cnfTransformation, [status(thm)], [f_147])).
% 48.15/37.05  tff(c_159, plain, (l2_lattices('#skF_14')), inference(resolution, [status(thm)], [c_142, c_155])).
% 48.15/37.05  tff(c_94, plain, (![A_90, B_97, D_101]: (r1_lattices(A_90, k15_lattice3(A_90, B_97), D_101) | ~r4_lattice3(A_90, D_101, B_97) | ~m1_subset_1(D_101, u1_struct_0(A_90)) | ~m1_subset_1(k15_lattice3(A_90, B_97), u1_struct_0(A_90)) | ~v4_lattice3(A_90) | ~v10_lattices(A_90) | ~l3_lattices(A_90) | v2_struct_0(A_90))), inference(cnfTransformation, [status(thm)], [f_229])).
% 48.15/37.05  tff(c_15537, plain, (![D_101]: (r1_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), D_101) | ~r4_lattice3('#skF_14', D_101, k1_xboole_0) | ~m1_subset_1(D_101, u1_struct_0('#skF_14')) | ~v4_lattice3('#skF_14') | ~v10_lattices('#skF_14') | ~l3_lattices('#skF_14') | v2_struct_0('#skF_14'))), inference(resolution, [status(thm)], [c_15528, c_94])).
% 48.15/37.05  tff(c_15570, plain, (![D_101]: (r1_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), D_101) | ~r4_lattice3('#skF_14', D_101, k1_xboole_0) | ~m1_subset_1(D_101, u1_struct_0('#skF_14')) | v2_struct_0('#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_146, c_144, c_15537])).
% 48.15/37.05  tff(c_15723, plain, (![D_731]: (r1_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), D_731) | ~r4_lattice3('#skF_14', D_731, k1_xboole_0) | ~m1_subset_1(D_731, u1_struct_0('#skF_14')))), inference(negUnitSimplification, [status(thm)], [c_148, c_15570])).
% 48.15/37.05  tff(c_52, plain, (![A_30, B_34, C_36]: (k1_lattices(A_30, B_34, C_36)=C_36 | ~r1_lattices(A_30, B_34, C_36) | ~m1_subset_1(C_36, u1_struct_0(A_30)) | ~m1_subset_1(B_34, u1_struct_0(A_30)) | ~l2_lattices(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_119])).
% 48.15/37.05  tff(c_15731, plain, (![D_731]: (k1_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), D_731)=D_731 | ~m1_subset_1(k15_lattice3('#skF_14', k1_xboole_0), u1_struct_0('#skF_14')) | ~l2_lattices('#skF_14') | v2_struct_0('#skF_14') | ~r4_lattice3('#skF_14', D_731, k1_xboole_0) | ~m1_subset_1(D_731, u1_struct_0('#skF_14')))), inference(resolution, [status(thm)], [c_15723, c_52])).
% 48.15/37.05  tff(c_15742, plain, (![D_731]: (k1_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), D_731)=D_731 | v2_struct_0('#skF_14') | ~r4_lattice3('#skF_14', D_731, k1_xboole_0) | ~m1_subset_1(D_731, u1_struct_0('#skF_14')))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_15528, c_15731])).
% 48.15/37.05  tff(c_15872, plain, (![D_736]: (k1_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), D_736)=D_736 | ~r4_lattice3('#skF_14', D_736, k1_xboole_0) | ~m1_subset_1(D_736, u1_struct_0('#skF_14')))), inference(negUnitSimplification, [status(thm)], [c_148, c_15742])).
% 48.15/37.05  tff(c_15875, plain, (k1_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), k15_lattice3('#skF_14', k1_xboole_0))=k15_lattice3('#skF_14', k1_xboole_0) | ~r4_lattice3('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_15528, c_15872])).
% 48.15/37.05  tff(c_15950, plain, (k1_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), k15_lattice3('#skF_14', k1_xboole_0))=k15_lattice3('#skF_14', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_15467, c_15875])).
% 48.15/37.05  tff(c_4509, plain, (![A_406, B_407, C_408]: (k2_lattices(A_406, B_407, k1_lattices(A_406, B_407, C_408))=B_407 | ~m1_subset_1(C_408, u1_struct_0(A_406)) | ~m1_subset_1(B_407, u1_struct_0(A_406)) | ~v9_lattices(A_406) | ~l3_lattices(A_406) | v2_struct_0(A_406))), inference(cnfTransformation, [status(thm)], [f_134])).
% 48.15/37.05  tff(c_17259, plain, (![A_751, B_752, B_753]: (k2_lattices(A_751, B_752, k1_lattices(A_751, B_752, k15_lattice3(A_751, B_753)))=B_752 | ~m1_subset_1(B_752, u1_struct_0(A_751)) | ~v9_lattices(A_751) | ~l3_lattices(A_751) | v2_struct_0(A_751))), inference(resolution, [status(thm)], [c_106, c_4509])).
% 48.15/37.05  tff(c_17277, plain, (k2_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), k15_lattice3('#skF_14', k1_xboole_0))=k15_lattice3('#skF_14', k1_xboole_0) | ~m1_subset_1(k15_lattice3('#skF_14', k1_xboole_0), u1_struct_0('#skF_14')) | ~v9_lattices('#skF_14') | ~l3_lattices('#skF_14') | v2_struct_0('#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_15950, c_17259])).
% 48.15/37.05  tff(c_17305, plain, (k2_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), k15_lattice3('#skF_14', k1_xboole_0))=k15_lattice3('#skF_14', k1_xboole_0) | ~v9_lattices('#skF_14') | v2_struct_0('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_15528, c_17277])).
% 48.15/37.05  tff(c_17306, plain, (k2_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), k15_lattice3('#skF_14', k1_xboole_0))=k15_lattice3('#skF_14', k1_xboole_0) | ~v9_lattices('#skF_14')), inference(negUnitSimplification, [status(thm)], [c_148, c_17305])).
% 48.15/37.05  tff(c_17316, plain, (~v9_lattices('#skF_14')), inference(splitLeft, [status(thm)], [c_17306])).
% 48.15/37.05  tff(c_17319, plain, (~v10_lattices('#skF_14') | v2_struct_0('#skF_14') | ~l3_lattices('#skF_14')), inference(resolution, [status(thm)], [c_28, c_17316])).
% 48.15/37.05  tff(c_17322, plain, (v2_struct_0('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_146, c_17319])).
% 48.15/37.05  tff(c_17324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_17322])).
% 48.15/37.05  tff(c_17326, plain, (v9_lattices('#skF_14')), inference(splitRight, [status(thm)], [c_17306])).
% 48.15/37.05  tff(c_15939, plain, (![B_114]: (k1_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), k15_lattice3('#skF_14', B_114))=k15_lattice3('#skF_14', B_114) | ~r4_lattice3('#skF_14', k15_lattice3('#skF_14', B_114), k1_xboole_0) | ~l3_lattices('#skF_14') | v2_struct_0('#skF_14'))), inference(resolution, [status(thm)], [c_106, c_15872])).
% 48.15/37.05  tff(c_16004, plain, (![B_114]: (k1_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), k15_lattice3('#skF_14', B_114))=k15_lattice3('#skF_14', B_114) | ~r4_lattice3('#skF_14', k15_lattice3('#skF_14', B_114), k1_xboole_0) | v2_struct_0('#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_15939])).
% 48.15/37.05  tff(c_19228, plain, (![B_804]: (k1_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), k15_lattice3('#skF_14', B_804))=k15_lattice3('#skF_14', B_804) | ~r4_lattice3('#skF_14', k15_lattice3('#skF_14', B_804), k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_148, c_16004])).
% 48.15/37.05  tff(c_4551, plain, (![A_113, B_407, B_114]: (k2_lattices(A_113, B_407, k1_lattices(A_113, B_407, k15_lattice3(A_113, B_114)))=B_407 | ~m1_subset_1(B_407, u1_struct_0(A_113)) | ~v9_lattices(A_113) | ~l3_lattices(A_113) | v2_struct_0(A_113))), inference(resolution, [status(thm)], [c_106, c_4509])).
% 48.15/37.05  tff(c_19238, plain, (![B_804]: (k2_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), k15_lattice3('#skF_14', B_804))=k15_lattice3('#skF_14', k1_xboole_0) | ~m1_subset_1(k15_lattice3('#skF_14', k1_xboole_0), u1_struct_0('#skF_14')) | ~v9_lattices('#skF_14') | ~l3_lattices('#skF_14') | v2_struct_0('#skF_14') | ~r4_lattice3('#skF_14', k15_lattice3('#skF_14', B_804), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_19228, c_4551])).
% 48.15/37.05  tff(c_19283, plain, (![B_804]: (k2_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), k15_lattice3('#skF_14', B_804))=k15_lattice3('#skF_14', k1_xboole_0) | v2_struct_0('#skF_14') | ~r4_lattice3('#skF_14', k15_lattice3('#skF_14', B_804), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_17326, c_15528, c_19238])).
% 48.15/37.05  tff(c_21314, plain, (![B_856]: (k2_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), k15_lattice3('#skF_14', B_856))=k15_lattice3('#skF_14', k1_xboole_0) | ~r4_lattice3('#skF_14', k15_lattice3('#skF_14', B_856), k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_148, c_19283])).
% 48.15/37.05  tff(c_21357, plain, (![B_144]: (k2_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), k15_lattice3('#skF_14', B_144))=k15_lattice3('#skF_14', k1_xboole_0) | ~r4_lattice3('#skF_14', k15_lattice3('#skF_14', a_2_5_lattice3('#skF_14', B_144)), k1_xboole_0) | ~l3_lattices('#skF_14') | ~v4_lattice3('#skF_14') | ~v10_lattices('#skF_14') | v2_struct_0('#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_136, c_21314])).
% 48.15/37.05  tff(c_21382, plain, (![B_144]: (k2_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), k15_lattice3('#skF_14', B_144))=k15_lattice3('#skF_14', k1_xboole_0) | ~r4_lattice3('#skF_14', k15_lattice3('#skF_14', a_2_5_lattice3('#skF_14', B_144)), k1_xboole_0) | v2_struct_0('#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_144, c_142, c_21357])).
% 48.15/37.05  tff(c_136946, plain, (![B_1581]: (k2_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), k15_lattice3('#skF_14', B_1581))=k15_lattice3('#skF_14', k1_xboole_0) | ~r4_lattice3('#skF_14', k15_lattice3('#skF_14', a_2_5_lattice3('#skF_14', B_1581)), k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_148, c_21382])).
% 48.15/37.05  tff(c_136972, plain, (![B_1581]: (k2_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), k15_lattice3('#skF_14', B_1581))=k15_lattice3('#skF_14', k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~l3_lattices('#skF_14') | v2_struct_0('#skF_14'))), inference(resolution, [status(thm)], [c_18366, c_136946])).
% 48.15/37.05  tff(c_137032, plain, (![B_1581]: (k2_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), k15_lattice3('#skF_14', B_1581))=k15_lattice3('#skF_14', k1_xboole_0) | v2_struct_0('#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_12, c_136972])).
% 48.15/37.05  tff(c_137079, plain, (![B_1582]: (k2_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), k15_lattice3('#skF_14', B_1582))=k15_lattice3('#skF_14', k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_148, c_137032])).
% 48.15/37.05  tff(c_137143, plain, (![B_66]: (k2_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), '#skF_6'('#skF_14', B_66))=k15_lattice3('#skF_14', k1_xboole_0) | ~l3_lattices('#skF_14') | ~v4_lattice3('#skF_14') | ~v10_lattices('#skF_14') | v13_lattices('#skF_14') | ~m1_subset_1(B_66, u1_struct_0('#skF_14')) | ~l1_lattices('#skF_14') | v2_struct_0('#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_1340, c_137079])).
% 48.15/37.05  tff(c_137240, plain, (![B_66]: (k2_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), '#skF_6'('#skF_14', B_66))=k15_lattice3('#skF_14', k1_xboole_0) | v13_lattices('#skF_14') | ~m1_subset_1(B_66, u1_struct_0('#skF_14')) | v2_struct_0('#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_146, c_144, c_142, c_137143])).
% 48.15/37.05  tff(c_137241, plain, (![B_66]: (k2_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), '#skF_6'('#skF_14', B_66))=k15_lattice3('#skF_14', k1_xboole_0) | ~m1_subset_1(B_66, u1_struct_0('#skF_14')))), inference(negUnitSimplification, [status(thm)], [c_148, c_180, c_137240])).
% 48.15/37.05  tff(c_137033, plain, (![B_1581]: (k2_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), k15_lattice3('#skF_14', B_1581))=k15_lattice3('#skF_14', k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_148, c_137032])).
% 48.15/37.05  tff(c_34, plain, (![A_19]: (v6_lattices(A_19) | ~v10_lattices(A_19) | v2_struct_0(A_19) | ~l3_lattices(A_19))), inference(cnfTransformation, [status(thm)], [f_85])).
% 48.15/37.05  tff(c_62, plain, (![A_48]: (m1_subset_1(k5_lattices(A_48), u1_struct_0(A_48)) | ~l1_lattices(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_141])).
% 48.15/37.05  tff(c_4191, plain, (![A_397, C_398, B_399]: (k2_lattices(A_397, C_398, B_399)=k2_lattices(A_397, B_399, C_398) | ~m1_subset_1(C_398, u1_struct_0(A_397)) | ~m1_subset_1(B_399, u1_struct_0(A_397)) | ~v6_lattices(A_397) | ~l1_lattices(A_397) | v2_struct_0(A_397))), inference(cnfTransformation, [status(thm)], [f_244])).
% 48.15/37.05  tff(c_4234, plain, (![A_48, B_399]: (k2_lattices(A_48, k5_lattices(A_48), B_399)=k2_lattices(A_48, B_399, k5_lattices(A_48)) | ~m1_subset_1(B_399, u1_struct_0(A_48)) | ~v6_lattices(A_48) | ~l1_lattices(A_48) | v2_struct_0(A_48))), inference(resolution, [status(thm)], [c_62, c_4191])).
% 48.15/37.05  tff(c_15530, plain, (k2_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), k5_lattices('#skF_14'))=k2_lattices('#skF_14', k5_lattices('#skF_14'), k15_lattice3('#skF_14', k1_xboole_0)) | ~v6_lattices('#skF_14') | ~l1_lattices('#skF_14') | v2_struct_0('#skF_14')), inference(resolution, [status(thm)], [c_15528, c_4234])).
% 48.15/37.05  tff(c_15558, plain, (k2_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), k5_lattices('#skF_14'))=k2_lattices('#skF_14', k5_lattices('#skF_14'), k15_lattice3('#skF_14', k1_xboole_0)) | ~v6_lattices('#skF_14') | v2_struct_0('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_15530])).
% 48.15/37.05  tff(c_15559, plain, (k2_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), k5_lattices('#skF_14'))=k2_lattices('#skF_14', k5_lattices('#skF_14'), k15_lattice3('#skF_14', k1_xboole_0)) | ~v6_lattices('#skF_14')), inference(negUnitSimplification, [status(thm)], [c_148, c_15558])).
% 48.15/37.05  tff(c_17431, plain, (~v6_lattices('#skF_14')), inference(splitLeft, [status(thm)], [c_15559])).
% 48.15/37.05  tff(c_17434, plain, (~v10_lattices('#skF_14') | v2_struct_0('#skF_14') | ~l3_lattices('#skF_14')), inference(resolution, [status(thm)], [c_34, c_17431])).
% 48.15/37.05  tff(c_17437, plain, (v2_struct_0('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_146, c_17434])).
% 48.15/37.05  tff(c_17439, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_17437])).
% 48.15/37.05  tff(c_17441, plain, (v6_lattices('#skF_14')), inference(splitRight, [status(thm)], [c_15559])).
% 48.15/37.05  tff(c_30655, plain, (![A_1015, B_1016, B_1017]: (k2_lattices(A_1015, k15_lattice3(A_1015, B_1016), B_1017)=k2_lattices(A_1015, B_1017, k15_lattice3(A_1015, B_1016)) | ~m1_subset_1(B_1017, u1_struct_0(A_1015)) | ~v6_lattices(A_1015) | ~l1_lattices(A_1015) | ~l3_lattices(A_1015) | v2_struct_0(A_1015))), inference(resolution, [status(thm)], [c_106, c_4191])).
% 48.15/37.05  tff(c_30659, plain, (![B_1016]: (k2_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), k15_lattice3('#skF_14', B_1016))=k2_lattices('#skF_14', k15_lattice3('#skF_14', B_1016), k15_lattice3('#skF_14', k1_xboole_0)) | ~v6_lattices('#skF_14') | ~l1_lattices('#skF_14') | ~l3_lattices('#skF_14') | v2_struct_0('#skF_14'))), inference(resolution, [status(thm)], [c_15528, c_30655])).
% 48.15/37.05  tff(c_30706, plain, (![B_1016]: (k2_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), k15_lattice3('#skF_14', B_1016))=k2_lattices('#skF_14', k15_lattice3('#skF_14', B_1016), k15_lattice3('#skF_14', k1_xboole_0)) | v2_struct_0('#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_164, c_17441, c_30659])).
% 48.15/37.05  tff(c_32096, plain, (![B_1025]: (k2_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), k15_lattice3('#skF_14', B_1025))=k2_lattices('#skF_14', k15_lattice3('#skF_14', B_1025), k15_lattice3('#skF_14', k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_148, c_30706])).
% 48.15/37.05  tff(c_32154, plain, (![B_144]: (k2_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), k15_lattice3('#skF_14', a_2_5_lattice3('#skF_14', B_144)))=k2_lattices('#skF_14', k15_lattice3('#skF_14', B_144), k15_lattice3('#skF_14', k1_xboole_0)) | ~l3_lattices('#skF_14') | ~v4_lattice3('#skF_14') | ~v10_lattices('#skF_14') | v2_struct_0('#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_136, c_32096])).
% 48.15/37.05  tff(c_32177, plain, (![B_144]: (k2_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), k15_lattice3('#skF_14', a_2_5_lattice3('#skF_14', B_144)))=k2_lattices('#skF_14', k15_lattice3('#skF_14', B_144), k15_lattice3('#skF_14', k1_xboole_0)) | v2_struct_0('#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_144, c_142, c_32154])).
% 48.15/37.05  tff(c_32178, plain, (![B_144]: (k2_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), k15_lattice3('#skF_14', a_2_5_lattice3('#skF_14', B_144)))=k2_lattices('#skF_14', k15_lattice3('#skF_14', B_144), k15_lattice3('#skF_14', k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_148, c_32177])).
% 48.15/37.05  tff(c_137285, plain, (![B_1583]: (k2_lattices('#skF_14', k15_lattice3('#skF_14', B_1583), k15_lattice3('#skF_14', k1_xboole_0))=k15_lattice3('#skF_14', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_137033, c_32178])).
% 48.15/37.05  tff(c_137319, plain, (![B_66]: (k2_lattices('#skF_14', '#skF_6'('#skF_14', B_66), k15_lattice3('#skF_14', k1_xboole_0))=k15_lattice3('#skF_14', k1_xboole_0) | ~l3_lattices('#skF_14') | ~v4_lattice3('#skF_14') | ~v10_lattices('#skF_14') | v13_lattices('#skF_14') | ~m1_subset_1(B_66, u1_struct_0('#skF_14')) | ~l1_lattices('#skF_14') | v2_struct_0('#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_1340, c_137285])).
% 48.15/37.05  tff(c_137387, plain, (![B_66]: (k2_lattices('#skF_14', '#skF_6'('#skF_14', B_66), k15_lattice3('#skF_14', k1_xboole_0))=k15_lattice3('#skF_14', k1_xboole_0) | v13_lattices('#skF_14') | ~m1_subset_1(B_66, u1_struct_0('#skF_14')) | v2_struct_0('#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_146, c_144, c_142, c_137319])).
% 48.15/37.05  tff(c_137593, plain, (![B_1588]: (k2_lattices('#skF_14', '#skF_6'('#skF_14', B_1588), k15_lattice3('#skF_14', k1_xboole_0))=k15_lattice3('#skF_14', k1_xboole_0) | ~m1_subset_1(B_1588, u1_struct_0('#skF_14')))), inference(negUnitSimplification, [status(thm)], [c_148, c_180, c_137387])).
% 48.15/37.05  tff(c_70, plain, (![A_57, B_66]: (k2_lattices(A_57, '#skF_6'(A_57, B_66), B_66)!=B_66 | k2_lattices(A_57, B_66, '#skF_6'(A_57, B_66))!=B_66 | v13_lattices(A_57) | ~m1_subset_1(B_66, u1_struct_0(A_57)) | ~l1_lattices(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_183])).
% 48.15/37.05  tff(c_137599, plain, (k2_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), '#skF_6'('#skF_14', k15_lattice3('#skF_14', k1_xboole_0)))!=k15_lattice3('#skF_14', k1_xboole_0) | v13_lattices('#skF_14') | ~l1_lattices('#skF_14') | v2_struct_0('#skF_14') | ~m1_subset_1(k15_lattice3('#skF_14', k1_xboole_0), u1_struct_0('#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_137593, c_70])).
% 48.15/37.05  tff(c_137606, plain, (k2_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), '#skF_6'('#skF_14', k15_lattice3('#skF_14', k1_xboole_0)))!=k15_lattice3('#skF_14', k1_xboole_0) | v13_lattices('#skF_14') | v2_struct_0('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_15528, c_164, c_137599])).
% 48.15/37.05  tff(c_137607, plain, (k2_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), '#skF_6'('#skF_14', k15_lattice3('#skF_14', k1_xboole_0)))!=k15_lattice3('#skF_14', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_148, c_180, c_137606])).
% 48.15/37.05  tff(c_137611, plain, (~m1_subset_1(k15_lattice3('#skF_14', k1_xboole_0), u1_struct_0('#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_137241, c_137607])).
% 48.15/37.05  tff(c_137615, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15528, c_137611])).
% 48.15/37.05  tff(c_137617, plain, (~m1_subset_1(k15_lattice3('#skF_14', k1_xboole_0), u1_struct_0('#skF_14'))), inference(splitRight, [status(thm)], [c_15279])).
% 48.15/37.05  tff(c_137713, plain, (~l3_lattices('#skF_14') | v2_struct_0('#skF_14')), inference(resolution, [status(thm)], [c_106, c_137617])).
% 48.15/37.05  tff(c_137716, plain, (v2_struct_0('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_137713])).
% 48.15/37.05  tff(c_137718, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_137716])).
% 48.15/37.05  tff(c_137720, plain, (v13_lattices('#skF_14')), inference(splitRight, [status(thm)], [c_151])).
% 48.15/37.05  tff(c_74, plain, (![A_57]: (m1_subset_1('#skF_5'(A_57), u1_struct_0(A_57)) | ~v13_lattices(A_57) | ~l1_lattices(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_183])).
% 48.15/37.05  tff(c_142059, plain, (![A_1845, C_1846]: (k2_lattices(A_1845, C_1846, k5_lattices(A_1845))=k5_lattices(A_1845) | ~m1_subset_1(C_1846, u1_struct_0(A_1845)) | ~m1_subset_1(k5_lattices(A_1845), u1_struct_0(A_1845)) | ~v13_lattices(A_1845) | ~l1_lattices(A_1845) | v2_struct_0(A_1845))), inference(cnfTransformation, [status(thm)], [f_104])).
% 48.15/37.05  tff(c_147531, plain, (![A_2052]: (k2_lattices(A_2052, '#skF_5'(A_2052), k5_lattices(A_2052))=k5_lattices(A_2052) | ~m1_subset_1(k5_lattices(A_2052), u1_struct_0(A_2052)) | ~v13_lattices(A_2052) | ~l1_lattices(A_2052) | v2_struct_0(A_2052))), inference(resolution, [status(thm)], [c_74, c_142059])).
% 48.15/37.05  tff(c_147535, plain, (![A_2053]: (k2_lattices(A_2053, '#skF_5'(A_2053), k5_lattices(A_2053))=k5_lattices(A_2053) | ~v13_lattices(A_2053) | ~l1_lattices(A_2053) | v2_struct_0(A_2053))), inference(resolution, [status(thm)], [c_62, c_147531])).
% 48.15/37.05  tff(c_138410, plain, (![A_1672, C_1673]: (k2_lattices(A_1672, '#skF_5'(A_1672), C_1673)='#skF_5'(A_1672) | ~m1_subset_1(C_1673, u1_struct_0(A_1672)) | ~v13_lattices(A_1672) | ~l1_lattices(A_1672) | v2_struct_0(A_1672))), inference(cnfTransformation, [status(thm)], [f_183])).
% 48.15/37.05  tff(c_138441, plain, (![A_48]: (k2_lattices(A_48, '#skF_5'(A_48), k5_lattices(A_48))='#skF_5'(A_48) | ~v13_lattices(A_48) | ~l1_lattices(A_48) | v2_struct_0(A_48))), inference(resolution, [status(thm)], [c_62, c_138410])).
% 48.15/37.05  tff(c_147541, plain, (![A_2053]: (k5_lattices(A_2053)='#skF_5'(A_2053) | ~v13_lattices(A_2053) | ~l1_lattices(A_2053) | v2_struct_0(A_2053) | ~v13_lattices(A_2053) | ~l1_lattices(A_2053) | v2_struct_0(A_2053))), inference(superposition, [status(thm), theory('equality')], [c_147535, c_138441])).
% 48.15/37.05  tff(c_147565, plain, (![A_2059]: (k5_lattices(A_2059)='#skF_5'(A_2059) | ~v13_lattices(A_2059) | ~l1_lattices(A_2059) | v2_struct_0(A_2059))), inference(factorization, [status(thm), theory('equality')], [c_147541])).
% 48.15/37.05  tff(c_147568, plain, (k5_lattices('#skF_14')='#skF_5'('#skF_14') | ~v13_lattices('#skF_14') | ~l1_lattices('#skF_14')), inference(resolution, [status(thm)], [c_147565, c_148])).
% 48.15/37.05  tff(c_147571, plain, (k5_lattices('#skF_14')='#skF_5'('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_137720, c_147568])).
% 48.15/37.05  tff(c_137719, plain, (k15_lattice3('#skF_14', k1_xboole_0)!=k5_lattices('#skF_14')), inference(splitRight, [status(thm)], [c_151])).
% 48.15/37.05  tff(c_147572, plain, (k15_lattice3('#skF_14', k1_xboole_0)!='#skF_5'('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_147571, c_137719])).
% 48.15/37.05  tff(c_137742, plain, (![A_1602, B_1603]: (r2_hidden('#skF_1'(A_1602, B_1603), A_1602) | r1_tarski(A_1602, B_1603))), inference(cnfTransformation, [status(thm)], [f_32])).
% 48.15/37.05  tff(c_137770, plain, (![A_1611, B_1612]: (m1_subset_1('#skF_1'(A_1611, B_1612), A_1611) | r1_tarski(A_1611, B_1612))), inference(resolution, [status(thm)], [c_137742, c_20])).
% 48.15/37.05  tff(c_137775, plain, (![B_16, B_1612]: (r1_tarski('#skF_1'(k1_zfmisc_1(B_16), B_1612), B_16) | r1_tarski(k1_zfmisc_1(B_16), B_1612))), inference(resolution, [status(thm)], [c_137770, c_22])).
% 48.15/37.05  tff(c_137796, plain, (![B_1621, B_1622]: (r1_tarski('#skF_1'(k1_zfmisc_1(B_1621), B_1622), B_1621) | r1_tarski(k1_zfmisc_1(B_1621), B_1622))), inference(resolution, [status(thm)], [c_137770, c_22])).
% 48.15/37.05  tff(c_137812, plain, (![B_1623]: ('#skF_1'(k1_zfmisc_1(k1_xboole_0), B_1623)=k1_xboole_0 | r1_tarski(k1_zfmisc_1(k1_xboole_0), B_1623))), inference(resolution, [status(thm)], [c_137796, c_18])).
% 48.15/37.05  tff(c_137832, plain, (k1_zfmisc_1(k1_xboole_0)=k1_xboole_0 | '#skF_1'(k1_zfmisc_1(k1_xboole_0), k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_137812, c_18])).
% 48.15/37.05  tff(c_137833, plain, ('#skF_1'(k1_zfmisc_1(k1_xboole_0), k1_xboole_0)=k1_xboole_0), inference(splitLeft, [status(thm)], [c_137832])).
% 48.15/37.05  tff(c_137846, plain, (r2_hidden(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)) | r1_tarski(k1_zfmisc_1(k1_xboole_0), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_137833, c_6])).
% 48.15/37.05  tff(c_137856, plain, (r1_tarski(k1_zfmisc_1(k1_xboole_0), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_137846])).
% 48.15/37.05  tff(c_137863, plain, (k1_zfmisc_1(k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_137856, c_8])).
% 48.15/37.05  tff(c_137871, plain, (k1_zfmisc_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_137863])).
% 48.15/37.05  tff(c_137917, plain, (![A_1627]: (r1_tarski(A_1627, k1_xboole_0) | ~m1_subset_1(A_1627, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_137871, c_22])).
% 48.15/37.05  tff(c_137776, plain, (![A_1613, C_1614, B_1615]: (r1_tarski(A_1613, C_1614) | ~r1_tarski(B_1615, C_1614) | ~r1_tarski(A_1613, B_1615))), inference(cnfTransformation, [status(thm)], [f_44])).
% 48.15/37.05  tff(c_137782, plain, (![A_1613, A_11]: (r1_tarski(A_1613, A_11) | ~r1_tarski(A_1613, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_137776])).
% 48.15/37.05  tff(c_137968, plain, (![A_1631, A_1632]: (r1_tarski(A_1631, A_1632) | ~m1_subset_1(A_1631, k1_xboole_0))), inference(resolution, [status(thm)], [c_137917, c_137782])).
% 48.15/37.05  tff(c_137997, plain, (![A_1635, A_1634]: (A_1635=A_1634 | ~r1_tarski(A_1634, A_1635) | ~m1_subset_1(A_1635, k1_xboole_0))), inference(resolution, [status(thm)], [c_137968, c_8])).
% 48.15/37.05  tff(c_138193, plain, (![B_1661, B_1662]: ('#skF_1'(k1_zfmisc_1(B_1661), B_1662)=B_1661 | ~m1_subset_1(B_1661, k1_xboole_0) | r1_tarski(k1_zfmisc_1(B_1661), B_1662))), inference(resolution, [status(thm)], [c_137775, c_137997])).
% 48.15/37.05  tff(c_137887, plain, (![A_15]: (m1_subset_1(A_15, k1_xboole_0) | ~r1_tarski(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_137871, c_24])).
% 48.15/37.05  tff(c_138228, plain, (![B_1661]: (m1_subset_1(k1_zfmisc_1(B_1661), k1_xboole_0) | '#skF_1'(k1_zfmisc_1(B_1661), k1_xboole_0)=B_1661 | ~m1_subset_1(B_1661, k1_xboole_0))), inference(resolution, [status(thm)], [c_138193, c_137887])).
% 48.15/37.05  tff(c_137927, plain, (![A_1627, A_11]: (r1_tarski(A_1627, A_11) | ~m1_subset_1(A_1627, k1_xboole_0))), inference(resolution, [status(thm)], [c_137917, c_137782])).
% 48.15/37.05  tff(c_139361, plain, (![A_1739, B_1740, C_1741]: (r2_hidden('#skF_13'(A_1739, B_1740, C_1741), C_1741) | ~r2_hidden(A_1739, a_2_5_lattice3(B_1740, C_1741)) | ~l3_lattices(B_1740) | ~v4_lattice3(B_1740) | ~v10_lattices(B_1740) | v2_struct_0(B_1740))), inference(cnfTransformation, [status(thm)], [f_294])).
% 48.15/37.05  tff(c_147822, plain, (![C_2061, A_2062, B_2063]: (~r1_tarski(C_2061, '#skF_13'(A_2062, B_2063, C_2061)) | ~r2_hidden(A_2062, a_2_5_lattice3(B_2063, C_2061)) | ~l3_lattices(B_2063) | ~v4_lattice3(B_2063) | ~v10_lattices(B_2063) | v2_struct_0(B_2063))), inference(resolution, [status(thm)], [c_139361, c_26])).
% 48.15/37.05  tff(c_149197, plain, (![A_2107, B_2108, A_2109]: (~r2_hidden(A_2107, a_2_5_lattice3(B_2108, A_2109)) | ~l3_lattices(B_2108) | ~v4_lattice3(B_2108) | ~v10_lattices(B_2108) | v2_struct_0(B_2108) | ~m1_subset_1(A_2109, k1_xboole_0))), inference(resolution, [status(thm)], [c_137927, c_147822])).
% 48.15/37.05  tff(c_149248, plain, (![B_2114, A_2115, B_2116]: (~l3_lattices(B_2114) | ~v4_lattice3(B_2114) | ~v10_lattices(B_2114) | v2_struct_0(B_2114) | ~m1_subset_1(A_2115, k1_xboole_0) | r1_tarski(a_2_5_lattice3(B_2114, A_2115), B_2116))), inference(resolution, [status(thm)], [c_6, c_149197])).
% 48.15/37.05  tff(c_149466, plain, (![B_2119, A_2120]: (a_2_5_lattice3(B_2119, A_2120)=k1_xboole_0 | ~l3_lattices(B_2119) | ~v4_lattice3(B_2119) | ~v10_lattices(B_2119) | v2_struct_0(B_2119) | ~m1_subset_1(A_2120, k1_xboole_0))), inference(resolution, [status(thm)], [c_149248, c_18])).
% 48.15/37.05  tff(c_149468, plain, (![A_2120]: (a_2_5_lattice3('#skF_14', A_2120)=k1_xboole_0 | ~l3_lattices('#skF_14') | ~v10_lattices('#skF_14') | v2_struct_0('#skF_14') | ~m1_subset_1(A_2120, k1_xboole_0))), inference(resolution, [status(thm)], [c_144, c_149466])).
% 48.15/37.05  tff(c_149471, plain, (![A_2120]: (a_2_5_lattice3('#skF_14', A_2120)=k1_xboole_0 | v2_struct_0('#skF_14') | ~m1_subset_1(A_2120, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_142, c_149468])).
% 48.15/37.05  tff(c_149473, plain, (![A_2121]: (a_2_5_lattice3('#skF_14', A_2121)=k1_xboole_0 | ~m1_subset_1(A_2121, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_148, c_149471])).
% 48.15/37.05  tff(c_149575, plain, (![B_2123]: (a_2_5_lattice3('#skF_14', k1_zfmisc_1(B_2123))=k1_xboole_0 | '#skF_1'(k1_zfmisc_1(B_2123), k1_xboole_0)=B_2123 | ~m1_subset_1(B_2123, k1_xboole_0))), inference(resolution, [status(thm)], [c_138228, c_149473])).
% 48.15/37.05  tff(c_149601, plain, (![B_2123]: (k15_lattice3('#skF_14', k1_zfmisc_1(B_2123))=k15_lattice3('#skF_14', k1_xboole_0) | ~l3_lattices('#skF_14') | ~v4_lattice3('#skF_14') | ~v10_lattices('#skF_14') | v2_struct_0('#skF_14') | '#skF_1'(k1_zfmisc_1(B_2123), k1_xboole_0)=B_2123 | ~m1_subset_1(B_2123, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_149575, c_136])).
% 48.15/37.05  tff(c_149631, plain, (![B_2123]: (k15_lattice3('#skF_14', k1_zfmisc_1(B_2123))=k15_lattice3('#skF_14', k1_xboole_0) | v2_struct_0('#skF_14') | '#skF_1'(k1_zfmisc_1(B_2123), k1_xboole_0)=B_2123 | ~m1_subset_1(B_2123, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_144, c_142, c_149601])).
% 48.15/37.05  tff(c_149817, plain, (![B_2128]: (k15_lattice3('#skF_14', k1_zfmisc_1(B_2128))=k15_lattice3('#skF_14', k1_xboole_0) | '#skF_1'(k1_zfmisc_1(B_2128), k1_xboole_0)=B_2128 | ~m1_subset_1(B_2128, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_148, c_149631])).
% 48.15/37.05  tff(c_149877, plain, (![B_2128]: (m1_subset_1(k15_lattice3('#skF_14', k1_xboole_0), u1_struct_0('#skF_14')) | ~l3_lattices('#skF_14') | v2_struct_0('#skF_14') | '#skF_1'(k1_zfmisc_1(B_2128), k1_xboole_0)=B_2128 | ~m1_subset_1(B_2128, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_149817, c_106])).
% 48.15/37.05  tff(c_149929, plain, (![B_2128]: (m1_subset_1(k15_lattice3('#skF_14', k1_xboole_0), u1_struct_0('#skF_14')) | v2_struct_0('#skF_14') | '#skF_1'(k1_zfmisc_1(B_2128), k1_xboole_0)=B_2128 | ~m1_subset_1(B_2128, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_149877])).
% 48.15/37.05  tff(c_149930, plain, (![B_2128]: (m1_subset_1(k15_lattice3('#skF_14', k1_xboole_0), u1_struct_0('#skF_14')) | '#skF_1'(k1_zfmisc_1(B_2128), k1_xboole_0)=B_2128 | ~m1_subset_1(B_2128, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_148, c_149929])).
% 48.15/37.05  tff(c_149937, plain, (m1_subset_1(k15_lattice3('#skF_14', k1_xboole_0), u1_struct_0('#skF_14'))), inference(splitLeft, [status(thm)], [c_149930])).
% 48.15/37.05  tff(c_147603, plain, (m1_subset_1('#skF_5'('#skF_14'), u1_struct_0('#skF_14')) | ~l1_lattices('#skF_14') | v2_struct_0('#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_147571, c_62])).
% 48.15/37.05  tff(c_147634, plain, (m1_subset_1('#skF_5'('#skF_14'), u1_struct_0('#skF_14')) | v2_struct_0('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_147603])).
% 48.15/37.05  tff(c_147635, plain, (m1_subset_1('#skF_5'('#skF_14'), u1_struct_0('#skF_14'))), inference(negUnitSimplification, [status(thm)], [c_148, c_147634])).
% 48.15/37.05  tff(c_98, plain, (![A_102, C_111, B_109]: (k2_lattices(A_102, C_111, B_109)=k2_lattices(A_102, B_109, C_111) | ~m1_subset_1(C_111, u1_struct_0(A_102)) | ~m1_subset_1(B_109, u1_struct_0(A_102)) | ~v6_lattices(A_102) | ~l1_lattices(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_244])).
% 48.15/37.05  tff(c_147647, plain, (![B_109]: (k2_lattices('#skF_14', B_109, '#skF_5'('#skF_14'))=k2_lattices('#skF_14', '#skF_5'('#skF_14'), B_109) | ~m1_subset_1(B_109, u1_struct_0('#skF_14')) | ~v6_lattices('#skF_14') | ~l1_lattices('#skF_14') | v2_struct_0('#skF_14'))), inference(resolution, [status(thm)], [c_147635, c_98])).
% 48.15/37.05  tff(c_147678, plain, (![B_109]: (k2_lattices('#skF_14', B_109, '#skF_5'('#skF_14'))=k2_lattices('#skF_14', '#skF_5'('#skF_14'), B_109) | ~m1_subset_1(B_109, u1_struct_0('#skF_14')) | ~v6_lattices('#skF_14') | v2_struct_0('#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_147647])).
% 48.15/37.05  tff(c_147679, plain, (![B_109]: (k2_lattices('#skF_14', B_109, '#skF_5'('#skF_14'))=k2_lattices('#skF_14', '#skF_5'('#skF_14'), B_109) | ~m1_subset_1(B_109, u1_struct_0('#skF_14')) | ~v6_lattices('#skF_14'))), inference(negUnitSimplification, [status(thm)], [c_148, c_147678])).
% 48.15/37.05  tff(c_148710, plain, (~v6_lattices('#skF_14')), inference(splitLeft, [status(thm)], [c_147679])).
% 48.15/37.05  tff(c_148713, plain, (~v10_lattices('#skF_14') | v2_struct_0('#skF_14') | ~l3_lattices('#skF_14')), inference(resolution, [status(thm)], [c_34, c_148710])).
% 48.15/37.05  tff(c_148716, plain, (v2_struct_0('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_146, c_148713])).
% 48.15/37.05  tff(c_148718, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_148716])).
% 48.15/37.05  tff(c_148721, plain, (![B_2101]: (k2_lattices('#skF_14', B_2101, '#skF_5'('#skF_14'))=k2_lattices('#skF_14', '#skF_5'('#skF_14'), B_2101) | ~m1_subset_1(B_2101, u1_struct_0('#skF_14')))), inference(splitRight, [status(thm)], [c_147679])).
% 48.15/37.05  tff(c_148784, plain, (![B_114]: (k2_lattices('#skF_14', k15_lattice3('#skF_14', B_114), '#skF_5'('#skF_14'))=k2_lattices('#skF_14', '#skF_5'('#skF_14'), k15_lattice3('#skF_14', B_114)) | ~l3_lattices('#skF_14') | v2_struct_0('#skF_14'))), inference(resolution, [status(thm)], [c_106, c_148721])).
% 48.15/37.05  tff(c_148847, plain, (![B_114]: (k2_lattices('#skF_14', k15_lattice3('#skF_14', B_114), '#skF_5'('#skF_14'))=k2_lattices('#skF_14', '#skF_5'('#skF_14'), k15_lattice3('#skF_14', B_114)) | v2_struct_0('#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_148784])).
% 48.15/37.05  tff(c_148854, plain, (![B_2102]: (k2_lattices('#skF_14', k15_lattice3('#skF_14', B_2102), '#skF_5'('#skF_14'))=k2_lattices('#skF_14', '#skF_5'('#skF_14'), k15_lattice3('#skF_14', B_2102)))), inference(negUnitSimplification, [status(thm)], [c_148, c_148847])).
% 48.15/37.05  tff(c_138277, plain, (![A_1664, C_1665]: (k2_lattices(A_1664, C_1665, '#skF_5'(A_1664))='#skF_5'(A_1664) | ~m1_subset_1(C_1665, u1_struct_0(A_1664)) | ~v13_lattices(A_1664) | ~l1_lattices(A_1664) | v2_struct_0(A_1664))), inference(cnfTransformation, [status(thm)], [f_183])).
% 48.15/37.05  tff(c_138307, plain, (![A_113, B_114]: (k2_lattices(A_113, k15_lattice3(A_113, B_114), '#skF_5'(A_113))='#skF_5'(A_113) | ~v13_lattices(A_113) | ~l1_lattices(A_113) | ~l3_lattices(A_113) | v2_struct_0(A_113))), inference(resolution, [status(thm)], [c_106, c_138277])).
% 48.15/37.05  tff(c_148860, plain, (![B_2102]: (k2_lattices('#skF_14', '#skF_5'('#skF_14'), k15_lattice3('#skF_14', B_2102))='#skF_5'('#skF_14') | ~v13_lattices('#skF_14') | ~l1_lattices('#skF_14') | ~l3_lattices('#skF_14') | v2_struct_0('#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_148854, c_138307])).
% 48.15/37.05  tff(c_148885, plain, (![B_2102]: (k2_lattices('#skF_14', '#skF_5'('#skF_14'), k15_lattice3('#skF_14', B_2102))='#skF_5'('#skF_14') | v2_struct_0('#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_164, c_137720, c_148860])).
% 48.15/37.05  tff(c_148886, plain, (![B_2102]: (k2_lattices('#skF_14', '#skF_5'('#skF_14'), k15_lattice3('#skF_14', B_2102))='#skF_5'('#skF_14'))), inference(negUnitSimplification, [status(thm)], [c_148, c_148885])).
% 48.15/37.05  tff(c_148848, plain, (![B_114]: (k2_lattices('#skF_14', k15_lattice3('#skF_14', B_114), '#skF_5'('#skF_14'))=k2_lattices('#skF_14', '#skF_5'('#skF_14'), k15_lattice3('#skF_14', B_114)))), inference(negUnitSimplification, [status(thm)], [c_148, c_148847])).
% 48.15/37.05  tff(c_148995, plain, (![B_114]: (k2_lattices('#skF_14', k15_lattice3('#skF_14', B_114), '#skF_5'('#skF_14'))='#skF_5'('#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_148886, c_148848])).
% 48.15/37.05  tff(c_138866, plain, (![A_1699, B_1700, C_1701]: (r2_hidden('#skF_7'(A_1699, B_1700, C_1701), C_1701) | r4_lattice3(A_1699, B_1700, C_1701) | ~m1_subset_1(B_1700, u1_struct_0(A_1699)) | ~l3_lattices(A_1699) | v2_struct_0(A_1699))), inference(cnfTransformation, [status(thm)], [f_201])).
% 48.15/37.05  tff(c_147306, plain, (![C_2025, A_2026, B_2027]: (~r1_tarski(C_2025, '#skF_7'(A_2026, B_2027, C_2025)) | r4_lattice3(A_2026, B_2027, C_2025) | ~m1_subset_1(B_2027, u1_struct_0(A_2026)) | ~l3_lattices(A_2026) | v2_struct_0(A_2026))), inference(resolution, [status(thm)], [c_138866, c_26])).
% 48.15/37.05  tff(c_147362, plain, (![A_2028, B_2029]: (r4_lattice3(A_2028, B_2029, k1_xboole_0) | ~m1_subset_1(B_2029, u1_struct_0(A_2028)) | ~l3_lattices(A_2028) | v2_struct_0(A_2028))), inference(resolution, [status(thm)], [c_16, c_147306])).
% 48.15/37.05  tff(c_147432, plain, (![A_48]: (r4_lattice3(A_48, k5_lattices(A_48), k1_xboole_0) | ~l3_lattices(A_48) | ~l1_lattices(A_48) | v2_struct_0(A_48))), inference(resolution, [status(thm)], [c_62, c_147362])).
% 48.15/37.05  tff(c_147588, plain, (r4_lattice3('#skF_14', '#skF_5'('#skF_14'), k1_xboole_0) | ~l3_lattices('#skF_14') | ~l1_lattices('#skF_14') | v2_struct_0('#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_147571, c_147432])).
% 48.15/37.05  tff(c_147619, plain, (r4_lattice3('#skF_14', '#skF_5'('#skF_14'), k1_xboole_0) | v2_struct_0('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_142, c_147588])).
% 48.15/37.05  tff(c_147620, plain, (r4_lattice3('#skF_14', '#skF_5'('#skF_14'), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_148, c_147619])).
% 48.15/37.05  tff(c_149949, plain, (![D_101]: (r1_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), D_101) | ~r4_lattice3('#skF_14', D_101, k1_xboole_0) | ~m1_subset_1(D_101, u1_struct_0('#skF_14')) | ~v4_lattice3('#skF_14') | ~v10_lattices('#skF_14') | ~l3_lattices('#skF_14') | v2_struct_0('#skF_14'))), inference(resolution, [status(thm)], [c_149937, c_94])).
% 48.15/37.05  tff(c_149984, plain, (![D_101]: (r1_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), D_101) | ~r4_lattice3('#skF_14', D_101, k1_xboole_0) | ~m1_subset_1(D_101, u1_struct_0('#skF_14')) | v2_struct_0('#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_146, c_144, c_149949])).
% 48.15/37.05  tff(c_150248, plain, (![D_2134]: (r1_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), D_2134) | ~r4_lattice3('#skF_14', D_2134, k1_xboole_0) | ~m1_subset_1(D_2134, u1_struct_0('#skF_14')))), inference(negUnitSimplification, [status(thm)], [c_148, c_149984])).
% 48.15/37.05  tff(c_150256, plain, (![D_2134]: (k1_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), D_2134)=D_2134 | ~m1_subset_1(k15_lattice3('#skF_14', k1_xboole_0), u1_struct_0('#skF_14')) | ~l2_lattices('#skF_14') | v2_struct_0('#skF_14') | ~r4_lattice3('#skF_14', D_2134, k1_xboole_0) | ~m1_subset_1(D_2134, u1_struct_0('#skF_14')))), inference(resolution, [status(thm)], [c_150248, c_52])).
% 48.15/37.05  tff(c_150267, plain, (![D_2134]: (k1_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), D_2134)=D_2134 | v2_struct_0('#skF_14') | ~r4_lattice3('#skF_14', D_2134, k1_xboole_0) | ~m1_subset_1(D_2134, u1_struct_0('#skF_14')))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_149937, c_150256])).
% 48.15/37.05  tff(c_150753, plain, (![D_2158]: (k1_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), D_2158)=D_2158 | ~r4_lattice3('#skF_14', D_2158, k1_xboole_0) | ~m1_subset_1(D_2158, u1_struct_0('#skF_14')))), inference(negUnitSimplification, [status(thm)], [c_148, c_150267])).
% 48.15/37.05  tff(c_150815, plain, (k1_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), '#skF_5'('#skF_14'))='#skF_5'('#skF_14') | ~r4_lattice3('#skF_14', '#skF_5'('#skF_14'), k1_xboole_0) | ~v13_lattices('#skF_14') | ~l1_lattices('#skF_14') | v2_struct_0('#skF_14')), inference(resolution, [status(thm)], [c_74, c_150753])).
% 48.15/37.05  tff(c_150882, plain, (k1_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), '#skF_5'('#skF_14'))='#skF_5'('#skF_14') | v2_struct_0('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_137720, c_147620, c_150815])).
% 48.15/37.05  tff(c_150883, plain, (k1_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), '#skF_5'('#skF_14'))='#skF_5'('#skF_14')), inference(negUnitSimplification, [status(thm)], [c_148, c_150882])).
% 48.15/37.05  tff(c_54, plain, (![A_37, B_44, C_46]: (k2_lattices(A_37, B_44, k1_lattices(A_37, B_44, C_46))=B_44 | ~m1_subset_1(C_46, u1_struct_0(A_37)) | ~m1_subset_1(B_44, u1_struct_0(A_37)) | ~v9_lattices(A_37) | ~l3_lattices(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_134])).
% 48.15/37.05  tff(c_147645, plain, (![B_44]: (k2_lattices('#skF_14', B_44, k1_lattices('#skF_14', B_44, '#skF_5'('#skF_14')))=B_44 | ~m1_subset_1(B_44, u1_struct_0('#skF_14')) | ~v9_lattices('#skF_14') | ~l3_lattices('#skF_14') | v2_struct_0('#skF_14'))), inference(resolution, [status(thm)], [c_147635, c_54])).
% 48.15/37.05  tff(c_147674, plain, (![B_44]: (k2_lattices('#skF_14', B_44, k1_lattices('#skF_14', B_44, '#skF_5'('#skF_14')))=B_44 | ~m1_subset_1(B_44, u1_struct_0('#skF_14')) | ~v9_lattices('#skF_14') | v2_struct_0('#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_147645])).
% 48.15/37.05  tff(c_147675, plain, (![B_44]: (k2_lattices('#skF_14', B_44, k1_lattices('#skF_14', B_44, '#skF_5'('#skF_14')))=B_44 | ~m1_subset_1(B_44, u1_struct_0('#skF_14')) | ~v9_lattices('#skF_14'))), inference(negUnitSimplification, [status(thm)], [c_148, c_147674])).
% 48.15/37.05  tff(c_148289, plain, (~v9_lattices('#skF_14')), inference(splitLeft, [status(thm)], [c_147675])).
% 48.15/37.05  tff(c_148292, plain, (~v10_lattices('#skF_14') | v2_struct_0('#skF_14') | ~l3_lattices('#skF_14')), inference(resolution, [status(thm)], [c_28, c_148289])).
% 48.15/37.05  tff(c_148295, plain, (v2_struct_0('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_146, c_148292])).
% 48.15/37.05  tff(c_148297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_148295])).
% 48.15/37.05  tff(c_148298, plain, (![B_44]: (k2_lattices('#skF_14', B_44, k1_lattices('#skF_14', B_44, '#skF_5'('#skF_14')))=B_44 | ~m1_subset_1(B_44, u1_struct_0('#skF_14')))), inference(splitRight, [status(thm)], [c_147675])).
% 48.15/37.05  tff(c_150896, plain, (k2_lattices('#skF_14', k15_lattice3('#skF_14', k1_xboole_0), '#skF_5'('#skF_14'))=k15_lattice3('#skF_14', k1_xboole_0) | ~m1_subset_1(k15_lattice3('#skF_14', k1_xboole_0), u1_struct_0('#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_150883, c_148298])).
% 48.15/37.05  tff(c_150900, plain, (k15_lattice3('#skF_14', k1_xboole_0)='#skF_5'('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_149937, c_148995, c_150896])).
% 48.15/37.05  tff(c_150902, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147572, c_150900])).
% 48.15/37.05  tff(c_150904, plain, (~m1_subset_1(k15_lattice3('#skF_14', k1_xboole_0), u1_struct_0('#skF_14'))), inference(splitRight, [status(thm)], [c_149930])).
% 48.15/37.05  tff(c_150907, plain, (~l3_lattices('#skF_14') | v2_struct_0('#skF_14')), inference(resolution, [status(thm)], [c_106, c_150904])).
% 48.15/37.05  tff(c_150910, plain, (v2_struct_0('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_150907])).
% 48.15/37.05  tff(c_150912, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_150910])).
% 48.15/37.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 48.15/37.05  
% 48.15/37.05  Inference rules
% 48.15/37.05  ----------------------
% 48.15/37.05  #Ref     : 0
% 48.15/37.05  #Sup     : 41128
% 48.15/37.05  #Fact    : 38
% 48.15/37.05  #Define  : 0
% 48.15/37.05  #Split   : 41
% 48.15/37.05  #Chain   : 0
% 48.15/37.05  #Close   : 0
% 48.15/37.05  
% 48.15/37.05  Ordering : KBO
% 48.15/37.05  
% 48.15/37.05  Simplification rules
% 48.15/37.05  ----------------------
% 48.15/37.05  #Subsume      : 23864
% 48.15/37.05  #Demod        : 13851
% 48.15/37.05  #Tautology    : 5065
% 48.15/37.05  #SimpNegUnit  : 2542
% 48.15/37.05  #BackRed      : 18
% 48.15/37.05  
% 48.15/37.05  #Partial instantiations: 0
% 48.15/37.05  #Strategies tried      : 1
% 48.15/37.05  
% 48.15/37.05  Timing (in seconds)
% 48.15/37.05  ----------------------
% 48.15/37.06  Preprocessing        : 0.44
% 48.15/37.06  Parsing              : 0.22
% 48.15/37.06  CNF conversion       : 0.04
% 48.15/37.06  Main loop            : 35.77
% 48.15/37.06  Inferencing          : 4.24
% 48.15/37.06  Reduction            : 7.27
% 48.15/37.06  Demodulation         : 5.20
% 48.15/37.06  BG Simplification    : 0.35
% 48.15/37.06  Subsumption          : 22.64
% 48.15/37.06  Abstraction          : 0.66
% 48.15/37.06  MUC search           : 0.00
% 48.15/37.06  Cooper               : 0.00
% 48.15/37.06  Total                : 36.31
% 48.15/37.06  Index Insertion      : 0.00
% 48.15/37.06  Index Deletion       : 0.00
% 48.15/37.06  Index Matching       : 0.00
% 48.15/37.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
