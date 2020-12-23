%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:52 EST 2020

% Result     : Theorem 26.73s
% Output     : CNFRefutation 26.92s
% Verified   : 
% Statistics : Number of formulae       :  224 (3541 expanded)
%              Number of leaves         :   57 (1280 expanded)
%              Depth                    :   32
%              Number of atoms          :  718 (15347 expanded)
%              Number of equality atoms :  108 (1794 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r1_lattices > r2_hidden > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k6_domain_1 > k16_lattice3 > k15_lattice3 > a_2_6_lattice3 > a_2_5_lattice3 > #nlpp > u1_struct_0 > k5_lattices > k1_xboole_0 > #skF_5 > #skF_9 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_1 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k2_lattices,type,(
    k2_lattices: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

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
    '#skF_9': $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_266,negated_conjecture,(
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

tff(f_99,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_176,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k15_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

tff(f_154,axiom,(
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

tff(f_215,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( k15_lattice3(A,k6_domain_1(u1_struct_0(A),B)) = B
            & k16_lattice3(A,k6_domain_1(u1_struct_0(A),B)) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattice3)).

tff(f_67,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_199,axiom,(
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

tff(f_45,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_245,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( k15_lattice3(A,B) = k15_lattice3(A,a_2_5_lattice3(A,B))
          & k16_lattice3(A,B) = k16_lattice3(A,a_2_6_lattice3(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_lattice3)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => m1_subset_1(k5_lattices(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

tff(f_169,axiom,(
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

tff(f_231,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B,C] :
          ( r1_tarski(B,C)
         => ( r3_lattices(A,k15_lattice3(A,B),k15_lattice3(A,C))
            & r3_lattices(A,k16_lattice3(A,C),k16_lattice3(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_lattice3)).

tff(f_118,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

tff(f_137,axiom,(
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

tff(f_86,axiom,(
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

tff(c_106,plain,(
    ~ v2_struct_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_100,plain,(
    l3_lattices('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_118,plain,(
    ! [A_85] :
      ( l1_lattices(A_85)
      | ~ l3_lattices(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_122,plain,(
    l1_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_100,c_118])).

tff(c_72,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(k15_lattice3(A_56,B_57),u1_struct_0(A_56))
      | ~ l3_lattices(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_104,plain,(
    v10_lattices('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_98,plain,
    ( k15_lattice3('#skF_9',k1_xboole_0) != k5_lattices('#skF_9')
    | ~ l3_lattices('#skF_9')
    | ~ v13_lattices('#skF_9')
    | ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_108,plain,
    ( k15_lattice3('#skF_9',k1_xboole_0) != k5_lattices('#skF_9')
    | ~ v13_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_100,c_98])).

tff(c_109,plain,
    ( k15_lattice3('#skF_9',k1_xboole_0) != k5_lattices('#skF_9')
    | ~ v13_lattices('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_108])).

tff(c_124,plain,(
    ~ v13_lattices('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_56,plain,(
    ! [A_34,B_43] :
      ( m1_subset_1('#skF_4'(A_34,B_43),u1_struct_0(A_34))
      | v13_lattices(A_34)
      | ~ m1_subset_1(B_43,u1_struct_0(A_34))
      | ~ l1_lattices(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_102,plain,(
    v4_lattice3('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_88,plain,(
    ! [A_71,B_73] :
      ( k15_lattice3(A_71,k6_domain_1(u1_struct_0(A_71),B_73)) = B_73
      | ~ m1_subset_1(B_73,u1_struct_0(A_71))
      | ~ l3_lattices(A_71)
      | ~ v4_lattice3(A_71)
      | ~ v10_lattices(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_24,plain,(
    ! [A_11] :
      ( v6_lattices(A_11)
      | ~ v10_lattices(A_11)
      | v2_struct_0(A_11)
      | ~ l3_lattices(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_401,plain,(
    ! [A_151,B_152,C_153] :
      ( r2_hidden('#skF_8'(A_151,B_152,C_153),C_153)
      | ~ r2_hidden(A_151,a_2_5_lattice3(B_152,C_153))
      | ~ l3_lattices(B_152)
      | ~ v4_lattice3(B_152)
      | ~ v10_lattices(B_152)
      | v2_struct_0(B_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_16,plain,(
    ! [B_10,A_9] :
      ( ~ r1_tarski(B_10,A_9)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_456,plain,(
    ! [C_164,A_165,B_166] :
      ( ~ r1_tarski(C_164,'#skF_8'(A_165,B_166,C_164))
      | ~ r2_hidden(A_165,a_2_5_lattice3(B_166,C_164))
      | ~ l3_lattices(B_166)
      | ~ v4_lattice3(B_166)
      | ~ v10_lattices(B_166)
      | v2_struct_0(B_166) ) ),
    inference(resolution,[status(thm)],[c_401,c_16])).

tff(c_461,plain,(
    ! [A_167,B_168] :
      ( ~ r2_hidden(A_167,a_2_5_lattice3(B_168,k1_xboole_0))
      | ~ l3_lattices(B_168)
      | ~ v4_lattice3(B_168)
      | ~ v10_lattices(B_168)
      | v2_struct_0(B_168) ) ),
    inference(resolution,[status(thm)],[c_14,c_456])).

tff(c_477,plain,(
    ! [B_169,B_170] :
      ( ~ l3_lattices(B_169)
      | ~ v4_lattice3(B_169)
      | ~ v10_lattices(B_169)
      | v2_struct_0(B_169)
      | r1_tarski(a_2_5_lattice3(B_169,k1_xboole_0),B_170) ) ),
    inference(resolution,[status(thm)],[c_6,c_461])).

tff(c_126,plain,(
    ! [B_89,A_90] :
      ( B_89 = A_90
      | ~ r1_tarski(B_89,A_90)
      | ~ r1_tarski(A_90,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_135,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_126])).

tff(c_514,plain,(
    ! [B_174] :
      ( a_2_5_lattice3(B_174,k1_xboole_0) = k1_xboole_0
      | ~ l3_lattices(B_174)
      | ~ v4_lattice3(B_174)
      | ~ v10_lattices(B_174)
      | v2_struct_0(B_174) ) ),
    inference(resolution,[status(thm)],[c_477,c_135])).

tff(c_517,plain,
    ( a_2_5_lattice3('#skF_9',k1_xboole_0) = k1_xboole_0
    | ~ l3_lattices('#skF_9')
    | ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_102,c_514])).

tff(c_520,plain,
    ( a_2_5_lattice3('#skF_9',k1_xboole_0) = k1_xboole_0
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_100,c_517])).

tff(c_521,plain,(
    a_2_5_lattice3('#skF_9',k1_xboole_0) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_520])).

tff(c_94,plain,(
    ! [A_79,B_81] :
      ( k15_lattice3(A_79,a_2_5_lattice3(A_79,B_81)) = k15_lattice3(A_79,B_81)
      | ~ l3_lattices(A_79)
      | ~ v4_lattice3(A_79)
      | ~ v10_lattices(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_40,plain,(
    ! [A_22] :
      ( m1_subset_1(k5_lattices(A_22),u1_struct_0(A_22))
      | ~ l1_lattices(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_725,plain,(
    ! [A_194,C_195,B_196] :
      ( k2_lattices(A_194,C_195,B_196) = k2_lattices(A_194,B_196,C_195)
      | ~ m1_subset_1(C_195,u1_struct_0(A_194))
      | ~ m1_subset_1(B_196,u1_struct_0(A_194))
      | ~ v6_lattices(A_194)
      | ~ l1_lattices(A_194)
      | v2_struct_0(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_772,plain,(
    ! [A_199,B_200] :
      ( k2_lattices(A_199,k5_lattices(A_199),B_200) = k2_lattices(A_199,B_200,k5_lattices(A_199))
      | ~ m1_subset_1(B_200,u1_struct_0(A_199))
      | ~ v6_lattices(A_199)
      | ~ l1_lattices(A_199)
      | v2_struct_0(A_199) ) ),
    inference(resolution,[status(thm)],[c_40,c_725])).

tff(c_1227,plain,(
    ! [A_265,B_266] :
      ( k2_lattices(A_265,k15_lattice3(A_265,B_266),k5_lattices(A_265)) = k2_lattices(A_265,k5_lattices(A_265),k15_lattice3(A_265,B_266))
      | ~ v6_lattices(A_265)
      | ~ l1_lattices(A_265)
      | ~ l3_lattices(A_265)
      | v2_struct_0(A_265) ) ),
    inference(resolution,[status(thm)],[c_72,c_772])).

tff(c_3307,plain,(
    ! [A_535,B_536] :
      ( k2_lattices(A_535,k5_lattices(A_535),k15_lattice3(A_535,a_2_5_lattice3(A_535,B_536))) = k2_lattices(A_535,k15_lattice3(A_535,B_536),k5_lattices(A_535))
      | ~ v6_lattices(A_535)
      | ~ l1_lattices(A_535)
      | ~ l3_lattices(A_535)
      | v2_struct_0(A_535)
      | ~ l3_lattices(A_535)
      | ~ v4_lattice3(A_535)
      | ~ v10_lattices(A_535)
      | v2_struct_0(A_535) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_1227])).

tff(c_3329,plain,
    ( k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),k5_lattices('#skF_9')) = k2_lattices('#skF_9',k5_lattices('#skF_9'),k15_lattice3('#skF_9',k1_xboole_0))
    | ~ v6_lattices('#skF_9')
    | ~ l1_lattices('#skF_9')
    | ~ l3_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_9')
    | ~ v4_lattice3('#skF_9')
    | ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_521,c_3307])).

tff(c_3336,plain,
    ( k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),k5_lattices('#skF_9')) = k2_lattices('#skF_9',k5_lattices('#skF_9'),k15_lattice3('#skF_9',k1_xboole_0))
    | ~ v6_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_100,c_100,c_122,c_3329])).

tff(c_3337,plain,
    ( k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),k5_lattices('#skF_9')) = k2_lattices('#skF_9',k5_lattices('#skF_9'),k15_lattice3('#skF_9',k1_xboole_0))
    | ~ v6_lattices('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_3336])).

tff(c_3338,plain,(
    ~ v6_lattices('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_3337])).

tff(c_3341,plain,
    ( ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_24,c_3338])).

tff(c_3344,plain,(
    v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_104,c_3341])).

tff(c_3346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_3344])).

tff(c_3348,plain,(
    v6_lattices('#skF_9') ),
    inference(splitRight,[status(thm)],[c_3337])).

tff(c_20,plain,(
    ! [A_11] :
      ( v8_lattices(A_11)
      | ~ v10_lattices(A_11)
      | v2_struct_0(A_11)
      | ~ l3_lattices(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_421,plain,(
    ! [A_156,B_157,C_158] :
      ( r3_lattices(A_156,k15_lattice3(A_156,B_157),k15_lattice3(A_156,C_158))
      | ~ r1_tarski(B_157,C_158)
      | ~ l3_lattices(A_156)
      | ~ v4_lattice3(A_156)
      | ~ v10_lattices(A_156)
      | v2_struct_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_2921,plain,(
    ! [A_457,B_458,B_459] :
      ( r3_lattices(A_457,k15_lattice3(A_457,B_458),B_459)
      | ~ r1_tarski(B_458,k6_domain_1(u1_struct_0(A_457),B_459))
      | ~ l3_lattices(A_457)
      | ~ v4_lattice3(A_457)
      | ~ v10_lattices(A_457)
      | v2_struct_0(A_457)
      | ~ m1_subset_1(B_459,u1_struct_0(A_457))
      | ~ l3_lattices(A_457)
      | ~ v4_lattice3(A_457)
      | ~ v10_lattices(A_457)
      | v2_struct_0(A_457) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_421])).

tff(c_2954,plain,(
    ! [A_460,B_461] :
      ( r3_lattices(A_460,k15_lattice3(A_460,k1_xboole_0),B_461)
      | ~ m1_subset_1(B_461,u1_struct_0(A_460))
      | ~ l3_lattices(A_460)
      | ~ v4_lattice3(A_460)
      | ~ v10_lattices(A_460)
      | v2_struct_0(A_460) ) ),
    inference(resolution,[status(thm)],[c_14,c_2921])).

tff(c_48,plain,(
    ! [A_24,B_25,C_26] :
      ( r1_lattices(A_24,B_25,C_26)
      | ~ r3_lattices(A_24,B_25,C_26)
      | ~ m1_subset_1(C_26,u1_struct_0(A_24))
      | ~ m1_subset_1(B_25,u1_struct_0(A_24))
      | ~ l3_lattices(A_24)
      | ~ v9_lattices(A_24)
      | ~ v8_lattices(A_24)
      | ~ v6_lattices(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_3128,plain,(
    ! [A_492,B_493] :
      ( r1_lattices(A_492,k15_lattice3(A_492,k1_xboole_0),B_493)
      | ~ m1_subset_1(k15_lattice3(A_492,k1_xboole_0),u1_struct_0(A_492))
      | ~ v9_lattices(A_492)
      | ~ v8_lattices(A_492)
      | ~ v6_lattices(A_492)
      | ~ m1_subset_1(B_493,u1_struct_0(A_492))
      | ~ l3_lattices(A_492)
      | ~ v4_lattice3(A_492)
      | ~ v10_lattices(A_492)
      | v2_struct_0(A_492) ) ),
    inference(resolution,[status(thm)],[c_2954,c_48])).

tff(c_3133,plain,(
    ! [A_494,B_495] :
      ( r1_lattices(A_494,k15_lattice3(A_494,k1_xboole_0),B_495)
      | ~ v9_lattices(A_494)
      | ~ v8_lattices(A_494)
      | ~ v6_lattices(A_494)
      | ~ m1_subset_1(B_495,u1_struct_0(A_494))
      | ~ v4_lattice3(A_494)
      | ~ v10_lattices(A_494)
      | ~ l3_lattices(A_494)
      | v2_struct_0(A_494) ) ),
    inference(resolution,[status(thm)],[c_72,c_3128])).

tff(c_52,plain,(
    ! [A_27,B_31,C_33] :
      ( k2_lattices(A_27,B_31,C_33) = B_31
      | ~ r1_lattices(A_27,B_31,C_33)
      | ~ m1_subset_1(C_33,u1_struct_0(A_27))
      | ~ m1_subset_1(B_31,u1_struct_0(A_27))
      | ~ l3_lattices(A_27)
      | ~ v9_lattices(A_27)
      | ~ v8_lattices(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_4070,plain,(
    ! [A_586,B_587] :
      ( k2_lattices(A_586,k15_lattice3(A_586,k1_xboole_0),B_587) = k15_lattice3(A_586,k1_xboole_0)
      | ~ m1_subset_1(k15_lattice3(A_586,k1_xboole_0),u1_struct_0(A_586))
      | ~ v9_lattices(A_586)
      | ~ v8_lattices(A_586)
      | ~ v6_lattices(A_586)
      | ~ m1_subset_1(B_587,u1_struct_0(A_586))
      | ~ v4_lattice3(A_586)
      | ~ v10_lattices(A_586)
      | ~ l3_lattices(A_586)
      | v2_struct_0(A_586) ) ),
    inference(resolution,[status(thm)],[c_3133,c_52])).

tff(c_4075,plain,(
    ! [A_588,B_589] :
      ( k2_lattices(A_588,k15_lattice3(A_588,k1_xboole_0),B_589) = k15_lattice3(A_588,k1_xboole_0)
      | ~ v9_lattices(A_588)
      | ~ v8_lattices(A_588)
      | ~ v6_lattices(A_588)
      | ~ m1_subset_1(B_589,u1_struct_0(A_588))
      | ~ v4_lattice3(A_588)
      | ~ v10_lattices(A_588)
      | ~ l3_lattices(A_588)
      | v2_struct_0(A_588) ) ),
    inference(resolution,[status(thm)],[c_72,c_4070])).

tff(c_4145,plain,(
    ! [A_592] :
      ( k2_lattices(A_592,k15_lattice3(A_592,k1_xboole_0),k5_lattices(A_592)) = k15_lattice3(A_592,k1_xboole_0)
      | ~ v9_lattices(A_592)
      | ~ v8_lattices(A_592)
      | ~ v6_lattices(A_592)
      | ~ v4_lattice3(A_592)
      | ~ v10_lattices(A_592)
      | ~ l3_lattices(A_592)
      | ~ l1_lattices(A_592)
      | v2_struct_0(A_592) ) ),
    inference(resolution,[status(thm)],[c_40,c_4075])).

tff(c_3347,plain,(
    k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),k5_lattices('#skF_9')) = k2_lattices('#skF_9',k5_lattices('#skF_9'),k15_lattice3('#skF_9',k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_3337])).

tff(c_4151,plain,
    ( k2_lattices('#skF_9',k5_lattices('#skF_9'),k15_lattice3('#skF_9',k1_xboole_0)) = k15_lattice3('#skF_9',k1_xboole_0)
    | ~ v9_lattices('#skF_9')
    | ~ v8_lattices('#skF_9')
    | ~ v6_lattices('#skF_9')
    | ~ v4_lattice3('#skF_9')
    | ~ v10_lattices('#skF_9')
    | ~ l3_lattices('#skF_9')
    | ~ l1_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_4145,c_3347])).

tff(c_4174,plain,
    ( k2_lattices('#skF_9',k5_lattices('#skF_9'),k15_lattice3('#skF_9',k1_xboole_0)) = k15_lattice3('#skF_9',k1_xboole_0)
    | ~ v9_lattices('#skF_9')
    | ~ v8_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_100,c_104,c_102,c_3348,c_4151])).

tff(c_4175,plain,
    ( k2_lattices('#skF_9',k5_lattices('#skF_9'),k15_lattice3('#skF_9',k1_xboole_0)) = k15_lattice3('#skF_9',k1_xboole_0)
    | ~ v9_lattices('#skF_9')
    | ~ v8_lattices('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_4174])).

tff(c_4180,plain,(
    ~ v8_lattices('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_4175])).

tff(c_4211,plain,
    ( ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_20,c_4180])).

tff(c_4214,plain,(
    v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_104,c_4211])).

tff(c_4216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_4214])).

tff(c_4218,plain,(
    v8_lattices('#skF_9') ),
    inference(splitRight,[status(thm)],[c_4175])).

tff(c_18,plain,(
    ! [A_11] :
      ( v9_lattices(A_11)
      | ~ v10_lattices(A_11)
      | v2_struct_0(A_11)
      | ~ l3_lattices(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4217,plain,
    ( ~ v9_lattices('#skF_9')
    | k2_lattices('#skF_9',k5_lattices('#skF_9'),k15_lattice3('#skF_9',k1_xboole_0)) = k15_lattice3('#skF_9',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_4175])).

tff(c_4219,plain,(
    ~ v9_lattices('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_4217])).

tff(c_4225,plain,
    ( ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_18,c_4219])).

tff(c_4228,plain,(
    v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_104,c_4225])).

tff(c_4230,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_4228])).

tff(c_4232,plain,(
    v9_lattices('#skF_9') ),
    inference(splitRight,[status(thm)],[c_4217])).

tff(c_1530,plain,(
    ! [A_291,B_292,B_293] :
      ( k2_lattices(A_291,k15_lattice3(A_291,B_292),B_293) = k2_lattices(A_291,B_293,k15_lattice3(A_291,B_292))
      | ~ m1_subset_1(B_293,u1_struct_0(A_291))
      | ~ v6_lattices(A_291)
      | ~ l1_lattices(A_291)
      | ~ l3_lattices(A_291)
      | v2_struct_0(A_291) ) ),
    inference(resolution,[status(thm)],[c_72,c_725])).

tff(c_1584,plain,(
    ! [A_298,B_300,B_299] :
      ( k2_lattices(A_298,k15_lattice3(A_298,B_300),k15_lattice3(A_298,B_299)) = k2_lattices(A_298,k15_lattice3(A_298,B_299),k15_lattice3(A_298,B_300))
      | ~ v6_lattices(A_298)
      | ~ l1_lattices(A_298)
      | ~ l3_lattices(A_298)
      | v2_struct_0(A_298) ) ),
    inference(resolution,[status(thm)],[c_72,c_1530])).

tff(c_4956,plain,(
    ! [A_649,B_650,B_651] :
      ( k2_lattices(A_649,k15_lattice3(A_649,a_2_5_lattice3(A_649,B_650)),k15_lattice3(A_649,B_651)) = k2_lattices(A_649,k15_lattice3(A_649,B_651),k15_lattice3(A_649,B_650))
      | ~ v6_lattices(A_649)
      | ~ l1_lattices(A_649)
      | ~ l3_lattices(A_649)
      | v2_struct_0(A_649)
      | ~ l3_lattices(A_649)
      | ~ v4_lattice3(A_649)
      | ~ v10_lattices(A_649)
      | v2_struct_0(A_649) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_1584])).

tff(c_5011,plain,(
    ! [B_651] :
      ( k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),k15_lattice3('#skF_9',B_651)) = k2_lattices('#skF_9',k15_lattice3('#skF_9',B_651),k15_lattice3('#skF_9',k1_xboole_0))
      | ~ v6_lattices('#skF_9')
      | ~ l1_lattices('#skF_9')
      | ~ l3_lattices('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ l3_lattices('#skF_9')
      | ~ v4_lattice3('#skF_9')
      | ~ v10_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_521,c_4956])).

tff(c_5024,plain,(
    ! [B_651] :
      ( k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),k15_lattice3('#skF_9',B_651)) = k2_lattices('#skF_9',k15_lattice3('#skF_9',B_651),k15_lattice3('#skF_9',k1_xboole_0))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_100,c_100,c_122,c_3348,c_5011])).

tff(c_5026,plain,(
    ! [B_652] : k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),k15_lattice3('#skF_9',B_652)) = k2_lattices('#skF_9',k15_lattice3('#skF_9',B_652),k15_lattice3('#skF_9',k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_5024])).

tff(c_4101,plain,(
    ! [A_56,B_57] :
      ( k2_lattices(A_56,k15_lattice3(A_56,k1_xboole_0),k15_lattice3(A_56,B_57)) = k15_lattice3(A_56,k1_xboole_0)
      | ~ v9_lattices(A_56)
      | ~ v8_lattices(A_56)
      | ~ v6_lattices(A_56)
      | ~ v4_lattice3(A_56)
      | ~ v10_lattices(A_56)
      | ~ l3_lattices(A_56)
      | v2_struct_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_72,c_4075])).

tff(c_5042,plain,(
    ! [B_652] :
      ( k2_lattices('#skF_9',k15_lattice3('#skF_9',B_652),k15_lattice3('#skF_9',k1_xboole_0)) = k15_lattice3('#skF_9',k1_xboole_0)
      | ~ v9_lattices('#skF_9')
      | ~ v8_lattices('#skF_9')
      | ~ v6_lattices('#skF_9')
      | ~ v4_lattice3('#skF_9')
      | ~ v10_lattices('#skF_9')
      | ~ l3_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5026,c_4101])).

tff(c_5110,plain,(
    ! [B_652] :
      ( k2_lattices('#skF_9',k15_lattice3('#skF_9',B_652),k15_lattice3('#skF_9',k1_xboole_0)) = k15_lattice3('#skF_9',k1_xboole_0)
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_104,c_102,c_3348,c_4218,c_4232,c_5042])).

tff(c_5172,plain,(
    ! [B_657] : k2_lattices('#skF_9',k15_lattice3('#skF_9',B_657),k15_lattice3('#skF_9',k1_xboole_0)) = k15_lattice3('#skF_9',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_5110])).

tff(c_5229,plain,(
    ! [B_73] :
      ( k2_lattices('#skF_9',B_73,k15_lattice3('#skF_9',k1_xboole_0)) = k15_lattice3('#skF_9',k1_xboole_0)
      | ~ m1_subset_1(B_73,u1_struct_0('#skF_9'))
      | ~ l3_lattices('#skF_9')
      | ~ v4_lattice3('#skF_9')
      | ~ v10_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_5172])).

tff(c_5282,plain,(
    ! [B_73] :
      ( k2_lattices('#skF_9',B_73,k15_lattice3('#skF_9',k1_xboole_0)) = k15_lattice3('#skF_9',k1_xboole_0)
      | ~ m1_subset_1(B_73,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_100,c_5229])).

tff(c_5485,plain,(
    ! [B_664] :
      ( k2_lattices('#skF_9',B_664,k15_lattice3('#skF_9',k1_xboole_0)) = k15_lattice3('#skF_9',k1_xboole_0)
      | ~ m1_subset_1(B_664,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_5282])).

tff(c_5501,plain,(
    ! [B_43] :
      ( k2_lattices('#skF_9','#skF_4'('#skF_9',B_43),k15_lattice3('#skF_9',k1_xboole_0)) = k15_lattice3('#skF_9',k1_xboole_0)
      | v13_lattices('#skF_9')
      | ~ m1_subset_1(B_43,u1_struct_0('#skF_9'))
      | ~ l1_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_56,c_5485])).

tff(c_5536,plain,(
    ! [B_43] :
      ( k2_lattices('#skF_9','#skF_4'('#skF_9',B_43),k15_lattice3('#skF_9',k1_xboole_0)) = k15_lattice3('#skF_9',k1_xboole_0)
      | v13_lattices('#skF_9')
      | ~ m1_subset_1(B_43,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_5501])).

tff(c_5595,plain,(
    ! [B_666] :
      ( k2_lattices('#skF_9','#skF_4'('#skF_9',B_666),k15_lattice3('#skF_9',k1_xboole_0)) = k15_lattice3('#skF_9',k1_xboole_0)
      | ~ m1_subset_1(B_666,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_124,c_5536])).

tff(c_54,plain,(
    ! [A_34,B_43] :
      ( k2_lattices(A_34,'#skF_4'(A_34,B_43),B_43) != B_43
      | k2_lattices(A_34,B_43,'#skF_4'(A_34,B_43)) != B_43
      | v13_lattices(A_34)
      | ~ m1_subset_1(B_43,u1_struct_0(A_34))
      | ~ l1_lattices(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_5604,plain,
    ( k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),'#skF_4'('#skF_9',k15_lattice3('#skF_9',k1_xboole_0))) != k15_lattice3('#skF_9',k1_xboole_0)
    | v13_lattices('#skF_9')
    | ~ l1_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ m1_subset_1(k15_lattice3('#skF_9',k1_xboole_0),u1_struct_0('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5595,c_54])).

tff(c_5618,plain,
    ( k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),'#skF_4'('#skF_9',k15_lattice3('#skF_9',k1_xboole_0))) != k15_lattice3('#skF_9',k1_xboole_0)
    | v13_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ m1_subset_1(k15_lattice3('#skF_9',k1_xboole_0),u1_struct_0('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_5604])).

tff(c_5619,plain,
    ( k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),'#skF_4'('#skF_9',k15_lattice3('#skF_9',k1_xboole_0))) != k15_lattice3('#skF_9',k1_xboole_0)
    | ~ m1_subset_1(k15_lattice3('#skF_9',k1_xboole_0),u1_struct_0('#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_124,c_5618])).

tff(c_5729,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_9',k1_xboole_0),u1_struct_0('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_5619])).

tff(c_5732,plain,
    ( ~ l3_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_72,c_5729])).

tff(c_5735,plain,(
    v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_5732])).

tff(c_5737,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_5735])).

tff(c_5739,plain,(
    m1_subset_1(k15_lattice3('#skF_9',k1_xboole_0),u1_struct_0('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_5619])).

tff(c_5111,plain,(
    ! [B_652] : k2_lattices('#skF_9',k15_lattice3('#skF_9',B_652),k15_lattice3('#skF_9',k1_xboole_0)) = k15_lattice3('#skF_9',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_5110])).

tff(c_5025,plain,(
    ! [B_651] : k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),k15_lattice3('#skF_9',B_651)) = k2_lattices('#skF_9',k15_lattice3('#skF_9',B_651),k15_lattice3('#skF_9',k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_5024])).

tff(c_5288,plain,(
    ! [B_658] : k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),k15_lattice3('#skF_9',B_658)) = k15_lattice3('#skF_9',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5111,c_5025])).

tff(c_5343,plain,(
    ! [B_73] :
      ( k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),B_73) = k15_lattice3('#skF_9',k1_xboole_0)
      | ~ m1_subset_1(B_73,u1_struct_0('#skF_9'))
      | ~ l3_lattices('#skF_9')
      | ~ v4_lattice3('#skF_9')
      | ~ v10_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_5288])).

tff(c_5392,plain,(
    ! [B_73] :
      ( k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),B_73) = k15_lattice3('#skF_9',k1_xboole_0)
      | ~ m1_subset_1(B_73,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_100,c_5343])).

tff(c_5412,plain,(
    ! [B_663] :
      ( k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),B_663) = k15_lattice3('#skF_9',k1_xboole_0)
      | ~ m1_subset_1(B_663,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_5392])).

tff(c_5428,plain,(
    ! [B_43] :
      ( k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),'#skF_4'('#skF_9',B_43)) = k15_lattice3('#skF_9',k1_xboole_0)
      | v13_lattices('#skF_9')
      | ~ m1_subset_1(B_43,u1_struct_0('#skF_9'))
      | ~ l1_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_56,c_5412])).

tff(c_5463,plain,(
    ! [B_43] :
      ( k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),'#skF_4'('#skF_9',B_43)) = k15_lattice3('#skF_9',k1_xboole_0)
      | v13_lattices('#skF_9')
      | ~ m1_subset_1(B_43,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_5428])).

tff(c_5464,plain,(
    ! [B_43] :
      ( k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),'#skF_4'('#skF_9',B_43)) = k15_lattice3('#skF_9',k1_xboole_0)
      | ~ m1_subset_1(B_43,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_124,c_5463])).

tff(c_5738,plain,(
    k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),'#skF_4'('#skF_9',k15_lattice3('#skF_9',k1_xboole_0))) != k15_lattice3('#skF_9',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_5619])).

tff(c_5876,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_9',k1_xboole_0),u1_struct_0('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5464,c_5738])).

tff(c_5883,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5739,c_5876])).

tff(c_5885,plain,(
    v13_lattices('#skF_9') ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_58,plain,(
    ! [A_34] :
      ( m1_subset_1('#skF_3'(A_34),u1_struct_0(A_34))
      | ~ v13_lattices(A_34)
      | ~ l1_lattices(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_6435,plain,(
    ! [A_782,C_783] :
      ( k2_lattices(A_782,C_783,k5_lattices(A_782)) = k5_lattices(A_782)
      | ~ m1_subset_1(C_783,u1_struct_0(A_782))
      | ~ m1_subset_1(k5_lattices(A_782),u1_struct_0(A_782))
      | ~ v13_lattices(A_782)
      | ~ l1_lattices(A_782)
      | v2_struct_0(A_782) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6463,plain,(
    ! [A_784] :
      ( k2_lattices(A_784,'#skF_3'(A_784),k5_lattices(A_784)) = k5_lattices(A_784)
      | ~ m1_subset_1(k5_lattices(A_784),u1_struct_0(A_784))
      | ~ v13_lattices(A_784)
      | ~ l1_lattices(A_784)
      | v2_struct_0(A_784) ) ),
    inference(resolution,[status(thm)],[c_58,c_6435])).

tff(c_6467,plain,(
    ! [A_785] :
      ( k2_lattices(A_785,'#skF_3'(A_785),k5_lattices(A_785)) = k5_lattices(A_785)
      | ~ v13_lattices(A_785)
      | ~ l1_lattices(A_785)
      | v2_struct_0(A_785) ) ),
    inference(resolution,[status(thm)],[c_40,c_6463])).

tff(c_6007,plain,(
    ! [A_723,C_724] :
      ( k2_lattices(A_723,'#skF_3'(A_723),C_724) = '#skF_3'(A_723)
      | ~ m1_subset_1(C_724,u1_struct_0(A_723))
      | ~ v13_lattices(A_723)
      | ~ l1_lattices(A_723)
      | v2_struct_0(A_723) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_6025,plain,(
    ! [A_22] :
      ( k2_lattices(A_22,'#skF_3'(A_22),k5_lattices(A_22)) = '#skF_3'(A_22)
      | ~ v13_lattices(A_22)
      | ~ l1_lattices(A_22)
      | v2_struct_0(A_22) ) ),
    inference(resolution,[status(thm)],[c_40,c_6007])).

tff(c_6473,plain,(
    ! [A_785] :
      ( k5_lattices(A_785) = '#skF_3'(A_785)
      | ~ v13_lattices(A_785)
      | ~ l1_lattices(A_785)
      | v2_struct_0(A_785)
      | ~ v13_lattices(A_785)
      | ~ l1_lattices(A_785)
      | v2_struct_0(A_785) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6467,c_6025])).

tff(c_6495,plain,(
    ! [A_787] :
      ( k5_lattices(A_787) = '#skF_3'(A_787)
      | ~ v13_lattices(A_787)
      | ~ l1_lattices(A_787)
      | v2_struct_0(A_787) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_6473])).

tff(c_6498,plain,
    ( k5_lattices('#skF_9') = '#skF_3'('#skF_9')
    | ~ v13_lattices('#skF_9')
    | ~ l1_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_6495,c_106])).

tff(c_6501,plain,(
    k5_lattices('#skF_9') = '#skF_3'('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_5885,c_6498])).

tff(c_5884,plain,(
    k15_lattice3('#skF_9',k1_xboole_0) != k5_lattices('#skF_9') ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_6502,plain,(
    k15_lattice3('#skF_9',k1_xboole_0) != '#skF_3'('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6501,c_5884])).

tff(c_6515,plain,
    ( m1_subset_1('#skF_3'('#skF_9'),u1_struct_0('#skF_9'))
    | ~ l1_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_6501,c_40])).

tff(c_6528,plain,
    ( m1_subset_1('#skF_3'('#skF_9'),u1_struct_0('#skF_9'))
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_6515])).

tff(c_6529,plain,(
    m1_subset_1('#skF_3'('#skF_9'),u1_struct_0('#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_6528])).

tff(c_64,plain,(
    ! [A_45,C_54,B_52] :
      ( k2_lattices(A_45,C_54,B_52) = k2_lattices(A_45,B_52,C_54)
      | ~ m1_subset_1(C_54,u1_struct_0(A_45))
      | ~ m1_subset_1(B_52,u1_struct_0(A_45))
      | ~ v6_lattices(A_45)
      | ~ l1_lattices(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_6566,plain,(
    ! [B_52] :
      ( k2_lattices('#skF_9',B_52,'#skF_3'('#skF_9')) = k2_lattices('#skF_9','#skF_3'('#skF_9'),B_52)
      | ~ m1_subset_1(B_52,u1_struct_0('#skF_9'))
      | ~ v6_lattices('#skF_9')
      | ~ l1_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_6529,c_64])).

tff(c_6585,plain,(
    ! [B_52] :
      ( k2_lattices('#skF_9',B_52,'#skF_3'('#skF_9')) = k2_lattices('#skF_9','#skF_3'('#skF_9'),B_52)
      | ~ m1_subset_1(B_52,u1_struct_0('#skF_9'))
      | ~ v6_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_6566])).

tff(c_6586,plain,(
    ! [B_52] :
      ( k2_lattices('#skF_9',B_52,'#skF_3'('#skF_9')) = k2_lattices('#skF_9','#skF_3'('#skF_9'),B_52)
      | ~ m1_subset_1(B_52,u1_struct_0('#skF_9'))
      | ~ v6_lattices('#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_6585])).

tff(c_6620,plain,(
    ~ v6_lattices('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_6586])).

tff(c_6623,plain,
    ( ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_24,c_6620])).

tff(c_6626,plain,(
    v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_104,c_6623])).

tff(c_6628,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_6626])).

tff(c_6630,plain,(
    v6_lattices('#skF_9') ),
    inference(splitRight,[status(thm)],[c_6586])).

tff(c_7023,plain,(
    ! [A_810,B_811,C_812] :
      ( r1_lattices(A_810,B_811,C_812)
      | k2_lattices(A_810,B_811,C_812) != B_811
      | ~ m1_subset_1(C_812,u1_struct_0(A_810))
      | ~ m1_subset_1(B_811,u1_struct_0(A_810))
      | ~ l3_lattices(A_810)
      | ~ v9_lattices(A_810)
      | ~ v8_lattices(A_810)
      | v2_struct_0(A_810) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_7025,plain,(
    ! [B_811] :
      ( r1_lattices('#skF_9',B_811,'#skF_3'('#skF_9'))
      | k2_lattices('#skF_9',B_811,'#skF_3'('#skF_9')) != B_811
      | ~ m1_subset_1(B_811,u1_struct_0('#skF_9'))
      | ~ l3_lattices('#skF_9')
      | ~ v9_lattices('#skF_9')
      | ~ v8_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_6529,c_7023])).

tff(c_7046,plain,(
    ! [B_811] :
      ( r1_lattices('#skF_9',B_811,'#skF_3'('#skF_9'))
      | k2_lattices('#skF_9',B_811,'#skF_3'('#skF_9')) != B_811
      | ~ m1_subset_1(B_811,u1_struct_0('#skF_9'))
      | ~ v9_lattices('#skF_9')
      | ~ v8_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_7025])).

tff(c_7047,plain,(
    ! [B_811] :
      ( r1_lattices('#skF_9',B_811,'#skF_3'('#skF_9'))
      | k2_lattices('#skF_9',B_811,'#skF_3'('#skF_9')) != B_811
      | ~ m1_subset_1(B_811,u1_struct_0('#skF_9'))
      | ~ v9_lattices('#skF_9')
      | ~ v8_lattices('#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_7046])).

tff(c_7097,plain,(
    ~ v8_lattices('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_7047])).

tff(c_7100,plain,
    ( ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_20,c_7097])).

tff(c_7103,plain,(
    v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_104,c_7100])).

tff(c_7105,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_7103])).

tff(c_7107,plain,(
    v8_lattices('#skF_9') ),
    inference(splitRight,[status(thm)],[c_7047])).

tff(c_7106,plain,(
    ! [B_811] :
      ( ~ v9_lattices('#skF_9')
      | r1_lattices('#skF_9',B_811,'#skF_3'('#skF_9'))
      | k2_lattices('#skF_9',B_811,'#skF_3'('#skF_9')) != B_811
      | ~ m1_subset_1(B_811,u1_struct_0('#skF_9')) ) ),
    inference(splitRight,[status(thm)],[c_7047])).

tff(c_7108,plain,(
    ~ v9_lattices('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_7106])).

tff(c_7111,plain,
    ( ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_18,c_7108])).

tff(c_7114,plain,(
    v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_104,c_7111])).

tff(c_7116,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_7114])).

tff(c_7118,plain,(
    v9_lattices('#skF_9') ),
    inference(splitRight,[status(thm)],[c_7106])).

tff(c_6631,plain,(
    ! [B_793] :
      ( k2_lattices('#skF_9',B_793,'#skF_3'('#skF_9')) = k2_lattices('#skF_9','#skF_3'('#skF_9'),B_793)
      | ~ m1_subset_1(B_793,u1_struct_0('#skF_9')) ) ),
    inference(splitRight,[status(thm)],[c_6586])).

tff(c_6666,plain,(
    ! [B_57] :
      ( k2_lattices('#skF_9',k15_lattice3('#skF_9',B_57),'#skF_3'('#skF_9')) = k2_lattices('#skF_9','#skF_3'('#skF_9'),k15_lattice3('#skF_9',B_57))
      | ~ l3_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_72,c_6631])).

tff(c_6703,plain,(
    ! [B_57] :
      ( k2_lattices('#skF_9',k15_lattice3('#skF_9',B_57),'#skF_3'('#skF_9')) = k2_lattices('#skF_9','#skF_3'('#skF_9'),k15_lattice3('#skF_9',B_57))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_6666])).

tff(c_6709,plain,(
    ! [B_794] : k2_lattices('#skF_9',k15_lattice3('#skF_9',B_794),'#skF_3'('#skF_9')) = k2_lattices('#skF_9','#skF_3'('#skF_9'),k15_lattice3('#skF_9',B_794)) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_6703])).

tff(c_6053,plain,(
    ! [A_728,C_729] :
      ( k2_lattices(A_728,C_729,'#skF_3'(A_728)) = '#skF_3'(A_728)
      | ~ m1_subset_1(C_729,u1_struct_0(A_728))
      | ~ v13_lattices(A_728)
      | ~ l1_lattices(A_728)
      | v2_struct_0(A_728) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_6070,plain,(
    ! [A_56,B_57] :
      ( k2_lattices(A_56,k15_lattice3(A_56,B_57),'#skF_3'(A_56)) = '#skF_3'(A_56)
      | ~ v13_lattices(A_56)
      | ~ l1_lattices(A_56)
      | ~ l3_lattices(A_56)
      | v2_struct_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_72,c_6053])).

tff(c_6715,plain,(
    ! [B_794] :
      ( k2_lattices('#skF_9','#skF_3'('#skF_9'),k15_lattice3('#skF_9',B_794)) = '#skF_3'('#skF_9')
      | ~ v13_lattices('#skF_9')
      | ~ l1_lattices('#skF_9')
      | ~ l3_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6709,c_6070])).

tff(c_6733,plain,(
    ! [B_794] :
      ( k2_lattices('#skF_9','#skF_3'('#skF_9'),k15_lattice3('#skF_9',B_794)) = '#skF_3'('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_122,c_5885,c_6715])).

tff(c_6734,plain,(
    ! [B_794] : k2_lattices('#skF_9','#skF_3'('#skF_9'),k15_lattice3('#skF_9',B_794)) = '#skF_3'('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_6733])).

tff(c_6704,plain,(
    ! [B_57] : k2_lattices('#skF_9',k15_lattice3('#skF_9',B_57),'#skF_3'('#skF_9')) = k2_lattices('#skF_9','#skF_3'('#skF_9'),k15_lattice3('#skF_9',B_57)) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_6703])).

tff(c_6745,plain,(
    ! [B_57] : k2_lattices('#skF_9',k15_lattice3('#skF_9',B_57),'#skF_3'('#skF_9')) = '#skF_3'('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6734,c_6704])).

tff(c_6186,plain,(
    ! [A_753,B_754] :
      ( k15_lattice3(A_753,k6_domain_1(u1_struct_0(A_753),B_754)) = B_754
      | ~ m1_subset_1(B_754,u1_struct_0(A_753))
      | ~ l3_lattices(A_753)
      | ~ v4_lattice3(A_753)
      | ~ v10_lattices(A_753)
      | v2_struct_0(A_753) ) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_92,plain,(
    ! [A_74,B_77,C_78] :
      ( r3_lattices(A_74,k15_lattice3(A_74,B_77),k15_lattice3(A_74,C_78))
      | ~ r1_tarski(B_77,C_78)
      | ~ l3_lattices(A_74)
      | ~ v4_lattice3(A_74)
      | ~ v10_lattices(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_10752,plain,(
    ! [A_1098,B_1099,B_1100] :
      ( r3_lattices(A_1098,k15_lattice3(A_1098,B_1099),B_1100)
      | ~ r1_tarski(B_1099,k6_domain_1(u1_struct_0(A_1098),B_1100))
      | ~ l3_lattices(A_1098)
      | ~ v4_lattice3(A_1098)
      | ~ v10_lattices(A_1098)
      | v2_struct_0(A_1098)
      | ~ m1_subset_1(B_1100,u1_struct_0(A_1098))
      | ~ l3_lattices(A_1098)
      | ~ v4_lattice3(A_1098)
      | ~ v10_lattices(A_1098)
      | v2_struct_0(A_1098) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6186,c_92])).

tff(c_10805,plain,(
    ! [A_1101,B_1102] :
      ( r3_lattices(A_1101,k15_lattice3(A_1101,k1_xboole_0),B_1102)
      | ~ m1_subset_1(B_1102,u1_struct_0(A_1101))
      | ~ l3_lattices(A_1101)
      | ~ v4_lattice3(A_1101)
      | ~ v10_lattices(A_1101)
      | v2_struct_0(A_1101) ) ),
    inference(resolution,[status(thm)],[c_14,c_10752])).

tff(c_11160,plain,(
    ! [A_1129,B_1130] :
      ( r1_lattices(A_1129,k15_lattice3(A_1129,k1_xboole_0),B_1130)
      | ~ m1_subset_1(k15_lattice3(A_1129,k1_xboole_0),u1_struct_0(A_1129))
      | ~ v9_lattices(A_1129)
      | ~ v8_lattices(A_1129)
      | ~ v6_lattices(A_1129)
      | ~ m1_subset_1(B_1130,u1_struct_0(A_1129))
      | ~ l3_lattices(A_1129)
      | ~ v4_lattice3(A_1129)
      | ~ v10_lattices(A_1129)
      | v2_struct_0(A_1129) ) ),
    inference(resolution,[status(thm)],[c_10805,c_48])).

tff(c_11165,plain,(
    ! [A_1131,B_1132] :
      ( r1_lattices(A_1131,k15_lattice3(A_1131,k1_xboole_0),B_1132)
      | ~ v9_lattices(A_1131)
      | ~ v8_lattices(A_1131)
      | ~ v6_lattices(A_1131)
      | ~ m1_subset_1(B_1132,u1_struct_0(A_1131))
      | ~ v4_lattice3(A_1131)
      | ~ v10_lattices(A_1131)
      | ~ l3_lattices(A_1131)
      | v2_struct_0(A_1131) ) ),
    inference(resolution,[status(thm)],[c_72,c_11160])).

tff(c_49278,plain,(
    ! [A_32319,B_32320] :
      ( k2_lattices(A_32319,k15_lattice3(A_32319,k1_xboole_0),B_32320) = k15_lattice3(A_32319,k1_xboole_0)
      | ~ m1_subset_1(k15_lattice3(A_32319,k1_xboole_0),u1_struct_0(A_32319))
      | ~ v9_lattices(A_32319)
      | ~ v8_lattices(A_32319)
      | ~ v6_lattices(A_32319)
      | ~ m1_subset_1(B_32320,u1_struct_0(A_32319))
      | ~ v4_lattice3(A_32319)
      | ~ v10_lattices(A_32319)
      | ~ l3_lattices(A_32319)
      | v2_struct_0(A_32319) ) ),
    inference(resolution,[status(thm)],[c_11165,c_52])).

tff(c_49283,plain,(
    ! [A_32321,B_32322] :
      ( k2_lattices(A_32321,k15_lattice3(A_32321,k1_xboole_0),B_32322) = k15_lattice3(A_32321,k1_xboole_0)
      | ~ v9_lattices(A_32321)
      | ~ v8_lattices(A_32321)
      | ~ v6_lattices(A_32321)
      | ~ m1_subset_1(B_32322,u1_struct_0(A_32321))
      | ~ v4_lattice3(A_32321)
      | ~ v10_lattices(A_32321)
      | ~ l3_lattices(A_32321)
      | v2_struct_0(A_32321) ) ),
    inference(resolution,[status(thm)],[c_72,c_49278])).

tff(c_49285,plain,
    ( k2_lattices('#skF_9',k15_lattice3('#skF_9',k1_xboole_0),'#skF_3'('#skF_9')) = k15_lattice3('#skF_9',k1_xboole_0)
    | ~ v9_lattices('#skF_9')
    | ~ v8_lattices('#skF_9')
    | ~ v6_lattices('#skF_9')
    | ~ v4_lattice3('#skF_9')
    | ~ v10_lattices('#skF_9')
    | ~ l3_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_6529,c_49283])).

tff(c_49306,plain,
    ( k15_lattice3('#skF_9',k1_xboole_0) = '#skF_3'('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_104,c_102,c_6630,c_7107,c_7118,c_6745,c_49285])).

tff(c_49308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_6502,c_49306])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:30:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 26.73/15.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.73/15.41  
% 26.73/15.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.73/15.42  %$ r3_lattices > r1_lattices > r2_hidden > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k6_domain_1 > k16_lattice3 > k15_lattice3 > a_2_6_lattice3 > a_2_5_lattice3 > #nlpp > u1_struct_0 > k5_lattices > k1_xboole_0 > #skF_5 > #skF_9 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_1 > #skF_6 > #skF_4
% 26.73/15.42  
% 26.73/15.42  %Foreground sorts:
% 26.73/15.42  
% 26.73/15.42  
% 26.73/15.42  %Background operators:
% 26.73/15.42  
% 26.73/15.42  
% 26.73/15.42  %Foreground operators:
% 26.73/15.42  tff(l3_lattices, type, l3_lattices: $i > $o).
% 26.73/15.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 26.73/15.42  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 26.73/15.42  tff('#skF_5', type, '#skF_5': $i > $i).
% 26.73/15.42  tff(l2_lattices, type, l2_lattices: $i > $o).
% 26.73/15.42  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 26.73/15.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 26.73/15.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 26.73/15.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 26.73/15.42  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 26.73/15.42  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 26.73/15.42  tff(l1_lattices, type, l1_lattices: $i > $o).
% 26.73/15.42  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 26.73/15.42  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 26.73/15.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 26.73/15.42  tff(v4_lattices, type, v4_lattices: $i > $o).
% 26.73/15.42  tff(v6_lattices, type, v6_lattices: $i > $o).
% 26.73/15.42  tff(v9_lattices, type, v9_lattices: $i > $o).
% 26.73/15.42  tff(a_2_5_lattice3, type, a_2_5_lattice3: ($i * $i) > $i).
% 26.73/15.42  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 26.73/15.42  tff(v5_lattices, type, v5_lattices: $i > $o).
% 26.73/15.42  tff(v10_lattices, type, v10_lattices: $i > $o).
% 26.73/15.42  tff('#skF_9', type, '#skF_9': $i).
% 26.73/15.42  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 26.73/15.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 26.73/15.42  tff(v13_lattices, type, v13_lattices: $i > $o).
% 26.73/15.42  tff('#skF_3', type, '#skF_3': $i > $i).
% 26.73/15.42  tff(v8_lattices, type, v8_lattices: $i > $o).
% 26.73/15.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 26.73/15.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 26.73/15.42  tff(k5_lattices, type, k5_lattices: $i > $i).
% 26.73/15.42  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 26.73/15.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 26.73/15.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 26.73/15.42  tff(a_2_6_lattice3, type, a_2_6_lattice3: ($i * $i) > $i).
% 26.73/15.42  tff('#skF_6', type, '#skF_6': $i > $i).
% 26.73/15.42  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 26.73/15.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 26.73/15.42  tff(v7_lattices, type, v7_lattices: $i > $o).
% 26.73/15.42  
% 26.92/15.45  tff(f_266, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v13_lattices(A)) & l3_lattices(A)) & (k5_lattices(A) = k15_lattice3(A, k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_lattice3)).
% 26.92/15.45  tff(f_99, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 26.92/15.45  tff(f_176, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k15_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 26.92/15.45  tff(f_154, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) <=> (?[B]: (m1_subset_1(B, u1_struct_0(A)) & (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_lattices)).
% 26.92/15.45  tff(f_215, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((k15_lattice3(A, k6_domain_1(u1_struct_0(A), B)) = B) & (k16_lattice3(A, k6_domain_1(u1_struct_0(A), B)) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_lattice3)).
% 26.92/15.45  tff(f_67, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 26.92/15.45  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 26.92/15.45  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 26.92/15.45  tff(f_199, axiom, (![A, B, C]: ((((~v2_struct_0(B) & v10_lattices(B)) & v4_lattice3(B)) & l3_lattices(B)) => (r2_hidden(A, a_2_5_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r3_lattices(B, D, E)) & r2_hidden(E, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_5_lattice3)).
% 26.92/15.45  tff(f_45, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 26.92/15.45  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 26.92/15.45  tff(f_245, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: ((k15_lattice3(A, B) = k15_lattice3(A, a_2_5_lattice3(A, B))) & (k16_lattice3(A, B) = k16_lattice3(A, a_2_6_lattice3(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_lattice3)).
% 26.92/15.45  tff(f_93, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => m1_subset_1(k5_lattices(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_lattices)).
% 26.92/15.45  tff(f_169, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v6_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, C) = k2_lattices(A, C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_lattices)).
% 26.92/15.45  tff(f_231, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (r1_tarski(B, C) => (r3_lattices(A, k15_lattice3(A, B), k15_lattice3(A, C)) & r3_lattices(A, k16_lattice3(A, C), k16_lattice3(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_lattice3)).
% 26.92/15.45  tff(f_118, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 26.92/15.45  tff(f_137, axiom, (![A]: ((((~v2_struct_0(A) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k2_lattices(A, B, C) = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_lattices)).
% 26.92/15.45  tff(f_86, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((B = k5_lattices(A)) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattices)).
% 26.92/15.45  tff(c_106, plain, (~v2_struct_0('#skF_9')), inference(cnfTransformation, [status(thm)], [f_266])).
% 26.92/15.45  tff(c_100, plain, (l3_lattices('#skF_9')), inference(cnfTransformation, [status(thm)], [f_266])).
% 26.92/15.45  tff(c_118, plain, (![A_85]: (l1_lattices(A_85) | ~l3_lattices(A_85))), inference(cnfTransformation, [status(thm)], [f_99])).
% 26.92/15.45  tff(c_122, plain, (l1_lattices('#skF_9')), inference(resolution, [status(thm)], [c_100, c_118])).
% 26.92/15.45  tff(c_72, plain, (![A_56, B_57]: (m1_subset_1(k15_lattice3(A_56, B_57), u1_struct_0(A_56)) | ~l3_lattices(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_176])).
% 26.92/15.45  tff(c_104, plain, (v10_lattices('#skF_9')), inference(cnfTransformation, [status(thm)], [f_266])).
% 26.92/15.45  tff(c_98, plain, (k15_lattice3('#skF_9', k1_xboole_0)!=k5_lattices('#skF_9') | ~l3_lattices('#skF_9') | ~v13_lattices('#skF_9') | ~v10_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(cnfTransformation, [status(thm)], [f_266])).
% 26.92/15.45  tff(c_108, plain, (k15_lattice3('#skF_9', k1_xboole_0)!=k5_lattices('#skF_9') | ~v13_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_100, c_98])).
% 26.92/15.45  tff(c_109, plain, (k15_lattice3('#skF_9', k1_xboole_0)!=k5_lattices('#skF_9') | ~v13_lattices('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_106, c_108])).
% 26.92/15.45  tff(c_124, plain, (~v13_lattices('#skF_9')), inference(splitLeft, [status(thm)], [c_109])).
% 26.92/15.45  tff(c_56, plain, (![A_34, B_43]: (m1_subset_1('#skF_4'(A_34, B_43), u1_struct_0(A_34)) | v13_lattices(A_34) | ~m1_subset_1(B_43, u1_struct_0(A_34)) | ~l1_lattices(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_154])).
% 26.92/15.45  tff(c_102, plain, (v4_lattice3('#skF_9')), inference(cnfTransformation, [status(thm)], [f_266])).
% 26.92/15.45  tff(c_88, plain, (![A_71, B_73]: (k15_lattice3(A_71, k6_domain_1(u1_struct_0(A_71), B_73))=B_73 | ~m1_subset_1(B_73, u1_struct_0(A_71)) | ~l3_lattices(A_71) | ~v4_lattice3(A_71) | ~v10_lattices(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_215])).
% 26.92/15.45  tff(c_24, plain, (![A_11]: (v6_lattices(A_11) | ~v10_lattices(A_11) | v2_struct_0(A_11) | ~l3_lattices(A_11))), inference(cnfTransformation, [status(thm)], [f_67])).
% 26.92/15.45  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 26.92/15.45  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 26.92/15.45  tff(c_401, plain, (![A_151, B_152, C_153]: (r2_hidden('#skF_8'(A_151, B_152, C_153), C_153) | ~r2_hidden(A_151, a_2_5_lattice3(B_152, C_153)) | ~l3_lattices(B_152) | ~v4_lattice3(B_152) | ~v10_lattices(B_152) | v2_struct_0(B_152))), inference(cnfTransformation, [status(thm)], [f_199])).
% 26.92/15.45  tff(c_16, plain, (![B_10, A_9]: (~r1_tarski(B_10, A_9) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 26.92/15.45  tff(c_456, plain, (![C_164, A_165, B_166]: (~r1_tarski(C_164, '#skF_8'(A_165, B_166, C_164)) | ~r2_hidden(A_165, a_2_5_lattice3(B_166, C_164)) | ~l3_lattices(B_166) | ~v4_lattice3(B_166) | ~v10_lattices(B_166) | v2_struct_0(B_166))), inference(resolution, [status(thm)], [c_401, c_16])).
% 26.92/15.45  tff(c_461, plain, (![A_167, B_168]: (~r2_hidden(A_167, a_2_5_lattice3(B_168, k1_xboole_0)) | ~l3_lattices(B_168) | ~v4_lattice3(B_168) | ~v10_lattices(B_168) | v2_struct_0(B_168))), inference(resolution, [status(thm)], [c_14, c_456])).
% 26.92/15.45  tff(c_477, plain, (![B_169, B_170]: (~l3_lattices(B_169) | ~v4_lattice3(B_169) | ~v10_lattices(B_169) | v2_struct_0(B_169) | r1_tarski(a_2_5_lattice3(B_169, k1_xboole_0), B_170))), inference(resolution, [status(thm)], [c_6, c_461])).
% 26.92/15.45  tff(c_126, plain, (![B_89, A_90]: (B_89=A_90 | ~r1_tarski(B_89, A_90) | ~r1_tarski(A_90, B_89))), inference(cnfTransformation, [status(thm)], [f_38])).
% 26.92/15.45  tff(c_135, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_126])).
% 26.92/15.45  tff(c_514, plain, (![B_174]: (a_2_5_lattice3(B_174, k1_xboole_0)=k1_xboole_0 | ~l3_lattices(B_174) | ~v4_lattice3(B_174) | ~v10_lattices(B_174) | v2_struct_0(B_174))), inference(resolution, [status(thm)], [c_477, c_135])).
% 26.92/15.45  tff(c_517, plain, (a_2_5_lattice3('#skF_9', k1_xboole_0)=k1_xboole_0 | ~l3_lattices('#skF_9') | ~v10_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_102, c_514])).
% 26.92/15.45  tff(c_520, plain, (a_2_5_lattice3('#skF_9', k1_xboole_0)=k1_xboole_0 | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_100, c_517])).
% 26.92/15.45  tff(c_521, plain, (a_2_5_lattice3('#skF_9', k1_xboole_0)=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_106, c_520])).
% 26.92/15.45  tff(c_94, plain, (![A_79, B_81]: (k15_lattice3(A_79, a_2_5_lattice3(A_79, B_81))=k15_lattice3(A_79, B_81) | ~l3_lattices(A_79) | ~v4_lattice3(A_79) | ~v10_lattices(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_245])).
% 26.92/15.45  tff(c_40, plain, (![A_22]: (m1_subset_1(k5_lattices(A_22), u1_struct_0(A_22)) | ~l1_lattices(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_93])).
% 26.92/15.45  tff(c_725, plain, (![A_194, C_195, B_196]: (k2_lattices(A_194, C_195, B_196)=k2_lattices(A_194, B_196, C_195) | ~m1_subset_1(C_195, u1_struct_0(A_194)) | ~m1_subset_1(B_196, u1_struct_0(A_194)) | ~v6_lattices(A_194) | ~l1_lattices(A_194) | v2_struct_0(A_194))), inference(cnfTransformation, [status(thm)], [f_169])).
% 26.92/15.45  tff(c_772, plain, (![A_199, B_200]: (k2_lattices(A_199, k5_lattices(A_199), B_200)=k2_lattices(A_199, B_200, k5_lattices(A_199)) | ~m1_subset_1(B_200, u1_struct_0(A_199)) | ~v6_lattices(A_199) | ~l1_lattices(A_199) | v2_struct_0(A_199))), inference(resolution, [status(thm)], [c_40, c_725])).
% 26.92/15.45  tff(c_1227, plain, (![A_265, B_266]: (k2_lattices(A_265, k15_lattice3(A_265, B_266), k5_lattices(A_265))=k2_lattices(A_265, k5_lattices(A_265), k15_lattice3(A_265, B_266)) | ~v6_lattices(A_265) | ~l1_lattices(A_265) | ~l3_lattices(A_265) | v2_struct_0(A_265))), inference(resolution, [status(thm)], [c_72, c_772])).
% 26.92/15.45  tff(c_3307, plain, (![A_535, B_536]: (k2_lattices(A_535, k5_lattices(A_535), k15_lattice3(A_535, a_2_5_lattice3(A_535, B_536)))=k2_lattices(A_535, k15_lattice3(A_535, B_536), k5_lattices(A_535)) | ~v6_lattices(A_535) | ~l1_lattices(A_535) | ~l3_lattices(A_535) | v2_struct_0(A_535) | ~l3_lattices(A_535) | ~v4_lattice3(A_535) | ~v10_lattices(A_535) | v2_struct_0(A_535))), inference(superposition, [status(thm), theory('equality')], [c_94, c_1227])).
% 26.92/15.45  tff(c_3329, plain, (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), k5_lattices('#skF_9'))=k2_lattices('#skF_9', k5_lattices('#skF_9'), k15_lattice3('#skF_9', k1_xboole_0)) | ~v6_lattices('#skF_9') | ~l1_lattices('#skF_9') | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9') | ~l3_lattices('#skF_9') | ~v4_lattice3('#skF_9') | ~v10_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_521, c_3307])).
% 26.92/15.45  tff(c_3336, plain, (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), k5_lattices('#skF_9'))=k2_lattices('#skF_9', k5_lattices('#skF_9'), k15_lattice3('#skF_9', k1_xboole_0)) | ~v6_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_100, c_100, c_122, c_3329])).
% 26.92/15.45  tff(c_3337, plain, (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), k5_lattices('#skF_9'))=k2_lattices('#skF_9', k5_lattices('#skF_9'), k15_lattice3('#skF_9', k1_xboole_0)) | ~v6_lattices('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_106, c_3336])).
% 26.92/15.45  tff(c_3338, plain, (~v6_lattices('#skF_9')), inference(splitLeft, [status(thm)], [c_3337])).
% 26.92/15.45  tff(c_3341, plain, (~v10_lattices('#skF_9') | v2_struct_0('#skF_9') | ~l3_lattices('#skF_9')), inference(resolution, [status(thm)], [c_24, c_3338])).
% 26.92/15.45  tff(c_3344, plain, (v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_104, c_3341])).
% 26.92/15.45  tff(c_3346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_3344])).
% 26.92/15.45  tff(c_3348, plain, (v6_lattices('#skF_9')), inference(splitRight, [status(thm)], [c_3337])).
% 26.92/15.45  tff(c_20, plain, (![A_11]: (v8_lattices(A_11) | ~v10_lattices(A_11) | v2_struct_0(A_11) | ~l3_lattices(A_11))), inference(cnfTransformation, [status(thm)], [f_67])).
% 26.92/15.45  tff(c_421, plain, (![A_156, B_157, C_158]: (r3_lattices(A_156, k15_lattice3(A_156, B_157), k15_lattice3(A_156, C_158)) | ~r1_tarski(B_157, C_158) | ~l3_lattices(A_156) | ~v4_lattice3(A_156) | ~v10_lattices(A_156) | v2_struct_0(A_156))), inference(cnfTransformation, [status(thm)], [f_231])).
% 26.92/15.45  tff(c_2921, plain, (![A_457, B_458, B_459]: (r3_lattices(A_457, k15_lattice3(A_457, B_458), B_459) | ~r1_tarski(B_458, k6_domain_1(u1_struct_0(A_457), B_459)) | ~l3_lattices(A_457) | ~v4_lattice3(A_457) | ~v10_lattices(A_457) | v2_struct_0(A_457) | ~m1_subset_1(B_459, u1_struct_0(A_457)) | ~l3_lattices(A_457) | ~v4_lattice3(A_457) | ~v10_lattices(A_457) | v2_struct_0(A_457))), inference(superposition, [status(thm), theory('equality')], [c_88, c_421])).
% 26.92/15.45  tff(c_2954, plain, (![A_460, B_461]: (r3_lattices(A_460, k15_lattice3(A_460, k1_xboole_0), B_461) | ~m1_subset_1(B_461, u1_struct_0(A_460)) | ~l3_lattices(A_460) | ~v4_lattice3(A_460) | ~v10_lattices(A_460) | v2_struct_0(A_460))), inference(resolution, [status(thm)], [c_14, c_2921])).
% 26.92/15.45  tff(c_48, plain, (![A_24, B_25, C_26]: (r1_lattices(A_24, B_25, C_26) | ~r3_lattices(A_24, B_25, C_26) | ~m1_subset_1(C_26, u1_struct_0(A_24)) | ~m1_subset_1(B_25, u1_struct_0(A_24)) | ~l3_lattices(A_24) | ~v9_lattices(A_24) | ~v8_lattices(A_24) | ~v6_lattices(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_118])).
% 26.92/15.45  tff(c_3128, plain, (![A_492, B_493]: (r1_lattices(A_492, k15_lattice3(A_492, k1_xboole_0), B_493) | ~m1_subset_1(k15_lattice3(A_492, k1_xboole_0), u1_struct_0(A_492)) | ~v9_lattices(A_492) | ~v8_lattices(A_492) | ~v6_lattices(A_492) | ~m1_subset_1(B_493, u1_struct_0(A_492)) | ~l3_lattices(A_492) | ~v4_lattice3(A_492) | ~v10_lattices(A_492) | v2_struct_0(A_492))), inference(resolution, [status(thm)], [c_2954, c_48])).
% 26.92/15.45  tff(c_3133, plain, (![A_494, B_495]: (r1_lattices(A_494, k15_lattice3(A_494, k1_xboole_0), B_495) | ~v9_lattices(A_494) | ~v8_lattices(A_494) | ~v6_lattices(A_494) | ~m1_subset_1(B_495, u1_struct_0(A_494)) | ~v4_lattice3(A_494) | ~v10_lattices(A_494) | ~l3_lattices(A_494) | v2_struct_0(A_494))), inference(resolution, [status(thm)], [c_72, c_3128])).
% 26.92/15.45  tff(c_52, plain, (![A_27, B_31, C_33]: (k2_lattices(A_27, B_31, C_33)=B_31 | ~r1_lattices(A_27, B_31, C_33) | ~m1_subset_1(C_33, u1_struct_0(A_27)) | ~m1_subset_1(B_31, u1_struct_0(A_27)) | ~l3_lattices(A_27) | ~v9_lattices(A_27) | ~v8_lattices(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_137])).
% 26.92/15.45  tff(c_4070, plain, (![A_586, B_587]: (k2_lattices(A_586, k15_lattice3(A_586, k1_xboole_0), B_587)=k15_lattice3(A_586, k1_xboole_0) | ~m1_subset_1(k15_lattice3(A_586, k1_xboole_0), u1_struct_0(A_586)) | ~v9_lattices(A_586) | ~v8_lattices(A_586) | ~v6_lattices(A_586) | ~m1_subset_1(B_587, u1_struct_0(A_586)) | ~v4_lattice3(A_586) | ~v10_lattices(A_586) | ~l3_lattices(A_586) | v2_struct_0(A_586))), inference(resolution, [status(thm)], [c_3133, c_52])).
% 26.92/15.45  tff(c_4075, plain, (![A_588, B_589]: (k2_lattices(A_588, k15_lattice3(A_588, k1_xboole_0), B_589)=k15_lattice3(A_588, k1_xboole_0) | ~v9_lattices(A_588) | ~v8_lattices(A_588) | ~v6_lattices(A_588) | ~m1_subset_1(B_589, u1_struct_0(A_588)) | ~v4_lattice3(A_588) | ~v10_lattices(A_588) | ~l3_lattices(A_588) | v2_struct_0(A_588))), inference(resolution, [status(thm)], [c_72, c_4070])).
% 26.92/15.45  tff(c_4145, plain, (![A_592]: (k2_lattices(A_592, k15_lattice3(A_592, k1_xboole_0), k5_lattices(A_592))=k15_lattice3(A_592, k1_xboole_0) | ~v9_lattices(A_592) | ~v8_lattices(A_592) | ~v6_lattices(A_592) | ~v4_lattice3(A_592) | ~v10_lattices(A_592) | ~l3_lattices(A_592) | ~l1_lattices(A_592) | v2_struct_0(A_592))), inference(resolution, [status(thm)], [c_40, c_4075])).
% 26.92/15.45  tff(c_3347, plain, (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), k5_lattices('#skF_9'))=k2_lattices('#skF_9', k5_lattices('#skF_9'), k15_lattice3('#skF_9', k1_xboole_0))), inference(splitRight, [status(thm)], [c_3337])).
% 26.92/15.45  tff(c_4151, plain, (k2_lattices('#skF_9', k5_lattices('#skF_9'), k15_lattice3('#skF_9', k1_xboole_0))=k15_lattice3('#skF_9', k1_xboole_0) | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9') | ~v6_lattices('#skF_9') | ~v4_lattice3('#skF_9') | ~v10_lattices('#skF_9') | ~l3_lattices('#skF_9') | ~l1_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_4145, c_3347])).
% 26.92/15.45  tff(c_4174, plain, (k2_lattices('#skF_9', k5_lattices('#skF_9'), k15_lattice3('#skF_9', k1_xboole_0))=k15_lattice3('#skF_9', k1_xboole_0) | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_100, c_104, c_102, c_3348, c_4151])).
% 26.92/15.45  tff(c_4175, plain, (k2_lattices('#skF_9', k5_lattices('#skF_9'), k15_lattice3('#skF_9', k1_xboole_0))=k15_lattice3('#skF_9', k1_xboole_0) | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_106, c_4174])).
% 26.92/15.45  tff(c_4180, plain, (~v8_lattices('#skF_9')), inference(splitLeft, [status(thm)], [c_4175])).
% 26.92/15.45  tff(c_4211, plain, (~v10_lattices('#skF_9') | v2_struct_0('#skF_9') | ~l3_lattices('#skF_9')), inference(resolution, [status(thm)], [c_20, c_4180])).
% 26.92/15.45  tff(c_4214, plain, (v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_104, c_4211])).
% 26.92/15.45  tff(c_4216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_4214])).
% 26.92/15.45  tff(c_4218, plain, (v8_lattices('#skF_9')), inference(splitRight, [status(thm)], [c_4175])).
% 26.92/15.45  tff(c_18, plain, (![A_11]: (v9_lattices(A_11) | ~v10_lattices(A_11) | v2_struct_0(A_11) | ~l3_lattices(A_11))), inference(cnfTransformation, [status(thm)], [f_67])).
% 26.92/15.45  tff(c_4217, plain, (~v9_lattices('#skF_9') | k2_lattices('#skF_9', k5_lattices('#skF_9'), k15_lattice3('#skF_9', k1_xboole_0))=k15_lattice3('#skF_9', k1_xboole_0)), inference(splitRight, [status(thm)], [c_4175])).
% 26.92/15.45  tff(c_4219, plain, (~v9_lattices('#skF_9')), inference(splitLeft, [status(thm)], [c_4217])).
% 26.92/15.45  tff(c_4225, plain, (~v10_lattices('#skF_9') | v2_struct_0('#skF_9') | ~l3_lattices('#skF_9')), inference(resolution, [status(thm)], [c_18, c_4219])).
% 26.92/15.45  tff(c_4228, plain, (v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_104, c_4225])).
% 26.92/15.45  tff(c_4230, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_4228])).
% 26.92/15.45  tff(c_4232, plain, (v9_lattices('#skF_9')), inference(splitRight, [status(thm)], [c_4217])).
% 26.92/15.45  tff(c_1530, plain, (![A_291, B_292, B_293]: (k2_lattices(A_291, k15_lattice3(A_291, B_292), B_293)=k2_lattices(A_291, B_293, k15_lattice3(A_291, B_292)) | ~m1_subset_1(B_293, u1_struct_0(A_291)) | ~v6_lattices(A_291) | ~l1_lattices(A_291) | ~l3_lattices(A_291) | v2_struct_0(A_291))), inference(resolution, [status(thm)], [c_72, c_725])).
% 26.92/15.45  tff(c_1584, plain, (![A_298, B_300, B_299]: (k2_lattices(A_298, k15_lattice3(A_298, B_300), k15_lattice3(A_298, B_299))=k2_lattices(A_298, k15_lattice3(A_298, B_299), k15_lattice3(A_298, B_300)) | ~v6_lattices(A_298) | ~l1_lattices(A_298) | ~l3_lattices(A_298) | v2_struct_0(A_298))), inference(resolution, [status(thm)], [c_72, c_1530])).
% 26.92/15.45  tff(c_4956, plain, (![A_649, B_650, B_651]: (k2_lattices(A_649, k15_lattice3(A_649, a_2_5_lattice3(A_649, B_650)), k15_lattice3(A_649, B_651))=k2_lattices(A_649, k15_lattice3(A_649, B_651), k15_lattice3(A_649, B_650)) | ~v6_lattices(A_649) | ~l1_lattices(A_649) | ~l3_lattices(A_649) | v2_struct_0(A_649) | ~l3_lattices(A_649) | ~v4_lattice3(A_649) | ~v10_lattices(A_649) | v2_struct_0(A_649))), inference(superposition, [status(thm), theory('equality')], [c_94, c_1584])).
% 26.92/15.45  tff(c_5011, plain, (![B_651]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), k15_lattice3('#skF_9', B_651))=k2_lattices('#skF_9', k15_lattice3('#skF_9', B_651), k15_lattice3('#skF_9', k1_xboole_0)) | ~v6_lattices('#skF_9') | ~l1_lattices('#skF_9') | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9') | ~l3_lattices('#skF_9') | ~v4_lattice3('#skF_9') | ~v10_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_521, c_4956])).
% 26.92/15.45  tff(c_5024, plain, (![B_651]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), k15_lattice3('#skF_9', B_651))=k2_lattices('#skF_9', k15_lattice3('#skF_9', B_651), k15_lattice3('#skF_9', k1_xboole_0)) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_100, c_100, c_122, c_3348, c_5011])).
% 26.92/15.45  tff(c_5026, plain, (![B_652]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), k15_lattice3('#skF_9', B_652))=k2_lattices('#skF_9', k15_lattice3('#skF_9', B_652), k15_lattice3('#skF_9', k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_106, c_5024])).
% 26.92/15.45  tff(c_4101, plain, (![A_56, B_57]: (k2_lattices(A_56, k15_lattice3(A_56, k1_xboole_0), k15_lattice3(A_56, B_57))=k15_lattice3(A_56, k1_xboole_0) | ~v9_lattices(A_56) | ~v8_lattices(A_56) | ~v6_lattices(A_56) | ~v4_lattice3(A_56) | ~v10_lattices(A_56) | ~l3_lattices(A_56) | v2_struct_0(A_56))), inference(resolution, [status(thm)], [c_72, c_4075])).
% 26.92/15.45  tff(c_5042, plain, (![B_652]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', B_652), k15_lattice3('#skF_9', k1_xboole_0))=k15_lattice3('#skF_9', k1_xboole_0) | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9') | ~v6_lattices('#skF_9') | ~v4_lattice3('#skF_9') | ~v10_lattices('#skF_9') | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_5026, c_4101])).
% 26.92/15.45  tff(c_5110, plain, (![B_652]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', B_652), k15_lattice3('#skF_9', k1_xboole_0))=k15_lattice3('#skF_9', k1_xboole_0) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_104, c_102, c_3348, c_4218, c_4232, c_5042])).
% 26.92/15.45  tff(c_5172, plain, (![B_657]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', B_657), k15_lattice3('#skF_9', k1_xboole_0))=k15_lattice3('#skF_9', k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_106, c_5110])).
% 26.92/15.45  tff(c_5229, plain, (![B_73]: (k2_lattices('#skF_9', B_73, k15_lattice3('#skF_9', k1_xboole_0))=k15_lattice3('#skF_9', k1_xboole_0) | ~m1_subset_1(B_73, u1_struct_0('#skF_9')) | ~l3_lattices('#skF_9') | ~v4_lattice3('#skF_9') | ~v10_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_5172])).
% 26.92/15.45  tff(c_5282, plain, (![B_73]: (k2_lattices('#skF_9', B_73, k15_lattice3('#skF_9', k1_xboole_0))=k15_lattice3('#skF_9', k1_xboole_0) | ~m1_subset_1(B_73, u1_struct_0('#skF_9')) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_100, c_5229])).
% 26.92/15.45  tff(c_5485, plain, (![B_664]: (k2_lattices('#skF_9', B_664, k15_lattice3('#skF_9', k1_xboole_0))=k15_lattice3('#skF_9', k1_xboole_0) | ~m1_subset_1(B_664, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_106, c_5282])).
% 26.92/15.45  tff(c_5501, plain, (![B_43]: (k2_lattices('#skF_9', '#skF_4'('#skF_9', B_43), k15_lattice3('#skF_9', k1_xboole_0))=k15_lattice3('#skF_9', k1_xboole_0) | v13_lattices('#skF_9') | ~m1_subset_1(B_43, u1_struct_0('#skF_9')) | ~l1_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_56, c_5485])).
% 26.92/15.45  tff(c_5536, plain, (![B_43]: (k2_lattices('#skF_9', '#skF_4'('#skF_9', B_43), k15_lattice3('#skF_9', k1_xboole_0))=k15_lattice3('#skF_9', k1_xboole_0) | v13_lattices('#skF_9') | ~m1_subset_1(B_43, u1_struct_0('#skF_9')) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_5501])).
% 26.92/15.45  tff(c_5595, plain, (![B_666]: (k2_lattices('#skF_9', '#skF_4'('#skF_9', B_666), k15_lattice3('#skF_9', k1_xboole_0))=k15_lattice3('#skF_9', k1_xboole_0) | ~m1_subset_1(B_666, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_106, c_124, c_5536])).
% 26.92/15.45  tff(c_54, plain, (![A_34, B_43]: (k2_lattices(A_34, '#skF_4'(A_34, B_43), B_43)!=B_43 | k2_lattices(A_34, B_43, '#skF_4'(A_34, B_43))!=B_43 | v13_lattices(A_34) | ~m1_subset_1(B_43, u1_struct_0(A_34)) | ~l1_lattices(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_154])).
% 26.92/15.45  tff(c_5604, plain, (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), '#skF_4'('#skF_9', k15_lattice3('#skF_9', k1_xboole_0)))!=k15_lattice3('#skF_9', k1_xboole_0) | v13_lattices('#skF_9') | ~l1_lattices('#skF_9') | v2_struct_0('#skF_9') | ~m1_subset_1(k15_lattice3('#skF_9', k1_xboole_0), u1_struct_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_5595, c_54])).
% 26.92/15.45  tff(c_5618, plain, (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), '#skF_4'('#skF_9', k15_lattice3('#skF_9', k1_xboole_0)))!=k15_lattice3('#skF_9', k1_xboole_0) | v13_lattices('#skF_9') | v2_struct_0('#skF_9') | ~m1_subset_1(k15_lattice3('#skF_9', k1_xboole_0), u1_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_5604])).
% 26.92/15.45  tff(c_5619, plain, (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), '#skF_4'('#skF_9', k15_lattice3('#skF_9', k1_xboole_0)))!=k15_lattice3('#skF_9', k1_xboole_0) | ~m1_subset_1(k15_lattice3('#skF_9', k1_xboole_0), u1_struct_0('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_106, c_124, c_5618])).
% 26.92/15.45  tff(c_5729, plain, (~m1_subset_1(k15_lattice3('#skF_9', k1_xboole_0), u1_struct_0('#skF_9'))), inference(splitLeft, [status(thm)], [c_5619])).
% 26.92/15.45  tff(c_5732, plain, (~l3_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_72, c_5729])).
% 26.92/15.45  tff(c_5735, plain, (v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_5732])).
% 26.92/15.45  tff(c_5737, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_5735])).
% 26.92/15.45  tff(c_5739, plain, (m1_subset_1(k15_lattice3('#skF_9', k1_xboole_0), u1_struct_0('#skF_9'))), inference(splitRight, [status(thm)], [c_5619])).
% 26.92/15.45  tff(c_5111, plain, (![B_652]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', B_652), k15_lattice3('#skF_9', k1_xboole_0))=k15_lattice3('#skF_9', k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_106, c_5110])).
% 26.92/15.45  tff(c_5025, plain, (![B_651]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), k15_lattice3('#skF_9', B_651))=k2_lattices('#skF_9', k15_lattice3('#skF_9', B_651), k15_lattice3('#skF_9', k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_106, c_5024])).
% 26.92/15.45  tff(c_5288, plain, (![B_658]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), k15_lattice3('#skF_9', B_658))=k15_lattice3('#skF_9', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_5111, c_5025])).
% 26.92/15.45  tff(c_5343, plain, (![B_73]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), B_73)=k15_lattice3('#skF_9', k1_xboole_0) | ~m1_subset_1(B_73, u1_struct_0('#skF_9')) | ~l3_lattices('#skF_9') | ~v4_lattice3('#skF_9') | ~v10_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_5288])).
% 26.92/15.45  tff(c_5392, plain, (![B_73]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), B_73)=k15_lattice3('#skF_9', k1_xboole_0) | ~m1_subset_1(B_73, u1_struct_0('#skF_9')) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_100, c_5343])).
% 26.92/15.45  tff(c_5412, plain, (![B_663]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), B_663)=k15_lattice3('#skF_9', k1_xboole_0) | ~m1_subset_1(B_663, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_106, c_5392])).
% 26.92/15.45  tff(c_5428, plain, (![B_43]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), '#skF_4'('#skF_9', B_43))=k15_lattice3('#skF_9', k1_xboole_0) | v13_lattices('#skF_9') | ~m1_subset_1(B_43, u1_struct_0('#skF_9')) | ~l1_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_56, c_5412])).
% 26.92/15.45  tff(c_5463, plain, (![B_43]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), '#skF_4'('#skF_9', B_43))=k15_lattice3('#skF_9', k1_xboole_0) | v13_lattices('#skF_9') | ~m1_subset_1(B_43, u1_struct_0('#skF_9')) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_5428])).
% 26.92/15.45  tff(c_5464, plain, (![B_43]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), '#skF_4'('#skF_9', B_43))=k15_lattice3('#skF_9', k1_xboole_0) | ~m1_subset_1(B_43, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_106, c_124, c_5463])).
% 26.92/15.45  tff(c_5738, plain, (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), '#skF_4'('#skF_9', k15_lattice3('#skF_9', k1_xboole_0)))!=k15_lattice3('#skF_9', k1_xboole_0)), inference(splitRight, [status(thm)], [c_5619])).
% 26.92/15.45  tff(c_5876, plain, (~m1_subset_1(k15_lattice3('#skF_9', k1_xboole_0), u1_struct_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_5464, c_5738])).
% 26.92/15.45  tff(c_5883, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5739, c_5876])).
% 26.92/15.45  tff(c_5885, plain, (v13_lattices('#skF_9')), inference(splitRight, [status(thm)], [c_109])).
% 26.92/15.45  tff(c_58, plain, (![A_34]: (m1_subset_1('#skF_3'(A_34), u1_struct_0(A_34)) | ~v13_lattices(A_34) | ~l1_lattices(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_154])).
% 26.92/15.45  tff(c_6435, plain, (![A_782, C_783]: (k2_lattices(A_782, C_783, k5_lattices(A_782))=k5_lattices(A_782) | ~m1_subset_1(C_783, u1_struct_0(A_782)) | ~m1_subset_1(k5_lattices(A_782), u1_struct_0(A_782)) | ~v13_lattices(A_782) | ~l1_lattices(A_782) | v2_struct_0(A_782))), inference(cnfTransformation, [status(thm)], [f_86])).
% 26.92/15.45  tff(c_6463, plain, (![A_784]: (k2_lattices(A_784, '#skF_3'(A_784), k5_lattices(A_784))=k5_lattices(A_784) | ~m1_subset_1(k5_lattices(A_784), u1_struct_0(A_784)) | ~v13_lattices(A_784) | ~l1_lattices(A_784) | v2_struct_0(A_784))), inference(resolution, [status(thm)], [c_58, c_6435])).
% 26.92/15.45  tff(c_6467, plain, (![A_785]: (k2_lattices(A_785, '#skF_3'(A_785), k5_lattices(A_785))=k5_lattices(A_785) | ~v13_lattices(A_785) | ~l1_lattices(A_785) | v2_struct_0(A_785))), inference(resolution, [status(thm)], [c_40, c_6463])).
% 26.92/15.45  tff(c_6007, plain, (![A_723, C_724]: (k2_lattices(A_723, '#skF_3'(A_723), C_724)='#skF_3'(A_723) | ~m1_subset_1(C_724, u1_struct_0(A_723)) | ~v13_lattices(A_723) | ~l1_lattices(A_723) | v2_struct_0(A_723))), inference(cnfTransformation, [status(thm)], [f_154])).
% 26.92/15.45  tff(c_6025, plain, (![A_22]: (k2_lattices(A_22, '#skF_3'(A_22), k5_lattices(A_22))='#skF_3'(A_22) | ~v13_lattices(A_22) | ~l1_lattices(A_22) | v2_struct_0(A_22))), inference(resolution, [status(thm)], [c_40, c_6007])).
% 26.92/15.45  tff(c_6473, plain, (![A_785]: (k5_lattices(A_785)='#skF_3'(A_785) | ~v13_lattices(A_785) | ~l1_lattices(A_785) | v2_struct_0(A_785) | ~v13_lattices(A_785) | ~l1_lattices(A_785) | v2_struct_0(A_785))), inference(superposition, [status(thm), theory('equality')], [c_6467, c_6025])).
% 26.92/15.45  tff(c_6495, plain, (![A_787]: (k5_lattices(A_787)='#skF_3'(A_787) | ~v13_lattices(A_787) | ~l1_lattices(A_787) | v2_struct_0(A_787))), inference(factorization, [status(thm), theory('equality')], [c_6473])).
% 26.92/15.45  tff(c_6498, plain, (k5_lattices('#skF_9')='#skF_3'('#skF_9') | ~v13_lattices('#skF_9') | ~l1_lattices('#skF_9')), inference(resolution, [status(thm)], [c_6495, c_106])).
% 26.92/15.45  tff(c_6501, plain, (k5_lattices('#skF_9')='#skF_3'('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_5885, c_6498])).
% 26.92/15.45  tff(c_5884, plain, (k15_lattice3('#skF_9', k1_xboole_0)!=k5_lattices('#skF_9')), inference(splitRight, [status(thm)], [c_109])).
% 26.92/15.45  tff(c_6502, plain, (k15_lattice3('#skF_9', k1_xboole_0)!='#skF_3'('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_6501, c_5884])).
% 26.92/15.45  tff(c_6515, plain, (m1_subset_1('#skF_3'('#skF_9'), u1_struct_0('#skF_9')) | ~l1_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_6501, c_40])).
% 26.92/15.45  tff(c_6528, plain, (m1_subset_1('#skF_3'('#skF_9'), u1_struct_0('#skF_9')) | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_6515])).
% 26.92/15.45  tff(c_6529, plain, (m1_subset_1('#skF_3'('#skF_9'), u1_struct_0('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_106, c_6528])).
% 26.92/15.45  tff(c_64, plain, (![A_45, C_54, B_52]: (k2_lattices(A_45, C_54, B_52)=k2_lattices(A_45, B_52, C_54) | ~m1_subset_1(C_54, u1_struct_0(A_45)) | ~m1_subset_1(B_52, u1_struct_0(A_45)) | ~v6_lattices(A_45) | ~l1_lattices(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_169])).
% 26.92/15.45  tff(c_6566, plain, (![B_52]: (k2_lattices('#skF_9', B_52, '#skF_3'('#skF_9'))=k2_lattices('#skF_9', '#skF_3'('#skF_9'), B_52) | ~m1_subset_1(B_52, u1_struct_0('#skF_9')) | ~v6_lattices('#skF_9') | ~l1_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_6529, c_64])).
% 26.92/15.45  tff(c_6585, plain, (![B_52]: (k2_lattices('#skF_9', B_52, '#skF_3'('#skF_9'))=k2_lattices('#skF_9', '#skF_3'('#skF_9'), B_52) | ~m1_subset_1(B_52, u1_struct_0('#skF_9')) | ~v6_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_6566])).
% 26.92/15.45  tff(c_6586, plain, (![B_52]: (k2_lattices('#skF_9', B_52, '#skF_3'('#skF_9'))=k2_lattices('#skF_9', '#skF_3'('#skF_9'), B_52) | ~m1_subset_1(B_52, u1_struct_0('#skF_9')) | ~v6_lattices('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_106, c_6585])).
% 26.92/15.45  tff(c_6620, plain, (~v6_lattices('#skF_9')), inference(splitLeft, [status(thm)], [c_6586])).
% 26.92/15.45  tff(c_6623, plain, (~v10_lattices('#skF_9') | v2_struct_0('#skF_9') | ~l3_lattices('#skF_9')), inference(resolution, [status(thm)], [c_24, c_6620])).
% 26.92/15.45  tff(c_6626, plain, (v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_104, c_6623])).
% 26.92/15.45  tff(c_6628, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_6626])).
% 26.92/15.45  tff(c_6630, plain, (v6_lattices('#skF_9')), inference(splitRight, [status(thm)], [c_6586])).
% 26.92/15.45  tff(c_7023, plain, (![A_810, B_811, C_812]: (r1_lattices(A_810, B_811, C_812) | k2_lattices(A_810, B_811, C_812)!=B_811 | ~m1_subset_1(C_812, u1_struct_0(A_810)) | ~m1_subset_1(B_811, u1_struct_0(A_810)) | ~l3_lattices(A_810) | ~v9_lattices(A_810) | ~v8_lattices(A_810) | v2_struct_0(A_810))), inference(cnfTransformation, [status(thm)], [f_137])).
% 26.92/15.45  tff(c_7025, plain, (![B_811]: (r1_lattices('#skF_9', B_811, '#skF_3'('#skF_9')) | k2_lattices('#skF_9', B_811, '#skF_3'('#skF_9'))!=B_811 | ~m1_subset_1(B_811, u1_struct_0('#skF_9')) | ~l3_lattices('#skF_9') | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_6529, c_7023])).
% 26.92/15.45  tff(c_7046, plain, (![B_811]: (r1_lattices('#skF_9', B_811, '#skF_3'('#skF_9')) | k2_lattices('#skF_9', B_811, '#skF_3'('#skF_9'))!=B_811 | ~m1_subset_1(B_811, u1_struct_0('#skF_9')) | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_7025])).
% 26.92/15.45  tff(c_7047, plain, (![B_811]: (r1_lattices('#skF_9', B_811, '#skF_3'('#skF_9')) | k2_lattices('#skF_9', B_811, '#skF_3'('#skF_9'))!=B_811 | ~m1_subset_1(B_811, u1_struct_0('#skF_9')) | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_106, c_7046])).
% 26.92/15.45  tff(c_7097, plain, (~v8_lattices('#skF_9')), inference(splitLeft, [status(thm)], [c_7047])).
% 26.92/15.45  tff(c_7100, plain, (~v10_lattices('#skF_9') | v2_struct_0('#skF_9') | ~l3_lattices('#skF_9')), inference(resolution, [status(thm)], [c_20, c_7097])).
% 26.92/15.45  tff(c_7103, plain, (v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_104, c_7100])).
% 26.92/15.45  tff(c_7105, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_7103])).
% 26.92/15.45  tff(c_7107, plain, (v8_lattices('#skF_9')), inference(splitRight, [status(thm)], [c_7047])).
% 26.92/15.45  tff(c_7106, plain, (![B_811]: (~v9_lattices('#skF_9') | r1_lattices('#skF_9', B_811, '#skF_3'('#skF_9')) | k2_lattices('#skF_9', B_811, '#skF_3'('#skF_9'))!=B_811 | ~m1_subset_1(B_811, u1_struct_0('#skF_9')))), inference(splitRight, [status(thm)], [c_7047])).
% 26.92/15.45  tff(c_7108, plain, (~v9_lattices('#skF_9')), inference(splitLeft, [status(thm)], [c_7106])).
% 26.92/15.45  tff(c_7111, plain, (~v10_lattices('#skF_9') | v2_struct_0('#skF_9') | ~l3_lattices('#skF_9')), inference(resolution, [status(thm)], [c_18, c_7108])).
% 26.92/15.45  tff(c_7114, plain, (v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_104, c_7111])).
% 26.92/15.45  tff(c_7116, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_7114])).
% 26.92/15.45  tff(c_7118, plain, (v9_lattices('#skF_9')), inference(splitRight, [status(thm)], [c_7106])).
% 26.92/15.45  tff(c_6631, plain, (![B_793]: (k2_lattices('#skF_9', B_793, '#skF_3'('#skF_9'))=k2_lattices('#skF_9', '#skF_3'('#skF_9'), B_793) | ~m1_subset_1(B_793, u1_struct_0('#skF_9')))), inference(splitRight, [status(thm)], [c_6586])).
% 26.92/15.45  tff(c_6666, plain, (![B_57]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', B_57), '#skF_3'('#skF_9'))=k2_lattices('#skF_9', '#skF_3'('#skF_9'), k15_lattice3('#skF_9', B_57)) | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_72, c_6631])).
% 26.92/15.45  tff(c_6703, plain, (![B_57]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', B_57), '#skF_3'('#skF_9'))=k2_lattices('#skF_9', '#skF_3'('#skF_9'), k15_lattice3('#skF_9', B_57)) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_6666])).
% 26.92/15.45  tff(c_6709, plain, (![B_794]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', B_794), '#skF_3'('#skF_9'))=k2_lattices('#skF_9', '#skF_3'('#skF_9'), k15_lattice3('#skF_9', B_794)))), inference(negUnitSimplification, [status(thm)], [c_106, c_6703])).
% 26.92/15.45  tff(c_6053, plain, (![A_728, C_729]: (k2_lattices(A_728, C_729, '#skF_3'(A_728))='#skF_3'(A_728) | ~m1_subset_1(C_729, u1_struct_0(A_728)) | ~v13_lattices(A_728) | ~l1_lattices(A_728) | v2_struct_0(A_728))), inference(cnfTransformation, [status(thm)], [f_154])).
% 26.92/15.45  tff(c_6070, plain, (![A_56, B_57]: (k2_lattices(A_56, k15_lattice3(A_56, B_57), '#skF_3'(A_56))='#skF_3'(A_56) | ~v13_lattices(A_56) | ~l1_lattices(A_56) | ~l3_lattices(A_56) | v2_struct_0(A_56))), inference(resolution, [status(thm)], [c_72, c_6053])).
% 26.92/15.45  tff(c_6715, plain, (![B_794]: (k2_lattices('#skF_9', '#skF_3'('#skF_9'), k15_lattice3('#skF_9', B_794))='#skF_3'('#skF_9') | ~v13_lattices('#skF_9') | ~l1_lattices('#skF_9') | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_6709, c_6070])).
% 26.92/15.45  tff(c_6733, plain, (![B_794]: (k2_lattices('#skF_9', '#skF_3'('#skF_9'), k15_lattice3('#skF_9', B_794))='#skF_3'('#skF_9') | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_122, c_5885, c_6715])).
% 26.92/15.45  tff(c_6734, plain, (![B_794]: (k2_lattices('#skF_9', '#skF_3'('#skF_9'), k15_lattice3('#skF_9', B_794))='#skF_3'('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_106, c_6733])).
% 26.92/15.45  tff(c_6704, plain, (![B_57]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', B_57), '#skF_3'('#skF_9'))=k2_lattices('#skF_9', '#skF_3'('#skF_9'), k15_lattice3('#skF_9', B_57)))), inference(negUnitSimplification, [status(thm)], [c_106, c_6703])).
% 26.92/15.45  tff(c_6745, plain, (![B_57]: (k2_lattices('#skF_9', k15_lattice3('#skF_9', B_57), '#skF_3'('#skF_9'))='#skF_3'('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_6734, c_6704])).
% 26.92/15.45  tff(c_6186, plain, (![A_753, B_754]: (k15_lattice3(A_753, k6_domain_1(u1_struct_0(A_753), B_754))=B_754 | ~m1_subset_1(B_754, u1_struct_0(A_753)) | ~l3_lattices(A_753) | ~v4_lattice3(A_753) | ~v10_lattices(A_753) | v2_struct_0(A_753))), inference(cnfTransformation, [status(thm)], [f_215])).
% 26.92/15.45  tff(c_92, plain, (![A_74, B_77, C_78]: (r3_lattices(A_74, k15_lattice3(A_74, B_77), k15_lattice3(A_74, C_78)) | ~r1_tarski(B_77, C_78) | ~l3_lattices(A_74) | ~v4_lattice3(A_74) | ~v10_lattices(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_231])).
% 26.92/15.45  tff(c_10752, plain, (![A_1098, B_1099, B_1100]: (r3_lattices(A_1098, k15_lattice3(A_1098, B_1099), B_1100) | ~r1_tarski(B_1099, k6_domain_1(u1_struct_0(A_1098), B_1100)) | ~l3_lattices(A_1098) | ~v4_lattice3(A_1098) | ~v10_lattices(A_1098) | v2_struct_0(A_1098) | ~m1_subset_1(B_1100, u1_struct_0(A_1098)) | ~l3_lattices(A_1098) | ~v4_lattice3(A_1098) | ~v10_lattices(A_1098) | v2_struct_0(A_1098))), inference(superposition, [status(thm), theory('equality')], [c_6186, c_92])).
% 26.92/15.45  tff(c_10805, plain, (![A_1101, B_1102]: (r3_lattices(A_1101, k15_lattice3(A_1101, k1_xboole_0), B_1102) | ~m1_subset_1(B_1102, u1_struct_0(A_1101)) | ~l3_lattices(A_1101) | ~v4_lattice3(A_1101) | ~v10_lattices(A_1101) | v2_struct_0(A_1101))), inference(resolution, [status(thm)], [c_14, c_10752])).
% 26.92/15.45  tff(c_11160, plain, (![A_1129, B_1130]: (r1_lattices(A_1129, k15_lattice3(A_1129, k1_xboole_0), B_1130) | ~m1_subset_1(k15_lattice3(A_1129, k1_xboole_0), u1_struct_0(A_1129)) | ~v9_lattices(A_1129) | ~v8_lattices(A_1129) | ~v6_lattices(A_1129) | ~m1_subset_1(B_1130, u1_struct_0(A_1129)) | ~l3_lattices(A_1129) | ~v4_lattice3(A_1129) | ~v10_lattices(A_1129) | v2_struct_0(A_1129))), inference(resolution, [status(thm)], [c_10805, c_48])).
% 26.92/15.45  tff(c_11165, plain, (![A_1131, B_1132]: (r1_lattices(A_1131, k15_lattice3(A_1131, k1_xboole_0), B_1132) | ~v9_lattices(A_1131) | ~v8_lattices(A_1131) | ~v6_lattices(A_1131) | ~m1_subset_1(B_1132, u1_struct_0(A_1131)) | ~v4_lattice3(A_1131) | ~v10_lattices(A_1131) | ~l3_lattices(A_1131) | v2_struct_0(A_1131))), inference(resolution, [status(thm)], [c_72, c_11160])).
% 26.92/15.45  tff(c_49278, plain, (![A_32319, B_32320]: (k2_lattices(A_32319, k15_lattice3(A_32319, k1_xboole_0), B_32320)=k15_lattice3(A_32319, k1_xboole_0) | ~m1_subset_1(k15_lattice3(A_32319, k1_xboole_0), u1_struct_0(A_32319)) | ~v9_lattices(A_32319) | ~v8_lattices(A_32319) | ~v6_lattices(A_32319) | ~m1_subset_1(B_32320, u1_struct_0(A_32319)) | ~v4_lattice3(A_32319) | ~v10_lattices(A_32319) | ~l3_lattices(A_32319) | v2_struct_0(A_32319))), inference(resolution, [status(thm)], [c_11165, c_52])).
% 26.92/15.45  tff(c_49283, plain, (![A_32321, B_32322]: (k2_lattices(A_32321, k15_lattice3(A_32321, k1_xboole_0), B_32322)=k15_lattice3(A_32321, k1_xboole_0) | ~v9_lattices(A_32321) | ~v8_lattices(A_32321) | ~v6_lattices(A_32321) | ~m1_subset_1(B_32322, u1_struct_0(A_32321)) | ~v4_lattice3(A_32321) | ~v10_lattices(A_32321) | ~l3_lattices(A_32321) | v2_struct_0(A_32321))), inference(resolution, [status(thm)], [c_72, c_49278])).
% 26.92/15.45  tff(c_49285, plain, (k2_lattices('#skF_9', k15_lattice3('#skF_9', k1_xboole_0), '#skF_3'('#skF_9'))=k15_lattice3('#skF_9', k1_xboole_0) | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9') | ~v6_lattices('#skF_9') | ~v4_lattice3('#skF_9') | ~v10_lattices('#skF_9') | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_6529, c_49283])).
% 26.92/15.45  tff(c_49306, plain, (k15_lattice3('#skF_9', k1_xboole_0)='#skF_3'('#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_104, c_102, c_6630, c_7107, c_7118, c_6745, c_49285])).
% 26.92/15.45  tff(c_49308, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_6502, c_49306])).
% 26.92/15.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.92/15.45  
% 26.92/15.45  Inference rules
% 26.92/15.45  ----------------------
% 26.92/15.45  #Ref     : 0
% 26.92/15.45  #Sup     : 9077
% 26.92/15.45  #Fact    : 4
% 26.92/15.45  #Define  : 0
% 26.92/15.45  #Split   : 32
% 26.92/15.45  #Chain   : 0
% 26.92/15.45  #Close   : 0
% 26.92/15.45  
% 26.92/15.45  Ordering : KBO
% 26.92/15.45  
% 26.92/15.45  Simplification rules
% 26.92/15.45  ----------------------
% 26.92/15.45  #Subsume      : 4013
% 26.92/15.45  #Demod        : 9983
% 26.92/15.45  #Tautology    : 1441
% 26.92/15.45  #SimpNegUnit  : 2444
% 26.92/15.45  #BackRed      : 4
% 26.92/15.45  
% 26.92/15.45  #Partial instantiations: 18486
% 26.92/15.45  #Strategies tried      : 1
% 26.92/15.45  
% 26.92/15.45  Timing (in seconds)
% 26.92/15.45  ----------------------
% 26.92/15.45  Preprocessing        : 0.42
% 26.92/15.45  Parsing              : 0.22
% 26.92/15.45  CNF conversion       : 0.03
% 26.92/15.45  Main loop            : 14.19
% 26.92/15.45  Inferencing          : 2.09
% 26.92/15.45  Reduction            : 2.10
% 26.92/15.45  Demodulation         : 1.56
% 26.92/15.45  BG Simplification    : 0.20
% 26.92/15.45  Subsumption          : 9.42
% 26.92/15.45  Abstraction          : 0.35
% 26.92/15.45  MUC search           : 0.00
% 26.92/15.45  Cooper               : 0.00
% 26.92/15.45  Total                : 14.67
% 26.92/15.45  Index Insertion      : 0.00
% 26.92/15.45  Index Deletion       : 0.00
% 26.92/15.45  Index Matching       : 0.00
% 26.92/15.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
