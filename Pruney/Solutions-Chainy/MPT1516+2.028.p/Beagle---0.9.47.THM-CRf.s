%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:54 EST 2020

% Result     : Theorem 37.98s
% Output     : CNFRefutation 37.98s
% Verified   : 
% Statistics : Number of formulae       :  180 (1535 expanded)
%              Number of leaves         :   47 ( 539 expanded)
%              Depth                    :   28
%              Number of atoms          :  747 (6737 expanded)
%              Number of equality atoms :   74 ( 821 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r1_lattices > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k16_lattice3 > k15_lattice3 > a_2_4_lattice3 > a_2_3_lattice3 > #nlpp > u1_struct_0 > k5_lattices > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_6 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(a_2_4_lattice3,type,(
    a_2_4_lattice3: ( $i * $i ) > $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff(a_2_3_lattice3,type,(
    a_2_3_lattice3: ( $i * $i ) > $i )).

tff(v4_lattice3,type,(
    v4_lattice3: $i > $o )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_211,negated_conjecture,(
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

tff(f_158,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k15_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

tff(f_81,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_49,axiom,(
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

tff(f_136,axiom,(
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

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_190,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B,C] :
          ( r1_tarski(B,C)
         => ( r3_lattices(A,k15_lattice3(A,B),k15_lattice3(A,C))
            & r3_lattices(A,k16_lattice3(A,C),k16_lattice3(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_lattice3)).

tff(f_100,axiom,(
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

tff(f_119,axiom,(
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

tff(f_174,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( B = k15_lattice3(A,a_2_3_lattice3(A,B))
            & B = k16_lattice3(A,a_2_4_lattice3(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_lattice3)).

tff(f_151,axiom,(
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

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => m1_subset_1(k5_lattices(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

tff(f_68,axiom,(
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

tff(c_76,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_70,plain,(
    l3_lattices('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_58,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(k15_lattice3(A_47,B_48),u1_struct_0(A_47))
      | ~ l3_lattices(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_81,plain,(
    ! [A_58] :
      ( l1_lattices(A_58)
      | ~ l3_lattices(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_85,plain,(
    l1_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_81])).

tff(c_74,plain,(
    v10_lattices('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_68,plain,
    ( k15_lattice3('#skF_6',k1_xboole_0) != k5_lattices('#skF_6')
    | ~ l3_lattices('#skF_6')
    | ~ v13_lattices('#skF_6')
    | ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_78,plain,
    ( k15_lattice3('#skF_6',k1_xboole_0) != k5_lattices('#skF_6')
    | ~ v13_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_68])).

tff(c_79,plain,
    ( k15_lattice3('#skF_6',k1_xboole_0) != k5_lattices('#skF_6')
    | ~ v13_lattices('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_78])).

tff(c_91,plain,(
    ~ v13_lattices('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_72,plain,(
    v4_lattice3('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_10,plain,(
    ! [A_2] :
      ( v6_lattices(A_2)
      | ~ v10_lattices(A_2)
      | v2_struct_0(A_2)
      | ~ l3_lattices(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [A_2] :
      ( v8_lattices(A_2)
      | ~ v10_lattices(A_2)
      | v2_struct_0(A_2)
      | ~ l3_lattices(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [A_2] :
      ( v9_lattices(A_2)
      | ~ v10_lattices(A_2)
      | v2_struct_0(A_2)
      | ~ l3_lattices(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_42,plain,(
    ! [A_25,B_34] :
      ( m1_subset_1('#skF_3'(A_25,B_34),u1_struct_0(A_25))
      | v13_lattices(A_25)
      | ~ m1_subset_1(B_34,u1_struct_0(A_25))
      | ~ l1_lattices(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_66,plain,(
    ! [A_52,B_55,C_56] :
      ( r3_lattices(A_52,k15_lattice3(A_52,B_55),k15_lattice3(A_52,C_56))
      | ~ r1_tarski(B_55,C_56)
      | ~ l3_lattices(A_52)
      | ~ v4_lattice3(A_52)
      | ~ v10_lattices(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_698,plain,(
    ! [A_148,B_149,C_150] :
      ( r1_lattices(A_148,B_149,C_150)
      | ~ r3_lattices(A_148,B_149,C_150)
      | ~ m1_subset_1(C_150,u1_struct_0(A_148))
      | ~ m1_subset_1(B_149,u1_struct_0(A_148))
      | ~ l3_lattices(A_148)
      | ~ v9_lattices(A_148)
      | ~ v8_lattices(A_148)
      | ~ v6_lattices(A_148)
      | v2_struct_0(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2210,plain,(
    ! [A_291,B_292,C_293] :
      ( r1_lattices(A_291,k15_lattice3(A_291,B_292),k15_lattice3(A_291,C_293))
      | ~ m1_subset_1(k15_lattice3(A_291,C_293),u1_struct_0(A_291))
      | ~ m1_subset_1(k15_lattice3(A_291,B_292),u1_struct_0(A_291))
      | ~ v9_lattices(A_291)
      | ~ v8_lattices(A_291)
      | ~ v6_lattices(A_291)
      | ~ r1_tarski(B_292,C_293)
      | ~ l3_lattices(A_291)
      | ~ v4_lattice3(A_291)
      | ~ v10_lattices(A_291)
      | v2_struct_0(A_291) ) ),
    inference(resolution,[status(thm)],[c_66,c_698])).

tff(c_38,plain,(
    ! [A_18,B_22,C_24] :
      ( k2_lattices(A_18,B_22,C_24) = B_22
      | ~ r1_lattices(A_18,B_22,C_24)
      | ~ m1_subset_1(C_24,u1_struct_0(A_18))
      | ~ m1_subset_1(B_22,u1_struct_0(A_18))
      | ~ l3_lattices(A_18)
      | ~ v9_lattices(A_18)
      | ~ v8_lattices(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_3087,plain,(
    ! [A_350,B_351,C_352] :
      ( k2_lattices(A_350,k15_lattice3(A_350,B_351),k15_lattice3(A_350,C_352)) = k15_lattice3(A_350,B_351)
      | ~ m1_subset_1(k15_lattice3(A_350,C_352),u1_struct_0(A_350))
      | ~ m1_subset_1(k15_lattice3(A_350,B_351),u1_struct_0(A_350))
      | ~ v9_lattices(A_350)
      | ~ v8_lattices(A_350)
      | ~ v6_lattices(A_350)
      | ~ r1_tarski(B_351,C_352)
      | ~ l3_lattices(A_350)
      | ~ v4_lattice3(A_350)
      | ~ v10_lattices(A_350)
      | v2_struct_0(A_350) ) ),
    inference(resolution,[status(thm)],[c_2210,c_38])).

tff(c_3105,plain,(
    ! [A_354,B_355,B_356] :
      ( k2_lattices(A_354,k15_lattice3(A_354,B_355),k15_lattice3(A_354,B_356)) = k15_lattice3(A_354,B_355)
      | ~ m1_subset_1(k15_lattice3(A_354,B_355),u1_struct_0(A_354))
      | ~ v9_lattices(A_354)
      | ~ v8_lattices(A_354)
      | ~ v6_lattices(A_354)
      | ~ r1_tarski(B_355,B_356)
      | ~ v4_lattice3(A_354)
      | ~ v10_lattices(A_354)
      | ~ l3_lattices(A_354)
      | v2_struct_0(A_354) ) ),
    inference(resolution,[status(thm)],[c_58,c_3087])).

tff(c_3119,plain,(
    ! [A_357,B_358,B_359] :
      ( k2_lattices(A_357,k15_lattice3(A_357,B_358),k15_lattice3(A_357,B_359)) = k15_lattice3(A_357,B_358)
      | ~ v9_lattices(A_357)
      | ~ v8_lattices(A_357)
      | ~ v6_lattices(A_357)
      | ~ r1_tarski(B_358,B_359)
      | ~ v4_lattice3(A_357)
      | ~ v10_lattices(A_357)
      | ~ l3_lattices(A_357)
      | v2_struct_0(A_357) ) ),
    inference(resolution,[status(thm)],[c_58,c_3105])).

tff(c_243,plain,(
    ! [A_92,B_93] :
      ( k15_lattice3(A_92,a_2_3_lattice3(A_92,B_93)) = B_93
      | ~ m1_subset_1(B_93,u1_struct_0(A_92))
      | ~ l3_lattices(A_92)
      | ~ v4_lattice3(A_92)
      | ~ v10_lattices(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_260,plain,(
    ! [A_47,B_48] :
      ( k15_lattice3(A_47,a_2_3_lattice3(A_47,k15_lattice3(A_47,B_48))) = k15_lattice3(A_47,B_48)
      | ~ v4_lattice3(A_47)
      | ~ v10_lattices(A_47)
      | ~ l3_lattices(A_47)
      | v2_struct_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_58,c_243])).

tff(c_614,plain,(
    ! [A_132,B_133,C_134] :
      ( r1_lattices(A_132,B_133,C_134)
      | k2_lattices(A_132,B_133,C_134) != B_133
      | ~ m1_subset_1(C_134,u1_struct_0(A_132))
      | ~ m1_subset_1(B_133,u1_struct_0(A_132))
      | ~ l3_lattices(A_132)
      | ~ v9_lattices(A_132)
      | ~ v8_lattices(A_132)
      | v2_struct_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_936,plain,(
    ! [A_176,B_177,B_178] :
      ( r1_lattices(A_176,B_177,k15_lattice3(A_176,B_178))
      | k2_lattices(A_176,B_177,k15_lattice3(A_176,B_178)) != B_177
      | ~ m1_subset_1(B_177,u1_struct_0(A_176))
      | ~ v9_lattices(A_176)
      | ~ v8_lattices(A_176)
      | ~ l3_lattices(A_176)
      | v2_struct_0(A_176) ) ),
    inference(resolution,[status(thm)],[c_58,c_614])).

tff(c_947,plain,(
    ! [A_47,B_177,B_48] :
      ( r1_lattices(A_47,B_177,k15_lattice3(A_47,B_48))
      | k2_lattices(A_47,B_177,k15_lattice3(A_47,a_2_3_lattice3(A_47,k15_lattice3(A_47,B_48)))) != B_177
      | ~ m1_subset_1(B_177,u1_struct_0(A_47))
      | ~ v9_lattices(A_47)
      | ~ v8_lattices(A_47)
      | ~ l3_lattices(A_47)
      | v2_struct_0(A_47)
      | ~ v4_lattice3(A_47)
      | ~ v10_lattices(A_47)
      | ~ l3_lattices(A_47)
      | v2_struct_0(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_936])).

tff(c_3256,plain,(
    ! [A_362,B_363,B_364] :
      ( r1_lattices(A_362,k15_lattice3(A_362,B_363),k15_lattice3(A_362,B_364))
      | ~ m1_subset_1(k15_lattice3(A_362,B_363),u1_struct_0(A_362))
      | ~ v9_lattices(A_362)
      | ~ v8_lattices(A_362)
      | ~ v6_lattices(A_362)
      | ~ r1_tarski(B_363,a_2_3_lattice3(A_362,k15_lattice3(A_362,B_364)))
      | ~ v4_lattice3(A_362)
      | ~ v10_lattices(A_362)
      | ~ l3_lattices(A_362)
      | v2_struct_0(A_362) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3119,c_947])).

tff(c_737,plain,(
    ! [A_157,B_158,C_159] :
      ( r3_lattices(A_157,B_158,C_159)
      | ~ r1_lattices(A_157,B_158,C_159)
      | ~ m1_subset_1(C_159,u1_struct_0(A_157))
      | ~ m1_subset_1(B_158,u1_struct_0(A_157))
      | ~ l3_lattices(A_157)
      | ~ v9_lattices(A_157)
      | ~ v8_lattices(A_157)
      | ~ v6_lattices(A_157)
      | v2_struct_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_953,plain,(
    ! [A_181,B_182,B_183] :
      ( r3_lattices(A_181,B_182,k15_lattice3(A_181,B_183))
      | ~ r1_lattices(A_181,B_182,k15_lattice3(A_181,B_183))
      | ~ m1_subset_1(B_182,u1_struct_0(A_181))
      | ~ v9_lattices(A_181)
      | ~ v8_lattices(A_181)
      | ~ v6_lattices(A_181)
      | ~ l3_lattices(A_181)
      | v2_struct_0(A_181) ) ),
    inference(resolution,[status(thm)],[c_58,c_737])).

tff(c_964,plain,(
    ! [A_47,B_182,B_48] :
      ( r3_lattices(A_47,B_182,k15_lattice3(A_47,B_48))
      | ~ r1_lattices(A_47,B_182,k15_lattice3(A_47,a_2_3_lattice3(A_47,k15_lattice3(A_47,B_48))))
      | ~ m1_subset_1(B_182,u1_struct_0(A_47))
      | ~ v9_lattices(A_47)
      | ~ v8_lattices(A_47)
      | ~ v6_lattices(A_47)
      | ~ l3_lattices(A_47)
      | v2_struct_0(A_47)
      | ~ v4_lattice3(A_47)
      | ~ v10_lattices(A_47)
      | ~ l3_lattices(A_47)
      | v2_struct_0(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_953])).

tff(c_3850,plain,(
    ! [A_405,B_406,B_407] :
      ( r3_lattices(A_405,k15_lattice3(A_405,B_406),k15_lattice3(A_405,B_407))
      | ~ m1_subset_1(k15_lattice3(A_405,B_406),u1_struct_0(A_405))
      | ~ v9_lattices(A_405)
      | ~ v8_lattices(A_405)
      | ~ v6_lattices(A_405)
      | ~ r1_tarski(B_406,a_2_3_lattice3(A_405,k15_lattice3(A_405,a_2_3_lattice3(A_405,k15_lattice3(A_405,B_407)))))
      | ~ v4_lattice3(A_405)
      | ~ v10_lattices(A_405)
      | ~ l3_lattices(A_405)
      | v2_struct_0(A_405) ) ),
    inference(resolution,[status(thm)],[c_3256,c_964])).

tff(c_3874,plain,(
    ! [A_408,B_409] :
      ( r3_lattices(A_408,k15_lattice3(A_408,k1_xboole_0),k15_lattice3(A_408,B_409))
      | ~ m1_subset_1(k15_lattice3(A_408,k1_xboole_0),u1_struct_0(A_408))
      | ~ v9_lattices(A_408)
      | ~ v8_lattices(A_408)
      | ~ v6_lattices(A_408)
      | ~ v4_lattice3(A_408)
      | ~ v10_lattices(A_408)
      | ~ l3_lattices(A_408)
      | v2_struct_0(A_408) ) ),
    inference(resolution,[status(thm)],[c_2,c_3850])).

tff(c_34,plain,(
    ! [A_15,B_16,C_17] :
      ( r1_lattices(A_15,B_16,C_17)
      | ~ r3_lattices(A_15,B_16,C_17)
      | ~ m1_subset_1(C_17,u1_struct_0(A_15))
      | ~ m1_subset_1(B_16,u1_struct_0(A_15))
      | ~ l3_lattices(A_15)
      | ~ v9_lattices(A_15)
      | ~ v8_lattices(A_15)
      | ~ v6_lattices(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_3893,plain,(
    ! [A_410,B_411] :
      ( r1_lattices(A_410,k15_lattice3(A_410,k1_xboole_0),k15_lattice3(A_410,B_411))
      | ~ m1_subset_1(k15_lattice3(A_410,B_411),u1_struct_0(A_410))
      | ~ m1_subset_1(k15_lattice3(A_410,k1_xboole_0),u1_struct_0(A_410))
      | ~ v9_lattices(A_410)
      | ~ v8_lattices(A_410)
      | ~ v6_lattices(A_410)
      | ~ v4_lattice3(A_410)
      | ~ v10_lattices(A_410)
      | ~ l3_lattices(A_410)
      | v2_struct_0(A_410) ) ),
    inference(resolution,[status(thm)],[c_3874,c_34])).

tff(c_3927,plain,(
    ! [A_412,B_413] :
      ( k2_lattices(A_412,k15_lattice3(A_412,k1_xboole_0),k15_lattice3(A_412,B_413)) = k15_lattice3(A_412,k1_xboole_0)
      | ~ m1_subset_1(k15_lattice3(A_412,B_413),u1_struct_0(A_412))
      | ~ m1_subset_1(k15_lattice3(A_412,k1_xboole_0),u1_struct_0(A_412))
      | ~ v9_lattices(A_412)
      | ~ v8_lattices(A_412)
      | ~ v6_lattices(A_412)
      | ~ v4_lattice3(A_412)
      | ~ v10_lattices(A_412)
      | ~ l3_lattices(A_412)
      | v2_struct_0(A_412) ) ),
    inference(resolution,[status(thm)],[c_3893,c_38])).

tff(c_3941,plain,(
    ! [A_414,B_415] :
      ( k2_lattices(A_414,k15_lattice3(A_414,k1_xboole_0),k15_lattice3(A_414,B_415)) = k15_lattice3(A_414,k1_xboole_0)
      | ~ m1_subset_1(k15_lattice3(A_414,k1_xboole_0),u1_struct_0(A_414))
      | ~ v9_lattices(A_414)
      | ~ v8_lattices(A_414)
      | ~ v6_lattices(A_414)
      | ~ v4_lattice3(A_414)
      | ~ v10_lattices(A_414)
      | ~ l3_lattices(A_414)
      | v2_struct_0(A_414) ) ),
    inference(resolution,[status(thm)],[c_58,c_3927])).

tff(c_3945,plain,(
    ! [A_47,B_415] :
      ( k2_lattices(A_47,k15_lattice3(A_47,k1_xboole_0),k15_lattice3(A_47,B_415)) = k15_lattice3(A_47,k1_xboole_0)
      | ~ v9_lattices(A_47)
      | ~ v8_lattices(A_47)
      | ~ v6_lattices(A_47)
      | ~ v4_lattice3(A_47)
      | ~ v10_lattices(A_47)
      | ~ l3_lattices(A_47)
      | v2_struct_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_58,c_3941])).

tff(c_981,plain,(
    ! [A_186,B_187] :
      ( k15_lattice3(A_186,a_2_3_lattice3(A_186,'#skF_3'(A_186,B_187))) = '#skF_3'(A_186,B_187)
      | ~ l3_lattices(A_186)
      | ~ v4_lattice3(A_186)
      | ~ v10_lattices(A_186)
      | v13_lattices(A_186)
      | ~ m1_subset_1(B_187,u1_struct_0(A_186))
      | ~ l1_lattices(A_186)
      | v2_struct_0(A_186) ) ),
    inference(resolution,[status(thm)],[c_42,c_243])).

tff(c_634,plain,(
    ! [A_47,B_133,B_48] :
      ( r1_lattices(A_47,B_133,k15_lattice3(A_47,B_48))
      | k2_lattices(A_47,B_133,k15_lattice3(A_47,B_48)) != B_133
      | ~ m1_subset_1(B_133,u1_struct_0(A_47))
      | ~ v9_lattices(A_47)
      | ~ v8_lattices(A_47)
      | ~ l3_lattices(A_47)
      | v2_struct_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_58,c_614])).

tff(c_4408,plain,(
    ! [A_450,B_451,B_452] :
      ( r1_lattices(A_450,B_451,'#skF_3'(A_450,B_452))
      | k2_lattices(A_450,B_451,k15_lattice3(A_450,a_2_3_lattice3(A_450,'#skF_3'(A_450,B_452)))) != B_451
      | ~ m1_subset_1(B_451,u1_struct_0(A_450))
      | ~ v9_lattices(A_450)
      | ~ v8_lattices(A_450)
      | ~ l3_lattices(A_450)
      | v2_struct_0(A_450)
      | ~ l3_lattices(A_450)
      | ~ v4_lattice3(A_450)
      | ~ v10_lattices(A_450)
      | v13_lattices(A_450)
      | ~ m1_subset_1(B_452,u1_struct_0(A_450))
      | ~ l1_lattices(A_450)
      | v2_struct_0(A_450) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_981,c_634])).

tff(c_4464,plain,(
    ! [A_453,B_454] :
      ( r1_lattices(A_453,k15_lattice3(A_453,k1_xboole_0),'#skF_3'(A_453,B_454))
      | ~ m1_subset_1(k15_lattice3(A_453,k1_xboole_0),u1_struct_0(A_453))
      | v13_lattices(A_453)
      | ~ m1_subset_1(B_454,u1_struct_0(A_453))
      | ~ l1_lattices(A_453)
      | ~ v9_lattices(A_453)
      | ~ v8_lattices(A_453)
      | ~ v6_lattices(A_453)
      | ~ v4_lattice3(A_453)
      | ~ v10_lattices(A_453)
      | ~ l3_lattices(A_453)
      | v2_struct_0(A_453) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3945,c_4408])).

tff(c_41587,plain,(
    ! [A_1334,B_1335] :
      ( k2_lattices(A_1334,k15_lattice3(A_1334,k1_xboole_0),'#skF_3'(A_1334,B_1335)) = k15_lattice3(A_1334,k1_xboole_0)
      | ~ m1_subset_1('#skF_3'(A_1334,B_1335),u1_struct_0(A_1334))
      | ~ m1_subset_1(k15_lattice3(A_1334,k1_xboole_0),u1_struct_0(A_1334))
      | v13_lattices(A_1334)
      | ~ m1_subset_1(B_1335,u1_struct_0(A_1334))
      | ~ l1_lattices(A_1334)
      | ~ v9_lattices(A_1334)
      | ~ v8_lattices(A_1334)
      | ~ v6_lattices(A_1334)
      | ~ v4_lattice3(A_1334)
      | ~ v10_lattices(A_1334)
      | ~ l3_lattices(A_1334)
      | v2_struct_0(A_1334) ) ),
    inference(resolution,[status(thm)],[c_4464,c_38])).

tff(c_41591,plain,(
    ! [A_1336,B_1337] :
      ( k2_lattices(A_1336,k15_lattice3(A_1336,k1_xboole_0),'#skF_3'(A_1336,B_1337)) = k15_lattice3(A_1336,k1_xboole_0)
      | ~ m1_subset_1(k15_lattice3(A_1336,k1_xboole_0),u1_struct_0(A_1336))
      | ~ v9_lattices(A_1336)
      | ~ v8_lattices(A_1336)
      | ~ v6_lattices(A_1336)
      | ~ v4_lattice3(A_1336)
      | ~ v10_lattices(A_1336)
      | ~ l3_lattices(A_1336)
      | v13_lattices(A_1336)
      | ~ m1_subset_1(B_1337,u1_struct_0(A_1336))
      | ~ l1_lattices(A_1336)
      | v2_struct_0(A_1336) ) ),
    inference(resolution,[status(thm)],[c_42,c_41587])).

tff(c_41595,plain,(
    ! [A_47,B_1337] :
      ( k2_lattices(A_47,k15_lattice3(A_47,k1_xboole_0),'#skF_3'(A_47,B_1337)) = k15_lattice3(A_47,k1_xboole_0)
      | ~ v9_lattices(A_47)
      | ~ v8_lattices(A_47)
      | ~ v6_lattices(A_47)
      | ~ v4_lattice3(A_47)
      | ~ v10_lattices(A_47)
      | v13_lattices(A_47)
      | ~ m1_subset_1(B_1337,u1_struct_0(A_47))
      | ~ l1_lattices(A_47)
      | ~ l3_lattices(A_47)
      | v2_struct_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_58,c_41591])).

tff(c_388,plain,(
    ! [A_109,C_110,B_111] :
      ( k2_lattices(A_109,C_110,B_111) = k2_lattices(A_109,B_111,C_110)
      | ~ m1_subset_1(C_110,u1_struct_0(A_109))
      | ~ m1_subset_1(B_111,u1_struct_0(A_109))
      | ~ v6_lattices(A_109)
      | ~ l1_lattices(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_821,plain,(
    ! [A_168,B_169,B_170] :
      ( k2_lattices(A_168,k15_lattice3(A_168,B_169),B_170) = k2_lattices(A_168,B_170,k15_lattice3(A_168,B_169))
      | ~ m1_subset_1(B_170,u1_struct_0(A_168))
      | ~ v6_lattices(A_168)
      | ~ l1_lattices(A_168)
      | ~ l3_lattices(A_168)
      | v2_struct_0(A_168) ) ),
    inference(resolution,[status(thm)],[c_58,c_388])).

tff(c_837,plain,(
    ! [A_25,B_169,B_34] :
      ( k2_lattices(A_25,k15_lattice3(A_25,B_169),'#skF_3'(A_25,B_34)) = k2_lattices(A_25,'#skF_3'(A_25,B_34),k15_lattice3(A_25,B_169))
      | ~ v6_lattices(A_25)
      | ~ l3_lattices(A_25)
      | v13_lattices(A_25)
      | ~ m1_subset_1(B_34,u1_struct_0(A_25))
      | ~ l1_lattices(A_25)
      | v2_struct_0(A_25) ) ),
    inference(resolution,[status(thm)],[c_42,c_821])).

tff(c_41596,plain,(
    ! [A_1338,B_1339] :
      ( k2_lattices(A_1338,k15_lattice3(A_1338,k1_xboole_0),'#skF_3'(A_1338,B_1339)) = k15_lattice3(A_1338,k1_xboole_0)
      | ~ v9_lattices(A_1338)
      | ~ v8_lattices(A_1338)
      | ~ v6_lattices(A_1338)
      | ~ v4_lattice3(A_1338)
      | ~ v10_lattices(A_1338)
      | v13_lattices(A_1338)
      | ~ m1_subset_1(B_1339,u1_struct_0(A_1338))
      | ~ l1_lattices(A_1338)
      | ~ l3_lattices(A_1338)
      | v2_struct_0(A_1338) ) ),
    inference(resolution,[status(thm)],[c_58,c_41591])).

tff(c_56012,plain,(
    ! [A_1614,B_1615] :
      ( k2_lattices(A_1614,'#skF_3'(A_1614,B_1615),k15_lattice3(A_1614,k1_xboole_0)) = k15_lattice3(A_1614,k1_xboole_0)
      | ~ v9_lattices(A_1614)
      | ~ v8_lattices(A_1614)
      | ~ v6_lattices(A_1614)
      | ~ v4_lattice3(A_1614)
      | ~ v10_lattices(A_1614)
      | v13_lattices(A_1614)
      | ~ m1_subset_1(B_1615,u1_struct_0(A_1614))
      | ~ l1_lattices(A_1614)
      | ~ l3_lattices(A_1614)
      | v2_struct_0(A_1614)
      | ~ v6_lattices(A_1614)
      | ~ l3_lattices(A_1614)
      | v13_lattices(A_1614)
      | ~ m1_subset_1(B_1615,u1_struct_0(A_1614))
      | ~ l1_lattices(A_1614)
      | v2_struct_0(A_1614) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_837,c_41596])).

tff(c_40,plain,(
    ! [A_25,B_34] :
      ( k2_lattices(A_25,'#skF_3'(A_25,B_34),B_34) != B_34
      | k2_lattices(A_25,B_34,'#skF_3'(A_25,B_34)) != B_34
      | v13_lattices(A_25)
      | ~ m1_subset_1(B_34,u1_struct_0(A_25))
      | ~ l1_lattices(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_56032,plain,(
    ! [A_1616] :
      ( k2_lattices(A_1616,k15_lattice3(A_1616,k1_xboole_0),'#skF_3'(A_1616,k15_lattice3(A_1616,k1_xboole_0))) != k15_lattice3(A_1616,k1_xboole_0)
      | ~ v9_lattices(A_1616)
      | ~ v8_lattices(A_1616)
      | ~ v4_lattice3(A_1616)
      | ~ v10_lattices(A_1616)
      | ~ v6_lattices(A_1616)
      | ~ l3_lattices(A_1616)
      | v13_lattices(A_1616)
      | ~ m1_subset_1(k15_lattice3(A_1616,k1_xboole_0),u1_struct_0(A_1616))
      | ~ l1_lattices(A_1616)
      | v2_struct_0(A_1616) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56012,c_40])).

tff(c_56038,plain,(
    ! [A_1617] :
      ( ~ v9_lattices(A_1617)
      | ~ v8_lattices(A_1617)
      | ~ v6_lattices(A_1617)
      | ~ v4_lattice3(A_1617)
      | ~ v10_lattices(A_1617)
      | v13_lattices(A_1617)
      | ~ m1_subset_1(k15_lattice3(A_1617,k1_xboole_0),u1_struct_0(A_1617))
      | ~ l1_lattices(A_1617)
      | ~ l3_lattices(A_1617)
      | v2_struct_0(A_1617) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41595,c_56032])).

tff(c_56044,plain,(
    ! [A_1618] :
      ( ~ v9_lattices(A_1618)
      | ~ v8_lattices(A_1618)
      | ~ v6_lattices(A_1618)
      | ~ v4_lattice3(A_1618)
      | ~ v10_lattices(A_1618)
      | v13_lattices(A_1618)
      | ~ l1_lattices(A_1618)
      | ~ l3_lattices(A_1618)
      | v2_struct_0(A_1618) ) ),
    inference(resolution,[status(thm)],[c_58,c_56038])).

tff(c_56125,plain,(
    ! [A_1622] :
      ( ~ v8_lattices(A_1622)
      | ~ v6_lattices(A_1622)
      | ~ v4_lattice3(A_1622)
      | v13_lattices(A_1622)
      | ~ l1_lattices(A_1622)
      | ~ v10_lattices(A_1622)
      | v2_struct_0(A_1622)
      | ~ l3_lattices(A_1622) ) ),
    inference(resolution,[status(thm)],[c_4,c_56044])).

tff(c_56130,plain,(
    ! [A_1623] :
      ( ~ v6_lattices(A_1623)
      | ~ v4_lattice3(A_1623)
      | v13_lattices(A_1623)
      | ~ l1_lattices(A_1623)
      | ~ v10_lattices(A_1623)
      | v2_struct_0(A_1623)
      | ~ l3_lattices(A_1623) ) ),
    inference(resolution,[status(thm)],[c_6,c_56125])).

tff(c_56135,plain,(
    ! [A_1624] :
      ( ~ v4_lattice3(A_1624)
      | v13_lattices(A_1624)
      | ~ l1_lattices(A_1624)
      | ~ v10_lattices(A_1624)
      | v2_struct_0(A_1624)
      | ~ l3_lattices(A_1624) ) ),
    inference(resolution,[status(thm)],[c_10,c_56130])).

tff(c_56138,plain,
    ( v13_lattices('#skF_6')
    | ~ l1_lattices('#skF_6')
    | ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l3_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_56135])).

tff(c_56141,plain,
    ( v13_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_74,c_85,c_56138])).

tff(c_56143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_91,c_56141])).

tff(c_56145,plain,(
    v13_lattices('#skF_6') ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_26,plain,(
    ! [A_13] :
      ( m1_subset_1(k5_lattices(A_13),u1_struct_0(A_13))
      | ~ l1_lattices(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_44,plain,(
    ! [A_25] :
      ( m1_subset_1('#skF_2'(A_25),u1_struct_0(A_25))
      | ~ v13_lattices(A_25)
      | ~ l1_lattices(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_56442,plain,(
    ! [A_1674,C_1675] :
      ( k2_lattices(A_1674,C_1675,k5_lattices(A_1674)) = k5_lattices(A_1674)
      | ~ m1_subset_1(C_1675,u1_struct_0(A_1674))
      | ~ m1_subset_1(k5_lattices(A_1674),u1_struct_0(A_1674))
      | ~ v13_lattices(A_1674)
      | ~ l1_lattices(A_1674)
      | v2_struct_0(A_1674) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_56464,plain,(
    ! [A_1676] :
      ( k2_lattices(A_1676,'#skF_2'(A_1676),k5_lattices(A_1676)) = k5_lattices(A_1676)
      | ~ m1_subset_1(k5_lattices(A_1676),u1_struct_0(A_1676))
      | ~ v13_lattices(A_1676)
      | ~ l1_lattices(A_1676)
      | v2_struct_0(A_1676) ) ),
    inference(resolution,[status(thm)],[c_44,c_56442])).

tff(c_56468,plain,(
    ! [A_1677] :
      ( k2_lattices(A_1677,'#skF_2'(A_1677),k5_lattices(A_1677)) = k5_lattices(A_1677)
      | ~ v13_lattices(A_1677)
      | ~ l1_lattices(A_1677)
      | v2_struct_0(A_1677) ) ),
    inference(resolution,[status(thm)],[c_26,c_56464])).

tff(c_56158,plain,(
    ! [A_1639,C_1640] :
      ( k2_lattices(A_1639,'#skF_2'(A_1639),C_1640) = '#skF_2'(A_1639)
      | ~ m1_subset_1(C_1640,u1_struct_0(A_1639))
      | ~ v13_lattices(A_1639)
      | ~ l1_lattices(A_1639)
      | v2_struct_0(A_1639) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_56176,plain,(
    ! [A_13] :
      ( k2_lattices(A_13,'#skF_2'(A_13),k5_lattices(A_13)) = '#skF_2'(A_13)
      | ~ v13_lattices(A_13)
      | ~ l1_lattices(A_13)
      | v2_struct_0(A_13) ) ),
    inference(resolution,[status(thm)],[c_26,c_56158])).

tff(c_56474,plain,(
    ! [A_1677] :
      ( k5_lattices(A_1677) = '#skF_2'(A_1677)
      | ~ v13_lattices(A_1677)
      | ~ l1_lattices(A_1677)
      | v2_struct_0(A_1677)
      | ~ v13_lattices(A_1677)
      | ~ l1_lattices(A_1677)
      | v2_struct_0(A_1677) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56468,c_56176])).

tff(c_56518,plain,(
    ! [A_1682] :
      ( k5_lattices(A_1682) = '#skF_2'(A_1682)
      | ~ v13_lattices(A_1682)
      | ~ l1_lattices(A_1682)
      | v2_struct_0(A_1682) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_56474])).

tff(c_56521,plain,
    ( k5_lattices('#skF_6') = '#skF_2'('#skF_6')
    | ~ v13_lattices('#skF_6')
    | ~ l1_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_56518,c_76])).

tff(c_56524,plain,(
    k5_lattices('#skF_6') = '#skF_2'('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_56145,c_56521])).

tff(c_56144,plain,(
    k15_lattice3('#skF_6',k1_xboole_0) != k5_lattices('#skF_6') ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_56525,plain,(
    k15_lattice3('#skF_6',k1_xboole_0) != '#skF_2'('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56524,c_56144])).

tff(c_56544,plain,
    ( m1_subset_1('#skF_2'('#skF_6'),u1_struct_0('#skF_6'))
    | ~ l1_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_56524,c_26])).

tff(c_56563,plain,
    ( m1_subset_1('#skF_2'('#skF_6'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_56544])).

tff(c_56564,plain,(
    m1_subset_1('#skF_2'('#skF_6'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_56563])).

tff(c_50,plain,(
    ! [A_36,C_45,B_43] :
      ( k2_lattices(A_36,C_45,B_43) = k2_lattices(A_36,B_43,C_45)
      | ~ m1_subset_1(C_45,u1_struct_0(A_36))
      | ~ m1_subset_1(B_43,u1_struct_0(A_36))
      | ~ v6_lattices(A_36)
      | ~ l1_lattices(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_56567,plain,(
    ! [B_43] :
      ( k2_lattices('#skF_6',B_43,'#skF_2'('#skF_6')) = k2_lattices('#skF_6','#skF_2'('#skF_6'),B_43)
      | ~ m1_subset_1(B_43,u1_struct_0('#skF_6'))
      | ~ v6_lattices('#skF_6')
      | ~ l1_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_56564,c_50])).

tff(c_56580,plain,(
    ! [B_43] :
      ( k2_lattices('#skF_6',B_43,'#skF_2'('#skF_6')) = k2_lattices('#skF_6','#skF_2'('#skF_6'),B_43)
      | ~ m1_subset_1(B_43,u1_struct_0('#skF_6'))
      | ~ v6_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_56567])).

tff(c_56581,plain,(
    ! [B_43] :
      ( k2_lattices('#skF_6',B_43,'#skF_2'('#skF_6')) = k2_lattices('#skF_6','#skF_2'('#skF_6'),B_43)
      | ~ m1_subset_1(B_43,u1_struct_0('#skF_6'))
      | ~ v6_lattices('#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_56580])).

tff(c_56849,plain,(
    ~ v6_lattices('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_56581])).

tff(c_56852,plain,
    ( ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l3_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_10,c_56849])).

tff(c_56855,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_74,c_56852])).

tff(c_56857,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_56855])).

tff(c_56859,plain,(
    v6_lattices('#skF_6') ),
    inference(splitRight,[status(thm)],[c_56581])).

tff(c_57061,plain,(
    ! [A_1702,B_1703,C_1704] :
      ( r3_lattices(A_1702,B_1703,C_1704)
      | ~ r1_lattices(A_1702,B_1703,C_1704)
      | ~ m1_subset_1(C_1704,u1_struct_0(A_1702))
      | ~ m1_subset_1(B_1703,u1_struct_0(A_1702))
      | ~ l3_lattices(A_1702)
      | ~ v9_lattices(A_1702)
      | ~ v8_lattices(A_1702)
      | ~ v6_lattices(A_1702)
      | v2_struct_0(A_1702) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_57063,plain,(
    ! [B_1703] :
      ( r3_lattices('#skF_6',B_1703,'#skF_2'('#skF_6'))
      | ~ r1_lattices('#skF_6',B_1703,'#skF_2'('#skF_6'))
      | ~ m1_subset_1(B_1703,u1_struct_0('#skF_6'))
      | ~ l3_lattices('#skF_6')
      | ~ v9_lattices('#skF_6')
      | ~ v8_lattices('#skF_6')
      | ~ v6_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_56564,c_57061])).

tff(c_57080,plain,(
    ! [B_1703] :
      ( r3_lattices('#skF_6',B_1703,'#skF_2'('#skF_6'))
      | ~ r1_lattices('#skF_6',B_1703,'#skF_2'('#skF_6'))
      | ~ m1_subset_1(B_1703,u1_struct_0('#skF_6'))
      | ~ v9_lattices('#skF_6')
      | ~ v8_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56859,c_70,c_57063])).

tff(c_57081,plain,(
    ! [B_1703] :
      ( r3_lattices('#skF_6',B_1703,'#skF_2'('#skF_6'))
      | ~ r1_lattices('#skF_6',B_1703,'#skF_2'('#skF_6'))
      | ~ m1_subset_1(B_1703,u1_struct_0('#skF_6'))
      | ~ v9_lattices('#skF_6')
      | ~ v8_lattices('#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_57080])).

tff(c_57146,plain,(
    ~ v8_lattices('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_57081])).

tff(c_57149,plain,
    ( ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l3_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_57146])).

tff(c_57152,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_74,c_57149])).

tff(c_57154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_57152])).

tff(c_57156,plain,(
    v8_lattices('#skF_6') ),
    inference(splitRight,[status(thm)],[c_57081])).

tff(c_57155,plain,(
    ! [B_1703] :
      ( ~ v9_lattices('#skF_6')
      | r3_lattices('#skF_6',B_1703,'#skF_2'('#skF_6'))
      | ~ r1_lattices('#skF_6',B_1703,'#skF_2'('#skF_6'))
      | ~ m1_subset_1(B_1703,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_57081])).

tff(c_57157,plain,(
    ~ v9_lattices('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_57155])).

tff(c_57160,plain,
    ( ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l3_lattices('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_57157])).

tff(c_57163,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_74,c_57160])).

tff(c_57165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_57163])).

tff(c_57167,plain,(
    v9_lattices('#skF_6') ),
    inference(splitRight,[status(thm)],[c_57155])).

tff(c_56879,plain,(
    ! [B_1698] :
      ( k2_lattices('#skF_6',B_1698,'#skF_2'('#skF_6')) = k2_lattices('#skF_6','#skF_2'('#skF_6'),B_1698)
      | ~ m1_subset_1(B_1698,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_56581])).

tff(c_56906,plain,(
    ! [B_48] :
      ( k2_lattices('#skF_6',k15_lattice3('#skF_6',B_48),'#skF_2'('#skF_6')) = k2_lattices('#skF_6','#skF_2'('#skF_6'),k15_lattice3('#skF_6',B_48))
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_58,c_56879])).

tff(c_56935,plain,(
    ! [B_48] :
      ( k2_lattices('#skF_6',k15_lattice3('#skF_6',B_48),'#skF_2'('#skF_6')) = k2_lattices('#skF_6','#skF_2'('#skF_6'),k15_lattice3('#skF_6',B_48))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_56906])).

tff(c_56941,plain,(
    ! [B_1699] : k2_lattices('#skF_6',k15_lattice3('#skF_6',B_1699),'#skF_2'('#skF_6')) = k2_lattices('#skF_6','#skF_2'('#skF_6'),k15_lattice3('#skF_6',B_1699)) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_56935])).

tff(c_56186,plain,(
    ! [A_1642,C_1643] :
      ( k2_lattices(A_1642,C_1643,'#skF_2'(A_1642)) = '#skF_2'(A_1642)
      | ~ m1_subset_1(C_1643,u1_struct_0(A_1642))
      | ~ v13_lattices(A_1642)
      | ~ l1_lattices(A_1642)
      | v2_struct_0(A_1642) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_56203,plain,(
    ! [A_47,B_48] :
      ( k2_lattices(A_47,k15_lattice3(A_47,B_48),'#skF_2'(A_47)) = '#skF_2'(A_47)
      | ~ v13_lattices(A_47)
      | ~ l1_lattices(A_47)
      | ~ l3_lattices(A_47)
      | v2_struct_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_58,c_56186])).

tff(c_56947,plain,(
    ! [B_1699] :
      ( k2_lattices('#skF_6','#skF_2'('#skF_6'),k15_lattice3('#skF_6',B_1699)) = '#skF_2'('#skF_6')
      | ~ v13_lattices('#skF_6')
      | ~ l1_lattices('#skF_6')
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56941,c_56203])).

tff(c_56968,plain,(
    ! [B_1699] :
      ( k2_lattices('#skF_6','#skF_2'('#skF_6'),k15_lattice3('#skF_6',B_1699)) = '#skF_2'('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_85,c_56145,c_56947])).

tff(c_56969,plain,(
    ! [B_1699] : k2_lattices('#skF_6','#skF_2'('#skF_6'),k15_lattice3('#skF_6',B_1699)) = '#skF_2'('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_56968])).

tff(c_56936,plain,(
    ! [B_48] : k2_lattices('#skF_6',k15_lattice3('#skF_6',B_48),'#skF_2'('#skF_6')) = k2_lattices('#skF_6','#skF_2'('#skF_6'),k15_lattice3('#skF_6',B_48)) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_56935])).

tff(c_56981,plain,(
    ! [B_48] : k2_lattices('#skF_6',k15_lattice3('#skF_6',B_48),'#skF_2'('#skF_6')) = '#skF_2'('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56969,c_56936])).

tff(c_56297,plain,(
    ! [A_1657,B_1658] :
      ( k15_lattice3(A_1657,a_2_3_lattice3(A_1657,B_1658)) = B_1658
      | ~ m1_subset_1(B_1658,u1_struct_0(A_1657))
      | ~ l3_lattices(A_1657)
      | ~ v4_lattice3(A_1657)
      | ~ v10_lattices(A_1657)
      | v2_struct_0(A_1657) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_56315,plain,(
    ! [A_13] :
      ( k15_lattice3(A_13,a_2_3_lattice3(A_13,k5_lattices(A_13))) = k5_lattices(A_13)
      | ~ l3_lattices(A_13)
      | ~ v4_lattice3(A_13)
      | ~ v10_lattices(A_13)
      | ~ l1_lattices(A_13)
      | v2_struct_0(A_13) ) ),
    inference(resolution,[status(thm)],[c_26,c_56297])).

tff(c_56532,plain,
    ( k15_lattice3('#skF_6',a_2_3_lattice3('#skF_6','#skF_2'('#skF_6'))) = k5_lattices('#skF_6')
    | ~ l3_lattices('#skF_6')
    | ~ v4_lattice3('#skF_6')
    | ~ v10_lattices('#skF_6')
    | ~ l1_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_56524,c_56315])).

tff(c_56551,plain,
    ( k15_lattice3('#skF_6',a_2_3_lattice3('#skF_6','#skF_2'('#skF_6'))) = '#skF_2'('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_74,c_72,c_70,c_56524,c_56532])).

tff(c_56552,plain,(
    k15_lattice3('#skF_6',a_2_3_lattice3('#skF_6','#skF_2'('#skF_6'))) = '#skF_2'('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_56551])).

tff(c_56685,plain,(
    ! [B_55] :
      ( r3_lattices('#skF_6',k15_lattice3('#skF_6',B_55),'#skF_2'('#skF_6'))
      | ~ r1_tarski(B_55,a_2_3_lattice3('#skF_6','#skF_2'('#skF_6')))
      | ~ l3_lattices('#skF_6')
      | ~ v4_lattice3('#skF_6')
      | ~ v10_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56552,c_66])).

tff(c_56707,plain,(
    ! [B_55] :
      ( r3_lattices('#skF_6',k15_lattice3('#skF_6',B_55),'#skF_2'('#skF_6'))
      | ~ r1_tarski(B_55,a_2_3_lattice3('#skF_6','#skF_2'('#skF_6')))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_56685])).

tff(c_56708,plain,(
    ! [B_55] :
      ( r3_lattices('#skF_6',k15_lattice3('#skF_6',B_55),'#skF_2'('#skF_6'))
      | ~ r1_tarski(B_55,a_2_3_lattice3('#skF_6','#skF_2'('#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_56707])).

tff(c_57168,plain,(
    ! [A_1708,B_1709,C_1710] :
      ( r1_lattices(A_1708,B_1709,C_1710)
      | ~ r3_lattices(A_1708,B_1709,C_1710)
      | ~ m1_subset_1(C_1710,u1_struct_0(A_1708))
      | ~ m1_subset_1(B_1709,u1_struct_0(A_1708))
      | ~ l3_lattices(A_1708)
      | ~ v9_lattices(A_1708)
      | ~ v8_lattices(A_1708)
      | ~ v6_lattices(A_1708)
      | v2_struct_0(A_1708) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_57176,plain,(
    ! [B_55] :
      ( r1_lattices('#skF_6',k15_lattice3('#skF_6',B_55),'#skF_2'('#skF_6'))
      | ~ m1_subset_1('#skF_2'('#skF_6'),u1_struct_0('#skF_6'))
      | ~ m1_subset_1(k15_lattice3('#skF_6',B_55),u1_struct_0('#skF_6'))
      | ~ l3_lattices('#skF_6')
      | ~ v9_lattices('#skF_6')
      | ~ v8_lattices('#skF_6')
      | ~ v6_lattices('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ r1_tarski(B_55,a_2_3_lattice3('#skF_6','#skF_2'('#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_56708,c_57168])).

tff(c_57195,plain,(
    ! [B_55] :
      ( r1_lattices('#skF_6',k15_lattice3('#skF_6',B_55),'#skF_2'('#skF_6'))
      | ~ m1_subset_1(k15_lattice3('#skF_6',B_55),u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6')
      | ~ r1_tarski(B_55,a_2_3_lattice3('#skF_6','#skF_2'('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56859,c_57156,c_57167,c_70,c_56564,c_57176])).

tff(c_57276,plain,(
    ! [B_1717] :
      ( r1_lattices('#skF_6',k15_lattice3('#skF_6',B_1717),'#skF_2'('#skF_6'))
      | ~ m1_subset_1(k15_lattice3('#skF_6',B_1717),u1_struct_0('#skF_6'))
      | ~ r1_tarski(B_1717,a_2_3_lattice3('#skF_6','#skF_2'('#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_57195])).

tff(c_57278,plain,(
    ! [B_1717] :
      ( k2_lattices('#skF_6',k15_lattice3('#skF_6',B_1717),'#skF_2'('#skF_6')) = k15_lattice3('#skF_6',B_1717)
      | ~ m1_subset_1('#skF_2'('#skF_6'),u1_struct_0('#skF_6'))
      | ~ l3_lattices('#skF_6')
      | ~ v9_lattices('#skF_6')
      | ~ v8_lattices('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ m1_subset_1(k15_lattice3('#skF_6',B_1717),u1_struct_0('#skF_6'))
      | ~ r1_tarski(B_1717,a_2_3_lattice3('#skF_6','#skF_2'('#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_57276,c_38])).

tff(c_57292,plain,(
    ! [B_1717] :
      ( k15_lattice3('#skF_6',B_1717) = '#skF_2'('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ m1_subset_1(k15_lattice3('#skF_6',B_1717),u1_struct_0('#skF_6'))
      | ~ r1_tarski(B_1717,a_2_3_lattice3('#skF_6','#skF_2'('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57156,c_57167,c_70,c_56564,c_56981,c_57278])).

tff(c_57303,plain,(
    ! [B_1720] :
      ( k15_lattice3('#skF_6',B_1720) = '#skF_2'('#skF_6')
      | ~ m1_subset_1(k15_lattice3('#skF_6',B_1720),u1_struct_0('#skF_6'))
      | ~ r1_tarski(B_1720,a_2_3_lattice3('#skF_6','#skF_2'('#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_57292])).

tff(c_57307,plain,
    ( k15_lattice3('#skF_6',k1_xboole_0) = '#skF_2'('#skF_6')
    | ~ m1_subset_1(k15_lattice3('#skF_6',k1_xboole_0),u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_2,c_57303])).

tff(c_57310,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_6',k1_xboole_0),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_56525,c_57307])).

tff(c_57313,plain,
    ( ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_57310])).

tff(c_57316,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_57313])).

tff(c_57318,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_57316])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:44:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 37.98/26.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 37.98/26.06  
% 37.98/26.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 37.98/26.06  %$ r3_lattices > r1_lattices > r1_tarski > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k16_lattice3 > k15_lattice3 > a_2_4_lattice3 > a_2_3_lattice3 > #nlpp > u1_struct_0 > k5_lattices > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_6 > #skF_1
% 37.98/26.06  
% 37.98/26.06  %Foreground sorts:
% 37.98/26.06  
% 37.98/26.06  
% 37.98/26.06  %Background operators:
% 37.98/26.06  
% 37.98/26.06  
% 37.98/26.06  %Foreground operators:
% 37.98/26.06  tff(l3_lattices, type, l3_lattices: $i > $o).
% 37.98/26.06  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 37.98/26.06  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 37.98/26.06  tff('#skF_5', type, '#skF_5': $i > $i).
% 37.98/26.06  tff(l2_lattices, type, l2_lattices: $i > $o).
% 37.98/26.06  tff('#skF_2', type, '#skF_2': $i > $i).
% 37.98/26.06  tff('#skF_4', type, '#skF_4': $i > $i).
% 37.98/26.06  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 37.98/26.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 37.98/26.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 37.98/26.06  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 37.98/26.06  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 37.98/26.06  tff(l1_lattices, type, l1_lattices: $i > $o).
% 37.98/26.06  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 37.98/26.06  tff(a_2_4_lattice3, type, a_2_4_lattice3: ($i * $i) > $i).
% 37.98/26.06  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 37.98/26.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 37.98/26.06  tff(v4_lattices, type, v4_lattices: $i > $o).
% 37.98/26.06  tff('#skF_6', type, '#skF_6': $i).
% 37.98/26.06  tff(v6_lattices, type, v6_lattices: $i > $o).
% 37.98/26.06  tff(v9_lattices, type, v9_lattices: $i > $o).
% 37.98/26.06  tff(a_2_3_lattice3, type, a_2_3_lattice3: ($i * $i) > $i).
% 37.98/26.06  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 37.98/26.06  tff(v5_lattices, type, v5_lattices: $i > $o).
% 37.98/26.06  tff(v10_lattices, type, v10_lattices: $i > $o).
% 37.98/26.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 37.98/26.06  tff(v13_lattices, type, v13_lattices: $i > $o).
% 37.98/26.06  tff(v8_lattices, type, v8_lattices: $i > $o).
% 37.98/26.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 37.98/26.06  tff(k5_lattices, type, k5_lattices: $i > $i).
% 37.98/26.06  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 37.98/26.06  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 37.98/26.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 37.98/26.06  tff(v7_lattices, type, v7_lattices: $i > $o).
% 37.98/26.06  
% 37.98/26.09  tff(f_211, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v13_lattices(A)) & l3_lattices(A)) & (k5_lattices(A) = k15_lattice3(A, k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_lattice3)).
% 37.98/26.09  tff(f_158, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k15_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 37.98/26.09  tff(f_81, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 37.98/26.09  tff(f_49, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 37.98/26.09  tff(f_136, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) <=> (?[B]: (m1_subset_1(B, u1_struct_0(A)) & (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_lattices)).
% 37.98/26.09  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 37.98/26.09  tff(f_190, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (r1_tarski(B, C) => (r3_lattices(A, k15_lattice3(A, B), k15_lattice3(A, C)) & r3_lattices(A, k16_lattice3(A, C), k16_lattice3(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_lattice3)).
% 37.98/26.09  tff(f_100, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 37.98/26.09  tff(f_119, axiom, (![A]: ((((~v2_struct_0(A) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k2_lattices(A, B, C) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 37.98/26.09  tff(f_174, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((B = k15_lattice3(A, a_2_3_lattice3(A, B))) & (B = k16_lattice3(A, a_2_4_lattice3(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_lattice3)).
% 37.98/26.09  tff(f_151, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v6_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, C) = k2_lattices(A, C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_lattices)).
% 37.98/26.09  tff(f_75, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => m1_subset_1(k5_lattices(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_lattices)).
% 37.98/26.09  tff(f_68, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((B = k5_lattices(A)) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattices)).
% 37.98/26.09  tff(c_76, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_211])).
% 37.98/26.09  tff(c_70, plain, (l3_lattices('#skF_6')), inference(cnfTransformation, [status(thm)], [f_211])).
% 37.98/26.09  tff(c_58, plain, (![A_47, B_48]: (m1_subset_1(k15_lattice3(A_47, B_48), u1_struct_0(A_47)) | ~l3_lattices(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_158])).
% 37.98/26.09  tff(c_81, plain, (![A_58]: (l1_lattices(A_58) | ~l3_lattices(A_58))), inference(cnfTransformation, [status(thm)], [f_81])).
% 37.98/26.09  tff(c_85, plain, (l1_lattices('#skF_6')), inference(resolution, [status(thm)], [c_70, c_81])).
% 37.98/26.09  tff(c_74, plain, (v10_lattices('#skF_6')), inference(cnfTransformation, [status(thm)], [f_211])).
% 37.98/26.09  tff(c_68, plain, (k15_lattice3('#skF_6', k1_xboole_0)!=k5_lattices('#skF_6') | ~l3_lattices('#skF_6') | ~v13_lattices('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_211])).
% 37.98/26.09  tff(c_78, plain, (k15_lattice3('#skF_6', k1_xboole_0)!=k5_lattices('#skF_6') | ~v13_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_68])).
% 37.98/26.09  tff(c_79, plain, (k15_lattice3('#skF_6', k1_xboole_0)!=k5_lattices('#skF_6') | ~v13_lattices('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_76, c_78])).
% 37.98/26.09  tff(c_91, plain, (~v13_lattices('#skF_6')), inference(splitLeft, [status(thm)], [c_79])).
% 37.98/26.09  tff(c_72, plain, (v4_lattice3('#skF_6')), inference(cnfTransformation, [status(thm)], [f_211])).
% 37.98/26.09  tff(c_10, plain, (![A_2]: (v6_lattices(A_2) | ~v10_lattices(A_2) | v2_struct_0(A_2) | ~l3_lattices(A_2))), inference(cnfTransformation, [status(thm)], [f_49])).
% 37.98/26.09  tff(c_6, plain, (![A_2]: (v8_lattices(A_2) | ~v10_lattices(A_2) | v2_struct_0(A_2) | ~l3_lattices(A_2))), inference(cnfTransformation, [status(thm)], [f_49])).
% 37.98/26.09  tff(c_4, plain, (![A_2]: (v9_lattices(A_2) | ~v10_lattices(A_2) | v2_struct_0(A_2) | ~l3_lattices(A_2))), inference(cnfTransformation, [status(thm)], [f_49])).
% 37.98/26.09  tff(c_42, plain, (![A_25, B_34]: (m1_subset_1('#skF_3'(A_25, B_34), u1_struct_0(A_25)) | v13_lattices(A_25) | ~m1_subset_1(B_34, u1_struct_0(A_25)) | ~l1_lattices(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_136])).
% 37.98/26.09  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 37.98/26.09  tff(c_66, plain, (![A_52, B_55, C_56]: (r3_lattices(A_52, k15_lattice3(A_52, B_55), k15_lattice3(A_52, C_56)) | ~r1_tarski(B_55, C_56) | ~l3_lattices(A_52) | ~v4_lattice3(A_52) | ~v10_lattices(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_190])).
% 37.98/26.09  tff(c_698, plain, (![A_148, B_149, C_150]: (r1_lattices(A_148, B_149, C_150) | ~r3_lattices(A_148, B_149, C_150) | ~m1_subset_1(C_150, u1_struct_0(A_148)) | ~m1_subset_1(B_149, u1_struct_0(A_148)) | ~l3_lattices(A_148) | ~v9_lattices(A_148) | ~v8_lattices(A_148) | ~v6_lattices(A_148) | v2_struct_0(A_148))), inference(cnfTransformation, [status(thm)], [f_100])).
% 37.98/26.09  tff(c_2210, plain, (![A_291, B_292, C_293]: (r1_lattices(A_291, k15_lattice3(A_291, B_292), k15_lattice3(A_291, C_293)) | ~m1_subset_1(k15_lattice3(A_291, C_293), u1_struct_0(A_291)) | ~m1_subset_1(k15_lattice3(A_291, B_292), u1_struct_0(A_291)) | ~v9_lattices(A_291) | ~v8_lattices(A_291) | ~v6_lattices(A_291) | ~r1_tarski(B_292, C_293) | ~l3_lattices(A_291) | ~v4_lattice3(A_291) | ~v10_lattices(A_291) | v2_struct_0(A_291))), inference(resolution, [status(thm)], [c_66, c_698])).
% 37.98/26.09  tff(c_38, plain, (![A_18, B_22, C_24]: (k2_lattices(A_18, B_22, C_24)=B_22 | ~r1_lattices(A_18, B_22, C_24) | ~m1_subset_1(C_24, u1_struct_0(A_18)) | ~m1_subset_1(B_22, u1_struct_0(A_18)) | ~l3_lattices(A_18) | ~v9_lattices(A_18) | ~v8_lattices(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_119])).
% 37.98/26.09  tff(c_3087, plain, (![A_350, B_351, C_352]: (k2_lattices(A_350, k15_lattice3(A_350, B_351), k15_lattice3(A_350, C_352))=k15_lattice3(A_350, B_351) | ~m1_subset_1(k15_lattice3(A_350, C_352), u1_struct_0(A_350)) | ~m1_subset_1(k15_lattice3(A_350, B_351), u1_struct_0(A_350)) | ~v9_lattices(A_350) | ~v8_lattices(A_350) | ~v6_lattices(A_350) | ~r1_tarski(B_351, C_352) | ~l3_lattices(A_350) | ~v4_lattice3(A_350) | ~v10_lattices(A_350) | v2_struct_0(A_350))), inference(resolution, [status(thm)], [c_2210, c_38])).
% 37.98/26.09  tff(c_3105, plain, (![A_354, B_355, B_356]: (k2_lattices(A_354, k15_lattice3(A_354, B_355), k15_lattice3(A_354, B_356))=k15_lattice3(A_354, B_355) | ~m1_subset_1(k15_lattice3(A_354, B_355), u1_struct_0(A_354)) | ~v9_lattices(A_354) | ~v8_lattices(A_354) | ~v6_lattices(A_354) | ~r1_tarski(B_355, B_356) | ~v4_lattice3(A_354) | ~v10_lattices(A_354) | ~l3_lattices(A_354) | v2_struct_0(A_354))), inference(resolution, [status(thm)], [c_58, c_3087])).
% 37.98/26.09  tff(c_3119, plain, (![A_357, B_358, B_359]: (k2_lattices(A_357, k15_lattice3(A_357, B_358), k15_lattice3(A_357, B_359))=k15_lattice3(A_357, B_358) | ~v9_lattices(A_357) | ~v8_lattices(A_357) | ~v6_lattices(A_357) | ~r1_tarski(B_358, B_359) | ~v4_lattice3(A_357) | ~v10_lattices(A_357) | ~l3_lattices(A_357) | v2_struct_0(A_357))), inference(resolution, [status(thm)], [c_58, c_3105])).
% 37.98/26.09  tff(c_243, plain, (![A_92, B_93]: (k15_lattice3(A_92, a_2_3_lattice3(A_92, B_93))=B_93 | ~m1_subset_1(B_93, u1_struct_0(A_92)) | ~l3_lattices(A_92) | ~v4_lattice3(A_92) | ~v10_lattices(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_174])).
% 37.98/26.09  tff(c_260, plain, (![A_47, B_48]: (k15_lattice3(A_47, a_2_3_lattice3(A_47, k15_lattice3(A_47, B_48)))=k15_lattice3(A_47, B_48) | ~v4_lattice3(A_47) | ~v10_lattices(A_47) | ~l3_lattices(A_47) | v2_struct_0(A_47))), inference(resolution, [status(thm)], [c_58, c_243])).
% 37.98/26.09  tff(c_614, plain, (![A_132, B_133, C_134]: (r1_lattices(A_132, B_133, C_134) | k2_lattices(A_132, B_133, C_134)!=B_133 | ~m1_subset_1(C_134, u1_struct_0(A_132)) | ~m1_subset_1(B_133, u1_struct_0(A_132)) | ~l3_lattices(A_132) | ~v9_lattices(A_132) | ~v8_lattices(A_132) | v2_struct_0(A_132))), inference(cnfTransformation, [status(thm)], [f_119])).
% 37.98/26.09  tff(c_936, plain, (![A_176, B_177, B_178]: (r1_lattices(A_176, B_177, k15_lattice3(A_176, B_178)) | k2_lattices(A_176, B_177, k15_lattice3(A_176, B_178))!=B_177 | ~m1_subset_1(B_177, u1_struct_0(A_176)) | ~v9_lattices(A_176) | ~v8_lattices(A_176) | ~l3_lattices(A_176) | v2_struct_0(A_176))), inference(resolution, [status(thm)], [c_58, c_614])).
% 37.98/26.09  tff(c_947, plain, (![A_47, B_177, B_48]: (r1_lattices(A_47, B_177, k15_lattice3(A_47, B_48)) | k2_lattices(A_47, B_177, k15_lattice3(A_47, a_2_3_lattice3(A_47, k15_lattice3(A_47, B_48))))!=B_177 | ~m1_subset_1(B_177, u1_struct_0(A_47)) | ~v9_lattices(A_47) | ~v8_lattices(A_47) | ~l3_lattices(A_47) | v2_struct_0(A_47) | ~v4_lattice3(A_47) | ~v10_lattices(A_47) | ~l3_lattices(A_47) | v2_struct_0(A_47))), inference(superposition, [status(thm), theory('equality')], [c_260, c_936])).
% 37.98/26.09  tff(c_3256, plain, (![A_362, B_363, B_364]: (r1_lattices(A_362, k15_lattice3(A_362, B_363), k15_lattice3(A_362, B_364)) | ~m1_subset_1(k15_lattice3(A_362, B_363), u1_struct_0(A_362)) | ~v9_lattices(A_362) | ~v8_lattices(A_362) | ~v6_lattices(A_362) | ~r1_tarski(B_363, a_2_3_lattice3(A_362, k15_lattice3(A_362, B_364))) | ~v4_lattice3(A_362) | ~v10_lattices(A_362) | ~l3_lattices(A_362) | v2_struct_0(A_362))), inference(superposition, [status(thm), theory('equality')], [c_3119, c_947])).
% 37.98/26.09  tff(c_737, plain, (![A_157, B_158, C_159]: (r3_lattices(A_157, B_158, C_159) | ~r1_lattices(A_157, B_158, C_159) | ~m1_subset_1(C_159, u1_struct_0(A_157)) | ~m1_subset_1(B_158, u1_struct_0(A_157)) | ~l3_lattices(A_157) | ~v9_lattices(A_157) | ~v8_lattices(A_157) | ~v6_lattices(A_157) | v2_struct_0(A_157))), inference(cnfTransformation, [status(thm)], [f_100])).
% 37.98/26.09  tff(c_953, plain, (![A_181, B_182, B_183]: (r3_lattices(A_181, B_182, k15_lattice3(A_181, B_183)) | ~r1_lattices(A_181, B_182, k15_lattice3(A_181, B_183)) | ~m1_subset_1(B_182, u1_struct_0(A_181)) | ~v9_lattices(A_181) | ~v8_lattices(A_181) | ~v6_lattices(A_181) | ~l3_lattices(A_181) | v2_struct_0(A_181))), inference(resolution, [status(thm)], [c_58, c_737])).
% 37.98/26.09  tff(c_964, plain, (![A_47, B_182, B_48]: (r3_lattices(A_47, B_182, k15_lattice3(A_47, B_48)) | ~r1_lattices(A_47, B_182, k15_lattice3(A_47, a_2_3_lattice3(A_47, k15_lattice3(A_47, B_48)))) | ~m1_subset_1(B_182, u1_struct_0(A_47)) | ~v9_lattices(A_47) | ~v8_lattices(A_47) | ~v6_lattices(A_47) | ~l3_lattices(A_47) | v2_struct_0(A_47) | ~v4_lattice3(A_47) | ~v10_lattices(A_47) | ~l3_lattices(A_47) | v2_struct_0(A_47))), inference(superposition, [status(thm), theory('equality')], [c_260, c_953])).
% 37.98/26.09  tff(c_3850, plain, (![A_405, B_406, B_407]: (r3_lattices(A_405, k15_lattice3(A_405, B_406), k15_lattice3(A_405, B_407)) | ~m1_subset_1(k15_lattice3(A_405, B_406), u1_struct_0(A_405)) | ~v9_lattices(A_405) | ~v8_lattices(A_405) | ~v6_lattices(A_405) | ~r1_tarski(B_406, a_2_3_lattice3(A_405, k15_lattice3(A_405, a_2_3_lattice3(A_405, k15_lattice3(A_405, B_407))))) | ~v4_lattice3(A_405) | ~v10_lattices(A_405) | ~l3_lattices(A_405) | v2_struct_0(A_405))), inference(resolution, [status(thm)], [c_3256, c_964])).
% 37.98/26.09  tff(c_3874, plain, (![A_408, B_409]: (r3_lattices(A_408, k15_lattice3(A_408, k1_xboole_0), k15_lattice3(A_408, B_409)) | ~m1_subset_1(k15_lattice3(A_408, k1_xboole_0), u1_struct_0(A_408)) | ~v9_lattices(A_408) | ~v8_lattices(A_408) | ~v6_lattices(A_408) | ~v4_lattice3(A_408) | ~v10_lattices(A_408) | ~l3_lattices(A_408) | v2_struct_0(A_408))), inference(resolution, [status(thm)], [c_2, c_3850])).
% 37.98/26.09  tff(c_34, plain, (![A_15, B_16, C_17]: (r1_lattices(A_15, B_16, C_17) | ~r3_lattices(A_15, B_16, C_17) | ~m1_subset_1(C_17, u1_struct_0(A_15)) | ~m1_subset_1(B_16, u1_struct_0(A_15)) | ~l3_lattices(A_15) | ~v9_lattices(A_15) | ~v8_lattices(A_15) | ~v6_lattices(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_100])).
% 37.98/26.09  tff(c_3893, plain, (![A_410, B_411]: (r1_lattices(A_410, k15_lattice3(A_410, k1_xboole_0), k15_lattice3(A_410, B_411)) | ~m1_subset_1(k15_lattice3(A_410, B_411), u1_struct_0(A_410)) | ~m1_subset_1(k15_lattice3(A_410, k1_xboole_0), u1_struct_0(A_410)) | ~v9_lattices(A_410) | ~v8_lattices(A_410) | ~v6_lattices(A_410) | ~v4_lattice3(A_410) | ~v10_lattices(A_410) | ~l3_lattices(A_410) | v2_struct_0(A_410))), inference(resolution, [status(thm)], [c_3874, c_34])).
% 37.98/26.09  tff(c_3927, plain, (![A_412, B_413]: (k2_lattices(A_412, k15_lattice3(A_412, k1_xboole_0), k15_lattice3(A_412, B_413))=k15_lattice3(A_412, k1_xboole_0) | ~m1_subset_1(k15_lattice3(A_412, B_413), u1_struct_0(A_412)) | ~m1_subset_1(k15_lattice3(A_412, k1_xboole_0), u1_struct_0(A_412)) | ~v9_lattices(A_412) | ~v8_lattices(A_412) | ~v6_lattices(A_412) | ~v4_lattice3(A_412) | ~v10_lattices(A_412) | ~l3_lattices(A_412) | v2_struct_0(A_412))), inference(resolution, [status(thm)], [c_3893, c_38])).
% 37.98/26.09  tff(c_3941, plain, (![A_414, B_415]: (k2_lattices(A_414, k15_lattice3(A_414, k1_xboole_0), k15_lattice3(A_414, B_415))=k15_lattice3(A_414, k1_xboole_0) | ~m1_subset_1(k15_lattice3(A_414, k1_xboole_0), u1_struct_0(A_414)) | ~v9_lattices(A_414) | ~v8_lattices(A_414) | ~v6_lattices(A_414) | ~v4_lattice3(A_414) | ~v10_lattices(A_414) | ~l3_lattices(A_414) | v2_struct_0(A_414))), inference(resolution, [status(thm)], [c_58, c_3927])).
% 37.98/26.09  tff(c_3945, plain, (![A_47, B_415]: (k2_lattices(A_47, k15_lattice3(A_47, k1_xboole_0), k15_lattice3(A_47, B_415))=k15_lattice3(A_47, k1_xboole_0) | ~v9_lattices(A_47) | ~v8_lattices(A_47) | ~v6_lattices(A_47) | ~v4_lattice3(A_47) | ~v10_lattices(A_47) | ~l3_lattices(A_47) | v2_struct_0(A_47))), inference(resolution, [status(thm)], [c_58, c_3941])).
% 37.98/26.09  tff(c_981, plain, (![A_186, B_187]: (k15_lattice3(A_186, a_2_3_lattice3(A_186, '#skF_3'(A_186, B_187)))='#skF_3'(A_186, B_187) | ~l3_lattices(A_186) | ~v4_lattice3(A_186) | ~v10_lattices(A_186) | v13_lattices(A_186) | ~m1_subset_1(B_187, u1_struct_0(A_186)) | ~l1_lattices(A_186) | v2_struct_0(A_186))), inference(resolution, [status(thm)], [c_42, c_243])).
% 37.98/26.09  tff(c_634, plain, (![A_47, B_133, B_48]: (r1_lattices(A_47, B_133, k15_lattice3(A_47, B_48)) | k2_lattices(A_47, B_133, k15_lattice3(A_47, B_48))!=B_133 | ~m1_subset_1(B_133, u1_struct_0(A_47)) | ~v9_lattices(A_47) | ~v8_lattices(A_47) | ~l3_lattices(A_47) | v2_struct_0(A_47))), inference(resolution, [status(thm)], [c_58, c_614])).
% 37.98/26.09  tff(c_4408, plain, (![A_450, B_451, B_452]: (r1_lattices(A_450, B_451, '#skF_3'(A_450, B_452)) | k2_lattices(A_450, B_451, k15_lattice3(A_450, a_2_3_lattice3(A_450, '#skF_3'(A_450, B_452))))!=B_451 | ~m1_subset_1(B_451, u1_struct_0(A_450)) | ~v9_lattices(A_450) | ~v8_lattices(A_450) | ~l3_lattices(A_450) | v2_struct_0(A_450) | ~l3_lattices(A_450) | ~v4_lattice3(A_450) | ~v10_lattices(A_450) | v13_lattices(A_450) | ~m1_subset_1(B_452, u1_struct_0(A_450)) | ~l1_lattices(A_450) | v2_struct_0(A_450))), inference(superposition, [status(thm), theory('equality')], [c_981, c_634])).
% 37.98/26.09  tff(c_4464, plain, (![A_453, B_454]: (r1_lattices(A_453, k15_lattice3(A_453, k1_xboole_0), '#skF_3'(A_453, B_454)) | ~m1_subset_1(k15_lattice3(A_453, k1_xboole_0), u1_struct_0(A_453)) | v13_lattices(A_453) | ~m1_subset_1(B_454, u1_struct_0(A_453)) | ~l1_lattices(A_453) | ~v9_lattices(A_453) | ~v8_lattices(A_453) | ~v6_lattices(A_453) | ~v4_lattice3(A_453) | ~v10_lattices(A_453) | ~l3_lattices(A_453) | v2_struct_0(A_453))), inference(superposition, [status(thm), theory('equality')], [c_3945, c_4408])).
% 37.98/26.09  tff(c_41587, plain, (![A_1334, B_1335]: (k2_lattices(A_1334, k15_lattice3(A_1334, k1_xboole_0), '#skF_3'(A_1334, B_1335))=k15_lattice3(A_1334, k1_xboole_0) | ~m1_subset_1('#skF_3'(A_1334, B_1335), u1_struct_0(A_1334)) | ~m1_subset_1(k15_lattice3(A_1334, k1_xboole_0), u1_struct_0(A_1334)) | v13_lattices(A_1334) | ~m1_subset_1(B_1335, u1_struct_0(A_1334)) | ~l1_lattices(A_1334) | ~v9_lattices(A_1334) | ~v8_lattices(A_1334) | ~v6_lattices(A_1334) | ~v4_lattice3(A_1334) | ~v10_lattices(A_1334) | ~l3_lattices(A_1334) | v2_struct_0(A_1334))), inference(resolution, [status(thm)], [c_4464, c_38])).
% 37.98/26.09  tff(c_41591, plain, (![A_1336, B_1337]: (k2_lattices(A_1336, k15_lattice3(A_1336, k1_xboole_0), '#skF_3'(A_1336, B_1337))=k15_lattice3(A_1336, k1_xboole_0) | ~m1_subset_1(k15_lattice3(A_1336, k1_xboole_0), u1_struct_0(A_1336)) | ~v9_lattices(A_1336) | ~v8_lattices(A_1336) | ~v6_lattices(A_1336) | ~v4_lattice3(A_1336) | ~v10_lattices(A_1336) | ~l3_lattices(A_1336) | v13_lattices(A_1336) | ~m1_subset_1(B_1337, u1_struct_0(A_1336)) | ~l1_lattices(A_1336) | v2_struct_0(A_1336))), inference(resolution, [status(thm)], [c_42, c_41587])).
% 37.98/26.09  tff(c_41595, plain, (![A_47, B_1337]: (k2_lattices(A_47, k15_lattice3(A_47, k1_xboole_0), '#skF_3'(A_47, B_1337))=k15_lattice3(A_47, k1_xboole_0) | ~v9_lattices(A_47) | ~v8_lattices(A_47) | ~v6_lattices(A_47) | ~v4_lattice3(A_47) | ~v10_lattices(A_47) | v13_lattices(A_47) | ~m1_subset_1(B_1337, u1_struct_0(A_47)) | ~l1_lattices(A_47) | ~l3_lattices(A_47) | v2_struct_0(A_47))), inference(resolution, [status(thm)], [c_58, c_41591])).
% 37.98/26.09  tff(c_388, plain, (![A_109, C_110, B_111]: (k2_lattices(A_109, C_110, B_111)=k2_lattices(A_109, B_111, C_110) | ~m1_subset_1(C_110, u1_struct_0(A_109)) | ~m1_subset_1(B_111, u1_struct_0(A_109)) | ~v6_lattices(A_109) | ~l1_lattices(A_109) | v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_151])).
% 37.98/26.09  tff(c_821, plain, (![A_168, B_169, B_170]: (k2_lattices(A_168, k15_lattice3(A_168, B_169), B_170)=k2_lattices(A_168, B_170, k15_lattice3(A_168, B_169)) | ~m1_subset_1(B_170, u1_struct_0(A_168)) | ~v6_lattices(A_168) | ~l1_lattices(A_168) | ~l3_lattices(A_168) | v2_struct_0(A_168))), inference(resolution, [status(thm)], [c_58, c_388])).
% 37.98/26.09  tff(c_837, plain, (![A_25, B_169, B_34]: (k2_lattices(A_25, k15_lattice3(A_25, B_169), '#skF_3'(A_25, B_34))=k2_lattices(A_25, '#skF_3'(A_25, B_34), k15_lattice3(A_25, B_169)) | ~v6_lattices(A_25) | ~l3_lattices(A_25) | v13_lattices(A_25) | ~m1_subset_1(B_34, u1_struct_0(A_25)) | ~l1_lattices(A_25) | v2_struct_0(A_25))), inference(resolution, [status(thm)], [c_42, c_821])).
% 37.98/26.09  tff(c_41596, plain, (![A_1338, B_1339]: (k2_lattices(A_1338, k15_lattice3(A_1338, k1_xboole_0), '#skF_3'(A_1338, B_1339))=k15_lattice3(A_1338, k1_xboole_0) | ~v9_lattices(A_1338) | ~v8_lattices(A_1338) | ~v6_lattices(A_1338) | ~v4_lattice3(A_1338) | ~v10_lattices(A_1338) | v13_lattices(A_1338) | ~m1_subset_1(B_1339, u1_struct_0(A_1338)) | ~l1_lattices(A_1338) | ~l3_lattices(A_1338) | v2_struct_0(A_1338))), inference(resolution, [status(thm)], [c_58, c_41591])).
% 37.98/26.09  tff(c_56012, plain, (![A_1614, B_1615]: (k2_lattices(A_1614, '#skF_3'(A_1614, B_1615), k15_lattice3(A_1614, k1_xboole_0))=k15_lattice3(A_1614, k1_xboole_0) | ~v9_lattices(A_1614) | ~v8_lattices(A_1614) | ~v6_lattices(A_1614) | ~v4_lattice3(A_1614) | ~v10_lattices(A_1614) | v13_lattices(A_1614) | ~m1_subset_1(B_1615, u1_struct_0(A_1614)) | ~l1_lattices(A_1614) | ~l3_lattices(A_1614) | v2_struct_0(A_1614) | ~v6_lattices(A_1614) | ~l3_lattices(A_1614) | v13_lattices(A_1614) | ~m1_subset_1(B_1615, u1_struct_0(A_1614)) | ~l1_lattices(A_1614) | v2_struct_0(A_1614))), inference(superposition, [status(thm), theory('equality')], [c_837, c_41596])).
% 37.98/26.09  tff(c_40, plain, (![A_25, B_34]: (k2_lattices(A_25, '#skF_3'(A_25, B_34), B_34)!=B_34 | k2_lattices(A_25, B_34, '#skF_3'(A_25, B_34))!=B_34 | v13_lattices(A_25) | ~m1_subset_1(B_34, u1_struct_0(A_25)) | ~l1_lattices(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_136])).
% 37.98/26.09  tff(c_56032, plain, (![A_1616]: (k2_lattices(A_1616, k15_lattice3(A_1616, k1_xboole_0), '#skF_3'(A_1616, k15_lattice3(A_1616, k1_xboole_0)))!=k15_lattice3(A_1616, k1_xboole_0) | ~v9_lattices(A_1616) | ~v8_lattices(A_1616) | ~v4_lattice3(A_1616) | ~v10_lattices(A_1616) | ~v6_lattices(A_1616) | ~l3_lattices(A_1616) | v13_lattices(A_1616) | ~m1_subset_1(k15_lattice3(A_1616, k1_xboole_0), u1_struct_0(A_1616)) | ~l1_lattices(A_1616) | v2_struct_0(A_1616))), inference(superposition, [status(thm), theory('equality')], [c_56012, c_40])).
% 37.98/26.09  tff(c_56038, plain, (![A_1617]: (~v9_lattices(A_1617) | ~v8_lattices(A_1617) | ~v6_lattices(A_1617) | ~v4_lattice3(A_1617) | ~v10_lattices(A_1617) | v13_lattices(A_1617) | ~m1_subset_1(k15_lattice3(A_1617, k1_xboole_0), u1_struct_0(A_1617)) | ~l1_lattices(A_1617) | ~l3_lattices(A_1617) | v2_struct_0(A_1617))), inference(superposition, [status(thm), theory('equality')], [c_41595, c_56032])).
% 37.98/26.09  tff(c_56044, plain, (![A_1618]: (~v9_lattices(A_1618) | ~v8_lattices(A_1618) | ~v6_lattices(A_1618) | ~v4_lattice3(A_1618) | ~v10_lattices(A_1618) | v13_lattices(A_1618) | ~l1_lattices(A_1618) | ~l3_lattices(A_1618) | v2_struct_0(A_1618))), inference(resolution, [status(thm)], [c_58, c_56038])).
% 37.98/26.09  tff(c_56125, plain, (![A_1622]: (~v8_lattices(A_1622) | ~v6_lattices(A_1622) | ~v4_lattice3(A_1622) | v13_lattices(A_1622) | ~l1_lattices(A_1622) | ~v10_lattices(A_1622) | v2_struct_0(A_1622) | ~l3_lattices(A_1622))), inference(resolution, [status(thm)], [c_4, c_56044])).
% 37.98/26.09  tff(c_56130, plain, (![A_1623]: (~v6_lattices(A_1623) | ~v4_lattice3(A_1623) | v13_lattices(A_1623) | ~l1_lattices(A_1623) | ~v10_lattices(A_1623) | v2_struct_0(A_1623) | ~l3_lattices(A_1623))), inference(resolution, [status(thm)], [c_6, c_56125])).
% 37.98/26.09  tff(c_56135, plain, (![A_1624]: (~v4_lattice3(A_1624) | v13_lattices(A_1624) | ~l1_lattices(A_1624) | ~v10_lattices(A_1624) | v2_struct_0(A_1624) | ~l3_lattices(A_1624))), inference(resolution, [status(thm)], [c_10, c_56130])).
% 37.98/26.09  tff(c_56138, plain, (v13_lattices('#skF_6') | ~l1_lattices('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6') | ~l3_lattices('#skF_6')), inference(resolution, [status(thm)], [c_72, c_56135])).
% 37.98/26.09  tff(c_56141, plain, (v13_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_74, c_85, c_56138])).
% 37.98/26.09  tff(c_56143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_91, c_56141])).
% 37.98/26.09  tff(c_56145, plain, (v13_lattices('#skF_6')), inference(splitRight, [status(thm)], [c_79])).
% 37.98/26.09  tff(c_26, plain, (![A_13]: (m1_subset_1(k5_lattices(A_13), u1_struct_0(A_13)) | ~l1_lattices(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_75])).
% 37.98/26.09  tff(c_44, plain, (![A_25]: (m1_subset_1('#skF_2'(A_25), u1_struct_0(A_25)) | ~v13_lattices(A_25) | ~l1_lattices(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_136])).
% 37.98/26.09  tff(c_56442, plain, (![A_1674, C_1675]: (k2_lattices(A_1674, C_1675, k5_lattices(A_1674))=k5_lattices(A_1674) | ~m1_subset_1(C_1675, u1_struct_0(A_1674)) | ~m1_subset_1(k5_lattices(A_1674), u1_struct_0(A_1674)) | ~v13_lattices(A_1674) | ~l1_lattices(A_1674) | v2_struct_0(A_1674))), inference(cnfTransformation, [status(thm)], [f_68])).
% 37.98/26.09  tff(c_56464, plain, (![A_1676]: (k2_lattices(A_1676, '#skF_2'(A_1676), k5_lattices(A_1676))=k5_lattices(A_1676) | ~m1_subset_1(k5_lattices(A_1676), u1_struct_0(A_1676)) | ~v13_lattices(A_1676) | ~l1_lattices(A_1676) | v2_struct_0(A_1676))), inference(resolution, [status(thm)], [c_44, c_56442])).
% 37.98/26.09  tff(c_56468, plain, (![A_1677]: (k2_lattices(A_1677, '#skF_2'(A_1677), k5_lattices(A_1677))=k5_lattices(A_1677) | ~v13_lattices(A_1677) | ~l1_lattices(A_1677) | v2_struct_0(A_1677))), inference(resolution, [status(thm)], [c_26, c_56464])).
% 37.98/26.09  tff(c_56158, plain, (![A_1639, C_1640]: (k2_lattices(A_1639, '#skF_2'(A_1639), C_1640)='#skF_2'(A_1639) | ~m1_subset_1(C_1640, u1_struct_0(A_1639)) | ~v13_lattices(A_1639) | ~l1_lattices(A_1639) | v2_struct_0(A_1639))), inference(cnfTransformation, [status(thm)], [f_136])).
% 37.98/26.09  tff(c_56176, plain, (![A_13]: (k2_lattices(A_13, '#skF_2'(A_13), k5_lattices(A_13))='#skF_2'(A_13) | ~v13_lattices(A_13) | ~l1_lattices(A_13) | v2_struct_0(A_13))), inference(resolution, [status(thm)], [c_26, c_56158])).
% 37.98/26.09  tff(c_56474, plain, (![A_1677]: (k5_lattices(A_1677)='#skF_2'(A_1677) | ~v13_lattices(A_1677) | ~l1_lattices(A_1677) | v2_struct_0(A_1677) | ~v13_lattices(A_1677) | ~l1_lattices(A_1677) | v2_struct_0(A_1677))), inference(superposition, [status(thm), theory('equality')], [c_56468, c_56176])).
% 37.98/26.09  tff(c_56518, plain, (![A_1682]: (k5_lattices(A_1682)='#skF_2'(A_1682) | ~v13_lattices(A_1682) | ~l1_lattices(A_1682) | v2_struct_0(A_1682))), inference(factorization, [status(thm), theory('equality')], [c_56474])).
% 37.98/26.09  tff(c_56521, plain, (k5_lattices('#skF_6')='#skF_2'('#skF_6') | ~v13_lattices('#skF_6') | ~l1_lattices('#skF_6')), inference(resolution, [status(thm)], [c_56518, c_76])).
% 37.98/26.09  tff(c_56524, plain, (k5_lattices('#skF_6')='#skF_2'('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_56145, c_56521])).
% 37.98/26.09  tff(c_56144, plain, (k15_lattice3('#skF_6', k1_xboole_0)!=k5_lattices('#skF_6')), inference(splitRight, [status(thm)], [c_79])).
% 37.98/26.09  tff(c_56525, plain, (k15_lattice3('#skF_6', k1_xboole_0)!='#skF_2'('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56524, c_56144])).
% 37.98/26.09  tff(c_56544, plain, (m1_subset_1('#skF_2'('#skF_6'), u1_struct_0('#skF_6')) | ~l1_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_56524, c_26])).
% 37.98/26.09  tff(c_56563, plain, (m1_subset_1('#skF_2'('#skF_6'), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_56544])).
% 37.98/26.09  tff(c_56564, plain, (m1_subset_1('#skF_2'('#skF_6'), u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_76, c_56563])).
% 37.98/26.09  tff(c_50, plain, (![A_36, C_45, B_43]: (k2_lattices(A_36, C_45, B_43)=k2_lattices(A_36, B_43, C_45) | ~m1_subset_1(C_45, u1_struct_0(A_36)) | ~m1_subset_1(B_43, u1_struct_0(A_36)) | ~v6_lattices(A_36) | ~l1_lattices(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_151])).
% 37.98/26.09  tff(c_56567, plain, (![B_43]: (k2_lattices('#skF_6', B_43, '#skF_2'('#skF_6'))=k2_lattices('#skF_6', '#skF_2'('#skF_6'), B_43) | ~m1_subset_1(B_43, u1_struct_0('#skF_6')) | ~v6_lattices('#skF_6') | ~l1_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_56564, c_50])).
% 37.98/26.09  tff(c_56580, plain, (![B_43]: (k2_lattices('#skF_6', B_43, '#skF_2'('#skF_6'))=k2_lattices('#skF_6', '#skF_2'('#skF_6'), B_43) | ~m1_subset_1(B_43, u1_struct_0('#skF_6')) | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_56567])).
% 37.98/26.09  tff(c_56581, plain, (![B_43]: (k2_lattices('#skF_6', B_43, '#skF_2'('#skF_6'))=k2_lattices('#skF_6', '#skF_2'('#skF_6'), B_43) | ~m1_subset_1(B_43, u1_struct_0('#skF_6')) | ~v6_lattices('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_76, c_56580])).
% 37.98/26.09  tff(c_56849, plain, (~v6_lattices('#skF_6')), inference(splitLeft, [status(thm)], [c_56581])).
% 37.98/26.09  tff(c_56852, plain, (~v10_lattices('#skF_6') | v2_struct_0('#skF_6') | ~l3_lattices('#skF_6')), inference(resolution, [status(thm)], [c_10, c_56849])).
% 37.98/26.09  tff(c_56855, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_74, c_56852])).
% 37.98/26.09  tff(c_56857, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_56855])).
% 37.98/26.09  tff(c_56859, plain, (v6_lattices('#skF_6')), inference(splitRight, [status(thm)], [c_56581])).
% 37.98/26.09  tff(c_57061, plain, (![A_1702, B_1703, C_1704]: (r3_lattices(A_1702, B_1703, C_1704) | ~r1_lattices(A_1702, B_1703, C_1704) | ~m1_subset_1(C_1704, u1_struct_0(A_1702)) | ~m1_subset_1(B_1703, u1_struct_0(A_1702)) | ~l3_lattices(A_1702) | ~v9_lattices(A_1702) | ~v8_lattices(A_1702) | ~v6_lattices(A_1702) | v2_struct_0(A_1702))), inference(cnfTransformation, [status(thm)], [f_100])).
% 37.98/26.09  tff(c_57063, plain, (![B_1703]: (r3_lattices('#skF_6', B_1703, '#skF_2'('#skF_6')) | ~r1_lattices('#skF_6', B_1703, '#skF_2'('#skF_6')) | ~m1_subset_1(B_1703, u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_56564, c_57061])).
% 37.98/26.09  tff(c_57080, plain, (![B_1703]: (r3_lattices('#skF_6', B_1703, '#skF_2'('#skF_6')) | ~r1_lattices('#skF_6', B_1703, '#skF_2'('#skF_6')) | ~m1_subset_1(B_1703, u1_struct_0('#skF_6')) | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56859, c_70, c_57063])).
% 37.98/26.09  tff(c_57081, plain, (![B_1703]: (r3_lattices('#skF_6', B_1703, '#skF_2'('#skF_6')) | ~r1_lattices('#skF_6', B_1703, '#skF_2'('#skF_6')) | ~m1_subset_1(B_1703, u1_struct_0('#skF_6')) | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_76, c_57080])).
% 37.98/26.09  tff(c_57146, plain, (~v8_lattices('#skF_6')), inference(splitLeft, [status(thm)], [c_57081])).
% 37.98/26.09  tff(c_57149, plain, (~v10_lattices('#skF_6') | v2_struct_0('#skF_6') | ~l3_lattices('#skF_6')), inference(resolution, [status(thm)], [c_6, c_57146])).
% 37.98/26.09  tff(c_57152, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_74, c_57149])).
% 37.98/26.09  tff(c_57154, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_57152])).
% 37.98/26.09  tff(c_57156, plain, (v8_lattices('#skF_6')), inference(splitRight, [status(thm)], [c_57081])).
% 37.98/26.09  tff(c_57155, plain, (![B_1703]: (~v9_lattices('#skF_6') | r3_lattices('#skF_6', B_1703, '#skF_2'('#skF_6')) | ~r1_lattices('#skF_6', B_1703, '#skF_2'('#skF_6')) | ~m1_subset_1(B_1703, u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_57081])).
% 37.98/26.09  tff(c_57157, plain, (~v9_lattices('#skF_6')), inference(splitLeft, [status(thm)], [c_57155])).
% 37.98/26.09  tff(c_57160, plain, (~v10_lattices('#skF_6') | v2_struct_0('#skF_6') | ~l3_lattices('#skF_6')), inference(resolution, [status(thm)], [c_4, c_57157])).
% 37.98/26.09  tff(c_57163, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_74, c_57160])).
% 37.98/26.09  tff(c_57165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_57163])).
% 37.98/26.09  tff(c_57167, plain, (v9_lattices('#skF_6')), inference(splitRight, [status(thm)], [c_57155])).
% 37.98/26.09  tff(c_56879, plain, (![B_1698]: (k2_lattices('#skF_6', B_1698, '#skF_2'('#skF_6'))=k2_lattices('#skF_6', '#skF_2'('#skF_6'), B_1698) | ~m1_subset_1(B_1698, u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_56581])).
% 37.98/26.09  tff(c_56906, plain, (![B_48]: (k2_lattices('#skF_6', k15_lattice3('#skF_6', B_48), '#skF_2'('#skF_6'))=k2_lattices('#skF_6', '#skF_2'('#skF_6'), k15_lattice3('#skF_6', B_48)) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_58, c_56879])).
% 37.98/26.09  tff(c_56935, plain, (![B_48]: (k2_lattices('#skF_6', k15_lattice3('#skF_6', B_48), '#skF_2'('#skF_6'))=k2_lattices('#skF_6', '#skF_2'('#skF_6'), k15_lattice3('#skF_6', B_48)) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_56906])).
% 37.98/26.09  tff(c_56941, plain, (![B_1699]: (k2_lattices('#skF_6', k15_lattice3('#skF_6', B_1699), '#skF_2'('#skF_6'))=k2_lattices('#skF_6', '#skF_2'('#skF_6'), k15_lattice3('#skF_6', B_1699)))), inference(negUnitSimplification, [status(thm)], [c_76, c_56935])).
% 37.98/26.09  tff(c_56186, plain, (![A_1642, C_1643]: (k2_lattices(A_1642, C_1643, '#skF_2'(A_1642))='#skF_2'(A_1642) | ~m1_subset_1(C_1643, u1_struct_0(A_1642)) | ~v13_lattices(A_1642) | ~l1_lattices(A_1642) | v2_struct_0(A_1642))), inference(cnfTransformation, [status(thm)], [f_136])).
% 37.98/26.09  tff(c_56203, plain, (![A_47, B_48]: (k2_lattices(A_47, k15_lattice3(A_47, B_48), '#skF_2'(A_47))='#skF_2'(A_47) | ~v13_lattices(A_47) | ~l1_lattices(A_47) | ~l3_lattices(A_47) | v2_struct_0(A_47))), inference(resolution, [status(thm)], [c_58, c_56186])).
% 37.98/26.09  tff(c_56947, plain, (![B_1699]: (k2_lattices('#skF_6', '#skF_2'('#skF_6'), k15_lattice3('#skF_6', B_1699))='#skF_2'('#skF_6') | ~v13_lattices('#skF_6') | ~l1_lattices('#skF_6') | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_56941, c_56203])).
% 37.98/26.09  tff(c_56968, plain, (![B_1699]: (k2_lattices('#skF_6', '#skF_2'('#skF_6'), k15_lattice3('#skF_6', B_1699))='#skF_2'('#skF_6') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_85, c_56145, c_56947])).
% 37.98/26.09  tff(c_56969, plain, (![B_1699]: (k2_lattices('#skF_6', '#skF_2'('#skF_6'), k15_lattice3('#skF_6', B_1699))='#skF_2'('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_76, c_56968])).
% 37.98/26.09  tff(c_56936, plain, (![B_48]: (k2_lattices('#skF_6', k15_lattice3('#skF_6', B_48), '#skF_2'('#skF_6'))=k2_lattices('#skF_6', '#skF_2'('#skF_6'), k15_lattice3('#skF_6', B_48)))), inference(negUnitSimplification, [status(thm)], [c_76, c_56935])).
% 37.98/26.09  tff(c_56981, plain, (![B_48]: (k2_lattices('#skF_6', k15_lattice3('#skF_6', B_48), '#skF_2'('#skF_6'))='#skF_2'('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56969, c_56936])).
% 37.98/26.09  tff(c_56297, plain, (![A_1657, B_1658]: (k15_lattice3(A_1657, a_2_3_lattice3(A_1657, B_1658))=B_1658 | ~m1_subset_1(B_1658, u1_struct_0(A_1657)) | ~l3_lattices(A_1657) | ~v4_lattice3(A_1657) | ~v10_lattices(A_1657) | v2_struct_0(A_1657))), inference(cnfTransformation, [status(thm)], [f_174])).
% 37.98/26.09  tff(c_56315, plain, (![A_13]: (k15_lattice3(A_13, a_2_3_lattice3(A_13, k5_lattices(A_13)))=k5_lattices(A_13) | ~l3_lattices(A_13) | ~v4_lattice3(A_13) | ~v10_lattices(A_13) | ~l1_lattices(A_13) | v2_struct_0(A_13))), inference(resolution, [status(thm)], [c_26, c_56297])).
% 37.98/26.09  tff(c_56532, plain, (k15_lattice3('#skF_6', a_2_3_lattice3('#skF_6', '#skF_2'('#skF_6')))=k5_lattices('#skF_6') | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | ~l1_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_56524, c_56315])).
% 37.98/26.09  tff(c_56551, plain, (k15_lattice3('#skF_6', a_2_3_lattice3('#skF_6', '#skF_2'('#skF_6')))='#skF_2'('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_74, c_72, c_70, c_56524, c_56532])).
% 37.98/26.09  tff(c_56552, plain, (k15_lattice3('#skF_6', a_2_3_lattice3('#skF_6', '#skF_2'('#skF_6')))='#skF_2'('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_76, c_56551])).
% 37.98/26.09  tff(c_56685, plain, (![B_55]: (r3_lattices('#skF_6', k15_lattice3('#skF_6', B_55), '#skF_2'('#skF_6')) | ~r1_tarski(B_55, a_2_3_lattice3('#skF_6', '#skF_2'('#skF_6'))) | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_56552, c_66])).
% 37.98/26.09  tff(c_56707, plain, (![B_55]: (r3_lattices('#skF_6', k15_lattice3('#skF_6', B_55), '#skF_2'('#skF_6')) | ~r1_tarski(B_55, a_2_3_lattice3('#skF_6', '#skF_2'('#skF_6'))) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_56685])).
% 37.98/26.09  tff(c_56708, plain, (![B_55]: (r3_lattices('#skF_6', k15_lattice3('#skF_6', B_55), '#skF_2'('#skF_6')) | ~r1_tarski(B_55, a_2_3_lattice3('#skF_6', '#skF_2'('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_56707])).
% 37.98/26.09  tff(c_57168, plain, (![A_1708, B_1709, C_1710]: (r1_lattices(A_1708, B_1709, C_1710) | ~r3_lattices(A_1708, B_1709, C_1710) | ~m1_subset_1(C_1710, u1_struct_0(A_1708)) | ~m1_subset_1(B_1709, u1_struct_0(A_1708)) | ~l3_lattices(A_1708) | ~v9_lattices(A_1708) | ~v8_lattices(A_1708) | ~v6_lattices(A_1708) | v2_struct_0(A_1708))), inference(cnfTransformation, [status(thm)], [f_100])).
% 37.98/26.09  tff(c_57176, plain, (![B_55]: (r1_lattices('#skF_6', k15_lattice3('#skF_6', B_55), '#skF_2'('#skF_6')) | ~m1_subset_1('#skF_2'('#skF_6'), u1_struct_0('#skF_6')) | ~m1_subset_1(k15_lattice3('#skF_6', B_55), u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | ~v6_lattices('#skF_6') | v2_struct_0('#skF_6') | ~r1_tarski(B_55, a_2_3_lattice3('#skF_6', '#skF_2'('#skF_6'))))), inference(resolution, [status(thm)], [c_56708, c_57168])).
% 37.98/26.09  tff(c_57195, plain, (![B_55]: (r1_lattices('#skF_6', k15_lattice3('#skF_6', B_55), '#skF_2'('#skF_6')) | ~m1_subset_1(k15_lattice3('#skF_6', B_55), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6') | ~r1_tarski(B_55, a_2_3_lattice3('#skF_6', '#skF_2'('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_56859, c_57156, c_57167, c_70, c_56564, c_57176])).
% 37.98/26.09  tff(c_57276, plain, (![B_1717]: (r1_lattices('#skF_6', k15_lattice3('#skF_6', B_1717), '#skF_2'('#skF_6')) | ~m1_subset_1(k15_lattice3('#skF_6', B_1717), u1_struct_0('#skF_6')) | ~r1_tarski(B_1717, a_2_3_lattice3('#skF_6', '#skF_2'('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_57195])).
% 37.98/26.09  tff(c_57278, plain, (![B_1717]: (k2_lattices('#skF_6', k15_lattice3('#skF_6', B_1717), '#skF_2'('#skF_6'))=k15_lattice3('#skF_6', B_1717) | ~m1_subset_1('#skF_2'('#skF_6'), u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v9_lattices('#skF_6') | ~v8_lattices('#skF_6') | v2_struct_0('#skF_6') | ~m1_subset_1(k15_lattice3('#skF_6', B_1717), u1_struct_0('#skF_6')) | ~r1_tarski(B_1717, a_2_3_lattice3('#skF_6', '#skF_2'('#skF_6'))))), inference(resolution, [status(thm)], [c_57276, c_38])).
% 37.98/26.09  tff(c_57292, plain, (![B_1717]: (k15_lattice3('#skF_6', B_1717)='#skF_2'('#skF_6') | v2_struct_0('#skF_6') | ~m1_subset_1(k15_lattice3('#skF_6', B_1717), u1_struct_0('#skF_6')) | ~r1_tarski(B_1717, a_2_3_lattice3('#skF_6', '#skF_2'('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_57156, c_57167, c_70, c_56564, c_56981, c_57278])).
% 37.98/26.09  tff(c_57303, plain, (![B_1720]: (k15_lattice3('#skF_6', B_1720)='#skF_2'('#skF_6') | ~m1_subset_1(k15_lattice3('#skF_6', B_1720), u1_struct_0('#skF_6')) | ~r1_tarski(B_1720, a_2_3_lattice3('#skF_6', '#skF_2'('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_57292])).
% 37.98/26.09  tff(c_57307, plain, (k15_lattice3('#skF_6', k1_xboole_0)='#skF_2'('#skF_6') | ~m1_subset_1(k15_lattice3('#skF_6', k1_xboole_0), u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_2, c_57303])).
% 37.98/26.09  tff(c_57310, plain, (~m1_subset_1(k15_lattice3('#skF_6', k1_xboole_0), u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_56525, c_57307])).
% 37.98/26.09  tff(c_57313, plain, (~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_58, c_57310])).
% 37.98/26.09  tff(c_57316, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_57313])).
% 37.98/26.09  tff(c_57318, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_57316])).
% 37.98/26.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 37.98/26.09  
% 37.98/26.09  Inference rules
% 37.98/26.09  ----------------------
% 37.98/26.09  #Ref     : 0
% 37.98/26.09  #Sup     : 17712
% 37.98/26.09  #Fact    : 4
% 37.98/26.09  #Define  : 0
% 37.98/26.09  #Split   : 6
% 37.98/26.09  #Chain   : 0
% 37.98/26.09  #Close   : 0
% 37.98/26.09  
% 37.98/26.09  Ordering : KBO
% 37.98/26.09  
% 37.98/26.09  Simplification rules
% 37.98/26.09  ----------------------
% 37.98/26.09  #Subsume      : 4309
% 37.98/26.09  #Demod        : 370
% 37.98/26.09  #Tautology    : 2113
% 37.98/26.09  #SimpNegUnit  : 88
% 37.98/26.09  #BackRed      : 2
% 37.98/26.09  
% 37.98/26.09  #Partial instantiations: 0
% 37.98/26.09  #Strategies tried      : 1
% 37.98/26.09  
% 37.98/26.09  Timing (in seconds)
% 37.98/26.09  ----------------------
% 38.26/26.10  Preprocessing        : 0.38
% 38.26/26.10  Parsing              : 0.19
% 38.26/26.10  CNF conversion       : 0.03
% 38.26/26.10  Main loop            : 24.92
% 38.26/26.10  Inferencing          : 7.06
% 38.26/26.10  Reduction            : 4.33
% 38.26/26.10  Demodulation         : 3.06
% 38.26/26.10  BG Simplification    : 0.75
% 38.26/26.10  Subsumption          : 11.75
% 38.26/26.10  Abstraction          : 0.79
% 38.26/26.10  MUC search           : 0.00
% 38.26/26.10  Cooper               : 0.00
% 38.26/26.10  Total                : 25.36
% 38.26/26.10  Index Insertion      : 0.00
% 38.26/26.10  Index Deletion       : 0.00
% 38.26/26.10  Index Matching       : 0.00
% 38.26/26.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
