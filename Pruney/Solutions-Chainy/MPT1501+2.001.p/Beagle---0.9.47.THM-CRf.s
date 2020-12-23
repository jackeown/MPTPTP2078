%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:44 EST 2020

% Result     : Theorem 23.65s
% Output     : CNFRefutation 24.21s
% Verified   : 
% Statistics : Number of formulae       :  556 (2579 expanded)
%              Number of leaves         :   40 ( 873 expanded)
%              Depth                    :   33
%              Number of atoms          : 2331 (13607 expanded)
%              Number of equality atoms :   94 ( 976 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_1_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k16_lattice3,type,(
    k16_lattice3: ( $i * $i ) > $i )).

tff(k15_lattice3,type,(
    k15_lattice3: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff(a_2_1_lattice3,type,(
    a_2_1_lattice3: ( $i * $i ) > $i )).

tff(r4_lattice3,type,(
    r4_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_lattice3,type,(
    v4_lattice3: $i > $o )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r3_lattice3,type,(
    r3_lattice3: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_177,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( B = k16_lattice3(A,C)
              <=> ( r3_lattice3(A,B,C)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r3_lattice3(A,D,C)
                       => r3_lattices(A,D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( r3_lattice3(A,B,C)
            <=> ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r2_hidden(D,C)
                   => r1_lattices(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).

tff(f_102,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).

tff(f_152,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & l3_lattices(B) )
     => ( r2_hidden(A,a_2_1_lattice3(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & r3_lattice3(B,D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).

tff(f_138,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] : k16_lattice3(A,B) = k15_lattice3(A,a_2_1_lattice3(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d22_lattice3)).

tff(f_130,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).

tff(f_47,axiom,(
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

tff(f_66,axiom,(
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

tff(c_64,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_82,plain,
    ( r3_lattice3('#skF_5','#skF_6','#skF_7')
    | m1_subset_1('#skF_9',u1_struct_0('#skF_5'))
    | ~ r3_lattice3('#skF_5','#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_101,plain,(
    ~ r3_lattice3('#skF_5','#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_58,plain,(
    l3_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_26,plain,(
    ! [A_5,B_17,C_23] :
      ( m1_subset_1('#skF_1'(A_5,B_17,C_23),u1_struct_0(A_5))
      | r3_lattice3(A_5,B_17,C_23)
      | ~ m1_subset_1(B_17,u1_struct_0(A_5))
      | ~ l3_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_32,plain,(
    ! [A_27,B_39,C_45] :
      ( r2_hidden('#skF_2'(A_27,B_39,C_45),C_45)
      | r4_lattice3(A_27,B_39,C_45)
      | ~ m1_subset_1(B_39,u1_struct_0(A_27))
      | ~ l3_lattices(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_124,plain,(
    ! [A_112,B_113,C_114] :
      ( r2_hidden('#skF_2'(A_112,B_113,C_114),C_114)
      | r4_lattice3(A_112,B_113,C_114)
      | ~ m1_subset_1(B_113,u1_struct_0(A_112))
      | ~ l3_lattices(A_112)
      | v2_struct_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_52,plain,(
    ! [A_64,B_65,C_66] :
      ( '#skF_4'(A_64,B_65,C_66) = A_64
      | ~ r2_hidden(A_64,a_2_1_lattice3(B_65,C_66))
      | ~ l3_lattices(B_65)
      | v2_struct_0(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1113,plain,(
    ! [A_348,B_349,B_350,C_351] :
      ( '#skF_4'('#skF_2'(A_348,B_349,a_2_1_lattice3(B_350,C_351)),B_350,C_351) = '#skF_2'(A_348,B_349,a_2_1_lattice3(B_350,C_351))
      | ~ l3_lattices(B_350)
      | v2_struct_0(B_350)
      | r4_lattice3(A_348,B_349,a_2_1_lattice3(B_350,C_351))
      | ~ m1_subset_1(B_349,u1_struct_0(A_348))
      | ~ l3_lattices(A_348)
      | v2_struct_0(A_348) ) ),
    inference(resolution,[status(thm)],[c_124,c_52])).

tff(c_54,plain,(
    ! [A_64,B_65,C_66] :
      ( m1_subset_1('#skF_4'(A_64,B_65,C_66),u1_struct_0(B_65))
      | ~ r2_hidden(A_64,a_2_1_lattice3(B_65,C_66))
      | ~ l3_lattices(B_65)
      | v2_struct_0(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_2034,plain,(
    ! [A_480,B_481,B_482,C_483] :
      ( m1_subset_1('#skF_2'(A_480,B_481,a_2_1_lattice3(B_482,C_483)),u1_struct_0(B_482))
      | ~ r2_hidden('#skF_2'(A_480,B_481,a_2_1_lattice3(B_482,C_483)),a_2_1_lattice3(B_482,C_483))
      | ~ l3_lattices(B_482)
      | v2_struct_0(B_482)
      | ~ l3_lattices(B_482)
      | v2_struct_0(B_482)
      | r4_lattice3(A_480,B_481,a_2_1_lattice3(B_482,C_483))
      | ~ m1_subset_1(B_481,u1_struct_0(A_480))
      | ~ l3_lattices(A_480)
      | v2_struct_0(A_480) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1113,c_54])).

tff(c_2043,plain,(
    ! [A_27,B_39,B_482,C_483] :
      ( m1_subset_1('#skF_2'(A_27,B_39,a_2_1_lattice3(B_482,C_483)),u1_struct_0(B_482))
      | ~ l3_lattices(B_482)
      | v2_struct_0(B_482)
      | r4_lattice3(A_27,B_39,a_2_1_lattice3(B_482,C_483))
      | ~ m1_subset_1(B_39,u1_struct_0(A_27))
      | ~ l3_lattices(A_27)
      | v2_struct_0(A_27) ) ),
    inference(resolution,[status(thm)],[c_32,c_2034])).

tff(c_50,plain,(
    ! [B_65,A_64,C_66] :
      ( r3_lattice3(B_65,'#skF_4'(A_64,B_65,C_66),C_66)
      | ~ r2_hidden(A_64,a_2_1_lattice3(B_65,C_66))
      | ~ l3_lattices(B_65)
      | v2_struct_0(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1805,plain,(
    ! [B_466,A_467,B_468,C_469] :
      ( r3_lattice3(B_466,'#skF_2'(A_467,B_468,a_2_1_lattice3(B_466,C_469)),C_469)
      | ~ r2_hidden('#skF_2'(A_467,B_468,a_2_1_lattice3(B_466,C_469)),a_2_1_lattice3(B_466,C_469))
      | ~ l3_lattices(B_466)
      | v2_struct_0(B_466)
      | ~ l3_lattices(B_466)
      | v2_struct_0(B_466)
      | r4_lattice3(A_467,B_468,a_2_1_lattice3(B_466,C_469))
      | ~ m1_subset_1(B_468,u1_struct_0(A_467))
      | ~ l3_lattices(A_467)
      | v2_struct_0(A_467) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1113,c_50])).

tff(c_1814,plain,(
    ! [B_466,A_27,B_39,C_469] :
      ( r3_lattice3(B_466,'#skF_2'(A_27,B_39,a_2_1_lattice3(B_466,C_469)),C_469)
      | ~ l3_lattices(B_466)
      | v2_struct_0(B_466)
      | r4_lattice3(A_27,B_39,a_2_1_lattice3(B_466,C_469))
      | ~ m1_subset_1(B_39,u1_struct_0(A_27))
      | ~ l3_lattices(A_27)
      | v2_struct_0(A_27) ) ),
    inference(resolution,[status(thm)],[c_32,c_1805])).

tff(c_24,plain,(
    ! [A_5,B_17,C_23] :
      ( r2_hidden('#skF_1'(A_5,B_17,C_23),C_23)
      | r3_lattice3(A_5,B_17,C_23)
      | ~ m1_subset_1(B_17,u1_struct_0(A_5))
      | ~ l3_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_153,plain,(
    ! [A_136,B_137,D_138,C_139] :
      ( r1_lattices(A_136,B_137,D_138)
      | ~ r2_hidden(D_138,C_139)
      | ~ m1_subset_1(D_138,u1_struct_0(A_136))
      | ~ r3_lattice3(A_136,B_137,C_139)
      | ~ m1_subset_1(B_137,u1_struct_0(A_136))
      | ~ l3_lattices(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1605,plain,(
    ! [C_432,B_435,B_433,A_436,A_434] :
      ( r1_lattices(A_436,B_435,'#skF_1'(A_434,B_433,C_432))
      | ~ m1_subset_1('#skF_1'(A_434,B_433,C_432),u1_struct_0(A_436))
      | ~ r3_lattice3(A_436,B_435,C_432)
      | ~ m1_subset_1(B_435,u1_struct_0(A_436))
      | ~ l3_lattices(A_436)
      | v2_struct_0(A_436)
      | r3_lattice3(A_434,B_433,C_432)
      | ~ m1_subset_1(B_433,u1_struct_0(A_434))
      | ~ l3_lattices(A_434)
      | v2_struct_0(A_434) ) ),
    inference(resolution,[status(thm)],[c_24,c_153])).

tff(c_1609,plain,(
    ! [A_437,B_438,B_439,C_440] :
      ( r1_lattices(A_437,B_438,'#skF_1'(A_437,B_439,C_440))
      | ~ r3_lattice3(A_437,B_438,C_440)
      | ~ m1_subset_1(B_438,u1_struct_0(A_437))
      | r3_lattice3(A_437,B_439,C_440)
      | ~ m1_subset_1(B_439,u1_struct_0(A_437))
      | ~ l3_lattices(A_437)
      | v2_struct_0(A_437) ) ),
    inference(resolution,[status(thm)],[c_26,c_1605])).

tff(c_30,plain,(
    ! [A_27,B_39,C_45] :
      ( ~ r1_lattices(A_27,'#skF_2'(A_27,B_39,C_45),B_39)
      | r4_lattice3(A_27,B_39,C_45)
      | ~ m1_subset_1(B_39,u1_struct_0(A_27))
      | ~ l3_lattices(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_6413,plain,(
    ! [A_758,B_759,C_760,C_761] :
      ( r4_lattice3(A_758,'#skF_1'(A_758,B_759,C_760),C_761)
      | ~ m1_subset_1('#skF_1'(A_758,B_759,C_760),u1_struct_0(A_758))
      | ~ r3_lattice3(A_758,'#skF_2'(A_758,'#skF_1'(A_758,B_759,C_760),C_761),C_760)
      | ~ m1_subset_1('#skF_2'(A_758,'#skF_1'(A_758,B_759,C_760),C_761),u1_struct_0(A_758))
      | r3_lattice3(A_758,B_759,C_760)
      | ~ m1_subset_1(B_759,u1_struct_0(A_758))
      | ~ l3_lattices(A_758)
      | v2_struct_0(A_758) ) ),
    inference(resolution,[status(thm)],[c_1609,c_30])).

tff(c_11538,plain,(
    ! [A_1062,B_1063,C_1064] :
      ( ~ m1_subset_1('#skF_2'(A_1062,'#skF_1'(A_1062,B_1063,C_1064),a_2_1_lattice3(A_1062,C_1064)),u1_struct_0(A_1062))
      | r3_lattice3(A_1062,B_1063,C_1064)
      | ~ m1_subset_1(B_1063,u1_struct_0(A_1062))
      | r4_lattice3(A_1062,'#skF_1'(A_1062,B_1063,C_1064),a_2_1_lattice3(A_1062,C_1064))
      | ~ m1_subset_1('#skF_1'(A_1062,B_1063,C_1064),u1_struct_0(A_1062))
      | ~ l3_lattices(A_1062)
      | v2_struct_0(A_1062) ) ),
    inference(resolution,[status(thm)],[c_1814,c_6413])).

tff(c_11549,plain,(
    ! [B_1065,B_1066,C_1067] :
      ( r3_lattice3(B_1065,B_1066,C_1067)
      | ~ m1_subset_1(B_1066,u1_struct_0(B_1065))
      | r4_lattice3(B_1065,'#skF_1'(B_1065,B_1066,C_1067),a_2_1_lattice3(B_1065,C_1067))
      | ~ m1_subset_1('#skF_1'(B_1065,B_1066,C_1067),u1_struct_0(B_1065))
      | ~ l3_lattices(B_1065)
      | v2_struct_0(B_1065) ) ),
    inference(resolution,[status(thm)],[c_2043,c_11538])).

tff(c_62,plain,(
    v10_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_60,plain,(
    v4_lattice3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_88,plain,
    ( r3_lattice3('#skF_5','#skF_6','#skF_7')
    | k16_lattice3('#skF_5','#skF_8') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_90,plain,(
    k16_lattice3('#skF_5','#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_46,plain,(
    ! [A_61,B_63] :
      ( k15_lattice3(A_61,a_2_1_lattice3(A_61,B_63)) = k16_lattice3(A_61,B_63)
      | ~ l3_lattices(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_140,plain,(
    ! [A_130,B_131] :
      ( r4_lattice3(A_130,k15_lattice3(A_130,B_131),B_131)
      | ~ m1_subset_1(k15_lattice3(A_130,B_131),u1_struct_0(A_130))
      | ~ v4_lattice3(A_130)
      | ~ v10_lattices(A_130)
      | ~ l3_lattices(A_130)
      | v2_struct_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1079,plain,(
    ! [A_338,B_339] :
      ( r4_lattice3(A_338,k15_lattice3(A_338,a_2_1_lattice3(A_338,B_339)),a_2_1_lattice3(A_338,B_339))
      | ~ m1_subset_1(k16_lattice3(A_338,B_339),u1_struct_0(A_338))
      | ~ v4_lattice3(A_338)
      | ~ v10_lattices(A_338)
      | ~ l3_lattices(A_338)
      | v2_struct_0(A_338)
      | ~ l3_lattices(A_338)
      | v2_struct_0(A_338) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_140])).

tff(c_1087,plain,(
    ! [A_341,B_342] :
      ( r4_lattice3(A_341,k16_lattice3(A_341,B_342),a_2_1_lattice3(A_341,B_342))
      | ~ m1_subset_1(k16_lattice3(A_341,B_342),u1_struct_0(A_341))
      | ~ v4_lattice3(A_341)
      | ~ v10_lattices(A_341)
      | ~ l3_lattices(A_341)
      | v2_struct_0(A_341)
      | ~ l3_lattices(A_341)
      | v2_struct_0(A_341)
      | ~ l3_lattices(A_341)
      | v2_struct_0(A_341) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1079])).

tff(c_1090,plain,
    ( r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_8'))
    | ~ m1_subset_1(k16_lattice3('#skF_5','#skF_8'),u1_struct_0('#skF_5'))
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_1087])).

tff(c_1092,plain,
    ( r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_8'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_58,c_58,c_62,c_60,c_56,c_90,c_1090])).

tff(c_1093,plain,(
    r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1092])).

tff(c_40,plain,(
    ! [A_49,B_56,C_57] :
      ( m1_subset_1('#skF_3'(A_49,B_56,C_57),u1_struct_0(A_49))
      | k15_lattice3(A_49,B_56) = C_57
      | ~ r4_lattice3(A_49,C_57,B_56)
      | ~ m1_subset_1(C_57,u1_struct_0(A_49))
      | ~ v4_lattice3(A_49)
      | ~ v10_lattices(A_49)
      | ~ l3_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_38,plain,(
    ! [A_49,B_56,C_57] :
      ( r4_lattice3(A_49,'#skF_3'(A_49,B_56,C_57),B_56)
      | k15_lattice3(A_49,B_56) = C_57
      | ~ r4_lattice3(A_49,C_57,B_56)
      | ~ m1_subset_1(C_57,u1_struct_0(A_49))
      | ~ v4_lattice3(A_49)
      | ~ v10_lattices(A_49)
      | ~ l3_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_142,plain,(
    ! [A_61,B_63] :
      ( r4_lattice3(A_61,k15_lattice3(A_61,a_2_1_lattice3(A_61,B_63)),a_2_1_lattice3(A_61,B_63))
      | ~ m1_subset_1(k16_lattice3(A_61,B_63),u1_struct_0(A_61))
      | ~ v4_lattice3(A_61)
      | ~ v10_lattices(A_61)
      | ~ l3_lattices(A_61)
      | v2_struct_0(A_61)
      | ~ l3_lattices(A_61)
      | v2_struct_0(A_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_140])).

tff(c_1003,plain,(
    ! [A_326,B_327,D_328] :
      ( r1_lattices(A_326,k15_lattice3(A_326,B_327),D_328)
      | ~ r4_lattice3(A_326,D_328,B_327)
      | ~ m1_subset_1(D_328,u1_struct_0(A_326))
      | ~ m1_subset_1(k15_lattice3(A_326,B_327),u1_struct_0(A_326))
      | ~ v4_lattice3(A_326)
      | ~ v10_lattices(A_326)
      | ~ l3_lattices(A_326)
      | v2_struct_0(A_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1342,plain,(
    ! [A_391,B_392,D_393] :
      ( r1_lattices(A_391,k15_lattice3(A_391,a_2_1_lattice3(A_391,B_392)),D_393)
      | ~ r4_lattice3(A_391,D_393,a_2_1_lattice3(A_391,B_392))
      | ~ m1_subset_1(D_393,u1_struct_0(A_391))
      | ~ m1_subset_1(k16_lattice3(A_391,B_392),u1_struct_0(A_391))
      | ~ v4_lattice3(A_391)
      | ~ v10_lattices(A_391)
      | ~ l3_lattices(A_391)
      | v2_struct_0(A_391)
      | ~ l3_lattices(A_391)
      | v2_struct_0(A_391) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1003])).

tff(c_1641,plain,(
    ! [A_452,B_453,D_454] :
      ( r1_lattices(A_452,k16_lattice3(A_452,B_453),D_454)
      | ~ r4_lattice3(A_452,D_454,a_2_1_lattice3(A_452,B_453))
      | ~ m1_subset_1(D_454,u1_struct_0(A_452))
      | ~ m1_subset_1(k16_lattice3(A_452,B_453),u1_struct_0(A_452))
      | ~ v4_lattice3(A_452)
      | ~ v10_lattices(A_452)
      | ~ l3_lattices(A_452)
      | v2_struct_0(A_452)
      | ~ l3_lattices(A_452)
      | v2_struct_0(A_452)
      | ~ l3_lattices(A_452)
      | v2_struct_0(A_452) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1342])).

tff(c_1671,plain,(
    ! [A_457,B_458] :
      ( r1_lattices(A_457,k16_lattice3(A_457,B_458),k15_lattice3(A_457,a_2_1_lattice3(A_457,B_458)))
      | ~ m1_subset_1(k15_lattice3(A_457,a_2_1_lattice3(A_457,B_458)),u1_struct_0(A_457))
      | ~ m1_subset_1(k16_lattice3(A_457,B_458),u1_struct_0(A_457))
      | ~ v4_lattice3(A_457)
      | ~ v10_lattices(A_457)
      | ~ l3_lattices(A_457)
      | v2_struct_0(A_457) ) ),
    inference(resolution,[status(thm)],[c_142,c_1641])).

tff(c_1677,plain,
    ( r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')))
    | ~ m1_subset_1(k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')),u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k16_lattice3('#skF_5','#skF_8'),u1_struct_0('#skF_5'))
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_1671])).

tff(c_1679,plain,
    ( r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')))
    | ~ m1_subset_1(k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')),u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_60,c_56,c_90,c_1677])).

tff(c_1680,plain,
    ( r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')))
    | ~ m1_subset_1(k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1679])).

tff(c_1685,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1680])).

tff(c_1688,plain,
    ( ~ m1_subset_1(k16_lattice3('#skF_5','#skF_8'),u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1685])).

tff(c_1690,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_90,c_1688])).

tff(c_1692,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1690])).

tff(c_1694,plain,(
    m1_subset_1(k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1680])).

tff(c_42,plain,(
    ! [A_49,B_56,D_60] :
      ( r1_lattices(A_49,k15_lattice3(A_49,B_56),D_60)
      | ~ r4_lattice3(A_49,D_60,B_56)
      | ~ m1_subset_1(D_60,u1_struct_0(A_49))
      | ~ m1_subset_1(k15_lattice3(A_49,B_56),u1_struct_0(A_49))
      | ~ v4_lattice3(A_49)
      | ~ v10_lattices(A_49)
      | ~ l3_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1721,plain,(
    ! [D_60] :
      ( r1_lattices('#skF_5',k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')),D_60)
      | ~ r4_lattice3('#skF_5',D_60,a_2_1_lattice3('#skF_5','#skF_8'))
      | ~ m1_subset_1(D_60,u1_struct_0('#skF_5'))
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1694,c_42])).

tff(c_1746,plain,(
    ! [D_60] :
      ( r1_lattices('#skF_5',k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')),D_60)
      | ~ r4_lattice3('#skF_5',D_60,a_2_1_lattice3('#skF_5','#skF_8'))
      | ~ m1_subset_1(D_60,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_60,c_1721])).

tff(c_1823,plain,(
    ! [D_470] :
      ( r1_lattices('#skF_5',k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')),D_470)
      | ~ r4_lattice3('#skF_5',D_470,a_2_1_lattice3('#skF_5','#skF_8'))
      | ~ m1_subset_1(D_470,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1746])).

tff(c_1838,plain,(
    ! [D_470] :
      ( r1_lattices('#skF_5',k16_lattice3('#skF_5','#skF_8'),D_470)
      | ~ r4_lattice3('#skF_5',D_470,a_2_1_lattice3('#skF_5','#skF_8'))
      | ~ m1_subset_1(D_470,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1823])).

tff(c_1851,plain,(
    ! [D_470] :
      ( r1_lattices('#skF_5','#skF_6',D_470)
      | ~ r4_lattice3('#skF_5',D_470,a_2_1_lattice3('#skF_5','#skF_8'))
      | ~ m1_subset_1(D_470,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_90,c_1838])).

tff(c_1853,plain,(
    ! [D_471] :
      ( r1_lattices('#skF_5','#skF_6',D_471)
      | ~ r4_lattice3('#skF_5',D_471,a_2_1_lattice3('#skF_5','#skF_8'))
      | ~ m1_subset_1(D_471,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1851])).

tff(c_1871,plain,(
    ! [C_57] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3('#skF_5','#skF_8'),C_57))
      | ~ m1_subset_1('#skF_3'('#skF_5',a_2_1_lattice3('#skF_5','#skF_8'),C_57),u1_struct_0('#skF_5'))
      | k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')) = C_57
      | ~ r4_lattice3('#skF_5',C_57,a_2_1_lattice3('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_57,u1_struct_0('#skF_5'))
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_38,c_1853])).

tff(c_1888,plain,(
    ! [C_57] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3('#skF_5','#skF_8'),C_57))
      | ~ m1_subset_1('#skF_3'('#skF_5',a_2_1_lattice3('#skF_5','#skF_8'),C_57),u1_struct_0('#skF_5'))
      | k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')) = C_57
      | ~ r4_lattice3('#skF_5',C_57,a_2_1_lattice3('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_57,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_60,c_1871])).

tff(c_7246,plain,(
    ! [C_813] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3('#skF_5','#skF_8'),C_813))
      | ~ m1_subset_1('#skF_3'('#skF_5',a_2_1_lattice3('#skF_5','#skF_8'),C_813),u1_struct_0('#skF_5'))
      | k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')) = C_813
      | ~ r4_lattice3('#skF_5',C_813,a_2_1_lattice3('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_813,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1888])).

tff(c_7250,plain,(
    ! [C_57] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3('#skF_5','#skF_8'),C_57))
      | k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')) = C_57
      | ~ r4_lattice3('#skF_5',C_57,a_2_1_lattice3('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_57,u1_struct_0('#skF_5'))
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_7246])).

tff(c_7253,plain,(
    ! [C_57] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3('#skF_5','#skF_8'),C_57))
      | k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')) = C_57
      | ~ r4_lattice3('#skF_5',C_57,a_2_1_lattice3('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_57,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_60,c_7250])).

tff(c_7255,plain,(
    ! [C_814] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3('#skF_5','#skF_8'),C_814))
      | k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')) = C_814
      | ~ r4_lattice3('#skF_5',C_814,a_2_1_lattice3('#skF_5','#skF_8'))
      | ~ m1_subset_1(C_814,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_7253])).

tff(c_36,plain,(
    ! [A_49,C_57,B_56] :
      ( ~ r1_lattices(A_49,C_57,'#skF_3'(A_49,B_56,C_57))
      | k15_lattice3(A_49,B_56) = C_57
      | ~ r4_lattice3(A_49,C_57,B_56)
      | ~ m1_subset_1(C_57,u1_struct_0(A_49))
      | ~ v4_lattice3(A_49)
      | ~ v10_lattices(A_49)
      | ~ l3_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_7259,plain,
    ( ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')) = '#skF_6'
    | ~ r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_7255,c_36])).

tff(c_7262,plain,
    ( v2_struct_0('#skF_5')
    | k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1093,c_58,c_62,c_60,c_7259])).

tff(c_7263,plain,(
    k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_7262])).

tff(c_22,plain,(
    ! [A_5,B_17,C_23] :
      ( ~ r1_lattices(A_5,B_17,'#skF_1'(A_5,B_17,C_23))
      | r3_lattice3(A_5,B_17,C_23)
      | ~ m1_subset_1(B_17,u1_struct_0(A_5))
      | ~ l3_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1835,plain,(
    ! [C_23] :
      ( r3_lattice3('#skF_5',k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')),C_23)
      | ~ m1_subset_1(k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r4_lattice3('#skF_5','#skF_1'('#skF_5',k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')),C_23),a_2_1_lattice3('#skF_5','#skF_8'))
      | ~ m1_subset_1('#skF_1'('#skF_5',k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')),C_23),u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1823,c_22])).

tff(c_1848,plain,(
    ! [C_23] :
      ( r3_lattice3('#skF_5',k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')),C_23)
      | v2_struct_0('#skF_5')
      | ~ r4_lattice3('#skF_5','#skF_1'('#skF_5',k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')),C_23),a_2_1_lattice3('#skF_5','#skF_8'))
      | ~ m1_subset_1('#skF_1'('#skF_5',k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')),C_23),u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1694,c_1835])).

tff(c_5682,plain,(
    ! [C_685] :
      ( r3_lattice3('#skF_5',k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')),C_685)
      | ~ r4_lattice3('#skF_5','#skF_1'('#skF_5',k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')),C_685),a_2_1_lattice3('#skF_5','#skF_8'))
      | ~ m1_subset_1('#skF_1'('#skF_5',k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')),C_685),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1848])).

tff(c_5685,plain,(
    ! [C_685] :
      ( r3_lattice3('#skF_5',k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')),C_685)
      | ~ r4_lattice3('#skF_5','#skF_1'('#skF_5',k16_lattice3('#skF_5','#skF_8'),C_685),a_2_1_lattice3('#skF_5','#skF_8'))
      | ~ m1_subset_1('#skF_1'('#skF_5',k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')),C_685),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_5682])).

tff(c_5687,plain,(
    ! [C_685] :
      ( r3_lattice3('#skF_5',k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')),C_685)
      | ~ r4_lattice3('#skF_5','#skF_1'('#skF_5','#skF_6',C_685),a_2_1_lattice3('#skF_5','#skF_8'))
      | ~ m1_subset_1('#skF_1'('#skF_5',k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')),C_685),u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_90,c_5685])).

tff(c_5689,plain,(
    ! [C_686] :
      ( r3_lattice3('#skF_5',k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')),C_686)
      | ~ r4_lattice3('#skF_5','#skF_1'('#skF_5','#skF_6',C_686),a_2_1_lattice3('#skF_5','#skF_8'))
      | ~ m1_subset_1('#skF_1'('#skF_5',k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')),C_686),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_5687])).

tff(c_5697,plain,(
    ! [C_23] :
      ( ~ r4_lattice3('#skF_5','#skF_1'('#skF_5','#skF_6',C_23),a_2_1_lattice3('#skF_5','#skF_8'))
      | r3_lattice3('#skF_5',k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')),C_23)
      | ~ m1_subset_1(k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_26,c_5689])).

tff(c_5707,plain,(
    ! [C_23] :
      ( ~ r4_lattice3('#skF_5','#skF_1'('#skF_5','#skF_6',C_23),a_2_1_lattice3('#skF_5','#skF_8'))
      | r3_lattice3('#skF_5',k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')),C_23)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1694,c_5697])).

tff(c_5708,plain,(
    ! [C_23] :
      ( ~ r4_lattice3('#skF_5','#skF_1'('#skF_5','#skF_6',C_23),a_2_1_lattice3('#skF_5','#skF_8'))
      | r3_lattice3('#skF_5',k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_8')),C_23) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_5707])).

tff(c_7283,plain,(
    ! [C_23] :
      ( ~ r4_lattice3('#skF_5','#skF_1'('#skF_5','#skF_6',C_23),a_2_1_lattice3('#skF_5','#skF_8'))
      | r3_lattice3('#skF_5','#skF_6',C_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7263,c_5708])).

tff(c_11559,plain,
    ( r3_lattice3('#skF_5','#skF_6','#skF_8')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_6','#skF_8'),u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_11549,c_7283])).

tff(c_11595,plain,
    ( r3_lattice3('#skF_5','#skF_6','#skF_8')
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_6','#skF_8'),u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_11559])).

tff(c_11596,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5','#skF_6','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_101,c_11595])).

tff(c_11615,plain,
    ( r3_lattice3('#skF_5','#skF_6','#skF_8')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_11596])).

tff(c_11618,plain,
    ( r3_lattice3('#skF_5','#skF_6','#skF_8')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_11615])).

tff(c_11620,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_101,c_11618])).

tff(c_11622,plain,(
    r3_lattice3('#skF_5','#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_72,plain,
    ( k16_lattice3('#skF_5','#skF_7') != '#skF_6'
    | r3_lattice3('#skF_5','#skF_9','#skF_8')
    | ~ r3_lattice3('#skF_5','#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_11625,plain,
    ( k16_lattice3('#skF_5','#skF_7') != '#skF_6'
    | r3_lattice3('#skF_5','#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11622,c_72])).

tff(c_11626,plain,(
    k16_lattice3('#skF_5','#skF_7') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_11625])).

tff(c_11621,plain,
    ( m1_subset_1('#skF_9',u1_struct_0('#skF_5'))
    | r3_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_11623,plain,(
    r3_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_11621])).

tff(c_46307,plain,(
    ! [A_3116,B_3117,C_3118] :
      ( r2_hidden('#skF_2'(A_3116,B_3117,C_3118),C_3118)
      | r4_lattice3(A_3116,B_3117,C_3118)
      | ~ m1_subset_1(B_3117,u1_struct_0(A_3116))
      | ~ l3_lattices(A_3116)
      | v2_struct_0(A_3116) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_47248,plain,(
    ! [A_3241,B_3242,B_3243,C_3244] :
      ( '#skF_4'('#skF_2'(A_3241,B_3242,a_2_1_lattice3(B_3243,C_3244)),B_3243,C_3244) = '#skF_2'(A_3241,B_3242,a_2_1_lattice3(B_3243,C_3244))
      | ~ l3_lattices(B_3243)
      | v2_struct_0(B_3243)
      | r4_lattice3(A_3241,B_3242,a_2_1_lattice3(B_3243,C_3244))
      | ~ m1_subset_1(B_3242,u1_struct_0(A_3241))
      | ~ l3_lattices(A_3241)
      | v2_struct_0(A_3241) ) ),
    inference(resolution,[status(thm)],[c_46307,c_52])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_80,plain,(
    ! [D_87] :
      ( r3_lattices('#skF_5',D_87,'#skF_6')
      | ~ r3_lattice3('#skF_5',D_87,'#skF_7')
      | ~ m1_subset_1(D_87,u1_struct_0('#skF_5'))
      | m1_subset_1('#skF_9',u1_struct_0('#skF_5'))
      | ~ r3_lattice3('#skF_5','#skF_6','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_46314,plain,(
    ! [D_87] :
      ( r3_lattices('#skF_5',D_87,'#skF_6')
      | ~ r3_lattice3('#skF_5',D_87,'#skF_7')
      | ~ m1_subset_1(D_87,u1_struct_0('#skF_5'))
      | m1_subset_1('#skF_9',u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11622,c_80])).

tff(c_46315,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_46314])).

tff(c_30661,plain,(
    ! [A_2272,B_2273,C_2274] :
      ( r2_hidden('#skF_2'(A_2272,B_2273,C_2274),C_2274)
      | r4_lattice3(A_2272,B_2273,C_2274)
      | ~ m1_subset_1(B_2273,u1_struct_0(A_2272))
      | ~ l3_lattices(A_2272)
      | v2_struct_0(A_2272) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_30666,plain,(
    ! [A_2272,B_2273,B_65,C_66] :
      ( '#skF_4'('#skF_2'(A_2272,B_2273,a_2_1_lattice3(B_65,C_66)),B_65,C_66) = '#skF_2'(A_2272,B_2273,a_2_1_lattice3(B_65,C_66))
      | ~ l3_lattices(B_65)
      | v2_struct_0(B_65)
      | r4_lattice3(A_2272,B_2273,a_2_1_lattice3(B_65,C_66))
      | ~ m1_subset_1(B_2273,u1_struct_0(A_2272))
      | ~ l3_lattices(A_2272)
      | v2_struct_0(A_2272) ) ),
    inference(resolution,[status(thm)],[c_30661,c_52])).

tff(c_11711,plain,(
    ! [A_1088,B_1089,C_1090] :
      ( r2_hidden('#skF_2'(A_1088,B_1089,C_1090),C_1090)
      | r4_lattice3(A_1088,B_1089,C_1090)
      | ~ m1_subset_1(B_1089,u1_struct_0(A_1088))
      | ~ l3_lattices(A_1088)
      | v2_struct_0(A_1088) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_14233,plain,(
    ! [A_1414,B_1415,B_1416,C_1417] :
      ( '#skF_4'('#skF_2'(A_1414,B_1415,a_2_1_lattice3(B_1416,C_1417)),B_1416,C_1417) = '#skF_2'(A_1414,B_1415,a_2_1_lattice3(B_1416,C_1417))
      | ~ l3_lattices(B_1416)
      | v2_struct_0(B_1416)
      | r4_lattice3(A_1414,B_1415,a_2_1_lattice3(B_1416,C_1417))
      | ~ m1_subset_1(B_1415,u1_struct_0(A_1414))
      | ~ l3_lattices(A_1414)
      | v2_struct_0(A_1414) ) ),
    inference(resolution,[status(thm)],[c_11711,c_52])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_13545,plain,(
    ! [A_1337,B_1338,C_1339] :
      ( r3_lattices(A_1337,B_1338,C_1339)
      | ~ r1_lattices(A_1337,B_1338,C_1339)
      | ~ m1_subset_1(C_1339,u1_struct_0(A_1337))
      | ~ m1_subset_1(B_1338,u1_struct_0(A_1337))
      | ~ l3_lattices(A_1337)
      | ~ v9_lattices(A_1337)
      | ~ v8_lattices(A_1337)
      | ~ v6_lattices(A_1337)
      | v2_struct_0(A_1337) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_13555,plain,(
    ! [B_1338] :
      ( r3_lattices('#skF_5',B_1338,'#skF_6')
      | ~ r1_lattices('#skF_5',B_1338,'#skF_6')
      | ~ m1_subset_1(B_1338,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_13545])).

tff(c_13565,plain,(
    ! [B_1338] :
      ( r3_lattices('#skF_5',B_1338,'#skF_6')
      | ~ r1_lattices('#skF_5',B_1338,'#skF_6')
      | ~ m1_subset_1(B_1338,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_13555])).

tff(c_13566,plain,(
    ! [B_1338] :
      ( r3_lattices('#skF_5',B_1338,'#skF_6')
      | ~ r1_lattices('#skF_5',B_1338,'#skF_6')
      | ~ m1_subset_1(B_1338,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_13565])).

tff(c_13567,plain,(
    ~ v6_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_13566])).

tff(c_13570,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_13567])).

tff(c_13573,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_13570])).

tff(c_13575,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_13573])).

tff(c_13577,plain,(
    v6_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_13566])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_13576,plain,(
    ! [B_1338] :
      ( ~ v8_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | r3_lattices('#skF_5',B_1338,'#skF_6')
      | ~ r1_lattices('#skF_5',B_1338,'#skF_6')
      | ~ m1_subset_1(B_1338,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_13566])).

tff(c_13578,plain,(
    ~ v9_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_13576])).

tff(c_13581,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_13578])).

tff(c_13584,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_13581])).

tff(c_13586,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_13584])).

tff(c_13588,plain,(
    v9_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_13576])).

tff(c_66,plain,
    ( k16_lattice3('#skF_5','#skF_7') != '#skF_6'
    | ~ r3_lattices('#skF_5','#skF_9','#skF_6')
    | ~ r3_lattice3('#skF_5','#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_11628,plain,
    ( k16_lattice3('#skF_5','#skF_7') != '#skF_6'
    | ~ r3_lattices('#skF_5','#skF_9','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11622,c_66])).

tff(c_11629,plain,(
    ~ r3_lattices('#skF_5','#skF_9','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_11628])).

tff(c_11649,plain,(
    ! [D_87] :
      ( r3_lattices('#skF_5',D_87,'#skF_6')
      | ~ r3_lattice3('#skF_5',D_87,'#skF_7')
      | ~ m1_subset_1(D_87,u1_struct_0('#skF_5'))
      | m1_subset_1('#skF_9',u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11622,c_80])).

tff(c_11650,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_11649])).

tff(c_11772,plain,(
    ! [A_1116,B_1117,C_1118] :
      ( r3_lattices(A_1116,B_1117,C_1118)
      | ~ r1_lattices(A_1116,B_1117,C_1118)
      | ~ m1_subset_1(C_1118,u1_struct_0(A_1116))
      | ~ m1_subset_1(B_1117,u1_struct_0(A_1116))
      | ~ l3_lattices(A_1116)
      | ~ v9_lattices(A_1116)
      | ~ v8_lattices(A_1116)
      | ~ v6_lattices(A_1116)
      | v2_struct_0(A_1116) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_11782,plain,(
    ! [B_1117] :
      ( r3_lattices('#skF_5',B_1117,'#skF_6')
      | ~ r1_lattices('#skF_5',B_1117,'#skF_6')
      | ~ m1_subset_1(B_1117,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_11772])).

tff(c_11792,plain,(
    ! [B_1117] :
      ( r3_lattices('#skF_5',B_1117,'#skF_6')
      | ~ r1_lattices('#skF_5',B_1117,'#skF_6')
      | ~ m1_subset_1(B_1117,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_11782])).

tff(c_11793,plain,(
    ! [B_1117] :
      ( r3_lattices('#skF_5',B_1117,'#skF_6')
      | ~ r1_lattices('#skF_5',B_1117,'#skF_6')
      | ~ m1_subset_1(B_1117,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_11792])).

tff(c_11794,plain,(
    ~ v6_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_11793])).

tff(c_11797,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_11794])).

tff(c_11800,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_11797])).

tff(c_11802,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_11800])).

tff(c_11803,plain,(
    ! [B_1117] :
      ( ~ v8_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | r3_lattices('#skF_5',B_1117,'#skF_6')
      | ~ r1_lattices('#skF_5',B_1117,'#skF_6')
      | ~ m1_subset_1(B_1117,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_11793])).

tff(c_11805,plain,(
    ~ v9_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_11803])).

tff(c_11809,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_11805])).

tff(c_11812,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_11809])).

tff(c_11814,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_11812])).

tff(c_11815,plain,(
    ! [B_1117] :
      ( ~ v8_lattices('#skF_5')
      | r3_lattices('#skF_5',B_1117,'#skF_6')
      | ~ r1_lattices('#skF_5',B_1117,'#skF_6')
      | ~ m1_subset_1(B_1117,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_11803])).

tff(c_11817,plain,(
    ~ v8_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_11815])).

tff(c_11823,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_11817])).

tff(c_11826,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_11823])).

tff(c_11828,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_11826])).

tff(c_11831,plain,(
    ! [B_1122] :
      ( r3_lattices('#skF_5',B_1122,'#skF_6')
      | ~ r1_lattices('#skF_5',B_1122,'#skF_6')
      | ~ m1_subset_1(B_1122,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_11815])).

tff(c_11846,plain,
    ( r3_lattices('#skF_5','#skF_9','#skF_6')
    | ~ r1_lattices('#skF_5','#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_11650,c_11831])).

tff(c_11864,plain,(
    ~ r1_lattices('#skF_5','#skF_9','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_11629,c_11846])).

tff(c_74,plain,(
    ! [D_87] :
      ( r3_lattices('#skF_5',D_87,'#skF_6')
      | ~ r3_lattice3('#skF_5',D_87,'#skF_7')
      | ~ m1_subset_1(D_87,u1_struct_0('#skF_5'))
      | r3_lattice3('#skF_5','#skF_9','#skF_8')
      | ~ r3_lattice3('#skF_5','#skF_6','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_11727,plain,(
    ! [D_87] :
      ( r3_lattices('#skF_5',D_87,'#skF_6')
      | ~ r3_lattice3('#skF_5',D_87,'#skF_7')
      | ~ m1_subset_1(D_87,u1_struct_0('#skF_5'))
      | r3_lattice3('#skF_5','#skF_9','#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11622,c_74])).

tff(c_11728,plain,(
    r3_lattice3('#skF_5','#skF_9','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_11727])).

tff(c_11723,plain,(
    ! [A_1103,B_1104] :
      ( r4_lattice3(A_1103,k15_lattice3(A_1103,B_1104),B_1104)
      | ~ m1_subset_1(k15_lattice3(A_1103,B_1104),u1_struct_0(A_1103))
      | ~ v4_lattice3(A_1103)
      | ~ v10_lattices(A_1103)
      | ~ l3_lattices(A_1103)
      | v2_struct_0(A_1103) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_12996,plain,(
    ! [A_1264,B_1265] :
      ( r4_lattice3(A_1264,k15_lattice3(A_1264,a_2_1_lattice3(A_1264,B_1265)),a_2_1_lattice3(A_1264,B_1265))
      | ~ m1_subset_1(k16_lattice3(A_1264,B_1265),u1_struct_0(A_1264))
      | ~ v4_lattice3(A_1264)
      | ~ v10_lattices(A_1264)
      | ~ l3_lattices(A_1264)
      | v2_struct_0(A_1264)
      | ~ l3_lattices(A_1264)
      | v2_struct_0(A_1264) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_11723])).

tff(c_13084,plain,(
    ! [A_1277,B_1278] :
      ( r4_lattice3(A_1277,k16_lattice3(A_1277,B_1278),a_2_1_lattice3(A_1277,B_1278))
      | ~ m1_subset_1(k16_lattice3(A_1277,B_1278),u1_struct_0(A_1277))
      | ~ v4_lattice3(A_1277)
      | ~ v10_lattices(A_1277)
      | ~ l3_lattices(A_1277)
      | v2_struct_0(A_1277)
      | ~ l3_lattices(A_1277)
      | v2_struct_0(A_1277)
      | ~ l3_lattices(A_1277)
      | v2_struct_0(A_1277) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_12996])).

tff(c_13087,plain,
    ( r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_8'))
    | ~ m1_subset_1(k16_lattice3('#skF_5','#skF_8'),u1_struct_0('#skF_5'))
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_13084])).

tff(c_13089,plain,
    ( r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_8'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_58,c_58,c_62,c_60,c_56,c_90,c_13087])).

tff(c_13090,plain,(
    r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_13089])).

tff(c_48,plain,(
    ! [D_69,B_65,C_66] :
      ( r2_hidden(D_69,a_2_1_lattice3(B_65,C_66))
      | ~ r3_lattice3(B_65,D_69,C_66)
      | ~ m1_subset_1(D_69,u1_struct_0(B_65))
      | ~ l3_lattices(B_65)
      | v2_struct_0(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_11761,plain,(
    ! [A_1109,D_1110,B_1111,C_1112] :
      ( r1_lattices(A_1109,D_1110,B_1111)
      | ~ r2_hidden(D_1110,C_1112)
      | ~ m1_subset_1(D_1110,u1_struct_0(A_1109))
      | ~ r4_lattice3(A_1109,B_1111,C_1112)
      | ~ m1_subset_1(B_1111,u1_struct_0(A_1109))
      | ~ l3_lattices(A_1109)
      | v2_struct_0(A_1109) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_13389,plain,(
    ! [B_1313,D_1314,A_1312,C_1311,B_1310] :
      ( r1_lattices(A_1312,D_1314,B_1313)
      | ~ m1_subset_1(D_1314,u1_struct_0(A_1312))
      | ~ r4_lattice3(A_1312,B_1313,a_2_1_lattice3(B_1310,C_1311))
      | ~ m1_subset_1(B_1313,u1_struct_0(A_1312))
      | ~ l3_lattices(A_1312)
      | v2_struct_0(A_1312)
      | ~ r3_lattice3(B_1310,D_1314,C_1311)
      | ~ m1_subset_1(D_1314,u1_struct_0(B_1310))
      | ~ l3_lattices(B_1310)
      | v2_struct_0(B_1310) ) ),
    inference(resolution,[status(thm)],[c_48,c_11761])).

tff(c_13399,plain,(
    ! [B_1313,B_1310,C_1311] :
      ( r1_lattices('#skF_5','#skF_9',B_1313)
      | ~ r4_lattice3('#skF_5',B_1313,a_2_1_lattice3(B_1310,C_1311))
      | ~ m1_subset_1(B_1313,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r3_lattice3(B_1310,'#skF_9',C_1311)
      | ~ m1_subset_1('#skF_9',u1_struct_0(B_1310))
      | ~ l3_lattices(B_1310)
      | v2_struct_0(B_1310) ) ),
    inference(resolution,[status(thm)],[c_11650,c_13389])).

tff(c_13408,plain,(
    ! [B_1313,B_1310,C_1311] :
      ( r1_lattices('#skF_5','#skF_9',B_1313)
      | ~ r4_lattice3('#skF_5',B_1313,a_2_1_lattice3(B_1310,C_1311))
      | ~ m1_subset_1(B_1313,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | ~ r3_lattice3(B_1310,'#skF_9',C_1311)
      | ~ m1_subset_1('#skF_9',u1_struct_0(B_1310))
      | ~ l3_lattices(B_1310)
      | v2_struct_0(B_1310) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_13399])).

tff(c_13452,plain,(
    ! [B_1319,B_1320,C_1321] :
      ( r1_lattices('#skF_5','#skF_9',B_1319)
      | ~ r4_lattice3('#skF_5',B_1319,a_2_1_lattice3(B_1320,C_1321))
      | ~ m1_subset_1(B_1319,u1_struct_0('#skF_5'))
      | ~ r3_lattice3(B_1320,'#skF_9',C_1321)
      | ~ m1_subset_1('#skF_9',u1_struct_0(B_1320))
      | ~ l3_lattices(B_1320)
      | v2_struct_0(B_1320) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_13408])).

tff(c_13455,plain,
    ( r1_lattices('#skF_5','#skF_9','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ r3_lattice3('#skF_5','#skF_9','#skF_8')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_13090,c_13452])).

tff(c_13470,plain,
    ( r1_lattices('#skF_5','#skF_9','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_11650,c_11728,c_56,c_13455])).

tff(c_13472,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_11864,c_13470])).

tff(c_13475,plain,(
    ! [D_1322] :
      ( r3_lattices('#skF_5',D_1322,'#skF_6')
      | ~ r3_lattice3('#skF_5',D_1322,'#skF_7')
      | ~ m1_subset_1(D_1322,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_11727])).

tff(c_13493,plain,
    ( r3_lattices('#skF_5','#skF_6','#skF_6')
    | ~ r3_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_13475])).

tff(c_13511,plain,(
    r3_lattices('#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11623,c_13493])).

tff(c_13589,plain,(
    ! [A_1340,B_1341,C_1342] :
      ( r1_lattices(A_1340,B_1341,C_1342)
      | ~ r3_lattices(A_1340,B_1341,C_1342)
      | ~ m1_subset_1(C_1342,u1_struct_0(A_1340))
      | ~ m1_subset_1(B_1341,u1_struct_0(A_1340))
      | ~ l3_lattices(A_1340)
      | ~ v9_lattices(A_1340)
      | ~ v8_lattices(A_1340)
      | ~ v6_lattices(A_1340)
      | v2_struct_0(A_1340) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_13597,plain,
    ( r1_lattices('#skF_5','#skF_6','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | ~ v9_lattices('#skF_5')
    | ~ v8_lattices('#skF_5')
    | ~ v6_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_13511,c_13589])).

tff(c_13612,plain,
    ( r1_lattices('#skF_5','#skF_6','#skF_6')
    | ~ v8_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13577,c_13588,c_58,c_56,c_13597])).

tff(c_13613,plain,
    ( r1_lattices('#skF_5','#skF_6','#skF_6')
    | ~ v8_lattices('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_13612])).

tff(c_13614,plain,(
    ~ v8_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_13613])).

tff(c_13617,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_13614])).

tff(c_13620,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_13617])).

tff(c_13622,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_13620])).

tff(c_13624,plain,(
    v8_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_13613])).

tff(c_13487,plain,(
    ! [A_64,C_66] :
      ( r3_lattices('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_7')
      | ~ r2_hidden(A_64,a_2_1_lattice3('#skF_5',C_66))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_13475])).

tff(c_13504,plain,(
    ! [A_64,C_66] :
      ( r3_lattices('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_7')
      | ~ r2_hidden(A_64,a_2_1_lattice3('#skF_5',C_66))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_13487])).

tff(c_13505,plain,(
    ! [A_64,C_66] :
      ( r3_lattices('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_7')
      | ~ r2_hidden(A_64,a_2_1_lattice3('#skF_5',C_66)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_13504])).

tff(c_13595,plain,(
    ! [A_64,C_66] :
      ( r1_lattices('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_4'(A_64,'#skF_5',C_66),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_7')
      | ~ r2_hidden(A_64,a_2_1_lattice3('#skF_5',C_66)) ) ),
    inference(resolution,[status(thm)],[c_13505,c_13589])).

tff(c_13608,plain,(
    ! [A_64,C_66] :
      ( r1_lattices('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_6')
      | ~ m1_subset_1('#skF_4'(A_64,'#skF_5',C_66),u1_struct_0('#skF_5'))
      | ~ v8_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_7')
      | ~ r2_hidden(A_64,a_2_1_lattice3('#skF_5',C_66)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13577,c_13588,c_58,c_56,c_13595])).

tff(c_13609,plain,(
    ! [A_64,C_66] :
      ( r1_lattices('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_6')
      | ~ m1_subset_1('#skF_4'(A_64,'#skF_5',C_66),u1_struct_0('#skF_5'))
      | ~ v8_lattices('#skF_5')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_7')
      | ~ r2_hidden(A_64,a_2_1_lattice3('#skF_5',C_66)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_13608])).

tff(c_13814,plain,(
    ! [A_1372,C_1373] :
      ( r1_lattices('#skF_5','#skF_4'(A_1372,'#skF_5',C_1373),'#skF_6')
      | ~ m1_subset_1('#skF_4'(A_1372,'#skF_5',C_1373),u1_struct_0('#skF_5'))
      | ~ r3_lattice3('#skF_5','#skF_4'(A_1372,'#skF_5',C_1373),'#skF_7')
      | ~ r2_hidden(A_1372,a_2_1_lattice3('#skF_5',C_1373)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13624,c_13609])).

tff(c_13824,plain,(
    ! [A_64,C_66] :
      ( r1_lattices('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_7')
      | ~ r2_hidden(A_64,a_2_1_lattice3('#skF_5',C_66))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_13814])).

tff(c_13831,plain,(
    ! [A_64,C_66] :
      ( r1_lattices('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_7')
      | ~ r2_hidden(A_64,a_2_1_lattice3('#skF_5',C_66))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_13824])).

tff(c_13833,plain,(
    ! [A_1374,C_1375] :
      ( r1_lattices('#skF_5','#skF_4'(A_1374,'#skF_5',C_1375),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_1374,'#skF_5',C_1375),'#skF_7')
      | ~ r2_hidden(A_1374,a_2_1_lattice3('#skF_5',C_1375)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_13831])).

tff(c_13843,plain,(
    ! [A_64] :
      ( r1_lattices('#skF_5','#skF_4'(A_64,'#skF_5','#skF_7'),'#skF_6')
      | ~ r2_hidden(A_64,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_13833])).

tff(c_13850,plain,(
    ! [A_64] :
      ( r1_lattices('#skF_5','#skF_4'(A_64,'#skF_5','#skF_7'),'#skF_6')
      | ~ r2_hidden(A_64,a_2_1_lattice3('#skF_5','#skF_7'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_13843])).

tff(c_13851,plain,(
    ! [A_64] :
      ( r1_lattices('#skF_5','#skF_4'(A_64,'#skF_5','#skF_7'),'#skF_6')
      | ~ r2_hidden(A_64,a_2_1_lattice3('#skF_5','#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_13850])).

tff(c_14240,plain,(
    ! [A_1414,B_1415] :
      ( r1_lattices('#skF_5','#skF_2'(A_1414,B_1415,a_2_1_lattice3('#skF_5','#skF_7')),'#skF_6')
      | ~ r2_hidden('#skF_2'(A_1414,B_1415,a_2_1_lattice3('#skF_5','#skF_7')),a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | r4_lattice3(A_1414,B_1415,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_1415,u1_struct_0(A_1414))
      | ~ l3_lattices(A_1414)
      | v2_struct_0(A_1414) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14233,c_13851])).

tff(c_14268,plain,(
    ! [A_1414,B_1415] :
      ( r1_lattices('#skF_5','#skF_2'(A_1414,B_1415,a_2_1_lattice3('#skF_5','#skF_7')),'#skF_6')
      | ~ r2_hidden('#skF_2'(A_1414,B_1415,a_2_1_lattice3('#skF_5','#skF_7')),a_2_1_lattice3('#skF_5','#skF_7'))
      | v2_struct_0('#skF_5')
      | r4_lattice3(A_1414,B_1415,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_1415,u1_struct_0(A_1414))
      | ~ l3_lattices(A_1414)
      | v2_struct_0(A_1414) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_14240])).

tff(c_14587,plain,(
    ! [A_1445,B_1446] :
      ( r1_lattices('#skF_5','#skF_2'(A_1445,B_1446,a_2_1_lattice3('#skF_5','#skF_7')),'#skF_6')
      | ~ r2_hidden('#skF_2'(A_1445,B_1446,a_2_1_lattice3('#skF_5','#skF_7')),a_2_1_lattice3('#skF_5','#skF_7'))
      | r4_lattice3(A_1445,B_1446,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_1446,u1_struct_0(A_1445))
      | ~ l3_lattices(A_1445)
      | v2_struct_0(A_1445) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_14268])).

tff(c_14600,plain,(
    ! [A_1447,B_1448] :
      ( r1_lattices('#skF_5','#skF_2'(A_1447,B_1448,a_2_1_lattice3('#skF_5','#skF_7')),'#skF_6')
      | r4_lattice3(A_1447,B_1448,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_1448,u1_struct_0(A_1447))
      | ~ l3_lattices(A_1447)
      | v2_struct_0(A_1447) ) ),
    inference(resolution,[status(thm)],[c_32,c_14587])).

tff(c_14604,plain,
    ( r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_7'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_14600,c_30])).

tff(c_14607,plain,
    ( r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_14604])).

tff(c_14608,plain,(
    r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_14607])).

tff(c_13535,plain,(
    ! [A_1333,D_1334,B_1335,C_1336] :
      ( r1_lattices(A_1333,D_1334,B_1335)
      | ~ r2_hidden(D_1334,C_1336)
      | ~ m1_subset_1(D_1334,u1_struct_0(A_1333))
      | ~ r4_lattice3(A_1333,B_1335,C_1336)
      | ~ m1_subset_1(B_1335,u1_struct_0(A_1333))
      | ~ l3_lattices(A_1333)
      | v2_struct_0(A_1333) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_14746,plain,(
    ! [B_1470,A_1473,D_1474,C_1471,B_1472] :
      ( r1_lattices(A_1473,D_1474,B_1472)
      | ~ m1_subset_1(D_1474,u1_struct_0(A_1473))
      | ~ r4_lattice3(A_1473,B_1472,a_2_1_lattice3(B_1470,C_1471))
      | ~ m1_subset_1(B_1472,u1_struct_0(A_1473))
      | ~ l3_lattices(A_1473)
      | v2_struct_0(A_1473)
      | ~ r3_lattice3(B_1470,D_1474,C_1471)
      | ~ m1_subset_1(D_1474,u1_struct_0(B_1470))
      | ~ l3_lattices(B_1470)
      | v2_struct_0(B_1470) ) ),
    inference(resolution,[status(thm)],[c_48,c_13535])).

tff(c_14758,plain,(
    ! [B_1472,B_1470,C_1471] :
      ( r1_lattices('#skF_5','#skF_6',B_1472)
      | ~ r4_lattice3('#skF_5',B_1472,a_2_1_lattice3(B_1470,C_1471))
      | ~ m1_subset_1(B_1472,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r3_lattice3(B_1470,'#skF_6',C_1471)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_1470))
      | ~ l3_lattices(B_1470)
      | v2_struct_0(B_1470) ) ),
    inference(resolution,[status(thm)],[c_56,c_14746])).

tff(c_14769,plain,(
    ! [B_1472,B_1470,C_1471] :
      ( r1_lattices('#skF_5','#skF_6',B_1472)
      | ~ r4_lattice3('#skF_5',B_1472,a_2_1_lattice3(B_1470,C_1471))
      | ~ m1_subset_1(B_1472,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | ~ r3_lattice3(B_1470,'#skF_6',C_1471)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_1470))
      | ~ l3_lattices(B_1470)
      | v2_struct_0(B_1470) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_14758])).

tff(c_14775,plain,(
    ! [B_1479,B_1480,C_1481] :
      ( r1_lattices('#skF_5','#skF_6',B_1479)
      | ~ r4_lattice3('#skF_5',B_1479,a_2_1_lattice3(B_1480,C_1481))
      | ~ m1_subset_1(B_1479,u1_struct_0('#skF_5'))
      | ~ r3_lattice3(B_1480,'#skF_6',C_1481)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_1480))
      | ~ l3_lattices(B_1480)
      | v2_struct_0(B_1480) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_14769])).

tff(c_14793,plain,(
    ! [B_1480,C_1481,C_57] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3(B_1480,C_1481),C_57))
      | ~ m1_subset_1('#skF_3'('#skF_5',a_2_1_lattice3(B_1480,C_1481),C_57),u1_struct_0('#skF_5'))
      | ~ r3_lattice3(B_1480,'#skF_6',C_1481)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_1480))
      | ~ l3_lattices(B_1480)
      | v2_struct_0(B_1480)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_1480,C_1481)) = C_57
      | ~ r4_lattice3('#skF_5',C_57,a_2_1_lattice3(B_1480,C_1481))
      | ~ m1_subset_1(C_57,u1_struct_0('#skF_5'))
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_38,c_14775])).

tff(c_14812,plain,(
    ! [B_1480,C_1481,C_57] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3(B_1480,C_1481),C_57))
      | ~ m1_subset_1('#skF_3'('#skF_5',a_2_1_lattice3(B_1480,C_1481),C_57),u1_struct_0('#skF_5'))
      | ~ r3_lattice3(B_1480,'#skF_6',C_1481)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_1480))
      | ~ l3_lattices(B_1480)
      | v2_struct_0(B_1480)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_1480,C_1481)) = C_57
      | ~ r4_lattice3('#skF_5',C_57,a_2_1_lattice3(B_1480,C_1481))
      | ~ m1_subset_1(C_57,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_60,c_14793])).

tff(c_23307,plain,(
    ! [B_1908,C_1909,C_1910] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3(B_1908,C_1909),C_1910))
      | ~ m1_subset_1('#skF_3'('#skF_5',a_2_1_lattice3(B_1908,C_1909),C_1910),u1_struct_0('#skF_5'))
      | ~ r3_lattice3(B_1908,'#skF_6',C_1909)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_1908))
      | ~ l3_lattices(B_1908)
      | v2_struct_0(B_1908)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_1908,C_1909)) = C_1910
      | ~ r4_lattice3('#skF_5',C_1910,a_2_1_lattice3(B_1908,C_1909))
      | ~ m1_subset_1(C_1910,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_14812])).

tff(c_23311,plain,(
    ! [B_1908,C_1909,C_57] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3(B_1908,C_1909),C_57))
      | ~ r3_lattice3(B_1908,'#skF_6',C_1909)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_1908))
      | ~ l3_lattices(B_1908)
      | v2_struct_0(B_1908)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_1908,C_1909)) = C_57
      | ~ r4_lattice3('#skF_5',C_57,a_2_1_lattice3(B_1908,C_1909))
      | ~ m1_subset_1(C_57,u1_struct_0('#skF_5'))
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_23307])).

tff(c_23314,plain,(
    ! [B_1908,C_1909,C_57] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3(B_1908,C_1909),C_57))
      | ~ r3_lattice3(B_1908,'#skF_6',C_1909)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_1908))
      | ~ l3_lattices(B_1908)
      | v2_struct_0(B_1908)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_1908,C_1909)) = C_57
      | ~ r4_lattice3('#skF_5',C_57,a_2_1_lattice3(B_1908,C_1909))
      | ~ m1_subset_1(C_57,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_60,c_23311])).

tff(c_30458,plain,(
    ! [B_2254,C_2255,C_2256] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3(B_2254,C_2255),C_2256))
      | ~ r3_lattice3(B_2254,'#skF_6',C_2255)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_2254))
      | ~ l3_lattices(B_2254)
      | v2_struct_0(B_2254)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_2254,C_2255)) = C_2256
      | ~ r4_lattice3('#skF_5',C_2256,a_2_1_lattice3(B_2254,C_2255))
      | ~ m1_subset_1(C_2256,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_23314])).

tff(c_30462,plain,(
    ! [B_2254,C_2255] :
      ( ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r3_lattice3(B_2254,'#skF_6',C_2255)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_2254))
      | ~ l3_lattices(B_2254)
      | v2_struct_0(B_2254)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_2254,C_2255)) = '#skF_6'
      | ~ r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3(B_2254,C_2255))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_30458,c_36])).

tff(c_30465,plain,(
    ! [B_2254,C_2255] :
      ( v2_struct_0('#skF_5')
      | ~ r3_lattice3(B_2254,'#skF_6',C_2255)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_2254))
      | ~ l3_lattices(B_2254)
      | v2_struct_0(B_2254)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_2254,C_2255)) = '#skF_6'
      | ~ r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3(B_2254,C_2255)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_62,c_60,c_30462])).

tff(c_30467,plain,(
    ! [B_2257,C_2258] :
      ( ~ r3_lattice3(B_2257,'#skF_6',C_2258)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_2257))
      | ~ l3_lattices(B_2257)
      | v2_struct_0(B_2257)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_2257,C_2258)) = '#skF_6'
      | ~ r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3(B_2257,C_2258)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_30465])).

tff(c_30470,plain,
    ( ~ r3_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_7')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_14608,c_30467])).

tff(c_30476,plain,
    ( v2_struct_0('#skF_5')
    | k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_11623,c_30470])).

tff(c_30477,plain,(
    k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_7')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_30476])).

tff(c_30531,plain,
    ( k16_lattice3('#skF_5','#skF_7') = '#skF_6'
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_30477,c_46])).

tff(c_30579,plain,
    ( k16_lattice3('#skF_5','#skF_7') = '#skF_6'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_30531])).

tff(c_30581,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_11626,c_30579])).

tff(c_30584,plain,(
    ! [D_2259] :
      ( r3_lattices('#skF_5',D_2259,'#skF_6')
      | ~ r3_lattice3('#skF_5',D_2259,'#skF_7')
      | ~ m1_subset_1(D_2259,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_11649])).

tff(c_30587,plain,
    ( r3_lattices('#skF_5','#skF_6','#skF_6')
    | ~ r3_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_30584])).

tff(c_30590,plain,(
    r3_lattices('#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11623,c_30587])).

tff(c_30725,plain,(
    ! [A_2303,B_2304,C_2305] :
      ( r1_lattices(A_2303,B_2304,C_2305)
      | ~ r3_lattices(A_2303,B_2304,C_2305)
      | ~ m1_subset_1(C_2305,u1_struct_0(A_2303))
      | ~ m1_subset_1(B_2304,u1_struct_0(A_2303))
      | ~ l3_lattices(A_2303)
      | ~ v9_lattices(A_2303)
      | ~ v8_lattices(A_2303)
      | ~ v6_lattices(A_2303)
      | v2_struct_0(A_2303) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_30733,plain,
    ( r1_lattices('#skF_5','#skF_6','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | ~ v9_lattices('#skF_5')
    | ~ v8_lattices('#skF_5')
    | ~ v6_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_30590,c_30725])).

tff(c_30748,plain,
    ( r1_lattices('#skF_5','#skF_6','#skF_6')
    | ~ v9_lattices('#skF_5')
    | ~ v8_lattices('#skF_5')
    | ~ v6_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_30733])).

tff(c_30749,plain,
    ( r1_lattices('#skF_5','#skF_6','#skF_6')
    | ~ v9_lattices('#skF_5')
    | ~ v8_lattices('#skF_5')
    | ~ v6_lattices('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_30748])).

tff(c_30750,plain,(
    ~ v6_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_30749])).

tff(c_30769,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_30750])).

tff(c_30772,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_30769])).

tff(c_30774,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_30772])).

tff(c_30776,plain,(
    v6_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_30749])).

tff(c_30775,plain,
    ( ~ v8_lattices('#skF_5')
    | ~ v9_lattices('#skF_5')
    | r1_lattices('#skF_5','#skF_6','#skF_6') ),
    inference(splitRight,[status(thm)],[c_30749])).

tff(c_30777,plain,(
    ~ v9_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_30775])).

tff(c_30783,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_30777])).

tff(c_30786,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_30783])).

tff(c_30788,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_30786])).

tff(c_30789,plain,
    ( ~ v8_lattices('#skF_5')
    | r1_lattices('#skF_5','#skF_6','#skF_6') ),
    inference(splitRight,[status(thm)],[c_30775])).

tff(c_30791,plain,(
    ~ v8_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_30789])).

tff(c_30794,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_30791])).

tff(c_30797,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_30794])).

tff(c_30799,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_30797])).

tff(c_30801,plain,(
    v8_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_30789])).

tff(c_30790,plain,(
    v9_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_30775])).

tff(c_30591,plain,(
    ! [A_2260,B_2261,C_2262] :
      ( m1_subset_1('#skF_4'(A_2260,B_2261,C_2262),u1_struct_0(B_2261))
      | ~ r2_hidden(A_2260,a_2_1_lattice3(B_2261,C_2262))
      | ~ l3_lattices(B_2261)
      | v2_struct_0(B_2261) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_30582,plain,(
    ! [D_87] :
      ( r3_lattices('#skF_5',D_87,'#skF_6')
      | ~ r3_lattice3('#skF_5',D_87,'#skF_7')
      | ~ m1_subset_1(D_87,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_11649])).

tff(c_30595,plain,(
    ! [A_2260,C_2262] :
      ( r3_lattices('#skF_5','#skF_4'(A_2260,'#skF_5',C_2262),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_2260,'#skF_5',C_2262),'#skF_7')
      | ~ r2_hidden(A_2260,a_2_1_lattice3('#skF_5',C_2262))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30591,c_30582])).

tff(c_30598,plain,(
    ! [A_2260,C_2262] :
      ( r3_lattices('#skF_5','#skF_4'(A_2260,'#skF_5',C_2262),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_2260,'#skF_5',C_2262),'#skF_7')
      | ~ r2_hidden(A_2260,a_2_1_lattice3('#skF_5',C_2262))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_30595])).

tff(c_30599,plain,(
    ! [A_2260,C_2262] :
      ( r3_lattices('#skF_5','#skF_4'(A_2260,'#skF_5',C_2262),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_2260,'#skF_5',C_2262),'#skF_7')
      | ~ r2_hidden(A_2260,a_2_1_lattice3('#skF_5',C_2262)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_30598])).

tff(c_30731,plain,(
    ! [A_2260,C_2262] :
      ( r1_lattices('#skF_5','#skF_4'(A_2260,'#skF_5',C_2262),'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_4'(A_2260,'#skF_5',C_2262),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_2260,'#skF_5',C_2262),'#skF_7')
      | ~ r2_hidden(A_2260,a_2_1_lattice3('#skF_5',C_2262)) ) ),
    inference(resolution,[status(thm)],[c_30599,c_30725])).

tff(c_30744,plain,(
    ! [A_2260,C_2262] :
      ( r1_lattices('#skF_5','#skF_4'(A_2260,'#skF_5',C_2262),'#skF_6')
      | ~ m1_subset_1('#skF_4'(A_2260,'#skF_5',C_2262),u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_2260,'#skF_5',C_2262),'#skF_7')
      | ~ r2_hidden(A_2260,a_2_1_lattice3('#skF_5',C_2262)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_30731])).

tff(c_30745,plain,(
    ! [A_2260,C_2262] :
      ( r1_lattices('#skF_5','#skF_4'(A_2260,'#skF_5',C_2262),'#skF_6')
      | ~ m1_subset_1('#skF_4'(A_2260,'#skF_5',C_2262),u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_2260,'#skF_5',C_2262),'#skF_7')
      | ~ r2_hidden(A_2260,a_2_1_lattice3('#skF_5',C_2262)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_30744])).

tff(c_31117,plain,(
    ! [A_2357,C_2358] :
      ( r1_lattices('#skF_5','#skF_4'(A_2357,'#skF_5',C_2358),'#skF_6')
      | ~ m1_subset_1('#skF_4'(A_2357,'#skF_5',C_2358),u1_struct_0('#skF_5'))
      | ~ r3_lattice3('#skF_5','#skF_4'(A_2357,'#skF_5',C_2358),'#skF_7')
      | ~ r2_hidden(A_2357,a_2_1_lattice3('#skF_5',C_2358)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30776,c_30801,c_30790,c_30745])).

tff(c_31134,plain,(
    ! [A_64,C_66] :
      ( r1_lattices('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_7')
      | ~ r2_hidden(A_64,a_2_1_lattice3('#skF_5',C_66))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_31117])).

tff(c_31144,plain,(
    ! [A_64,C_66] :
      ( r1_lattices('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_7')
      | ~ r2_hidden(A_64,a_2_1_lattice3('#skF_5',C_66))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_31134])).

tff(c_31146,plain,(
    ! [A_2359,C_2360] :
      ( r1_lattices('#skF_5','#skF_4'(A_2359,'#skF_5',C_2360),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_2359,'#skF_5',C_2360),'#skF_7')
      | ~ r2_hidden(A_2359,a_2_1_lattice3('#skF_5',C_2360)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_31144])).

tff(c_31163,plain,(
    ! [A_64] :
      ( r1_lattices('#skF_5','#skF_4'(A_64,'#skF_5','#skF_7'),'#skF_6')
      | ~ r2_hidden(A_64,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_31146])).

tff(c_31173,plain,(
    ! [A_64] :
      ( r1_lattices('#skF_5','#skF_4'(A_64,'#skF_5','#skF_7'),'#skF_6')
      | ~ r2_hidden(A_64,a_2_1_lattice3('#skF_5','#skF_7'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_31163])).

tff(c_31175,plain,(
    ! [A_2361] :
      ( r1_lattices('#skF_5','#skF_4'(A_2361,'#skF_5','#skF_7'),'#skF_6')
      | ~ r2_hidden(A_2361,a_2_1_lattice3('#skF_5','#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_31173])).

tff(c_31183,plain,(
    ! [A_2272,B_2273] :
      ( r1_lattices('#skF_5','#skF_2'(A_2272,B_2273,a_2_1_lattice3('#skF_5','#skF_7')),'#skF_6')
      | ~ r2_hidden('#skF_2'(A_2272,B_2273,a_2_1_lattice3('#skF_5','#skF_7')),a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | r4_lattice3(A_2272,B_2273,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_2273,u1_struct_0(A_2272))
      | ~ l3_lattices(A_2272)
      | v2_struct_0(A_2272) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30666,c_31175])).

tff(c_31195,plain,(
    ! [A_2272,B_2273] :
      ( r1_lattices('#skF_5','#skF_2'(A_2272,B_2273,a_2_1_lattice3('#skF_5','#skF_7')),'#skF_6')
      | ~ r2_hidden('#skF_2'(A_2272,B_2273,a_2_1_lattice3('#skF_5','#skF_7')),a_2_1_lattice3('#skF_5','#skF_7'))
      | v2_struct_0('#skF_5')
      | r4_lattice3(A_2272,B_2273,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_2273,u1_struct_0(A_2272))
      | ~ l3_lattices(A_2272)
      | v2_struct_0(A_2272) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_31183])).

tff(c_31463,plain,(
    ! [A_2383,B_2384] :
      ( r1_lattices('#skF_5','#skF_2'(A_2383,B_2384,a_2_1_lattice3('#skF_5','#skF_7')),'#skF_6')
      | ~ r2_hidden('#skF_2'(A_2383,B_2384,a_2_1_lattice3('#skF_5','#skF_7')),a_2_1_lattice3('#skF_5','#skF_7'))
      | r4_lattice3(A_2383,B_2384,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_2384,u1_struct_0(A_2383))
      | ~ l3_lattices(A_2383)
      | v2_struct_0(A_2383) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_31195])).

tff(c_31476,plain,(
    ! [A_2385,B_2386] :
      ( r1_lattices('#skF_5','#skF_2'(A_2385,B_2386,a_2_1_lattice3('#skF_5','#skF_7')),'#skF_6')
      | r4_lattice3(A_2385,B_2386,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_2386,u1_struct_0(A_2385))
      | ~ l3_lattices(A_2385)
      | v2_struct_0(A_2385) ) ),
    inference(resolution,[status(thm)],[c_32,c_31463])).

tff(c_31480,plain,
    ( r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_7'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_31476,c_30])).

tff(c_31483,plain,
    ( r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_31480])).

tff(c_31484,plain,(
    r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_31483])).

tff(c_30715,plain,(
    ! [A_2299,D_2300,B_2301,C_2302] :
      ( r1_lattices(A_2299,D_2300,B_2301)
      | ~ r2_hidden(D_2300,C_2302)
      | ~ m1_subset_1(D_2300,u1_struct_0(A_2299))
      | ~ r4_lattice3(A_2299,B_2301,C_2302)
      | ~ m1_subset_1(B_2301,u1_struct_0(A_2299))
      | ~ l3_lattices(A_2299)
      | v2_struct_0(A_2299) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_31596,plain,(
    ! [C_2404,D_2407,A_2406,B_2405,B_2403] :
      ( r1_lattices(A_2406,D_2407,B_2405)
      | ~ m1_subset_1(D_2407,u1_struct_0(A_2406))
      | ~ r4_lattice3(A_2406,B_2405,a_2_1_lattice3(B_2403,C_2404))
      | ~ m1_subset_1(B_2405,u1_struct_0(A_2406))
      | ~ l3_lattices(A_2406)
      | v2_struct_0(A_2406)
      | ~ r3_lattice3(B_2403,D_2407,C_2404)
      | ~ m1_subset_1(D_2407,u1_struct_0(B_2403))
      | ~ l3_lattices(B_2403)
      | v2_struct_0(B_2403) ) ),
    inference(resolution,[status(thm)],[c_48,c_30715])).

tff(c_31606,plain,(
    ! [B_2405,B_2403,C_2404] :
      ( r1_lattices('#skF_5','#skF_6',B_2405)
      | ~ r4_lattice3('#skF_5',B_2405,a_2_1_lattice3(B_2403,C_2404))
      | ~ m1_subset_1(B_2405,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r3_lattice3(B_2403,'#skF_6',C_2404)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_2403))
      | ~ l3_lattices(B_2403)
      | v2_struct_0(B_2403) ) ),
    inference(resolution,[status(thm)],[c_56,c_31596])).

tff(c_31613,plain,(
    ! [B_2405,B_2403,C_2404] :
      ( r1_lattices('#skF_5','#skF_6',B_2405)
      | ~ r4_lattice3('#skF_5',B_2405,a_2_1_lattice3(B_2403,C_2404))
      | ~ m1_subset_1(B_2405,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | ~ r3_lattice3(B_2403,'#skF_6',C_2404)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_2403))
      | ~ l3_lattices(B_2403)
      | v2_struct_0(B_2403) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_31606])).

tff(c_31615,plain,(
    ! [B_2408,B_2409,C_2410] :
      ( r1_lattices('#skF_5','#skF_6',B_2408)
      | ~ r4_lattice3('#skF_5',B_2408,a_2_1_lattice3(B_2409,C_2410))
      | ~ m1_subset_1(B_2408,u1_struct_0('#skF_5'))
      | ~ r3_lattice3(B_2409,'#skF_6',C_2410)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_2409))
      | ~ l3_lattices(B_2409)
      | v2_struct_0(B_2409) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_31613])).

tff(c_31633,plain,(
    ! [B_2409,C_2410,C_57] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3(B_2409,C_2410),C_57))
      | ~ m1_subset_1('#skF_3'('#skF_5',a_2_1_lattice3(B_2409,C_2410),C_57),u1_struct_0('#skF_5'))
      | ~ r3_lattice3(B_2409,'#skF_6',C_2410)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_2409))
      | ~ l3_lattices(B_2409)
      | v2_struct_0(B_2409)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_2409,C_2410)) = C_57
      | ~ r4_lattice3('#skF_5',C_57,a_2_1_lattice3(B_2409,C_2410))
      | ~ m1_subset_1(C_57,u1_struct_0('#skF_5'))
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_38,c_31615])).

tff(c_31652,plain,(
    ! [B_2409,C_2410,C_57] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3(B_2409,C_2410),C_57))
      | ~ m1_subset_1('#skF_3'('#skF_5',a_2_1_lattice3(B_2409,C_2410),C_57),u1_struct_0('#skF_5'))
      | ~ r3_lattice3(B_2409,'#skF_6',C_2410)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_2409))
      | ~ l3_lattices(B_2409)
      | v2_struct_0(B_2409)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_2409,C_2410)) = C_57
      | ~ r4_lattice3('#skF_5',C_57,a_2_1_lattice3(B_2409,C_2410))
      | ~ m1_subset_1(C_57,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_60,c_31633])).

tff(c_39614,plain,(
    ! [B_2824,C_2825,C_2826] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3(B_2824,C_2825),C_2826))
      | ~ m1_subset_1('#skF_3'('#skF_5',a_2_1_lattice3(B_2824,C_2825),C_2826),u1_struct_0('#skF_5'))
      | ~ r3_lattice3(B_2824,'#skF_6',C_2825)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_2824))
      | ~ l3_lattices(B_2824)
      | v2_struct_0(B_2824)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_2824,C_2825)) = C_2826
      | ~ r4_lattice3('#skF_5',C_2826,a_2_1_lattice3(B_2824,C_2825))
      | ~ m1_subset_1(C_2826,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_31652])).

tff(c_39618,plain,(
    ! [B_2824,C_2825,C_57] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3(B_2824,C_2825),C_57))
      | ~ r3_lattice3(B_2824,'#skF_6',C_2825)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_2824))
      | ~ l3_lattices(B_2824)
      | v2_struct_0(B_2824)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_2824,C_2825)) = C_57
      | ~ r4_lattice3('#skF_5',C_57,a_2_1_lattice3(B_2824,C_2825))
      | ~ m1_subset_1(C_57,u1_struct_0('#skF_5'))
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_39614])).

tff(c_39621,plain,(
    ! [B_2824,C_2825,C_57] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3(B_2824,C_2825),C_57))
      | ~ r3_lattice3(B_2824,'#skF_6',C_2825)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_2824))
      | ~ l3_lattices(B_2824)
      | v2_struct_0(B_2824)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_2824,C_2825)) = C_57
      | ~ r4_lattice3('#skF_5',C_57,a_2_1_lattice3(B_2824,C_2825))
      | ~ m1_subset_1(C_57,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_60,c_39618])).

tff(c_46107,plain,(
    ! [B_3091,C_3092,C_3093] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3(B_3091,C_3092),C_3093))
      | ~ r3_lattice3(B_3091,'#skF_6',C_3092)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_3091))
      | ~ l3_lattices(B_3091)
      | v2_struct_0(B_3091)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_3091,C_3092)) = C_3093
      | ~ r4_lattice3('#skF_5',C_3093,a_2_1_lattice3(B_3091,C_3092))
      | ~ m1_subset_1(C_3093,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_39621])).

tff(c_46111,plain,(
    ! [B_3091,C_3092] :
      ( ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r3_lattice3(B_3091,'#skF_6',C_3092)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_3091))
      | ~ l3_lattices(B_3091)
      | v2_struct_0(B_3091)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_3091,C_3092)) = '#skF_6'
      | ~ r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3(B_3091,C_3092))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_46107,c_36])).

tff(c_46114,plain,(
    ! [B_3091,C_3092] :
      ( v2_struct_0('#skF_5')
      | ~ r3_lattice3(B_3091,'#skF_6',C_3092)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_3091))
      | ~ l3_lattices(B_3091)
      | v2_struct_0(B_3091)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_3091,C_3092)) = '#skF_6'
      | ~ r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3(B_3091,C_3092)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_62,c_60,c_46111])).

tff(c_46116,plain,(
    ! [B_3094,C_3095] :
      ( ~ r3_lattice3(B_3094,'#skF_6',C_3095)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_3094))
      | ~ l3_lattices(B_3094)
      | v2_struct_0(B_3094)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_3094,C_3095)) = '#skF_6'
      | ~ r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3(B_3094,C_3095)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46114])).

tff(c_46119,plain,
    ( ~ r3_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_7')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_31484,c_46116])).

tff(c_46125,plain,
    ( v2_struct_0('#skF_5')
    | k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_11623,c_46119])).

tff(c_46126,plain,(
    k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_7')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46125])).

tff(c_46177,plain,
    ( k16_lattice3('#skF_5','#skF_7') = '#skF_6'
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_46126,c_46])).

tff(c_46224,plain,
    ( k16_lattice3('#skF_5','#skF_7') = '#skF_6'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_46177])).

tff(c_46226,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_11626,c_46224])).

tff(c_46228,plain,(
    r3_lattices('#skF_5','#skF_9','#skF_6') ),
    inference(splitRight,[status(thm)],[c_11628])).

tff(c_46418,plain,(
    ! [A_3151,B_3152,C_3153] :
      ( r1_lattices(A_3151,B_3152,C_3153)
      | ~ r3_lattices(A_3151,B_3152,C_3153)
      | ~ m1_subset_1(C_3153,u1_struct_0(A_3151))
      | ~ m1_subset_1(B_3152,u1_struct_0(A_3151))
      | ~ l3_lattices(A_3151)
      | ~ v9_lattices(A_3151)
      | ~ v8_lattices(A_3151)
      | ~ v6_lattices(A_3151)
      | v2_struct_0(A_3151) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_46428,plain,
    ( r1_lattices('#skF_5','#skF_9','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | ~ v9_lattices('#skF_5')
    | ~ v8_lattices('#skF_5')
    | ~ v6_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_46228,c_46418])).

tff(c_46447,plain,
    ( r1_lattices('#skF_5','#skF_9','#skF_6')
    | ~ v9_lattices('#skF_5')
    | ~ v8_lattices('#skF_5')
    | ~ v6_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_46315,c_56,c_46428])).

tff(c_46448,plain,
    ( r1_lattices('#skF_5','#skF_9','#skF_6')
    | ~ v9_lattices('#skF_5')
    | ~ v8_lattices('#skF_5')
    | ~ v6_lattices('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46447])).

tff(c_46449,plain,(
    ~ v6_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_46448])).

tff(c_46452,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_46449])).

tff(c_46455,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_46452])).

tff(c_46457,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46455])).

tff(c_46459,plain,(
    v6_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_46448])).

tff(c_68,plain,(
    ! [D_87] :
      ( r3_lattices('#skF_5',D_87,'#skF_6')
      | ~ r3_lattice3('#skF_5',D_87,'#skF_7')
      | ~ m1_subset_1(D_87,u1_struct_0('#skF_5'))
      | ~ r3_lattices('#skF_5','#skF_9','#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_6','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_46322,plain,(
    ! [D_3131] :
      ( r3_lattices('#skF_5',D_3131,'#skF_6')
      | ~ r3_lattice3('#skF_5',D_3131,'#skF_7')
      | ~ m1_subset_1(D_3131,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11622,c_46228,c_68])).

tff(c_46340,plain,
    ( r3_lattices('#skF_5','#skF_6','#skF_6')
    | ~ r3_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_46322])).

tff(c_46357,plain,(
    r3_lattices('#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11623,c_46340])).

tff(c_46426,plain,
    ( r1_lattices('#skF_5','#skF_6','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | ~ v9_lattices('#skF_5')
    | ~ v8_lattices('#skF_5')
    | ~ v6_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_46357,c_46418])).

tff(c_46443,plain,
    ( r1_lattices('#skF_5','#skF_6','#skF_6')
    | ~ v9_lattices('#skF_5')
    | ~ v8_lattices('#skF_5')
    | ~ v6_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_46426])).

tff(c_46444,plain,
    ( r1_lattices('#skF_5','#skF_6','#skF_6')
    | ~ v9_lattices('#skF_5')
    | ~ v8_lattices('#skF_5')
    | ~ v6_lattices('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46443])).

tff(c_46461,plain,
    ( r1_lattices('#skF_5','#skF_6','#skF_6')
    | ~ v9_lattices('#skF_5')
    | ~ v8_lattices('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46459,c_46444])).

tff(c_46462,plain,(
    ~ v8_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_46461])).

tff(c_46465,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_46462])).

tff(c_46468,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_46465])).

tff(c_46470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46468])).

tff(c_46472,plain,(
    v8_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_46461])).

tff(c_46471,plain,
    ( ~ v9_lattices('#skF_5')
    | r1_lattices('#skF_5','#skF_6','#skF_6') ),
    inference(splitRight,[status(thm)],[c_46461])).

tff(c_46473,plain,(
    ~ v9_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_46471])).

tff(c_46476,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_46473])).

tff(c_46479,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_46476])).

tff(c_46481,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46479])).

tff(c_46483,plain,(
    v9_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_46471])).

tff(c_46337,plain,(
    ! [A_64,C_66] :
      ( r3_lattices('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_7')
      | ~ r2_hidden(A_64,a_2_1_lattice3('#skF_5',C_66))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_46322])).

tff(c_46353,plain,(
    ! [A_64,C_66] :
      ( r3_lattices('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_7')
      | ~ r2_hidden(A_64,a_2_1_lattice3('#skF_5',C_66))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_46337])).

tff(c_46354,plain,(
    ! [A_64,C_66] :
      ( r3_lattices('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_7')
      | ~ r2_hidden(A_64,a_2_1_lattice3('#skF_5',C_66)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46353])).

tff(c_46424,plain,(
    ! [A_64,C_66] :
      ( r1_lattices('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_4'(A_64,'#skF_5',C_66),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_7')
      | ~ r2_hidden(A_64,a_2_1_lattice3('#skF_5',C_66)) ) ),
    inference(resolution,[status(thm)],[c_46354,c_46418])).

tff(c_46439,plain,(
    ! [A_64,C_66] :
      ( r1_lattices('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_6')
      | ~ m1_subset_1('#skF_4'(A_64,'#skF_5',C_66),u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_7')
      | ~ r2_hidden(A_64,a_2_1_lattice3('#skF_5',C_66)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_46424])).

tff(c_46440,plain,(
    ! [A_64,C_66] :
      ( r1_lattices('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_6')
      | ~ m1_subset_1('#skF_4'(A_64,'#skF_5',C_66),u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_7')
      | ~ r2_hidden(A_64,a_2_1_lattice3('#skF_5',C_66)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46439])).

tff(c_46881,plain,(
    ! [A_3206,C_3207] :
      ( r1_lattices('#skF_5','#skF_4'(A_3206,'#skF_5',C_3207),'#skF_6')
      | ~ m1_subset_1('#skF_4'(A_3206,'#skF_5',C_3207),u1_struct_0('#skF_5'))
      | ~ r3_lattice3('#skF_5','#skF_4'(A_3206,'#skF_5',C_3207),'#skF_7')
      | ~ r2_hidden(A_3206,a_2_1_lattice3('#skF_5',C_3207)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46459,c_46472,c_46483,c_46440])).

tff(c_46897,plain,(
    ! [A_64,C_66] :
      ( r1_lattices('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_7')
      | ~ r2_hidden(A_64,a_2_1_lattice3('#skF_5',C_66))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_46881])).

tff(c_46904,plain,(
    ! [A_64,C_66] :
      ( r1_lattices('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_7')
      | ~ r2_hidden(A_64,a_2_1_lattice3('#skF_5',C_66))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_46897])).

tff(c_46906,plain,(
    ! [A_3208,C_3209] :
      ( r1_lattices('#skF_5','#skF_4'(A_3208,'#skF_5',C_3209),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_3208,'#skF_5',C_3209),'#skF_7')
      | ~ r2_hidden(A_3208,a_2_1_lattice3('#skF_5',C_3209)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46904])).

tff(c_46922,plain,(
    ! [A_64] :
      ( r1_lattices('#skF_5','#skF_4'(A_64,'#skF_5','#skF_7'),'#skF_6')
      | ~ r2_hidden(A_64,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_46906])).

tff(c_46929,plain,(
    ! [A_64] :
      ( r1_lattices('#skF_5','#skF_4'(A_64,'#skF_5','#skF_7'),'#skF_6')
      | ~ r2_hidden(A_64,a_2_1_lattice3('#skF_5','#skF_7'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_46922])).

tff(c_46930,plain,(
    ! [A_64] :
      ( r1_lattices('#skF_5','#skF_4'(A_64,'#skF_5','#skF_7'),'#skF_6')
      | ~ r2_hidden(A_64,a_2_1_lattice3('#skF_5','#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46929])).

tff(c_47258,plain,(
    ! [A_3241,B_3242] :
      ( r1_lattices('#skF_5','#skF_2'(A_3241,B_3242,a_2_1_lattice3('#skF_5','#skF_7')),'#skF_6')
      | ~ r2_hidden('#skF_2'(A_3241,B_3242,a_2_1_lattice3('#skF_5','#skF_7')),a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | r4_lattice3(A_3241,B_3242,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_3242,u1_struct_0(A_3241))
      | ~ l3_lattices(A_3241)
      | v2_struct_0(A_3241) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47248,c_46930])).

tff(c_47286,plain,(
    ! [A_3241,B_3242] :
      ( r1_lattices('#skF_5','#skF_2'(A_3241,B_3242,a_2_1_lattice3('#skF_5','#skF_7')),'#skF_6')
      | ~ r2_hidden('#skF_2'(A_3241,B_3242,a_2_1_lattice3('#skF_5','#skF_7')),a_2_1_lattice3('#skF_5','#skF_7'))
      | v2_struct_0('#skF_5')
      | r4_lattice3(A_3241,B_3242,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_3242,u1_struct_0(A_3241))
      | ~ l3_lattices(A_3241)
      | v2_struct_0(A_3241) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_47258])).

tff(c_47334,plain,(
    ! [A_3248,B_3249] :
      ( r1_lattices('#skF_5','#skF_2'(A_3248,B_3249,a_2_1_lattice3('#skF_5','#skF_7')),'#skF_6')
      | ~ r2_hidden('#skF_2'(A_3248,B_3249,a_2_1_lattice3('#skF_5','#skF_7')),a_2_1_lattice3('#skF_5','#skF_7'))
      | r4_lattice3(A_3248,B_3249,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_3249,u1_struct_0(A_3248))
      | ~ l3_lattices(A_3248)
      | v2_struct_0(A_3248) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_47286])).

tff(c_47347,plain,(
    ! [A_3250,B_3251] :
      ( r1_lattices('#skF_5','#skF_2'(A_3250,B_3251,a_2_1_lattice3('#skF_5','#skF_7')),'#skF_6')
      | r4_lattice3(A_3250,B_3251,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_3251,u1_struct_0(A_3250))
      | ~ l3_lattices(A_3250)
      | v2_struct_0(A_3250) ) ),
    inference(resolution,[status(thm)],[c_32,c_47334])).

tff(c_47351,plain,
    ( r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_7'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_47347,c_30])).

tff(c_47354,plain,
    ( r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_47351])).

tff(c_47355,plain,(
    r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_47354])).

tff(c_46376,plain,(
    ! [A_3140,D_3141,B_3142,C_3143] :
      ( r1_lattices(A_3140,D_3141,B_3142)
      | ~ r2_hidden(D_3141,C_3143)
      | ~ m1_subset_1(D_3141,u1_struct_0(A_3140))
      | ~ r4_lattice3(A_3140,B_3142,C_3143)
      | ~ m1_subset_1(B_3142,u1_struct_0(A_3140))
      | ~ l3_lattices(A_3140)
      | v2_struct_0(A_3140) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_47485,plain,(
    ! [D_3264,C_3261,B_3260,B_3263,A_3262] :
      ( r1_lattices(A_3262,D_3264,B_3263)
      | ~ m1_subset_1(D_3264,u1_struct_0(A_3262))
      | ~ r4_lattice3(A_3262,B_3263,a_2_1_lattice3(B_3260,C_3261))
      | ~ m1_subset_1(B_3263,u1_struct_0(A_3262))
      | ~ l3_lattices(A_3262)
      | v2_struct_0(A_3262)
      | ~ r3_lattice3(B_3260,D_3264,C_3261)
      | ~ m1_subset_1(D_3264,u1_struct_0(B_3260))
      | ~ l3_lattices(B_3260)
      | v2_struct_0(B_3260) ) ),
    inference(resolution,[status(thm)],[c_48,c_46376])).

tff(c_47497,plain,(
    ! [B_3263,B_3260,C_3261] :
      ( r1_lattices('#skF_5','#skF_6',B_3263)
      | ~ r4_lattice3('#skF_5',B_3263,a_2_1_lattice3(B_3260,C_3261))
      | ~ m1_subset_1(B_3263,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r3_lattice3(B_3260,'#skF_6',C_3261)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_3260))
      | ~ l3_lattices(B_3260)
      | v2_struct_0(B_3260) ) ),
    inference(resolution,[status(thm)],[c_56,c_47485])).

tff(c_47508,plain,(
    ! [B_3263,B_3260,C_3261] :
      ( r1_lattices('#skF_5','#skF_6',B_3263)
      | ~ r4_lattice3('#skF_5',B_3263,a_2_1_lattice3(B_3260,C_3261))
      | ~ m1_subset_1(B_3263,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | ~ r3_lattice3(B_3260,'#skF_6',C_3261)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_3260))
      | ~ l3_lattices(B_3260)
      | v2_struct_0(B_3260) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_47497])).

tff(c_47510,plain,(
    ! [B_3265,B_3266,C_3267] :
      ( r1_lattices('#skF_5','#skF_6',B_3265)
      | ~ r4_lattice3('#skF_5',B_3265,a_2_1_lattice3(B_3266,C_3267))
      | ~ m1_subset_1(B_3265,u1_struct_0('#skF_5'))
      | ~ r3_lattice3(B_3266,'#skF_6',C_3267)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_3266))
      | ~ l3_lattices(B_3266)
      | v2_struct_0(B_3266) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_47508])).

tff(c_47528,plain,(
    ! [B_3266,C_3267,C_57] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3(B_3266,C_3267),C_57))
      | ~ m1_subset_1('#skF_3'('#skF_5',a_2_1_lattice3(B_3266,C_3267),C_57),u1_struct_0('#skF_5'))
      | ~ r3_lattice3(B_3266,'#skF_6',C_3267)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_3266))
      | ~ l3_lattices(B_3266)
      | v2_struct_0(B_3266)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_3266,C_3267)) = C_57
      | ~ r4_lattice3('#skF_5',C_57,a_2_1_lattice3(B_3266,C_3267))
      | ~ m1_subset_1(C_57,u1_struct_0('#skF_5'))
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_38,c_47510])).

tff(c_47547,plain,(
    ! [B_3266,C_3267,C_57] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3(B_3266,C_3267),C_57))
      | ~ m1_subset_1('#skF_3'('#skF_5',a_2_1_lattice3(B_3266,C_3267),C_57),u1_struct_0('#skF_5'))
      | ~ r3_lattice3(B_3266,'#skF_6',C_3267)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_3266))
      | ~ l3_lattices(B_3266)
      | v2_struct_0(B_3266)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_3266,C_3267)) = C_57
      | ~ r4_lattice3('#skF_5',C_57,a_2_1_lattice3(B_3266,C_3267))
      | ~ m1_subset_1(C_57,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_60,c_47528])).

tff(c_56646,plain,(
    ! [B_3754,C_3755,C_3756] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3(B_3754,C_3755),C_3756))
      | ~ m1_subset_1('#skF_3'('#skF_5',a_2_1_lattice3(B_3754,C_3755),C_3756),u1_struct_0('#skF_5'))
      | ~ r3_lattice3(B_3754,'#skF_6',C_3755)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_3754))
      | ~ l3_lattices(B_3754)
      | v2_struct_0(B_3754)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_3754,C_3755)) = C_3756
      | ~ r4_lattice3('#skF_5',C_3756,a_2_1_lattice3(B_3754,C_3755))
      | ~ m1_subset_1(C_3756,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_47547])).

tff(c_56650,plain,(
    ! [B_3754,C_3755,C_57] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3(B_3754,C_3755),C_57))
      | ~ r3_lattice3(B_3754,'#skF_6',C_3755)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_3754))
      | ~ l3_lattices(B_3754)
      | v2_struct_0(B_3754)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_3754,C_3755)) = C_57
      | ~ r4_lattice3('#skF_5',C_57,a_2_1_lattice3(B_3754,C_3755))
      | ~ m1_subset_1(C_57,u1_struct_0('#skF_5'))
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_56646])).

tff(c_56653,plain,(
    ! [B_3754,C_3755,C_57] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3(B_3754,C_3755),C_57))
      | ~ r3_lattice3(B_3754,'#skF_6',C_3755)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_3754))
      | ~ l3_lattices(B_3754)
      | v2_struct_0(B_3754)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_3754,C_3755)) = C_57
      | ~ r4_lattice3('#skF_5',C_57,a_2_1_lattice3(B_3754,C_3755))
      | ~ m1_subset_1(C_57,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_60,c_56650])).

tff(c_64045,plain,(
    ! [B_4068,C_4069,C_4070] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3(B_4068,C_4069),C_4070))
      | ~ r3_lattice3(B_4068,'#skF_6',C_4069)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_4068))
      | ~ l3_lattices(B_4068)
      | v2_struct_0(B_4068)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_4068,C_4069)) = C_4070
      | ~ r4_lattice3('#skF_5',C_4070,a_2_1_lattice3(B_4068,C_4069))
      | ~ m1_subset_1(C_4070,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_56653])).

tff(c_64049,plain,(
    ! [B_4068,C_4069] :
      ( ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r3_lattice3(B_4068,'#skF_6',C_4069)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_4068))
      | ~ l3_lattices(B_4068)
      | v2_struct_0(B_4068)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_4068,C_4069)) = '#skF_6'
      | ~ r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3(B_4068,C_4069))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_64045,c_36])).

tff(c_64052,plain,(
    ! [B_4068,C_4069] :
      ( v2_struct_0('#skF_5')
      | ~ r3_lattice3(B_4068,'#skF_6',C_4069)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_4068))
      | ~ l3_lattices(B_4068)
      | v2_struct_0(B_4068)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_4068,C_4069)) = '#skF_6'
      | ~ r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3(B_4068,C_4069)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_62,c_60,c_64049])).

tff(c_64054,plain,(
    ! [B_4071,C_4072] :
      ( ~ r3_lattice3(B_4071,'#skF_6',C_4072)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_4071))
      | ~ l3_lattices(B_4071)
      | v2_struct_0(B_4071)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_4071,C_4072)) = '#skF_6'
      | ~ r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3(B_4071,C_4072)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_64052])).

tff(c_64057,plain,
    ( ~ r3_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_7')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_47355,c_64054])).

tff(c_64063,plain,
    ( v2_struct_0('#skF_5')
    | k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_11623,c_64057])).

tff(c_64064,plain,(
    k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_7')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_64063])).

tff(c_64118,plain,
    ( k16_lattice3('#skF_5','#skF_7') = '#skF_6'
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_64064,c_46])).

tff(c_64166,plain,
    ( k16_lattice3('#skF_5','#skF_7') = '#skF_6'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_64118])).

tff(c_64168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_11626,c_64166])).

tff(c_64170,plain,(
    k16_lattice3('#skF_5','#skF_7') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_11625])).

tff(c_64176,plain,(
    ~ r3_lattices('#skF_5','#skF_9','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11622,c_64170,c_66])).

tff(c_78,plain,
    ( k16_lattice3('#skF_5','#skF_7') != '#skF_6'
    | m1_subset_1('#skF_9',u1_struct_0('#skF_5'))
    | ~ r3_lattice3('#skF_5','#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_64191,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11622,c_64170,c_78])).

tff(c_64317,plain,(
    ! [A_4121,B_4122,C_4123] :
      ( r3_lattices(A_4121,B_4122,C_4123)
      | ~ r1_lattices(A_4121,B_4122,C_4123)
      | ~ m1_subset_1(C_4123,u1_struct_0(A_4121))
      | ~ m1_subset_1(B_4122,u1_struct_0(A_4121))
      | ~ l3_lattices(A_4121)
      | ~ v9_lattices(A_4121)
      | ~ v8_lattices(A_4121)
      | ~ v6_lattices(A_4121)
      | v2_struct_0(A_4121) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_64327,plain,(
    ! [B_4122] :
      ( r3_lattices('#skF_5',B_4122,'#skF_6')
      | ~ r1_lattices('#skF_5',B_4122,'#skF_6')
      | ~ m1_subset_1(B_4122,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_64317])).

tff(c_64337,plain,(
    ! [B_4122] :
      ( r3_lattices('#skF_5',B_4122,'#skF_6')
      | ~ r1_lattices('#skF_5',B_4122,'#skF_6')
      | ~ m1_subset_1(B_4122,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_64327])).

tff(c_64338,plain,(
    ! [B_4122] :
      ( r3_lattices('#skF_5',B_4122,'#skF_6')
      | ~ r1_lattices('#skF_5',B_4122,'#skF_6')
      | ~ m1_subset_1(B_4122,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_64337])).

tff(c_64339,plain,(
    ~ v6_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_64338])).

tff(c_64342,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_64339])).

tff(c_64345,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_64342])).

tff(c_64347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_64345])).

tff(c_64349,plain,(
    v6_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_64338])).

tff(c_64348,plain,(
    ! [B_4122] :
      ( ~ v8_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | r3_lattices('#skF_5',B_4122,'#skF_6')
      | ~ r1_lattices('#skF_5',B_4122,'#skF_6')
      | ~ m1_subset_1(B_4122,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_64338])).

tff(c_64354,plain,(
    ~ v9_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_64348])).

tff(c_64357,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_64354])).

tff(c_64360,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_64357])).

tff(c_64362,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_64360])).

tff(c_64364,plain,(
    v9_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_64348])).

tff(c_64325,plain,(
    ! [B_4122] :
      ( r3_lattices('#skF_5',B_4122,'#skF_9')
      | ~ r1_lattices('#skF_5',B_4122,'#skF_9')
      | ~ m1_subset_1(B_4122,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64191,c_64317])).

tff(c_64333,plain,(
    ! [B_4122] :
      ( r3_lattices('#skF_5',B_4122,'#skF_9')
      | ~ r1_lattices('#skF_5',B_4122,'#skF_9')
      | ~ m1_subset_1(B_4122,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_64325])).

tff(c_64334,plain,(
    ! [B_4122] :
      ( r3_lattices('#skF_5',B_4122,'#skF_9')
      | ~ r1_lattices('#skF_5',B_4122,'#skF_9')
      | ~ m1_subset_1(B_4122,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_64333])).

tff(c_64366,plain,(
    ! [B_4122] :
      ( r3_lattices('#skF_5',B_4122,'#skF_9')
      | ~ r1_lattices('#skF_5',B_4122,'#skF_9')
      | ~ m1_subset_1(B_4122,u1_struct_0('#skF_5'))
      | ~ v8_lattices('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64349,c_64364,c_64334])).

tff(c_64367,plain,(
    ~ v8_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_64366])).

tff(c_64370,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_64367])).

tff(c_64373,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_64370])).

tff(c_64375,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_64373])).

tff(c_64377,plain,(
    v8_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_64366])).

tff(c_64363,plain,(
    ! [B_4122] :
      ( ~ v8_lattices('#skF_5')
      | r3_lattices('#skF_5',B_4122,'#skF_6')
      | ~ r1_lattices('#skF_5',B_4122,'#skF_6')
      | ~ m1_subset_1(B_4122,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_64348])).

tff(c_64424,plain,(
    ! [B_4131] :
      ( r3_lattices('#skF_5',B_4131,'#skF_6')
      | ~ r1_lattices('#skF_5',B_4131,'#skF_6')
      | ~ m1_subset_1(B_4131,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64377,c_64363])).

tff(c_64443,plain,
    ( r3_lattices('#skF_5','#skF_9','#skF_6')
    | ~ r1_lattices('#skF_5','#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_64191,c_64424])).

tff(c_64465,plain,(
    ~ r1_lattices('#skF_5','#skF_9','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_64176,c_64443])).

tff(c_64169,plain,(
    r3_lattice3('#skF_5','#skF_9','#skF_8') ),
    inference(splitRight,[status(thm)],[c_11625])).

tff(c_64293,plain,(
    ! [A_4108,B_4109] :
      ( r4_lattice3(A_4108,k15_lattice3(A_4108,B_4109),B_4109)
      | ~ m1_subset_1(k15_lattice3(A_4108,B_4109),u1_struct_0(A_4108))
      | ~ v4_lattice3(A_4108)
      | ~ v10_lattices(A_4108)
      | ~ l3_lattices(A_4108)
      | v2_struct_0(A_4108) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_65447,plain,(
    ! [A_4248,B_4249] :
      ( r4_lattice3(A_4248,k15_lattice3(A_4248,a_2_1_lattice3(A_4248,B_4249)),a_2_1_lattice3(A_4248,B_4249))
      | ~ m1_subset_1(k16_lattice3(A_4248,B_4249),u1_struct_0(A_4248))
      | ~ v4_lattice3(A_4248)
      | ~ v10_lattices(A_4248)
      | ~ l3_lattices(A_4248)
      | v2_struct_0(A_4248)
      | ~ l3_lattices(A_4248)
      | v2_struct_0(A_4248) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_64293])).

tff(c_65498,plain,(
    ! [A_4254,B_4255] :
      ( r4_lattice3(A_4254,k16_lattice3(A_4254,B_4255),a_2_1_lattice3(A_4254,B_4255))
      | ~ m1_subset_1(k16_lattice3(A_4254,B_4255),u1_struct_0(A_4254))
      | ~ v4_lattice3(A_4254)
      | ~ v10_lattices(A_4254)
      | ~ l3_lattices(A_4254)
      | v2_struct_0(A_4254)
      | ~ l3_lattices(A_4254)
      | v2_struct_0(A_4254)
      | ~ l3_lattices(A_4254)
      | v2_struct_0(A_4254) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_65447])).

tff(c_65504,plain,
    ( r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_8'))
    | ~ m1_subset_1(k16_lattice3('#skF_5','#skF_8'),u1_struct_0('#skF_5'))
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_65498])).

tff(c_65509,plain,
    ( r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_8'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_58,c_58,c_62,c_60,c_56,c_90,c_65504])).

tff(c_65510,plain,(
    r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_65509])).

tff(c_64306,plain,(
    ! [A_4114,D_4115,B_4116,C_4117] :
      ( r1_lattices(A_4114,D_4115,B_4116)
      | ~ r2_hidden(D_4115,C_4117)
      | ~ m1_subset_1(D_4115,u1_struct_0(A_4114))
      | ~ r4_lattice3(A_4114,B_4116,C_4117)
      | ~ m1_subset_1(B_4116,u1_struct_0(A_4114))
      | ~ l3_lattices(A_4114)
      | v2_struct_0(A_4114) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_65803,plain,(
    ! [B_4284,A_4286,C_4285,B_4283,D_4287] :
      ( r1_lattices(A_4286,D_4287,B_4284)
      | ~ m1_subset_1(D_4287,u1_struct_0(A_4286))
      | ~ r4_lattice3(A_4286,B_4284,a_2_1_lattice3(B_4283,C_4285))
      | ~ m1_subset_1(B_4284,u1_struct_0(A_4286))
      | ~ l3_lattices(A_4286)
      | v2_struct_0(A_4286)
      | ~ r3_lattice3(B_4283,D_4287,C_4285)
      | ~ m1_subset_1(D_4287,u1_struct_0(B_4283))
      | ~ l3_lattices(B_4283)
      | v2_struct_0(B_4283) ) ),
    inference(resolution,[status(thm)],[c_48,c_64306])).

tff(c_65813,plain,(
    ! [B_4284,B_4283,C_4285] :
      ( r1_lattices('#skF_5','#skF_9',B_4284)
      | ~ r4_lattice3('#skF_5',B_4284,a_2_1_lattice3(B_4283,C_4285))
      | ~ m1_subset_1(B_4284,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r3_lattice3(B_4283,'#skF_9',C_4285)
      | ~ m1_subset_1('#skF_9',u1_struct_0(B_4283))
      | ~ l3_lattices(B_4283)
      | v2_struct_0(B_4283) ) ),
    inference(resolution,[status(thm)],[c_64191,c_65803])).

tff(c_65822,plain,(
    ! [B_4284,B_4283,C_4285] :
      ( r1_lattices('#skF_5','#skF_9',B_4284)
      | ~ r4_lattice3('#skF_5',B_4284,a_2_1_lattice3(B_4283,C_4285))
      | ~ m1_subset_1(B_4284,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | ~ r3_lattice3(B_4283,'#skF_9',C_4285)
      | ~ m1_subset_1('#skF_9',u1_struct_0(B_4283))
      | ~ l3_lattices(B_4283)
      | v2_struct_0(B_4283) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_65813])).

tff(c_65912,plain,(
    ! [B_4300,B_4301,C_4302] :
      ( r1_lattices('#skF_5','#skF_9',B_4300)
      | ~ r4_lattice3('#skF_5',B_4300,a_2_1_lattice3(B_4301,C_4302))
      | ~ m1_subset_1(B_4300,u1_struct_0('#skF_5'))
      | ~ r3_lattice3(B_4301,'#skF_9',C_4302)
      | ~ m1_subset_1('#skF_9',u1_struct_0(B_4301))
      | ~ l3_lattices(B_4301)
      | v2_struct_0(B_4301) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_65822])).

tff(c_65918,plain,
    ( r1_lattices('#skF_5','#skF_9','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ r3_lattice3('#skF_5','#skF_9','#skF_8')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_65510,c_65912])).

tff(c_65937,plain,
    ( r1_lattices('#skF_5','#skF_9','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_64191,c_64169,c_56,c_65918])).

tff(c_65939,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_64465,c_65937])).

tff(c_65941,plain,(
    ~ r3_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_11621])).

tff(c_70,plain,
    ( r3_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ r3_lattices('#skF_5','#skF_9','#skF_6')
    | ~ r3_lattice3('#skF_5','#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_65951,plain,
    ( r3_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ r3_lattices('#skF_5','#skF_9','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11622,c_70])).

tff(c_65952,plain,(
    ~ r3_lattices('#skF_5','#skF_9','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_65941,c_65951])).

tff(c_65940,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_11621])).

tff(c_66067,plain,(
    ! [A_4351,B_4352,C_4353] :
      ( r3_lattices(A_4351,B_4352,C_4353)
      | ~ r1_lattices(A_4351,B_4352,C_4353)
      | ~ m1_subset_1(C_4353,u1_struct_0(A_4351))
      | ~ m1_subset_1(B_4352,u1_struct_0(A_4351))
      | ~ l3_lattices(A_4351)
      | ~ v9_lattices(A_4351)
      | ~ v8_lattices(A_4351)
      | ~ v6_lattices(A_4351)
      | v2_struct_0(A_4351) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_66077,plain,(
    ! [B_4352] :
      ( r3_lattices('#skF_5',B_4352,'#skF_6')
      | ~ r1_lattices('#skF_5',B_4352,'#skF_6')
      | ~ m1_subset_1(B_4352,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_66067])).

tff(c_66087,plain,(
    ! [B_4352] :
      ( r3_lattices('#skF_5',B_4352,'#skF_6')
      | ~ r1_lattices('#skF_5',B_4352,'#skF_6')
      | ~ m1_subset_1(B_4352,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_66077])).

tff(c_66088,plain,(
    ! [B_4352] :
      ( r3_lattices('#skF_5',B_4352,'#skF_6')
      | ~ r1_lattices('#skF_5',B_4352,'#skF_6')
      | ~ m1_subset_1(B_4352,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_66087])).

tff(c_66089,plain,(
    ~ v6_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_66088])).

tff(c_66092,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_66089])).

tff(c_66095,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_66092])).

tff(c_66097,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_66095])).

tff(c_66098,plain,(
    ! [B_4352] :
      ( ~ v8_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | r3_lattices('#skF_5',B_4352,'#skF_6')
      | ~ r1_lattices('#skF_5',B_4352,'#skF_6')
      | ~ m1_subset_1(B_4352,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_66088])).

tff(c_66100,plain,(
    ~ v9_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_66098])).

tff(c_66104,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_66100])).

tff(c_66107,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_66104])).

tff(c_66109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_66107])).

tff(c_66110,plain,(
    ! [B_4352] :
      ( ~ v8_lattices('#skF_5')
      | r3_lattices('#skF_5',B_4352,'#skF_6')
      | ~ r1_lattices('#skF_5',B_4352,'#skF_6')
      | ~ m1_subset_1(B_4352,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_66098])).

tff(c_66112,plain,(
    ~ v8_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_66110])).

tff(c_66118,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_66112])).

tff(c_66121,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_66118])).

tff(c_66123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_66121])).

tff(c_66126,plain,(
    ! [B_4357] :
      ( r3_lattices('#skF_5',B_4357,'#skF_6')
      | ~ r1_lattices('#skF_5',B_4357,'#skF_6')
      | ~ m1_subset_1(B_4357,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_66110])).

tff(c_66141,plain,
    ( r3_lattices('#skF_5','#skF_9','#skF_6')
    | ~ r1_lattices('#skF_5','#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_65940,c_66126])).

tff(c_66159,plain,(
    ~ r1_lattices('#skF_5','#skF_9','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_65952,c_66141])).

tff(c_76,plain,
    ( r3_lattice3('#skF_5','#skF_6','#skF_7')
    | r3_lattice3('#skF_5','#skF_9','#skF_8')
    | ~ r3_lattice3('#skF_5','#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_65948,plain,
    ( r3_lattice3('#skF_5','#skF_6','#skF_7')
    | r3_lattice3('#skF_5','#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11622,c_76])).

tff(c_65949,plain,(
    r3_lattice3('#skF_5','#skF_9','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_65941,c_65948])).

tff(c_66039,plain,(
    ! [A_4338,B_4339] :
      ( r4_lattice3(A_4338,k15_lattice3(A_4338,B_4339),B_4339)
      | ~ m1_subset_1(k15_lattice3(A_4338,B_4339),u1_struct_0(A_4338))
      | ~ v4_lattice3(A_4338)
      | ~ v10_lattices(A_4338)
      | ~ l3_lattices(A_4338)
      | v2_struct_0(A_4338) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_67193,plain,(
    ! [A_4499,B_4500] :
      ( r4_lattice3(A_4499,k15_lattice3(A_4499,a_2_1_lattice3(A_4499,B_4500)),a_2_1_lattice3(A_4499,B_4500))
      | ~ m1_subset_1(k16_lattice3(A_4499,B_4500),u1_struct_0(A_4499))
      | ~ v4_lattice3(A_4499)
      | ~ v10_lattices(A_4499)
      | ~ l3_lattices(A_4499)
      | v2_struct_0(A_4499)
      | ~ l3_lattices(A_4499)
      | v2_struct_0(A_4499) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_66039])).

tff(c_67271,plain,(
    ! [A_4512,B_4513] :
      ( r4_lattice3(A_4512,k16_lattice3(A_4512,B_4513),a_2_1_lattice3(A_4512,B_4513))
      | ~ m1_subset_1(k16_lattice3(A_4512,B_4513),u1_struct_0(A_4512))
      | ~ v4_lattice3(A_4512)
      | ~ v10_lattices(A_4512)
      | ~ l3_lattices(A_4512)
      | v2_struct_0(A_4512)
      | ~ l3_lattices(A_4512)
      | v2_struct_0(A_4512)
      | ~ l3_lattices(A_4512)
      | v2_struct_0(A_4512) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_67193])).

tff(c_67274,plain,
    ( r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_8'))
    | ~ m1_subset_1(k16_lattice3('#skF_5','#skF_8'),u1_struct_0('#skF_5'))
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_67271])).

tff(c_67276,plain,
    ( r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_8'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_58,c_58,c_62,c_60,c_56,c_90,c_67274])).

tff(c_67277,plain,(
    r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_67276])).

tff(c_66056,plain,(
    ! [A_4344,D_4345,B_4346,C_4347] :
      ( r1_lattices(A_4344,D_4345,B_4346)
      | ~ r2_hidden(D_4345,C_4347)
      | ~ m1_subset_1(D_4345,u1_struct_0(A_4344))
      | ~ r4_lattice3(A_4344,B_4346,C_4347)
      | ~ m1_subset_1(B_4346,u1_struct_0(A_4344))
      | ~ l3_lattices(A_4344)
      | v2_struct_0(A_4344) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_67549,plain,(
    ! [A_4548,B_4545,C_4546,B_4547,D_4549] :
      ( r1_lattices(A_4548,D_4549,B_4547)
      | ~ m1_subset_1(D_4549,u1_struct_0(A_4548))
      | ~ r4_lattice3(A_4548,B_4547,a_2_1_lattice3(B_4545,C_4546))
      | ~ m1_subset_1(B_4547,u1_struct_0(A_4548))
      | ~ l3_lattices(A_4548)
      | v2_struct_0(A_4548)
      | ~ r3_lattice3(B_4545,D_4549,C_4546)
      | ~ m1_subset_1(D_4549,u1_struct_0(B_4545))
      | ~ l3_lattices(B_4545)
      | v2_struct_0(B_4545) ) ),
    inference(resolution,[status(thm)],[c_48,c_66056])).

tff(c_67559,plain,(
    ! [B_4547,B_4545,C_4546] :
      ( r1_lattices('#skF_5','#skF_9',B_4547)
      | ~ r4_lattice3('#skF_5',B_4547,a_2_1_lattice3(B_4545,C_4546))
      | ~ m1_subset_1(B_4547,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r3_lattice3(B_4545,'#skF_9',C_4546)
      | ~ m1_subset_1('#skF_9',u1_struct_0(B_4545))
      | ~ l3_lattices(B_4545)
      | v2_struct_0(B_4545) ) ),
    inference(resolution,[status(thm)],[c_65940,c_67549])).

tff(c_67568,plain,(
    ! [B_4547,B_4545,C_4546] :
      ( r1_lattices('#skF_5','#skF_9',B_4547)
      | ~ r4_lattice3('#skF_5',B_4547,a_2_1_lattice3(B_4545,C_4546))
      | ~ m1_subset_1(B_4547,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | ~ r3_lattice3(B_4545,'#skF_9',C_4546)
      | ~ m1_subset_1('#skF_9',u1_struct_0(B_4545))
      | ~ l3_lattices(B_4545)
      | v2_struct_0(B_4545) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_67559])).

tff(c_67612,plain,(
    ! [B_4554,B_4555,C_4556] :
      ( r1_lattices('#skF_5','#skF_9',B_4554)
      | ~ r4_lattice3('#skF_5',B_4554,a_2_1_lattice3(B_4555,C_4556))
      | ~ m1_subset_1(B_4554,u1_struct_0('#skF_5'))
      | ~ r3_lattice3(B_4555,'#skF_9',C_4556)
      | ~ m1_subset_1('#skF_9',u1_struct_0(B_4555))
      | ~ l3_lattices(B_4555)
      | v2_struct_0(B_4555) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_67568])).

tff(c_67615,plain,
    ( r1_lattices('#skF_5','#skF_9','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ r3_lattice3('#skF_5','#skF_9','#skF_8')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_67277,c_67612])).

tff(c_67630,plain,
    ( r1_lattices('#skF_5','#skF_9','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_65940,c_65949,c_56,c_67615])).

tff(c_67632,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_66159,c_67630])).

tff(c_67634,plain,(
    k16_lattice3('#skF_5','#skF_8') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_84,plain,
    ( k16_lattice3('#skF_5','#skF_7') != '#skF_6'
    | k16_lattice3('#skF_5','#skF_8') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_67635,plain,(
    k16_lattice3('#skF_5','#skF_7') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_67633,plain,(
    r3_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_67703,plain,(
    ! [A_4580,B_4581,C_4582] :
      ( r2_hidden('#skF_2'(A_4580,B_4581,C_4582),C_4582)
      | r4_lattice3(A_4580,B_4581,C_4582)
      | ~ m1_subset_1(B_4581,u1_struct_0(A_4580))
      | ~ l3_lattices(A_4580)
      | v2_struct_0(A_4580) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_68228,plain,(
    ! [A_4683,B_4684,B_4685,C_4686] :
      ( '#skF_4'('#skF_2'(A_4683,B_4684,a_2_1_lattice3(B_4685,C_4686)),B_4685,C_4686) = '#skF_2'(A_4683,B_4684,a_2_1_lattice3(B_4685,C_4686))
      | ~ l3_lattices(B_4685)
      | v2_struct_0(B_4685)
      | r4_lattice3(A_4683,B_4684,a_2_1_lattice3(B_4685,C_4686))
      | ~ m1_subset_1(B_4684,u1_struct_0(A_4683))
      | ~ l3_lattices(A_4683)
      | v2_struct_0(A_4683) ) ),
    inference(resolution,[status(thm)],[c_67703,c_52])).

tff(c_67766,plain,(
    ! [A_4614,B_4615,C_4616] :
      ( r3_lattices(A_4614,B_4615,C_4616)
      | ~ r1_lattices(A_4614,B_4615,C_4616)
      | ~ m1_subset_1(C_4616,u1_struct_0(A_4614))
      | ~ m1_subset_1(B_4615,u1_struct_0(A_4614))
      | ~ l3_lattices(A_4614)
      | ~ v9_lattices(A_4614)
      | ~ v8_lattices(A_4614)
      | ~ v6_lattices(A_4614)
      | v2_struct_0(A_4614) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_67774,plain,(
    ! [B_4615] :
      ( r3_lattices('#skF_5',B_4615,'#skF_6')
      | ~ r1_lattices('#skF_5',B_4615,'#skF_6')
      | ~ m1_subset_1(B_4615,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_67766])).

tff(c_67780,plain,(
    ! [B_4615] :
      ( r3_lattices('#skF_5',B_4615,'#skF_6')
      | ~ r1_lattices('#skF_5',B_4615,'#skF_6')
      | ~ m1_subset_1(B_4615,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_67774])).

tff(c_67781,plain,(
    ! [B_4615] :
      ( r3_lattices('#skF_5',B_4615,'#skF_6')
      | ~ r1_lattices('#skF_5',B_4615,'#skF_6')
      | ~ m1_subset_1(B_4615,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_67780])).

tff(c_67782,plain,(
    ~ v6_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_67781])).

tff(c_67785,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_67782])).

tff(c_67788,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_67785])).

tff(c_67790,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_67788])).

tff(c_67792,plain,(
    v6_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_67781])).

tff(c_67791,plain,(
    ! [B_4615] :
      ( ~ v8_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | r3_lattices('#skF_5',B_4615,'#skF_6')
      | ~ r1_lattices('#skF_5',B_4615,'#skF_6')
      | ~ m1_subset_1(B_4615,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_67781])).

tff(c_67793,plain,(
    ~ v9_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_67791])).

tff(c_67796,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_67793])).

tff(c_67799,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_67796])).

tff(c_67801,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_67799])).

tff(c_67803,plain,(
    v9_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_67791])).

tff(c_86,plain,(
    ! [D_87] :
      ( r3_lattices('#skF_5',D_87,'#skF_6')
      | ~ r3_lattice3('#skF_5',D_87,'#skF_7')
      | ~ m1_subset_1(D_87,u1_struct_0('#skF_5'))
      | k16_lattice3('#skF_5','#skF_8') = '#skF_6' ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_67656,plain,(
    ! [D_4570] :
      ( r3_lattices('#skF_5',D_4570,'#skF_6')
      | ~ r3_lattice3('#skF_5',D_4570,'#skF_7')
      | ~ m1_subset_1(D_4570,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_67634,c_86])).

tff(c_67659,plain,
    ( r3_lattices('#skF_5','#skF_6','#skF_6')
    | ~ r3_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_67656])).

tff(c_67662,plain,(
    r3_lattices('#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67633,c_67659])).

tff(c_67804,plain,(
    ! [A_4617,B_4618,C_4619] :
      ( r1_lattices(A_4617,B_4618,C_4619)
      | ~ r3_lattices(A_4617,B_4618,C_4619)
      | ~ m1_subset_1(C_4619,u1_struct_0(A_4617))
      | ~ m1_subset_1(B_4618,u1_struct_0(A_4617))
      | ~ l3_lattices(A_4617)
      | ~ v9_lattices(A_4617)
      | ~ v8_lattices(A_4617)
      | ~ v6_lattices(A_4617)
      | v2_struct_0(A_4617) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_67812,plain,
    ( r1_lattices('#skF_5','#skF_6','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | ~ v9_lattices('#skF_5')
    | ~ v8_lattices('#skF_5')
    | ~ v6_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_67662,c_67804])).

tff(c_67827,plain,
    ( r1_lattices('#skF_5','#skF_6','#skF_6')
    | ~ v8_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67792,c_67803,c_58,c_56,c_67812])).

tff(c_67828,plain,
    ( r1_lattices('#skF_5','#skF_6','#skF_6')
    | ~ v8_lattices('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_67827])).

tff(c_67829,plain,(
    ~ v8_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_67828])).

tff(c_67832,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_67829])).

tff(c_67835,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_67832])).

tff(c_67837,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_67835])).

tff(c_67839,plain,(
    v8_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_67828])).

tff(c_67663,plain,(
    ! [A_4571,B_4572,C_4573] :
      ( m1_subset_1('#skF_4'(A_4571,B_4572,C_4573),u1_struct_0(B_4572))
      | ~ r2_hidden(A_4571,a_2_1_lattice3(B_4572,C_4573))
      | ~ l3_lattices(B_4572)
      | v2_struct_0(B_4572) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_67655,plain,(
    ! [D_87] :
      ( r3_lattices('#skF_5',D_87,'#skF_6')
      | ~ r3_lattice3('#skF_5',D_87,'#skF_7')
      | ~ m1_subset_1(D_87,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_67634,c_86])).

tff(c_67667,plain,(
    ! [A_4571,C_4573] :
      ( r3_lattices('#skF_5','#skF_4'(A_4571,'#skF_5',C_4573),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_4571,'#skF_5',C_4573),'#skF_7')
      | ~ r2_hidden(A_4571,a_2_1_lattice3('#skF_5',C_4573))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_67663,c_67655])).

tff(c_67670,plain,(
    ! [A_4571,C_4573] :
      ( r3_lattices('#skF_5','#skF_4'(A_4571,'#skF_5',C_4573),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_4571,'#skF_5',C_4573),'#skF_7')
      | ~ r2_hidden(A_4571,a_2_1_lattice3('#skF_5',C_4573))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_67667])).

tff(c_67671,plain,(
    ! [A_4571,C_4573] :
      ( r3_lattices('#skF_5','#skF_4'(A_4571,'#skF_5',C_4573),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_4571,'#skF_5',C_4573),'#skF_7')
      | ~ r2_hidden(A_4571,a_2_1_lattice3('#skF_5',C_4573)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_67670])).

tff(c_67810,plain,(
    ! [A_4571,C_4573] :
      ( r1_lattices('#skF_5','#skF_4'(A_4571,'#skF_5',C_4573),'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_4'(A_4571,'#skF_5',C_4573),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_4571,'#skF_5',C_4573),'#skF_7')
      | ~ r2_hidden(A_4571,a_2_1_lattice3('#skF_5',C_4573)) ) ),
    inference(resolution,[status(thm)],[c_67671,c_67804])).

tff(c_67823,plain,(
    ! [A_4571,C_4573] :
      ( r1_lattices('#skF_5','#skF_4'(A_4571,'#skF_5',C_4573),'#skF_6')
      | ~ m1_subset_1('#skF_4'(A_4571,'#skF_5',C_4573),u1_struct_0('#skF_5'))
      | ~ v8_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_4571,'#skF_5',C_4573),'#skF_7')
      | ~ r2_hidden(A_4571,a_2_1_lattice3('#skF_5',C_4573)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67792,c_67803,c_58,c_56,c_67810])).

tff(c_67824,plain,(
    ! [A_4571,C_4573] :
      ( r1_lattices('#skF_5','#skF_4'(A_4571,'#skF_5',C_4573),'#skF_6')
      | ~ m1_subset_1('#skF_4'(A_4571,'#skF_5',C_4573),u1_struct_0('#skF_5'))
      | ~ v8_lattices('#skF_5')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_4571,'#skF_5',C_4573),'#skF_7')
      | ~ r2_hidden(A_4571,a_2_1_lattice3('#skF_5',C_4573)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_67823])).

tff(c_67842,plain,(
    ! [A_4620,C_4621] :
      ( r1_lattices('#skF_5','#skF_4'(A_4620,'#skF_5',C_4621),'#skF_6')
      | ~ m1_subset_1('#skF_4'(A_4620,'#skF_5',C_4621),u1_struct_0('#skF_5'))
      | ~ r3_lattice3('#skF_5','#skF_4'(A_4620,'#skF_5',C_4621),'#skF_7')
      | ~ r2_hidden(A_4620,a_2_1_lattice3('#skF_5',C_4621)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67839,c_67824])).

tff(c_67849,plain,(
    ! [A_64,C_66] :
      ( r1_lattices('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_7')
      | ~ r2_hidden(A_64,a_2_1_lattice3('#skF_5',C_66))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_67842])).

tff(c_67854,plain,(
    ! [A_64,C_66] :
      ( r1_lattices('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_64,'#skF_5',C_66),'#skF_7')
      | ~ r2_hidden(A_64,a_2_1_lattice3('#skF_5',C_66))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_67849])).

tff(c_67890,plain,(
    ! [A_4623,C_4624] :
      ( r1_lattices('#skF_5','#skF_4'(A_4623,'#skF_5',C_4624),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_4623,'#skF_5',C_4624),'#skF_7')
      | ~ r2_hidden(A_4623,a_2_1_lattice3('#skF_5',C_4624)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_67854])).

tff(c_67897,plain,(
    ! [A_64] :
      ( r1_lattices('#skF_5','#skF_4'(A_64,'#skF_5','#skF_7'),'#skF_6')
      | ~ r2_hidden(A_64,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_67890])).

tff(c_67902,plain,(
    ! [A_64] :
      ( r1_lattices('#skF_5','#skF_4'(A_64,'#skF_5','#skF_7'),'#skF_6')
      | ~ r2_hidden(A_64,a_2_1_lattice3('#skF_5','#skF_7'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_67897])).

tff(c_67903,plain,(
    ! [A_64] :
      ( r1_lattices('#skF_5','#skF_4'(A_64,'#skF_5','#skF_7'),'#skF_6')
      | ~ r2_hidden(A_64,a_2_1_lattice3('#skF_5','#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_67902])).

tff(c_68242,plain,(
    ! [A_4683,B_4684] :
      ( r1_lattices('#skF_5','#skF_2'(A_4683,B_4684,a_2_1_lattice3('#skF_5','#skF_7')),'#skF_6')
      | ~ r2_hidden('#skF_2'(A_4683,B_4684,a_2_1_lattice3('#skF_5','#skF_7')),a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | r4_lattice3(A_4683,B_4684,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_4684,u1_struct_0(A_4683))
      | ~ l3_lattices(A_4683)
      | v2_struct_0(A_4683) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68228,c_67903])).

tff(c_68265,plain,(
    ! [A_4683,B_4684] :
      ( r1_lattices('#skF_5','#skF_2'(A_4683,B_4684,a_2_1_lattice3('#skF_5','#skF_7')),'#skF_6')
      | ~ r2_hidden('#skF_2'(A_4683,B_4684,a_2_1_lattice3('#skF_5','#skF_7')),a_2_1_lattice3('#skF_5','#skF_7'))
      | v2_struct_0('#skF_5')
      | r4_lattice3(A_4683,B_4684,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_4684,u1_struct_0(A_4683))
      | ~ l3_lattices(A_4683)
      | v2_struct_0(A_4683) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_68242])).

tff(c_68330,plain,(
    ! [A_4695,B_4696] :
      ( r1_lattices('#skF_5','#skF_2'(A_4695,B_4696,a_2_1_lattice3('#skF_5','#skF_7')),'#skF_6')
      | ~ r2_hidden('#skF_2'(A_4695,B_4696,a_2_1_lattice3('#skF_5','#skF_7')),a_2_1_lattice3('#skF_5','#skF_7'))
      | r4_lattice3(A_4695,B_4696,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_4696,u1_struct_0(A_4695))
      | ~ l3_lattices(A_4695)
      | v2_struct_0(A_4695) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_68265])).

tff(c_68343,plain,(
    ! [A_4697,B_4698] :
      ( r1_lattices('#skF_5','#skF_2'(A_4697,B_4698,a_2_1_lattice3('#skF_5','#skF_7')),'#skF_6')
      | r4_lattice3(A_4697,B_4698,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_4698,u1_struct_0(A_4697))
      | ~ l3_lattices(A_4697)
      | v2_struct_0(A_4697) ) ),
    inference(resolution,[status(thm)],[c_32,c_68330])).

tff(c_68347,plain,
    ( r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_7'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_68343,c_30])).

tff(c_68350,plain,
    ( r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_68347])).

tff(c_68351,plain,(
    r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_68350])).

tff(c_67745,plain,(
    ! [A_4604,D_4605,B_4606,C_4607] :
      ( r1_lattices(A_4604,D_4605,B_4606)
      | ~ r2_hidden(D_4605,C_4607)
      | ~ m1_subset_1(D_4605,u1_struct_0(A_4604))
      | ~ r4_lattice3(A_4604,B_4606,C_4607)
      | ~ m1_subset_1(B_4606,u1_struct_0(A_4604))
      | ~ l3_lattices(A_4604)
      | v2_struct_0(A_4604) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_68603,plain,(
    ! [C_4726,A_4728,D_4729,B_4727,B_4725] :
      ( r1_lattices(A_4728,D_4729,B_4727)
      | ~ m1_subset_1(D_4729,u1_struct_0(A_4728))
      | ~ r4_lattice3(A_4728,B_4727,a_2_1_lattice3(B_4725,C_4726))
      | ~ m1_subset_1(B_4727,u1_struct_0(A_4728))
      | ~ l3_lattices(A_4728)
      | v2_struct_0(A_4728)
      | ~ r3_lattice3(B_4725,D_4729,C_4726)
      | ~ m1_subset_1(D_4729,u1_struct_0(B_4725))
      | ~ l3_lattices(B_4725)
      | v2_struct_0(B_4725) ) ),
    inference(resolution,[status(thm)],[c_48,c_67745])).

tff(c_68613,plain,(
    ! [B_4727,B_4725,C_4726] :
      ( r1_lattices('#skF_5','#skF_6',B_4727)
      | ~ r4_lattice3('#skF_5',B_4727,a_2_1_lattice3(B_4725,C_4726))
      | ~ m1_subset_1(B_4727,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r3_lattice3(B_4725,'#skF_6',C_4726)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_4725))
      | ~ l3_lattices(B_4725)
      | v2_struct_0(B_4725) ) ),
    inference(resolution,[status(thm)],[c_56,c_68603])).

tff(c_68620,plain,(
    ! [B_4727,B_4725,C_4726] :
      ( r1_lattices('#skF_5','#skF_6',B_4727)
      | ~ r4_lattice3('#skF_5',B_4727,a_2_1_lattice3(B_4725,C_4726))
      | ~ m1_subset_1(B_4727,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | ~ r3_lattice3(B_4725,'#skF_6',C_4726)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_4725))
      | ~ l3_lattices(B_4725)
      | v2_struct_0(B_4725) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_68613])).

tff(c_68622,plain,(
    ! [B_4730,B_4731,C_4732] :
      ( r1_lattices('#skF_5','#skF_6',B_4730)
      | ~ r4_lattice3('#skF_5',B_4730,a_2_1_lattice3(B_4731,C_4732))
      | ~ m1_subset_1(B_4730,u1_struct_0('#skF_5'))
      | ~ r3_lattice3(B_4731,'#skF_6',C_4732)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_4731))
      | ~ l3_lattices(B_4731)
      | v2_struct_0(B_4731) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_68620])).

tff(c_68637,plain,(
    ! [B_4731,C_4732,C_57] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3(B_4731,C_4732),C_57))
      | ~ m1_subset_1('#skF_3'('#skF_5',a_2_1_lattice3(B_4731,C_4732),C_57),u1_struct_0('#skF_5'))
      | ~ r3_lattice3(B_4731,'#skF_6',C_4732)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_4731))
      | ~ l3_lattices(B_4731)
      | v2_struct_0(B_4731)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_4731,C_4732)) = C_57
      | ~ r4_lattice3('#skF_5',C_57,a_2_1_lattice3(B_4731,C_4732))
      | ~ m1_subset_1(C_57,u1_struct_0('#skF_5'))
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_38,c_68622])).

tff(c_68652,plain,(
    ! [B_4731,C_4732,C_57] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3(B_4731,C_4732),C_57))
      | ~ m1_subset_1('#skF_3'('#skF_5',a_2_1_lattice3(B_4731,C_4732),C_57),u1_struct_0('#skF_5'))
      | ~ r3_lattice3(B_4731,'#skF_6',C_4732)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_4731))
      | ~ l3_lattices(B_4731)
      | v2_struct_0(B_4731)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_4731,C_4732)) = C_57
      | ~ r4_lattice3('#skF_5',C_57,a_2_1_lattice3(B_4731,C_4732))
      | ~ m1_subset_1(C_57,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_60,c_68637])).

tff(c_72273,plain,(
    ! [B_5128,C_5129,C_5130] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3(B_5128,C_5129),C_5130))
      | ~ m1_subset_1('#skF_3'('#skF_5',a_2_1_lattice3(B_5128,C_5129),C_5130),u1_struct_0('#skF_5'))
      | ~ r3_lattice3(B_5128,'#skF_6',C_5129)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_5128))
      | ~ l3_lattices(B_5128)
      | v2_struct_0(B_5128)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_5128,C_5129)) = C_5130
      | ~ r4_lattice3('#skF_5',C_5130,a_2_1_lattice3(B_5128,C_5129))
      | ~ m1_subset_1(C_5130,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_68652])).

tff(c_72277,plain,(
    ! [B_5128,C_5129,C_57] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3(B_5128,C_5129),C_57))
      | ~ r3_lattice3(B_5128,'#skF_6',C_5129)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_5128))
      | ~ l3_lattices(B_5128)
      | v2_struct_0(B_5128)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_5128,C_5129)) = C_57
      | ~ r4_lattice3('#skF_5',C_57,a_2_1_lattice3(B_5128,C_5129))
      | ~ m1_subset_1(C_57,u1_struct_0('#skF_5'))
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_72273])).

tff(c_72280,plain,(
    ! [B_5128,C_5129,C_57] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3(B_5128,C_5129),C_57))
      | ~ r3_lattice3(B_5128,'#skF_6',C_5129)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_5128))
      | ~ l3_lattices(B_5128)
      | v2_struct_0(B_5128)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_5128,C_5129)) = C_57
      | ~ r4_lattice3('#skF_5',C_57,a_2_1_lattice3(B_5128,C_5129))
      | ~ m1_subset_1(C_57,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_60,c_72277])).

tff(c_72282,plain,(
    ! [B_5131,C_5132,C_5133] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3(B_5131,C_5132),C_5133))
      | ~ r3_lattice3(B_5131,'#skF_6',C_5132)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_5131))
      | ~ l3_lattices(B_5131)
      | v2_struct_0(B_5131)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_5131,C_5132)) = C_5133
      | ~ r4_lattice3('#skF_5',C_5133,a_2_1_lattice3(B_5131,C_5132))
      | ~ m1_subset_1(C_5133,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_72280])).

tff(c_72286,plain,(
    ! [B_5131,C_5132] :
      ( ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r3_lattice3(B_5131,'#skF_6',C_5132)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_5131))
      | ~ l3_lattices(B_5131)
      | v2_struct_0(B_5131)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_5131,C_5132)) = '#skF_6'
      | ~ r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3(B_5131,C_5132))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_72282,c_36])).

tff(c_72289,plain,(
    ! [B_5131,C_5132] :
      ( v2_struct_0('#skF_5')
      | ~ r3_lattice3(B_5131,'#skF_6',C_5132)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_5131))
      | ~ l3_lattices(B_5131)
      | v2_struct_0(B_5131)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_5131,C_5132)) = '#skF_6'
      | ~ r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3(B_5131,C_5132)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_62,c_60,c_72286])).

tff(c_72291,plain,(
    ! [B_5134,C_5135] :
      ( ~ r3_lattice3(B_5134,'#skF_6',C_5135)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_5134))
      | ~ l3_lattices(B_5134)
      | v2_struct_0(B_5134)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_5134,C_5135)) = '#skF_6'
      | ~ r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3(B_5134,C_5135)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_72289])).

tff(c_72297,plain,
    ( ~ r3_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_7')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_68351,c_72291])).

tff(c_72304,plain,
    ( v2_struct_0('#skF_5')
    | k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_67633,c_72297])).

tff(c_72305,plain,(
    k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_7')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_72304])).

tff(c_72331,plain,
    ( k16_lattice3('#skF_5','#skF_7') = '#skF_6'
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_72305,c_46])).

tff(c_72361,plain,
    ( k16_lattice3('#skF_5','#skF_7') = '#skF_6'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_72331])).

tff(c_72363,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_67635,c_72361])).

tff(c_72364,plain,(
    k16_lattice3('#skF_5','#skF_8') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_72366,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67634,c_72364])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:27:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.65/13.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.97/13.15  
% 23.97/13.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.97/13.15  %$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_1_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3
% 23.97/13.15  
% 23.97/13.15  %Foreground sorts:
% 23.97/13.15  
% 23.97/13.15  
% 23.97/13.15  %Background operators:
% 23.97/13.15  
% 23.97/13.15  
% 23.97/13.15  %Foreground operators:
% 23.97/13.15  tff(l3_lattices, type, l3_lattices: $i > $o).
% 23.97/13.15  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 23.97/13.15  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 23.97/13.15  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 23.97/13.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.97/13.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 23.97/13.15  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 23.97/13.15  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 23.97/13.15  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 23.97/13.15  tff('#skF_7', type, '#skF_7': $i).
% 23.97/13.15  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 23.97/13.15  tff('#skF_5', type, '#skF_5': $i).
% 23.97/13.15  tff(v4_lattices, type, v4_lattices: $i > $o).
% 23.97/13.15  tff('#skF_6', type, '#skF_6': $i).
% 23.97/13.15  tff(v6_lattices, type, v6_lattices: $i > $o).
% 23.97/13.15  tff(v9_lattices, type, v9_lattices: $i > $o).
% 23.97/13.15  tff(a_2_1_lattice3, type, a_2_1_lattice3: ($i * $i) > $i).
% 23.97/13.15  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 23.97/13.15  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 23.97/13.15  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 23.97/13.15  tff(v5_lattices, type, v5_lattices: $i > $o).
% 23.97/13.15  tff(v10_lattices, type, v10_lattices: $i > $o).
% 23.97/13.15  tff('#skF_9', type, '#skF_9': $i).
% 23.97/13.15  tff('#skF_8', type, '#skF_8': $i).
% 23.97/13.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.97/13.15  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 23.97/13.15  tff(v8_lattices, type, v8_lattices: $i > $o).
% 23.97/13.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.97/13.15  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 23.97/13.15  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 23.97/13.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 23.97/13.15  tff(v7_lattices, type, v7_lattices: $i > $o).
% 23.97/13.15  
% 24.21/13.21  tff(f_177, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((B = k16_lattice3(A, C)) <=> (r3_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_lattice3(A, D, C) => r3_lattices(A, D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_lattice3)).
% 24.21/13.21  tff(f_84, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattice3)).
% 24.21/13.21  tff(f_102, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 24.21/13.21  tff(f_152, axiom, (![A, B, C]: ((~v2_struct_0(B) & l3_lattices(B)) => (r2_hidden(A, a_2_1_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & r3_lattice3(B, D, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_lattice3)).
% 24.21/13.21  tff(f_138, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (k16_lattice3(A, B) = k15_lattice3(A, a_2_1_lattice3(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d22_lattice3)).
% 24.21/13.21  tff(f_130, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k15_lattice3(A, B)) <=> (r4_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d21_lattice3)).
% 24.21/13.21  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 24.21/13.21  tff(f_66, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 24.21/13.21  tff(c_64, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_177])).
% 24.21/13.21  tff(c_82, plain, (r3_lattice3('#skF_5', '#skF_6', '#skF_7') | m1_subset_1('#skF_9', u1_struct_0('#skF_5')) | ~r3_lattice3('#skF_5', '#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_177])).
% 24.21/13.21  tff(c_101, plain, (~r3_lattice3('#skF_5', '#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_82])).
% 24.21/13.21  tff(c_58, plain, (l3_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_177])).
% 24.21/13.21  tff(c_56, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_177])).
% 24.21/13.21  tff(c_26, plain, (![A_5, B_17, C_23]: (m1_subset_1('#skF_1'(A_5, B_17, C_23), u1_struct_0(A_5)) | r3_lattice3(A_5, B_17, C_23) | ~m1_subset_1(B_17, u1_struct_0(A_5)) | ~l3_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_84])).
% 24.21/13.21  tff(c_32, plain, (![A_27, B_39, C_45]: (r2_hidden('#skF_2'(A_27, B_39, C_45), C_45) | r4_lattice3(A_27, B_39, C_45) | ~m1_subset_1(B_39, u1_struct_0(A_27)) | ~l3_lattices(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_102])).
% 24.21/13.21  tff(c_124, plain, (![A_112, B_113, C_114]: (r2_hidden('#skF_2'(A_112, B_113, C_114), C_114) | r4_lattice3(A_112, B_113, C_114) | ~m1_subset_1(B_113, u1_struct_0(A_112)) | ~l3_lattices(A_112) | v2_struct_0(A_112))), inference(cnfTransformation, [status(thm)], [f_102])).
% 24.21/13.21  tff(c_52, plain, (![A_64, B_65, C_66]: ('#skF_4'(A_64, B_65, C_66)=A_64 | ~r2_hidden(A_64, a_2_1_lattice3(B_65, C_66)) | ~l3_lattices(B_65) | v2_struct_0(B_65))), inference(cnfTransformation, [status(thm)], [f_152])).
% 24.21/13.21  tff(c_1113, plain, (![A_348, B_349, B_350, C_351]: ('#skF_4'('#skF_2'(A_348, B_349, a_2_1_lattice3(B_350, C_351)), B_350, C_351)='#skF_2'(A_348, B_349, a_2_1_lattice3(B_350, C_351)) | ~l3_lattices(B_350) | v2_struct_0(B_350) | r4_lattice3(A_348, B_349, a_2_1_lattice3(B_350, C_351)) | ~m1_subset_1(B_349, u1_struct_0(A_348)) | ~l3_lattices(A_348) | v2_struct_0(A_348))), inference(resolution, [status(thm)], [c_124, c_52])).
% 24.21/13.21  tff(c_54, plain, (![A_64, B_65, C_66]: (m1_subset_1('#skF_4'(A_64, B_65, C_66), u1_struct_0(B_65)) | ~r2_hidden(A_64, a_2_1_lattice3(B_65, C_66)) | ~l3_lattices(B_65) | v2_struct_0(B_65))), inference(cnfTransformation, [status(thm)], [f_152])).
% 24.21/13.21  tff(c_2034, plain, (![A_480, B_481, B_482, C_483]: (m1_subset_1('#skF_2'(A_480, B_481, a_2_1_lattice3(B_482, C_483)), u1_struct_0(B_482)) | ~r2_hidden('#skF_2'(A_480, B_481, a_2_1_lattice3(B_482, C_483)), a_2_1_lattice3(B_482, C_483)) | ~l3_lattices(B_482) | v2_struct_0(B_482) | ~l3_lattices(B_482) | v2_struct_0(B_482) | r4_lattice3(A_480, B_481, a_2_1_lattice3(B_482, C_483)) | ~m1_subset_1(B_481, u1_struct_0(A_480)) | ~l3_lattices(A_480) | v2_struct_0(A_480))), inference(superposition, [status(thm), theory('equality')], [c_1113, c_54])).
% 24.21/13.21  tff(c_2043, plain, (![A_27, B_39, B_482, C_483]: (m1_subset_1('#skF_2'(A_27, B_39, a_2_1_lattice3(B_482, C_483)), u1_struct_0(B_482)) | ~l3_lattices(B_482) | v2_struct_0(B_482) | r4_lattice3(A_27, B_39, a_2_1_lattice3(B_482, C_483)) | ~m1_subset_1(B_39, u1_struct_0(A_27)) | ~l3_lattices(A_27) | v2_struct_0(A_27))), inference(resolution, [status(thm)], [c_32, c_2034])).
% 24.21/13.21  tff(c_50, plain, (![B_65, A_64, C_66]: (r3_lattice3(B_65, '#skF_4'(A_64, B_65, C_66), C_66) | ~r2_hidden(A_64, a_2_1_lattice3(B_65, C_66)) | ~l3_lattices(B_65) | v2_struct_0(B_65))), inference(cnfTransformation, [status(thm)], [f_152])).
% 24.21/13.21  tff(c_1805, plain, (![B_466, A_467, B_468, C_469]: (r3_lattice3(B_466, '#skF_2'(A_467, B_468, a_2_1_lattice3(B_466, C_469)), C_469) | ~r2_hidden('#skF_2'(A_467, B_468, a_2_1_lattice3(B_466, C_469)), a_2_1_lattice3(B_466, C_469)) | ~l3_lattices(B_466) | v2_struct_0(B_466) | ~l3_lattices(B_466) | v2_struct_0(B_466) | r4_lattice3(A_467, B_468, a_2_1_lattice3(B_466, C_469)) | ~m1_subset_1(B_468, u1_struct_0(A_467)) | ~l3_lattices(A_467) | v2_struct_0(A_467))), inference(superposition, [status(thm), theory('equality')], [c_1113, c_50])).
% 24.21/13.21  tff(c_1814, plain, (![B_466, A_27, B_39, C_469]: (r3_lattice3(B_466, '#skF_2'(A_27, B_39, a_2_1_lattice3(B_466, C_469)), C_469) | ~l3_lattices(B_466) | v2_struct_0(B_466) | r4_lattice3(A_27, B_39, a_2_1_lattice3(B_466, C_469)) | ~m1_subset_1(B_39, u1_struct_0(A_27)) | ~l3_lattices(A_27) | v2_struct_0(A_27))), inference(resolution, [status(thm)], [c_32, c_1805])).
% 24.21/13.21  tff(c_24, plain, (![A_5, B_17, C_23]: (r2_hidden('#skF_1'(A_5, B_17, C_23), C_23) | r3_lattice3(A_5, B_17, C_23) | ~m1_subset_1(B_17, u1_struct_0(A_5)) | ~l3_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_84])).
% 24.21/13.21  tff(c_153, plain, (![A_136, B_137, D_138, C_139]: (r1_lattices(A_136, B_137, D_138) | ~r2_hidden(D_138, C_139) | ~m1_subset_1(D_138, u1_struct_0(A_136)) | ~r3_lattice3(A_136, B_137, C_139) | ~m1_subset_1(B_137, u1_struct_0(A_136)) | ~l3_lattices(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_84])).
% 24.21/13.21  tff(c_1605, plain, (![C_432, B_435, B_433, A_436, A_434]: (r1_lattices(A_436, B_435, '#skF_1'(A_434, B_433, C_432)) | ~m1_subset_1('#skF_1'(A_434, B_433, C_432), u1_struct_0(A_436)) | ~r3_lattice3(A_436, B_435, C_432) | ~m1_subset_1(B_435, u1_struct_0(A_436)) | ~l3_lattices(A_436) | v2_struct_0(A_436) | r3_lattice3(A_434, B_433, C_432) | ~m1_subset_1(B_433, u1_struct_0(A_434)) | ~l3_lattices(A_434) | v2_struct_0(A_434))), inference(resolution, [status(thm)], [c_24, c_153])).
% 24.21/13.21  tff(c_1609, plain, (![A_437, B_438, B_439, C_440]: (r1_lattices(A_437, B_438, '#skF_1'(A_437, B_439, C_440)) | ~r3_lattice3(A_437, B_438, C_440) | ~m1_subset_1(B_438, u1_struct_0(A_437)) | r3_lattice3(A_437, B_439, C_440) | ~m1_subset_1(B_439, u1_struct_0(A_437)) | ~l3_lattices(A_437) | v2_struct_0(A_437))), inference(resolution, [status(thm)], [c_26, c_1605])).
% 24.21/13.21  tff(c_30, plain, (![A_27, B_39, C_45]: (~r1_lattices(A_27, '#skF_2'(A_27, B_39, C_45), B_39) | r4_lattice3(A_27, B_39, C_45) | ~m1_subset_1(B_39, u1_struct_0(A_27)) | ~l3_lattices(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_102])).
% 24.21/13.21  tff(c_6413, plain, (![A_758, B_759, C_760, C_761]: (r4_lattice3(A_758, '#skF_1'(A_758, B_759, C_760), C_761) | ~m1_subset_1('#skF_1'(A_758, B_759, C_760), u1_struct_0(A_758)) | ~r3_lattice3(A_758, '#skF_2'(A_758, '#skF_1'(A_758, B_759, C_760), C_761), C_760) | ~m1_subset_1('#skF_2'(A_758, '#skF_1'(A_758, B_759, C_760), C_761), u1_struct_0(A_758)) | r3_lattice3(A_758, B_759, C_760) | ~m1_subset_1(B_759, u1_struct_0(A_758)) | ~l3_lattices(A_758) | v2_struct_0(A_758))), inference(resolution, [status(thm)], [c_1609, c_30])).
% 24.21/13.21  tff(c_11538, plain, (![A_1062, B_1063, C_1064]: (~m1_subset_1('#skF_2'(A_1062, '#skF_1'(A_1062, B_1063, C_1064), a_2_1_lattice3(A_1062, C_1064)), u1_struct_0(A_1062)) | r3_lattice3(A_1062, B_1063, C_1064) | ~m1_subset_1(B_1063, u1_struct_0(A_1062)) | r4_lattice3(A_1062, '#skF_1'(A_1062, B_1063, C_1064), a_2_1_lattice3(A_1062, C_1064)) | ~m1_subset_1('#skF_1'(A_1062, B_1063, C_1064), u1_struct_0(A_1062)) | ~l3_lattices(A_1062) | v2_struct_0(A_1062))), inference(resolution, [status(thm)], [c_1814, c_6413])).
% 24.21/13.21  tff(c_11549, plain, (![B_1065, B_1066, C_1067]: (r3_lattice3(B_1065, B_1066, C_1067) | ~m1_subset_1(B_1066, u1_struct_0(B_1065)) | r4_lattice3(B_1065, '#skF_1'(B_1065, B_1066, C_1067), a_2_1_lattice3(B_1065, C_1067)) | ~m1_subset_1('#skF_1'(B_1065, B_1066, C_1067), u1_struct_0(B_1065)) | ~l3_lattices(B_1065) | v2_struct_0(B_1065))), inference(resolution, [status(thm)], [c_2043, c_11538])).
% 24.21/13.21  tff(c_62, plain, (v10_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_177])).
% 24.21/13.21  tff(c_60, plain, (v4_lattice3('#skF_5')), inference(cnfTransformation, [status(thm)], [f_177])).
% 24.21/13.21  tff(c_88, plain, (r3_lattice3('#skF_5', '#skF_6', '#skF_7') | k16_lattice3('#skF_5', '#skF_8')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_177])).
% 24.21/13.21  tff(c_90, plain, (k16_lattice3('#skF_5', '#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_88])).
% 24.21/13.21  tff(c_46, plain, (![A_61, B_63]: (k15_lattice3(A_61, a_2_1_lattice3(A_61, B_63))=k16_lattice3(A_61, B_63) | ~l3_lattices(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_138])).
% 24.21/13.21  tff(c_140, plain, (![A_130, B_131]: (r4_lattice3(A_130, k15_lattice3(A_130, B_131), B_131) | ~m1_subset_1(k15_lattice3(A_130, B_131), u1_struct_0(A_130)) | ~v4_lattice3(A_130) | ~v10_lattices(A_130) | ~l3_lattices(A_130) | v2_struct_0(A_130))), inference(cnfTransformation, [status(thm)], [f_130])).
% 24.21/13.21  tff(c_1079, plain, (![A_338, B_339]: (r4_lattice3(A_338, k15_lattice3(A_338, a_2_1_lattice3(A_338, B_339)), a_2_1_lattice3(A_338, B_339)) | ~m1_subset_1(k16_lattice3(A_338, B_339), u1_struct_0(A_338)) | ~v4_lattice3(A_338) | ~v10_lattices(A_338) | ~l3_lattices(A_338) | v2_struct_0(A_338) | ~l3_lattices(A_338) | v2_struct_0(A_338))), inference(superposition, [status(thm), theory('equality')], [c_46, c_140])).
% 24.21/13.21  tff(c_1087, plain, (![A_341, B_342]: (r4_lattice3(A_341, k16_lattice3(A_341, B_342), a_2_1_lattice3(A_341, B_342)) | ~m1_subset_1(k16_lattice3(A_341, B_342), u1_struct_0(A_341)) | ~v4_lattice3(A_341) | ~v10_lattices(A_341) | ~l3_lattices(A_341) | v2_struct_0(A_341) | ~l3_lattices(A_341) | v2_struct_0(A_341) | ~l3_lattices(A_341) | v2_struct_0(A_341))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1079])).
% 24.21/13.21  tff(c_1090, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_8')) | ~m1_subset_1(k16_lattice3('#skF_5', '#skF_8'), u1_struct_0('#skF_5')) | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_90, c_1087])).
% 24.21/13.21  tff(c_1092, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_8')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_58, c_58, c_62, c_60, c_56, c_90, c_1090])).
% 24.21/13.21  tff(c_1093, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_64, c_1092])).
% 24.21/13.21  tff(c_40, plain, (![A_49, B_56, C_57]: (m1_subset_1('#skF_3'(A_49, B_56, C_57), u1_struct_0(A_49)) | k15_lattice3(A_49, B_56)=C_57 | ~r4_lattice3(A_49, C_57, B_56) | ~m1_subset_1(C_57, u1_struct_0(A_49)) | ~v4_lattice3(A_49) | ~v10_lattices(A_49) | ~l3_lattices(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_130])).
% 24.21/13.21  tff(c_38, plain, (![A_49, B_56, C_57]: (r4_lattice3(A_49, '#skF_3'(A_49, B_56, C_57), B_56) | k15_lattice3(A_49, B_56)=C_57 | ~r4_lattice3(A_49, C_57, B_56) | ~m1_subset_1(C_57, u1_struct_0(A_49)) | ~v4_lattice3(A_49) | ~v10_lattices(A_49) | ~l3_lattices(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_130])).
% 24.21/13.21  tff(c_142, plain, (![A_61, B_63]: (r4_lattice3(A_61, k15_lattice3(A_61, a_2_1_lattice3(A_61, B_63)), a_2_1_lattice3(A_61, B_63)) | ~m1_subset_1(k16_lattice3(A_61, B_63), u1_struct_0(A_61)) | ~v4_lattice3(A_61) | ~v10_lattices(A_61) | ~l3_lattices(A_61) | v2_struct_0(A_61) | ~l3_lattices(A_61) | v2_struct_0(A_61))), inference(superposition, [status(thm), theory('equality')], [c_46, c_140])).
% 24.21/13.21  tff(c_1003, plain, (![A_326, B_327, D_328]: (r1_lattices(A_326, k15_lattice3(A_326, B_327), D_328) | ~r4_lattice3(A_326, D_328, B_327) | ~m1_subset_1(D_328, u1_struct_0(A_326)) | ~m1_subset_1(k15_lattice3(A_326, B_327), u1_struct_0(A_326)) | ~v4_lattice3(A_326) | ~v10_lattices(A_326) | ~l3_lattices(A_326) | v2_struct_0(A_326))), inference(cnfTransformation, [status(thm)], [f_130])).
% 24.21/13.21  tff(c_1342, plain, (![A_391, B_392, D_393]: (r1_lattices(A_391, k15_lattice3(A_391, a_2_1_lattice3(A_391, B_392)), D_393) | ~r4_lattice3(A_391, D_393, a_2_1_lattice3(A_391, B_392)) | ~m1_subset_1(D_393, u1_struct_0(A_391)) | ~m1_subset_1(k16_lattice3(A_391, B_392), u1_struct_0(A_391)) | ~v4_lattice3(A_391) | ~v10_lattices(A_391) | ~l3_lattices(A_391) | v2_struct_0(A_391) | ~l3_lattices(A_391) | v2_struct_0(A_391))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1003])).
% 24.21/13.21  tff(c_1641, plain, (![A_452, B_453, D_454]: (r1_lattices(A_452, k16_lattice3(A_452, B_453), D_454) | ~r4_lattice3(A_452, D_454, a_2_1_lattice3(A_452, B_453)) | ~m1_subset_1(D_454, u1_struct_0(A_452)) | ~m1_subset_1(k16_lattice3(A_452, B_453), u1_struct_0(A_452)) | ~v4_lattice3(A_452) | ~v10_lattices(A_452) | ~l3_lattices(A_452) | v2_struct_0(A_452) | ~l3_lattices(A_452) | v2_struct_0(A_452) | ~l3_lattices(A_452) | v2_struct_0(A_452))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1342])).
% 24.21/13.21  tff(c_1671, plain, (![A_457, B_458]: (r1_lattices(A_457, k16_lattice3(A_457, B_458), k15_lattice3(A_457, a_2_1_lattice3(A_457, B_458))) | ~m1_subset_1(k15_lattice3(A_457, a_2_1_lattice3(A_457, B_458)), u1_struct_0(A_457)) | ~m1_subset_1(k16_lattice3(A_457, B_458), u1_struct_0(A_457)) | ~v4_lattice3(A_457) | ~v10_lattices(A_457) | ~l3_lattices(A_457) | v2_struct_0(A_457))), inference(resolution, [status(thm)], [c_142, c_1641])).
% 24.21/13.21  tff(c_1677, plain, (r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8'))) | ~m1_subset_1(k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8')), u1_struct_0('#skF_5')) | ~m1_subset_1(k16_lattice3('#skF_5', '#skF_8'), u1_struct_0('#skF_5')) | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_90, c_1671])).
% 24.21/13.21  tff(c_1679, plain, (r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8'))) | ~m1_subset_1(k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8')), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_60, c_56, c_90, c_1677])).
% 24.21/13.21  tff(c_1680, plain, (r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8'))) | ~m1_subset_1(k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8')), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_1679])).
% 24.21/13.21  tff(c_1685, plain, (~m1_subset_1(k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8')), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_1680])).
% 24.21/13.21  tff(c_1688, plain, (~m1_subset_1(k16_lattice3('#skF_5', '#skF_8'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_46, c_1685])).
% 24.21/13.21  tff(c_1690, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_90, c_1688])).
% 24.21/13.21  tff(c_1692, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_1690])).
% 24.21/13.21  tff(c_1694, plain, (m1_subset_1(k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8')), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_1680])).
% 24.21/13.21  tff(c_42, plain, (![A_49, B_56, D_60]: (r1_lattices(A_49, k15_lattice3(A_49, B_56), D_60) | ~r4_lattice3(A_49, D_60, B_56) | ~m1_subset_1(D_60, u1_struct_0(A_49)) | ~m1_subset_1(k15_lattice3(A_49, B_56), u1_struct_0(A_49)) | ~v4_lattice3(A_49) | ~v10_lattices(A_49) | ~l3_lattices(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_130])).
% 24.21/13.21  tff(c_1721, plain, (![D_60]: (r1_lattices('#skF_5', k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8')), D_60) | ~r4_lattice3('#skF_5', D_60, a_2_1_lattice3('#skF_5', '#skF_8')) | ~m1_subset_1(D_60, u1_struct_0('#skF_5')) | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_1694, c_42])).
% 24.21/13.21  tff(c_1746, plain, (![D_60]: (r1_lattices('#skF_5', k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8')), D_60) | ~r4_lattice3('#skF_5', D_60, a_2_1_lattice3('#skF_5', '#skF_8')) | ~m1_subset_1(D_60, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_60, c_1721])).
% 24.21/13.21  tff(c_1823, plain, (![D_470]: (r1_lattices('#skF_5', k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8')), D_470) | ~r4_lattice3('#skF_5', D_470, a_2_1_lattice3('#skF_5', '#skF_8')) | ~m1_subset_1(D_470, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_1746])).
% 24.21/13.21  tff(c_1838, plain, (![D_470]: (r1_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_8'), D_470) | ~r4_lattice3('#skF_5', D_470, a_2_1_lattice3('#skF_5', '#skF_8')) | ~m1_subset_1(D_470, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1823])).
% 24.21/13.21  tff(c_1851, plain, (![D_470]: (r1_lattices('#skF_5', '#skF_6', D_470) | ~r4_lattice3('#skF_5', D_470, a_2_1_lattice3('#skF_5', '#skF_8')) | ~m1_subset_1(D_470, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_90, c_1838])).
% 24.21/13.21  tff(c_1853, plain, (![D_471]: (r1_lattices('#skF_5', '#skF_6', D_471) | ~r4_lattice3('#skF_5', D_471, a_2_1_lattice3('#skF_5', '#skF_8')) | ~m1_subset_1(D_471, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_1851])).
% 24.21/13.21  tff(c_1871, plain, (![C_57]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8'), C_57)) | ~m1_subset_1('#skF_3'('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8'), C_57), u1_struct_0('#skF_5')) | k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8'))=C_57 | ~r4_lattice3('#skF_5', C_57, a_2_1_lattice3('#skF_5', '#skF_8')) | ~m1_subset_1(C_57, u1_struct_0('#skF_5')) | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_1853])).
% 24.21/13.21  tff(c_1888, plain, (![C_57]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8'), C_57)) | ~m1_subset_1('#skF_3'('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8'), C_57), u1_struct_0('#skF_5')) | k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8'))=C_57 | ~r4_lattice3('#skF_5', C_57, a_2_1_lattice3('#skF_5', '#skF_8')) | ~m1_subset_1(C_57, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_60, c_1871])).
% 24.21/13.21  tff(c_7246, plain, (![C_813]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8'), C_813)) | ~m1_subset_1('#skF_3'('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8'), C_813), u1_struct_0('#skF_5')) | k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8'))=C_813 | ~r4_lattice3('#skF_5', C_813, a_2_1_lattice3('#skF_5', '#skF_8')) | ~m1_subset_1(C_813, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_1888])).
% 24.21/13.21  tff(c_7250, plain, (![C_57]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8'), C_57)) | k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8'))=C_57 | ~r4_lattice3('#skF_5', C_57, a_2_1_lattice3('#skF_5', '#skF_8')) | ~m1_subset_1(C_57, u1_struct_0('#skF_5')) | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_7246])).
% 24.21/13.21  tff(c_7253, plain, (![C_57]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8'), C_57)) | k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8'))=C_57 | ~r4_lattice3('#skF_5', C_57, a_2_1_lattice3('#skF_5', '#skF_8')) | ~m1_subset_1(C_57, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_60, c_7250])).
% 24.21/13.21  tff(c_7255, plain, (![C_814]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8'), C_814)) | k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8'))=C_814 | ~r4_lattice3('#skF_5', C_814, a_2_1_lattice3('#skF_5', '#skF_8')) | ~m1_subset_1(C_814, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_7253])).
% 24.21/13.21  tff(c_36, plain, (![A_49, C_57, B_56]: (~r1_lattices(A_49, C_57, '#skF_3'(A_49, B_56, C_57)) | k15_lattice3(A_49, B_56)=C_57 | ~r4_lattice3(A_49, C_57, B_56) | ~m1_subset_1(C_57, u1_struct_0(A_49)) | ~v4_lattice3(A_49) | ~v10_lattices(A_49) | ~l3_lattices(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_130])).
% 24.21/13.21  tff(c_7259, plain, (~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8'))='#skF_6' | ~r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_8')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_7255, c_36])).
% 24.21/13.21  tff(c_7262, plain, (v2_struct_0('#skF_5') | k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1093, c_58, c_62, c_60, c_7259])).
% 24.21/13.21  tff(c_7263, plain, (k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_64, c_7262])).
% 24.21/13.21  tff(c_22, plain, (![A_5, B_17, C_23]: (~r1_lattices(A_5, B_17, '#skF_1'(A_5, B_17, C_23)) | r3_lattice3(A_5, B_17, C_23) | ~m1_subset_1(B_17, u1_struct_0(A_5)) | ~l3_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_84])).
% 24.21/13.21  tff(c_1835, plain, (![C_23]: (r3_lattice3('#skF_5', k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8')), C_23) | ~m1_subset_1(k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8')), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r4_lattice3('#skF_5', '#skF_1'('#skF_5', k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8')), C_23), a_2_1_lattice3('#skF_5', '#skF_8')) | ~m1_subset_1('#skF_1'('#skF_5', k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8')), C_23), u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_1823, c_22])).
% 24.21/13.21  tff(c_1848, plain, (![C_23]: (r3_lattice3('#skF_5', k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8')), C_23) | v2_struct_0('#skF_5') | ~r4_lattice3('#skF_5', '#skF_1'('#skF_5', k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8')), C_23), a_2_1_lattice3('#skF_5', '#skF_8')) | ~m1_subset_1('#skF_1'('#skF_5', k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8')), C_23), u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1694, c_1835])).
% 24.21/13.21  tff(c_5682, plain, (![C_685]: (r3_lattice3('#skF_5', k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8')), C_685) | ~r4_lattice3('#skF_5', '#skF_1'('#skF_5', k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8')), C_685), a_2_1_lattice3('#skF_5', '#skF_8')) | ~m1_subset_1('#skF_1'('#skF_5', k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8')), C_685), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_1848])).
% 24.21/13.21  tff(c_5685, plain, (![C_685]: (r3_lattice3('#skF_5', k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8')), C_685) | ~r4_lattice3('#skF_5', '#skF_1'('#skF_5', k16_lattice3('#skF_5', '#skF_8'), C_685), a_2_1_lattice3('#skF_5', '#skF_8')) | ~m1_subset_1('#skF_1'('#skF_5', k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8')), C_685), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_5682])).
% 24.21/13.21  tff(c_5687, plain, (![C_685]: (r3_lattice3('#skF_5', k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8')), C_685) | ~r4_lattice3('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_685), a_2_1_lattice3('#skF_5', '#skF_8')) | ~m1_subset_1('#skF_1'('#skF_5', k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8')), C_685), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_90, c_5685])).
% 24.21/13.21  tff(c_5689, plain, (![C_686]: (r3_lattice3('#skF_5', k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8')), C_686) | ~r4_lattice3('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_686), a_2_1_lattice3('#skF_5', '#skF_8')) | ~m1_subset_1('#skF_1'('#skF_5', k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8')), C_686), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_5687])).
% 24.21/13.21  tff(c_5697, plain, (![C_23]: (~r4_lattice3('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_23), a_2_1_lattice3('#skF_5', '#skF_8')) | r3_lattice3('#skF_5', k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8')), C_23) | ~m1_subset_1(k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8')), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_26, c_5689])).
% 24.21/13.21  tff(c_5707, plain, (![C_23]: (~r4_lattice3('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_23), a_2_1_lattice3('#skF_5', '#skF_8')) | r3_lattice3('#skF_5', k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8')), C_23) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1694, c_5697])).
% 24.21/13.21  tff(c_5708, plain, (![C_23]: (~r4_lattice3('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_23), a_2_1_lattice3('#skF_5', '#skF_8')) | r3_lattice3('#skF_5', k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_8')), C_23))), inference(negUnitSimplification, [status(thm)], [c_64, c_5707])).
% 24.21/13.21  tff(c_7283, plain, (![C_23]: (~r4_lattice3('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_23), a_2_1_lattice3('#skF_5', '#skF_8')) | r3_lattice3('#skF_5', '#skF_6', C_23))), inference(demodulation, [status(thm), theory('equality')], [c_7263, c_5708])).
% 24.21/13.21  tff(c_11559, plain, (r3_lattice3('#skF_5', '#skF_6', '#skF_8') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_1'('#skF_5', '#skF_6', '#skF_8'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_11549, c_7283])).
% 24.21/13.21  tff(c_11595, plain, (r3_lattice3('#skF_5', '#skF_6', '#skF_8') | ~m1_subset_1('#skF_1'('#skF_5', '#skF_6', '#skF_8'), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_11559])).
% 24.21/13.21  tff(c_11596, plain, (~m1_subset_1('#skF_1'('#skF_5', '#skF_6', '#skF_8'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_101, c_11595])).
% 24.21/13.21  tff(c_11615, plain, (r3_lattice3('#skF_5', '#skF_6', '#skF_8') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_26, c_11596])).
% 24.21/13.21  tff(c_11618, plain, (r3_lattice3('#skF_5', '#skF_6', '#skF_8') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_11615])).
% 24.21/13.21  tff(c_11620, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_101, c_11618])).
% 24.21/13.21  tff(c_11622, plain, (r3_lattice3('#skF_5', '#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_82])).
% 24.21/13.21  tff(c_72, plain, (k16_lattice3('#skF_5', '#skF_7')!='#skF_6' | r3_lattice3('#skF_5', '#skF_9', '#skF_8') | ~r3_lattice3('#skF_5', '#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_177])).
% 24.21/13.21  tff(c_11625, plain, (k16_lattice3('#skF_5', '#skF_7')!='#skF_6' | r3_lattice3('#skF_5', '#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_11622, c_72])).
% 24.21/13.21  tff(c_11626, plain, (k16_lattice3('#skF_5', '#skF_7')!='#skF_6'), inference(splitLeft, [status(thm)], [c_11625])).
% 24.21/13.21  tff(c_11621, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_5')) | r3_lattice3('#skF_5', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_82])).
% 24.21/13.21  tff(c_11623, plain, (r3_lattice3('#skF_5', '#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_11621])).
% 24.21/13.21  tff(c_46307, plain, (![A_3116, B_3117, C_3118]: (r2_hidden('#skF_2'(A_3116, B_3117, C_3118), C_3118) | r4_lattice3(A_3116, B_3117, C_3118) | ~m1_subset_1(B_3117, u1_struct_0(A_3116)) | ~l3_lattices(A_3116) | v2_struct_0(A_3116))), inference(cnfTransformation, [status(thm)], [f_102])).
% 24.21/13.21  tff(c_47248, plain, (![A_3241, B_3242, B_3243, C_3244]: ('#skF_4'('#skF_2'(A_3241, B_3242, a_2_1_lattice3(B_3243, C_3244)), B_3243, C_3244)='#skF_2'(A_3241, B_3242, a_2_1_lattice3(B_3243, C_3244)) | ~l3_lattices(B_3243) | v2_struct_0(B_3243) | r4_lattice3(A_3241, B_3242, a_2_1_lattice3(B_3243, C_3244)) | ~m1_subset_1(B_3242, u1_struct_0(A_3241)) | ~l3_lattices(A_3241) | v2_struct_0(A_3241))), inference(resolution, [status(thm)], [c_46307, c_52])).
% 24.21/13.21  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 24.21/13.21  tff(c_80, plain, (![D_87]: (r3_lattices('#skF_5', D_87, '#skF_6') | ~r3_lattice3('#skF_5', D_87, '#skF_7') | ~m1_subset_1(D_87, u1_struct_0('#skF_5')) | m1_subset_1('#skF_9', u1_struct_0('#skF_5')) | ~r3_lattice3('#skF_5', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_177])).
% 24.21/13.21  tff(c_46314, plain, (![D_87]: (r3_lattices('#skF_5', D_87, '#skF_6') | ~r3_lattice3('#skF_5', D_87, '#skF_7') | ~m1_subset_1(D_87, u1_struct_0('#skF_5')) | m1_subset_1('#skF_9', u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_11622, c_80])).
% 24.21/13.21  tff(c_46315, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_46314])).
% 24.21/13.21  tff(c_30661, plain, (![A_2272, B_2273, C_2274]: (r2_hidden('#skF_2'(A_2272, B_2273, C_2274), C_2274) | r4_lattice3(A_2272, B_2273, C_2274) | ~m1_subset_1(B_2273, u1_struct_0(A_2272)) | ~l3_lattices(A_2272) | v2_struct_0(A_2272))), inference(cnfTransformation, [status(thm)], [f_102])).
% 24.21/13.21  tff(c_30666, plain, (![A_2272, B_2273, B_65, C_66]: ('#skF_4'('#skF_2'(A_2272, B_2273, a_2_1_lattice3(B_65, C_66)), B_65, C_66)='#skF_2'(A_2272, B_2273, a_2_1_lattice3(B_65, C_66)) | ~l3_lattices(B_65) | v2_struct_0(B_65) | r4_lattice3(A_2272, B_2273, a_2_1_lattice3(B_65, C_66)) | ~m1_subset_1(B_2273, u1_struct_0(A_2272)) | ~l3_lattices(A_2272) | v2_struct_0(A_2272))), inference(resolution, [status(thm)], [c_30661, c_52])).
% 24.21/13.21  tff(c_11711, plain, (![A_1088, B_1089, C_1090]: (r2_hidden('#skF_2'(A_1088, B_1089, C_1090), C_1090) | r4_lattice3(A_1088, B_1089, C_1090) | ~m1_subset_1(B_1089, u1_struct_0(A_1088)) | ~l3_lattices(A_1088) | v2_struct_0(A_1088))), inference(cnfTransformation, [status(thm)], [f_102])).
% 24.21/13.21  tff(c_14233, plain, (![A_1414, B_1415, B_1416, C_1417]: ('#skF_4'('#skF_2'(A_1414, B_1415, a_2_1_lattice3(B_1416, C_1417)), B_1416, C_1417)='#skF_2'(A_1414, B_1415, a_2_1_lattice3(B_1416, C_1417)) | ~l3_lattices(B_1416) | v2_struct_0(B_1416) | r4_lattice3(A_1414, B_1415, a_2_1_lattice3(B_1416, C_1417)) | ~m1_subset_1(B_1415, u1_struct_0(A_1414)) | ~l3_lattices(A_1414) | v2_struct_0(A_1414))), inference(resolution, [status(thm)], [c_11711, c_52])).
% 24.21/13.21  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 24.21/13.21  tff(c_13545, plain, (![A_1337, B_1338, C_1339]: (r3_lattices(A_1337, B_1338, C_1339) | ~r1_lattices(A_1337, B_1338, C_1339) | ~m1_subset_1(C_1339, u1_struct_0(A_1337)) | ~m1_subset_1(B_1338, u1_struct_0(A_1337)) | ~l3_lattices(A_1337) | ~v9_lattices(A_1337) | ~v8_lattices(A_1337) | ~v6_lattices(A_1337) | v2_struct_0(A_1337))), inference(cnfTransformation, [status(thm)], [f_66])).
% 24.21/13.21  tff(c_13555, plain, (![B_1338]: (r3_lattices('#skF_5', B_1338, '#skF_6') | ~r1_lattices('#skF_5', B_1338, '#skF_6') | ~m1_subset_1(B_1338, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_13545])).
% 24.21/13.21  tff(c_13565, plain, (![B_1338]: (r3_lattices('#skF_5', B_1338, '#skF_6') | ~r1_lattices('#skF_5', B_1338, '#skF_6') | ~m1_subset_1(B_1338, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_13555])).
% 24.21/13.21  tff(c_13566, plain, (![B_1338]: (r3_lattices('#skF_5', B_1338, '#skF_6') | ~r1_lattices('#skF_5', B_1338, '#skF_6') | ~m1_subset_1(B_1338, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_13565])).
% 24.21/13.21  tff(c_13567, plain, (~v6_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_13566])).
% 24.21/13.21  tff(c_13570, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_8, c_13567])).
% 24.21/13.21  tff(c_13573, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_13570])).
% 24.21/13.21  tff(c_13575, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_13573])).
% 24.21/13.21  tff(c_13577, plain, (v6_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_13566])).
% 24.21/13.21  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 24.21/13.21  tff(c_13576, plain, (![B_1338]: (~v8_lattices('#skF_5') | ~v9_lattices('#skF_5') | r3_lattices('#skF_5', B_1338, '#skF_6') | ~r1_lattices('#skF_5', B_1338, '#skF_6') | ~m1_subset_1(B_1338, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_13566])).
% 24.21/13.21  tff(c_13578, plain, (~v9_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_13576])).
% 24.21/13.21  tff(c_13581, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_2, c_13578])).
% 24.21/13.21  tff(c_13584, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_13581])).
% 24.21/13.21  tff(c_13586, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_13584])).
% 24.21/13.21  tff(c_13588, plain, (v9_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_13576])).
% 24.21/13.21  tff(c_66, plain, (k16_lattice3('#skF_5', '#skF_7')!='#skF_6' | ~r3_lattices('#skF_5', '#skF_9', '#skF_6') | ~r3_lattice3('#skF_5', '#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_177])).
% 24.21/13.21  tff(c_11628, plain, (k16_lattice3('#skF_5', '#skF_7')!='#skF_6' | ~r3_lattices('#skF_5', '#skF_9', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11622, c_66])).
% 24.21/13.21  tff(c_11629, plain, (~r3_lattices('#skF_5', '#skF_9', '#skF_6')), inference(splitLeft, [status(thm)], [c_11628])).
% 24.21/13.21  tff(c_11649, plain, (![D_87]: (r3_lattices('#skF_5', D_87, '#skF_6') | ~r3_lattice3('#skF_5', D_87, '#skF_7') | ~m1_subset_1(D_87, u1_struct_0('#skF_5')) | m1_subset_1('#skF_9', u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_11622, c_80])).
% 24.21/13.21  tff(c_11650, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_11649])).
% 24.21/13.21  tff(c_11772, plain, (![A_1116, B_1117, C_1118]: (r3_lattices(A_1116, B_1117, C_1118) | ~r1_lattices(A_1116, B_1117, C_1118) | ~m1_subset_1(C_1118, u1_struct_0(A_1116)) | ~m1_subset_1(B_1117, u1_struct_0(A_1116)) | ~l3_lattices(A_1116) | ~v9_lattices(A_1116) | ~v8_lattices(A_1116) | ~v6_lattices(A_1116) | v2_struct_0(A_1116))), inference(cnfTransformation, [status(thm)], [f_66])).
% 24.21/13.21  tff(c_11782, plain, (![B_1117]: (r3_lattices('#skF_5', B_1117, '#skF_6') | ~r1_lattices('#skF_5', B_1117, '#skF_6') | ~m1_subset_1(B_1117, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_11772])).
% 24.21/13.21  tff(c_11792, plain, (![B_1117]: (r3_lattices('#skF_5', B_1117, '#skF_6') | ~r1_lattices('#skF_5', B_1117, '#skF_6') | ~m1_subset_1(B_1117, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_11782])).
% 24.21/13.21  tff(c_11793, plain, (![B_1117]: (r3_lattices('#skF_5', B_1117, '#skF_6') | ~r1_lattices('#skF_5', B_1117, '#skF_6') | ~m1_subset_1(B_1117, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_11792])).
% 24.21/13.21  tff(c_11794, plain, (~v6_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_11793])).
% 24.21/13.21  tff(c_11797, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_8, c_11794])).
% 24.21/13.21  tff(c_11800, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_11797])).
% 24.21/13.21  tff(c_11802, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_11800])).
% 24.21/13.21  tff(c_11803, plain, (![B_1117]: (~v8_lattices('#skF_5') | ~v9_lattices('#skF_5') | r3_lattices('#skF_5', B_1117, '#skF_6') | ~r1_lattices('#skF_5', B_1117, '#skF_6') | ~m1_subset_1(B_1117, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_11793])).
% 24.21/13.21  tff(c_11805, plain, (~v9_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_11803])).
% 24.21/13.21  tff(c_11809, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_2, c_11805])).
% 24.21/13.21  tff(c_11812, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_11809])).
% 24.21/13.21  tff(c_11814, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_11812])).
% 24.21/13.21  tff(c_11815, plain, (![B_1117]: (~v8_lattices('#skF_5') | r3_lattices('#skF_5', B_1117, '#skF_6') | ~r1_lattices('#skF_5', B_1117, '#skF_6') | ~m1_subset_1(B_1117, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_11803])).
% 24.21/13.21  tff(c_11817, plain, (~v8_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_11815])).
% 24.21/13.21  tff(c_11823, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_4, c_11817])).
% 24.21/13.21  tff(c_11826, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_11823])).
% 24.21/13.21  tff(c_11828, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_11826])).
% 24.21/13.21  tff(c_11831, plain, (![B_1122]: (r3_lattices('#skF_5', B_1122, '#skF_6') | ~r1_lattices('#skF_5', B_1122, '#skF_6') | ~m1_subset_1(B_1122, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_11815])).
% 24.21/13.21  tff(c_11846, plain, (r3_lattices('#skF_5', '#skF_9', '#skF_6') | ~r1_lattices('#skF_5', '#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_11650, c_11831])).
% 24.21/13.21  tff(c_11864, plain, (~r1_lattices('#skF_5', '#skF_9', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_11629, c_11846])).
% 24.21/13.21  tff(c_74, plain, (![D_87]: (r3_lattices('#skF_5', D_87, '#skF_6') | ~r3_lattice3('#skF_5', D_87, '#skF_7') | ~m1_subset_1(D_87, u1_struct_0('#skF_5')) | r3_lattice3('#skF_5', '#skF_9', '#skF_8') | ~r3_lattice3('#skF_5', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_177])).
% 24.21/13.21  tff(c_11727, plain, (![D_87]: (r3_lattices('#skF_5', D_87, '#skF_6') | ~r3_lattice3('#skF_5', D_87, '#skF_7') | ~m1_subset_1(D_87, u1_struct_0('#skF_5')) | r3_lattice3('#skF_5', '#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_11622, c_74])).
% 24.21/13.21  tff(c_11728, plain, (r3_lattice3('#skF_5', '#skF_9', '#skF_8')), inference(splitLeft, [status(thm)], [c_11727])).
% 24.21/13.21  tff(c_11723, plain, (![A_1103, B_1104]: (r4_lattice3(A_1103, k15_lattice3(A_1103, B_1104), B_1104) | ~m1_subset_1(k15_lattice3(A_1103, B_1104), u1_struct_0(A_1103)) | ~v4_lattice3(A_1103) | ~v10_lattices(A_1103) | ~l3_lattices(A_1103) | v2_struct_0(A_1103))), inference(cnfTransformation, [status(thm)], [f_130])).
% 24.21/13.21  tff(c_12996, plain, (![A_1264, B_1265]: (r4_lattice3(A_1264, k15_lattice3(A_1264, a_2_1_lattice3(A_1264, B_1265)), a_2_1_lattice3(A_1264, B_1265)) | ~m1_subset_1(k16_lattice3(A_1264, B_1265), u1_struct_0(A_1264)) | ~v4_lattice3(A_1264) | ~v10_lattices(A_1264) | ~l3_lattices(A_1264) | v2_struct_0(A_1264) | ~l3_lattices(A_1264) | v2_struct_0(A_1264))), inference(superposition, [status(thm), theory('equality')], [c_46, c_11723])).
% 24.21/13.21  tff(c_13084, plain, (![A_1277, B_1278]: (r4_lattice3(A_1277, k16_lattice3(A_1277, B_1278), a_2_1_lattice3(A_1277, B_1278)) | ~m1_subset_1(k16_lattice3(A_1277, B_1278), u1_struct_0(A_1277)) | ~v4_lattice3(A_1277) | ~v10_lattices(A_1277) | ~l3_lattices(A_1277) | v2_struct_0(A_1277) | ~l3_lattices(A_1277) | v2_struct_0(A_1277) | ~l3_lattices(A_1277) | v2_struct_0(A_1277))), inference(superposition, [status(thm), theory('equality')], [c_46, c_12996])).
% 24.21/13.21  tff(c_13087, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_8')) | ~m1_subset_1(k16_lattice3('#skF_5', '#skF_8'), u1_struct_0('#skF_5')) | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_90, c_13084])).
% 24.21/13.21  tff(c_13089, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_8')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_58, c_58, c_62, c_60, c_56, c_90, c_13087])).
% 24.21/13.21  tff(c_13090, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_64, c_13089])).
% 24.21/13.21  tff(c_48, plain, (![D_69, B_65, C_66]: (r2_hidden(D_69, a_2_1_lattice3(B_65, C_66)) | ~r3_lattice3(B_65, D_69, C_66) | ~m1_subset_1(D_69, u1_struct_0(B_65)) | ~l3_lattices(B_65) | v2_struct_0(B_65))), inference(cnfTransformation, [status(thm)], [f_152])).
% 24.21/13.21  tff(c_11761, plain, (![A_1109, D_1110, B_1111, C_1112]: (r1_lattices(A_1109, D_1110, B_1111) | ~r2_hidden(D_1110, C_1112) | ~m1_subset_1(D_1110, u1_struct_0(A_1109)) | ~r4_lattice3(A_1109, B_1111, C_1112) | ~m1_subset_1(B_1111, u1_struct_0(A_1109)) | ~l3_lattices(A_1109) | v2_struct_0(A_1109))), inference(cnfTransformation, [status(thm)], [f_102])).
% 24.21/13.21  tff(c_13389, plain, (![B_1313, D_1314, A_1312, C_1311, B_1310]: (r1_lattices(A_1312, D_1314, B_1313) | ~m1_subset_1(D_1314, u1_struct_0(A_1312)) | ~r4_lattice3(A_1312, B_1313, a_2_1_lattice3(B_1310, C_1311)) | ~m1_subset_1(B_1313, u1_struct_0(A_1312)) | ~l3_lattices(A_1312) | v2_struct_0(A_1312) | ~r3_lattice3(B_1310, D_1314, C_1311) | ~m1_subset_1(D_1314, u1_struct_0(B_1310)) | ~l3_lattices(B_1310) | v2_struct_0(B_1310))), inference(resolution, [status(thm)], [c_48, c_11761])).
% 24.21/13.21  tff(c_13399, plain, (![B_1313, B_1310, C_1311]: (r1_lattices('#skF_5', '#skF_9', B_1313) | ~r4_lattice3('#skF_5', B_1313, a_2_1_lattice3(B_1310, C_1311)) | ~m1_subset_1(B_1313, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r3_lattice3(B_1310, '#skF_9', C_1311) | ~m1_subset_1('#skF_9', u1_struct_0(B_1310)) | ~l3_lattices(B_1310) | v2_struct_0(B_1310))), inference(resolution, [status(thm)], [c_11650, c_13389])).
% 24.21/13.21  tff(c_13408, plain, (![B_1313, B_1310, C_1311]: (r1_lattices('#skF_5', '#skF_9', B_1313) | ~r4_lattice3('#skF_5', B_1313, a_2_1_lattice3(B_1310, C_1311)) | ~m1_subset_1(B_1313, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5') | ~r3_lattice3(B_1310, '#skF_9', C_1311) | ~m1_subset_1('#skF_9', u1_struct_0(B_1310)) | ~l3_lattices(B_1310) | v2_struct_0(B_1310))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_13399])).
% 24.21/13.21  tff(c_13452, plain, (![B_1319, B_1320, C_1321]: (r1_lattices('#skF_5', '#skF_9', B_1319) | ~r4_lattice3('#skF_5', B_1319, a_2_1_lattice3(B_1320, C_1321)) | ~m1_subset_1(B_1319, u1_struct_0('#skF_5')) | ~r3_lattice3(B_1320, '#skF_9', C_1321) | ~m1_subset_1('#skF_9', u1_struct_0(B_1320)) | ~l3_lattices(B_1320) | v2_struct_0(B_1320))), inference(negUnitSimplification, [status(thm)], [c_64, c_13408])).
% 24.21/13.21  tff(c_13455, plain, (r1_lattices('#skF_5', '#skF_9', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~r3_lattice3('#skF_5', '#skF_9', '#skF_8') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_13090, c_13452])).
% 24.21/13.21  tff(c_13470, plain, (r1_lattices('#skF_5', '#skF_9', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_11650, c_11728, c_56, c_13455])).
% 24.21/13.21  tff(c_13472, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_11864, c_13470])).
% 24.21/13.21  tff(c_13475, plain, (![D_1322]: (r3_lattices('#skF_5', D_1322, '#skF_6') | ~r3_lattice3('#skF_5', D_1322, '#skF_7') | ~m1_subset_1(D_1322, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_11727])).
% 24.21/13.21  tff(c_13493, plain, (r3_lattices('#skF_5', '#skF_6', '#skF_6') | ~r3_lattice3('#skF_5', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_56, c_13475])).
% 24.21/13.21  tff(c_13511, plain, (r3_lattices('#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11623, c_13493])).
% 24.21/13.21  tff(c_13589, plain, (![A_1340, B_1341, C_1342]: (r1_lattices(A_1340, B_1341, C_1342) | ~r3_lattices(A_1340, B_1341, C_1342) | ~m1_subset_1(C_1342, u1_struct_0(A_1340)) | ~m1_subset_1(B_1341, u1_struct_0(A_1340)) | ~l3_lattices(A_1340) | ~v9_lattices(A_1340) | ~v8_lattices(A_1340) | ~v6_lattices(A_1340) | v2_struct_0(A_1340))), inference(cnfTransformation, [status(thm)], [f_66])).
% 24.21/13.21  tff(c_13597, plain, (r1_lattices('#skF_5', '#skF_6', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_13511, c_13589])).
% 24.21/13.21  tff(c_13612, plain, (r1_lattices('#skF_5', '#skF_6', '#skF_6') | ~v8_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_13577, c_13588, c_58, c_56, c_13597])).
% 24.21/13.21  tff(c_13613, plain, (r1_lattices('#skF_5', '#skF_6', '#skF_6') | ~v8_lattices('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_13612])).
% 24.21/13.21  tff(c_13614, plain, (~v8_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_13613])).
% 24.21/13.21  tff(c_13617, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_4, c_13614])).
% 24.21/13.21  tff(c_13620, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_13617])).
% 24.21/13.21  tff(c_13622, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_13620])).
% 24.21/13.21  tff(c_13624, plain, (v8_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_13613])).
% 24.21/13.21  tff(c_13487, plain, (![A_64, C_66]: (r3_lattices('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_7') | ~r2_hidden(A_64, a_2_1_lattice3('#skF_5', C_66)) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_13475])).
% 24.21/13.21  tff(c_13504, plain, (![A_64, C_66]: (r3_lattices('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_7') | ~r2_hidden(A_64, a_2_1_lattice3('#skF_5', C_66)) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_13487])).
% 24.21/13.21  tff(c_13505, plain, (![A_64, C_66]: (r3_lattices('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_7') | ~r2_hidden(A_64, a_2_1_lattice3('#skF_5', C_66)))), inference(negUnitSimplification, [status(thm)], [c_64, c_13504])).
% 24.21/13.21  tff(c_13595, plain, (![A_64, C_66]: (r1_lattices('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_4'(A_64, '#skF_5', C_66), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r3_lattice3('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_7') | ~r2_hidden(A_64, a_2_1_lattice3('#skF_5', C_66)))), inference(resolution, [status(thm)], [c_13505, c_13589])).
% 24.21/13.21  tff(c_13608, plain, (![A_64, C_66]: (r1_lattices('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_6') | ~m1_subset_1('#skF_4'(A_64, '#skF_5', C_66), u1_struct_0('#skF_5')) | ~v8_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r3_lattice3('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_7') | ~r2_hidden(A_64, a_2_1_lattice3('#skF_5', C_66)))), inference(demodulation, [status(thm), theory('equality')], [c_13577, c_13588, c_58, c_56, c_13595])).
% 24.21/13.21  tff(c_13609, plain, (![A_64, C_66]: (r1_lattices('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_6') | ~m1_subset_1('#skF_4'(A_64, '#skF_5', C_66), u1_struct_0('#skF_5')) | ~v8_lattices('#skF_5') | ~r3_lattice3('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_7') | ~r2_hidden(A_64, a_2_1_lattice3('#skF_5', C_66)))), inference(negUnitSimplification, [status(thm)], [c_64, c_13608])).
% 24.21/13.21  tff(c_13814, plain, (![A_1372, C_1373]: (r1_lattices('#skF_5', '#skF_4'(A_1372, '#skF_5', C_1373), '#skF_6') | ~m1_subset_1('#skF_4'(A_1372, '#skF_5', C_1373), u1_struct_0('#skF_5')) | ~r3_lattice3('#skF_5', '#skF_4'(A_1372, '#skF_5', C_1373), '#skF_7') | ~r2_hidden(A_1372, a_2_1_lattice3('#skF_5', C_1373)))), inference(demodulation, [status(thm), theory('equality')], [c_13624, c_13609])).
% 24.21/13.21  tff(c_13824, plain, (![A_64, C_66]: (r1_lattices('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_7') | ~r2_hidden(A_64, a_2_1_lattice3('#skF_5', C_66)) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_13814])).
% 24.21/13.21  tff(c_13831, plain, (![A_64, C_66]: (r1_lattices('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_7') | ~r2_hidden(A_64, a_2_1_lattice3('#skF_5', C_66)) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_13824])).
% 24.21/13.21  tff(c_13833, plain, (![A_1374, C_1375]: (r1_lattices('#skF_5', '#skF_4'(A_1374, '#skF_5', C_1375), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'(A_1374, '#skF_5', C_1375), '#skF_7') | ~r2_hidden(A_1374, a_2_1_lattice3('#skF_5', C_1375)))), inference(negUnitSimplification, [status(thm)], [c_64, c_13831])).
% 24.21/13.21  tff(c_13843, plain, (![A_64]: (r1_lattices('#skF_5', '#skF_4'(A_64, '#skF_5', '#skF_7'), '#skF_6') | ~r2_hidden(A_64, a_2_1_lattice3('#skF_5', '#skF_7')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_13833])).
% 24.21/13.21  tff(c_13850, plain, (![A_64]: (r1_lattices('#skF_5', '#skF_4'(A_64, '#skF_5', '#skF_7'), '#skF_6') | ~r2_hidden(A_64, a_2_1_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_13843])).
% 24.21/13.21  tff(c_13851, plain, (![A_64]: (r1_lattices('#skF_5', '#skF_4'(A_64, '#skF_5', '#skF_7'), '#skF_6') | ~r2_hidden(A_64, a_2_1_lattice3('#skF_5', '#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_64, c_13850])).
% 24.21/13.21  tff(c_14240, plain, (![A_1414, B_1415]: (r1_lattices('#skF_5', '#skF_2'(A_1414, B_1415, a_2_1_lattice3('#skF_5', '#skF_7')), '#skF_6') | ~r2_hidden('#skF_2'(A_1414, B_1415, a_2_1_lattice3('#skF_5', '#skF_7')), a_2_1_lattice3('#skF_5', '#skF_7')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | r4_lattice3(A_1414, B_1415, a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_1415, u1_struct_0(A_1414)) | ~l3_lattices(A_1414) | v2_struct_0(A_1414))), inference(superposition, [status(thm), theory('equality')], [c_14233, c_13851])).
% 24.21/13.21  tff(c_14268, plain, (![A_1414, B_1415]: (r1_lattices('#skF_5', '#skF_2'(A_1414, B_1415, a_2_1_lattice3('#skF_5', '#skF_7')), '#skF_6') | ~r2_hidden('#skF_2'(A_1414, B_1415, a_2_1_lattice3('#skF_5', '#skF_7')), a_2_1_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5') | r4_lattice3(A_1414, B_1415, a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_1415, u1_struct_0(A_1414)) | ~l3_lattices(A_1414) | v2_struct_0(A_1414))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_14240])).
% 24.21/13.21  tff(c_14587, plain, (![A_1445, B_1446]: (r1_lattices('#skF_5', '#skF_2'(A_1445, B_1446, a_2_1_lattice3('#skF_5', '#skF_7')), '#skF_6') | ~r2_hidden('#skF_2'(A_1445, B_1446, a_2_1_lattice3('#skF_5', '#skF_7')), a_2_1_lattice3('#skF_5', '#skF_7')) | r4_lattice3(A_1445, B_1446, a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_1446, u1_struct_0(A_1445)) | ~l3_lattices(A_1445) | v2_struct_0(A_1445))), inference(negUnitSimplification, [status(thm)], [c_64, c_14268])).
% 24.21/13.21  tff(c_14600, plain, (![A_1447, B_1448]: (r1_lattices('#skF_5', '#skF_2'(A_1447, B_1448, a_2_1_lattice3('#skF_5', '#skF_7')), '#skF_6') | r4_lattice3(A_1447, B_1448, a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_1448, u1_struct_0(A_1447)) | ~l3_lattices(A_1447) | v2_struct_0(A_1447))), inference(resolution, [status(thm)], [c_32, c_14587])).
% 24.21/13.21  tff(c_14604, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_14600, c_30])).
% 24.21/13.21  tff(c_14607, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_14604])).
% 24.21/13.21  tff(c_14608, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_64, c_14607])).
% 24.21/13.21  tff(c_13535, plain, (![A_1333, D_1334, B_1335, C_1336]: (r1_lattices(A_1333, D_1334, B_1335) | ~r2_hidden(D_1334, C_1336) | ~m1_subset_1(D_1334, u1_struct_0(A_1333)) | ~r4_lattice3(A_1333, B_1335, C_1336) | ~m1_subset_1(B_1335, u1_struct_0(A_1333)) | ~l3_lattices(A_1333) | v2_struct_0(A_1333))), inference(cnfTransformation, [status(thm)], [f_102])).
% 24.21/13.21  tff(c_14746, plain, (![B_1470, A_1473, D_1474, C_1471, B_1472]: (r1_lattices(A_1473, D_1474, B_1472) | ~m1_subset_1(D_1474, u1_struct_0(A_1473)) | ~r4_lattice3(A_1473, B_1472, a_2_1_lattice3(B_1470, C_1471)) | ~m1_subset_1(B_1472, u1_struct_0(A_1473)) | ~l3_lattices(A_1473) | v2_struct_0(A_1473) | ~r3_lattice3(B_1470, D_1474, C_1471) | ~m1_subset_1(D_1474, u1_struct_0(B_1470)) | ~l3_lattices(B_1470) | v2_struct_0(B_1470))), inference(resolution, [status(thm)], [c_48, c_13535])).
% 24.21/13.21  tff(c_14758, plain, (![B_1472, B_1470, C_1471]: (r1_lattices('#skF_5', '#skF_6', B_1472) | ~r4_lattice3('#skF_5', B_1472, a_2_1_lattice3(B_1470, C_1471)) | ~m1_subset_1(B_1472, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r3_lattice3(B_1470, '#skF_6', C_1471) | ~m1_subset_1('#skF_6', u1_struct_0(B_1470)) | ~l3_lattices(B_1470) | v2_struct_0(B_1470))), inference(resolution, [status(thm)], [c_56, c_14746])).
% 24.21/13.21  tff(c_14769, plain, (![B_1472, B_1470, C_1471]: (r1_lattices('#skF_5', '#skF_6', B_1472) | ~r4_lattice3('#skF_5', B_1472, a_2_1_lattice3(B_1470, C_1471)) | ~m1_subset_1(B_1472, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5') | ~r3_lattice3(B_1470, '#skF_6', C_1471) | ~m1_subset_1('#skF_6', u1_struct_0(B_1470)) | ~l3_lattices(B_1470) | v2_struct_0(B_1470))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_14758])).
% 24.21/13.21  tff(c_14775, plain, (![B_1479, B_1480, C_1481]: (r1_lattices('#skF_5', '#skF_6', B_1479) | ~r4_lattice3('#skF_5', B_1479, a_2_1_lattice3(B_1480, C_1481)) | ~m1_subset_1(B_1479, u1_struct_0('#skF_5')) | ~r3_lattice3(B_1480, '#skF_6', C_1481) | ~m1_subset_1('#skF_6', u1_struct_0(B_1480)) | ~l3_lattices(B_1480) | v2_struct_0(B_1480))), inference(negUnitSimplification, [status(thm)], [c_64, c_14769])).
% 24.21/13.21  tff(c_14793, plain, (![B_1480, C_1481, C_57]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3(B_1480, C_1481), C_57)) | ~m1_subset_1('#skF_3'('#skF_5', a_2_1_lattice3(B_1480, C_1481), C_57), u1_struct_0('#skF_5')) | ~r3_lattice3(B_1480, '#skF_6', C_1481) | ~m1_subset_1('#skF_6', u1_struct_0(B_1480)) | ~l3_lattices(B_1480) | v2_struct_0(B_1480) | k15_lattice3('#skF_5', a_2_1_lattice3(B_1480, C_1481))=C_57 | ~r4_lattice3('#skF_5', C_57, a_2_1_lattice3(B_1480, C_1481)) | ~m1_subset_1(C_57, u1_struct_0('#skF_5')) | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_14775])).
% 24.21/13.21  tff(c_14812, plain, (![B_1480, C_1481, C_57]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3(B_1480, C_1481), C_57)) | ~m1_subset_1('#skF_3'('#skF_5', a_2_1_lattice3(B_1480, C_1481), C_57), u1_struct_0('#skF_5')) | ~r3_lattice3(B_1480, '#skF_6', C_1481) | ~m1_subset_1('#skF_6', u1_struct_0(B_1480)) | ~l3_lattices(B_1480) | v2_struct_0(B_1480) | k15_lattice3('#skF_5', a_2_1_lattice3(B_1480, C_1481))=C_57 | ~r4_lattice3('#skF_5', C_57, a_2_1_lattice3(B_1480, C_1481)) | ~m1_subset_1(C_57, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_60, c_14793])).
% 24.21/13.21  tff(c_23307, plain, (![B_1908, C_1909, C_1910]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3(B_1908, C_1909), C_1910)) | ~m1_subset_1('#skF_3'('#skF_5', a_2_1_lattice3(B_1908, C_1909), C_1910), u1_struct_0('#skF_5')) | ~r3_lattice3(B_1908, '#skF_6', C_1909) | ~m1_subset_1('#skF_6', u1_struct_0(B_1908)) | ~l3_lattices(B_1908) | v2_struct_0(B_1908) | k15_lattice3('#skF_5', a_2_1_lattice3(B_1908, C_1909))=C_1910 | ~r4_lattice3('#skF_5', C_1910, a_2_1_lattice3(B_1908, C_1909)) | ~m1_subset_1(C_1910, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_14812])).
% 24.21/13.21  tff(c_23311, plain, (![B_1908, C_1909, C_57]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3(B_1908, C_1909), C_57)) | ~r3_lattice3(B_1908, '#skF_6', C_1909) | ~m1_subset_1('#skF_6', u1_struct_0(B_1908)) | ~l3_lattices(B_1908) | v2_struct_0(B_1908) | k15_lattice3('#skF_5', a_2_1_lattice3(B_1908, C_1909))=C_57 | ~r4_lattice3('#skF_5', C_57, a_2_1_lattice3(B_1908, C_1909)) | ~m1_subset_1(C_57, u1_struct_0('#skF_5')) | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_23307])).
% 24.21/13.21  tff(c_23314, plain, (![B_1908, C_1909, C_57]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3(B_1908, C_1909), C_57)) | ~r3_lattice3(B_1908, '#skF_6', C_1909) | ~m1_subset_1('#skF_6', u1_struct_0(B_1908)) | ~l3_lattices(B_1908) | v2_struct_0(B_1908) | k15_lattice3('#skF_5', a_2_1_lattice3(B_1908, C_1909))=C_57 | ~r4_lattice3('#skF_5', C_57, a_2_1_lattice3(B_1908, C_1909)) | ~m1_subset_1(C_57, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_60, c_23311])).
% 24.21/13.21  tff(c_30458, plain, (![B_2254, C_2255, C_2256]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3(B_2254, C_2255), C_2256)) | ~r3_lattice3(B_2254, '#skF_6', C_2255) | ~m1_subset_1('#skF_6', u1_struct_0(B_2254)) | ~l3_lattices(B_2254) | v2_struct_0(B_2254) | k15_lattice3('#skF_5', a_2_1_lattice3(B_2254, C_2255))=C_2256 | ~r4_lattice3('#skF_5', C_2256, a_2_1_lattice3(B_2254, C_2255)) | ~m1_subset_1(C_2256, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_23314])).
% 24.21/13.21  tff(c_30462, plain, (![B_2254, C_2255]: (~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r3_lattice3(B_2254, '#skF_6', C_2255) | ~m1_subset_1('#skF_6', u1_struct_0(B_2254)) | ~l3_lattices(B_2254) | v2_struct_0(B_2254) | k15_lattice3('#skF_5', a_2_1_lattice3(B_2254, C_2255))='#skF_6' | ~r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3(B_2254, C_2255)) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_30458, c_36])).
% 24.21/13.21  tff(c_30465, plain, (![B_2254, C_2255]: (v2_struct_0('#skF_5') | ~r3_lattice3(B_2254, '#skF_6', C_2255) | ~m1_subset_1('#skF_6', u1_struct_0(B_2254)) | ~l3_lattices(B_2254) | v2_struct_0(B_2254) | k15_lattice3('#skF_5', a_2_1_lattice3(B_2254, C_2255))='#skF_6' | ~r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3(B_2254, C_2255)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_62, c_60, c_30462])).
% 24.21/13.21  tff(c_30467, plain, (![B_2257, C_2258]: (~r3_lattice3(B_2257, '#skF_6', C_2258) | ~m1_subset_1('#skF_6', u1_struct_0(B_2257)) | ~l3_lattices(B_2257) | v2_struct_0(B_2257) | k15_lattice3('#skF_5', a_2_1_lattice3(B_2257, C_2258))='#skF_6' | ~r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3(B_2257, C_2258)))), inference(negUnitSimplification, [status(thm)], [c_64, c_30465])).
% 24.21/13.21  tff(c_30470, plain, (~r3_lattice3('#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_7'))='#skF_6'), inference(resolution, [status(thm)], [c_14608, c_30467])).
% 24.21/13.21  tff(c_30476, plain, (v2_struct_0('#skF_5') | k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_7'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_11623, c_30470])).
% 24.21/13.21  tff(c_30477, plain, (k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_7'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_64, c_30476])).
% 24.21/13.21  tff(c_30531, plain, (k16_lattice3('#skF_5', '#skF_7')='#skF_6' | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_30477, c_46])).
% 24.21/13.21  tff(c_30579, plain, (k16_lattice3('#skF_5', '#skF_7')='#skF_6' | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_30531])).
% 24.21/13.21  tff(c_30581, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_11626, c_30579])).
% 24.21/13.21  tff(c_30584, plain, (![D_2259]: (r3_lattices('#skF_5', D_2259, '#skF_6') | ~r3_lattice3('#skF_5', D_2259, '#skF_7') | ~m1_subset_1(D_2259, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_11649])).
% 24.21/13.21  tff(c_30587, plain, (r3_lattices('#skF_5', '#skF_6', '#skF_6') | ~r3_lattice3('#skF_5', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_56, c_30584])).
% 24.21/13.21  tff(c_30590, plain, (r3_lattices('#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11623, c_30587])).
% 24.21/13.21  tff(c_30725, plain, (![A_2303, B_2304, C_2305]: (r1_lattices(A_2303, B_2304, C_2305) | ~r3_lattices(A_2303, B_2304, C_2305) | ~m1_subset_1(C_2305, u1_struct_0(A_2303)) | ~m1_subset_1(B_2304, u1_struct_0(A_2303)) | ~l3_lattices(A_2303) | ~v9_lattices(A_2303) | ~v8_lattices(A_2303) | ~v6_lattices(A_2303) | v2_struct_0(A_2303))), inference(cnfTransformation, [status(thm)], [f_66])).
% 24.21/13.21  tff(c_30733, plain, (r1_lattices('#skF_5', '#skF_6', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_30590, c_30725])).
% 24.21/13.21  tff(c_30748, plain, (r1_lattices('#skF_5', '#skF_6', '#skF_6') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_30733])).
% 24.21/13.21  tff(c_30749, plain, (r1_lattices('#skF_5', '#skF_6', '#skF_6') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_30748])).
% 24.21/13.21  tff(c_30750, plain, (~v6_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_30749])).
% 24.21/13.21  tff(c_30769, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_8, c_30750])).
% 24.21/13.21  tff(c_30772, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_30769])).
% 24.21/13.21  tff(c_30774, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_30772])).
% 24.21/13.21  tff(c_30776, plain, (v6_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_30749])).
% 24.21/13.21  tff(c_30775, plain, (~v8_lattices('#skF_5') | ~v9_lattices('#skF_5') | r1_lattices('#skF_5', '#skF_6', '#skF_6')), inference(splitRight, [status(thm)], [c_30749])).
% 24.21/13.21  tff(c_30777, plain, (~v9_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_30775])).
% 24.21/13.21  tff(c_30783, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_2, c_30777])).
% 24.21/13.21  tff(c_30786, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_30783])).
% 24.21/13.21  tff(c_30788, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_30786])).
% 24.21/13.21  tff(c_30789, plain, (~v8_lattices('#skF_5') | r1_lattices('#skF_5', '#skF_6', '#skF_6')), inference(splitRight, [status(thm)], [c_30775])).
% 24.21/13.21  tff(c_30791, plain, (~v8_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_30789])).
% 24.21/13.21  tff(c_30794, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_4, c_30791])).
% 24.21/13.21  tff(c_30797, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_30794])).
% 24.21/13.21  tff(c_30799, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_30797])).
% 24.21/13.21  tff(c_30801, plain, (v8_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_30789])).
% 24.21/13.21  tff(c_30790, plain, (v9_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_30775])).
% 24.21/13.21  tff(c_30591, plain, (![A_2260, B_2261, C_2262]: (m1_subset_1('#skF_4'(A_2260, B_2261, C_2262), u1_struct_0(B_2261)) | ~r2_hidden(A_2260, a_2_1_lattice3(B_2261, C_2262)) | ~l3_lattices(B_2261) | v2_struct_0(B_2261))), inference(cnfTransformation, [status(thm)], [f_152])).
% 24.21/13.21  tff(c_30582, plain, (![D_87]: (r3_lattices('#skF_5', D_87, '#skF_6') | ~r3_lattice3('#skF_5', D_87, '#skF_7') | ~m1_subset_1(D_87, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_11649])).
% 24.21/13.21  tff(c_30595, plain, (![A_2260, C_2262]: (r3_lattices('#skF_5', '#skF_4'(A_2260, '#skF_5', C_2262), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'(A_2260, '#skF_5', C_2262), '#skF_7') | ~r2_hidden(A_2260, a_2_1_lattice3('#skF_5', C_2262)) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_30591, c_30582])).
% 24.21/13.21  tff(c_30598, plain, (![A_2260, C_2262]: (r3_lattices('#skF_5', '#skF_4'(A_2260, '#skF_5', C_2262), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'(A_2260, '#skF_5', C_2262), '#skF_7') | ~r2_hidden(A_2260, a_2_1_lattice3('#skF_5', C_2262)) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_30595])).
% 24.21/13.21  tff(c_30599, plain, (![A_2260, C_2262]: (r3_lattices('#skF_5', '#skF_4'(A_2260, '#skF_5', C_2262), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'(A_2260, '#skF_5', C_2262), '#skF_7') | ~r2_hidden(A_2260, a_2_1_lattice3('#skF_5', C_2262)))), inference(negUnitSimplification, [status(thm)], [c_64, c_30598])).
% 24.21/13.21  tff(c_30731, plain, (![A_2260, C_2262]: (r1_lattices('#skF_5', '#skF_4'(A_2260, '#skF_5', C_2262), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_4'(A_2260, '#skF_5', C_2262), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r3_lattice3('#skF_5', '#skF_4'(A_2260, '#skF_5', C_2262), '#skF_7') | ~r2_hidden(A_2260, a_2_1_lattice3('#skF_5', C_2262)))), inference(resolution, [status(thm)], [c_30599, c_30725])).
% 24.21/13.21  tff(c_30744, plain, (![A_2260, C_2262]: (r1_lattices('#skF_5', '#skF_4'(A_2260, '#skF_5', C_2262), '#skF_6') | ~m1_subset_1('#skF_4'(A_2260, '#skF_5', C_2262), u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r3_lattice3('#skF_5', '#skF_4'(A_2260, '#skF_5', C_2262), '#skF_7') | ~r2_hidden(A_2260, a_2_1_lattice3('#skF_5', C_2262)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_30731])).
% 24.21/13.21  tff(c_30745, plain, (![A_2260, C_2262]: (r1_lattices('#skF_5', '#skF_4'(A_2260, '#skF_5', C_2262), '#skF_6') | ~m1_subset_1('#skF_4'(A_2260, '#skF_5', C_2262), u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | ~r3_lattice3('#skF_5', '#skF_4'(A_2260, '#skF_5', C_2262), '#skF_7') | ~r2_hidden(A_2260, a_2_1_lattice3('#skF_5', C_2262)))), inference(negUnitSimplification, [status(thm)], [c_64, c_30744])).
% 24.21/13.21  tff(c_31117, plain, (![A_2357, C_2358]: (r1_lattices('#skF_5', '#skF_4'(A_2357, '#skF_5', C_2358), '#skF_6') | ~m1_subset_1('#skF_4'(A_2357, '#skF_5', C_2358), u1_struct_0('#skF_5')) | ~r3_lattice3('#skF_5', '#skF_4'(A_2357, '#skF_5', C_2358), '#skF_7') | ~r2_hidden(A_2357, a_2_1_lattice3('#skF_5', C_2358)))), inference(demodulation, [status(thm), theory('equality')], [c_30776, c_30801, c_30790, c_30745])).
% 24.21/13.21  tff(c_31134, plain, (![A_64, C_66]: (r1_lattices('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_7') | ~r2_hidden(A_64, a_2_1_lattice3('#skF_5', C_66)) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_31117])).
% 24.21/13.21  tff(c_31144, plain, (![A_64, C_66]: (r1_lattices('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_7') | ~r2_hidden(A_64, a_2_1_lattice3('#skF_5', C_66)) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_31134])).
% 24.21/13.21  tff(c_31146, plain, (![A_2359, C_2360]: (r1_lattices('#skF_5', '#skF_4'(A_2359, '#skF_5', C_2360), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'(A_2359, '#skF_5', C_2360), '#skF_7') | ~r2_hidden(A_2359, a_2_1_lattice3('#skF_5', C_2360)))), inference(negUnitSimplification, [status(thm)], [c_64, c_31144])).
% 24.21/13.21  tff(c_31163, plain, (![A_64]: (r1_lattices('#skF_5', '#skF_4'(A_64, '#skF_5', '#skF_7'), '#skF_6') | ~r2_hidden(A_64, a_2_1_lattice3('#skF_5', '#skF_7')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_31146])).
% 24.21/13.21  tff(c_31173, plain, (![A_64]: (r1_lattices('#skF_5', '#skF_4'(A_64, '#skF_5', '#skF_7'), '#skF_6') | ~r2_hidden(A_64, a_2_1_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_31163])).
% 24.21/13.21  tff(c_31175, plain, (![A_2361]: (r1_lattices('#skF_5', '#skF_4'(A_2361, '#skF_5', '#skF_7'), '#skF_6') | ~r2_hidden(A_2361, a_2_1_lattice3('#skF_5', '#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_64, c_31173])).
% 24.21/13.21  tff(c_31183, plain, (![A_2272, B_2273]: (r1_lattices('#skF_5', '#skF_2'(A_2272, B_2273, a_2_1_lattice3('#skF_5', '#skF_7')), '#skF_6') | ~r2_hidden('#skF_2'(A_2272, B_2273, a_2_1_lattice3('#skF_5', '#skF_7')), a_2_1_lattice3('#skF_5', '#skF_7')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | r4_lattice3(A_2272, B_2273, a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_2273, u1_struct_0(A_2272)) | ~l3_lattices(A_2272) | v2_struct_0(A_2272))), inference(superposition, [status(thm), theory('equality')], [c_30666, c_31175])).
% 24.21/13.21  tff(c_31195, plain, (![A_2272, B_2273]: (r1_lattices('#skF_5', '#skF_2'(A_2272, B_2273, a_2_1_lattice3('#skF_5', '#skF_7')), '#skF_6') | ~r2_hidden('#skF_2'(A_2272, B_2273, a_2_1_lattice3('#skF_5', '#skF_7')), a_2_1_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5') | r4_lattice3(A_2272, B_2273, a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_2273, u1_struct_0(A_2272)) | ~l3_lattices(A_2272) | v2_struct_0(A_2272))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_31183])).
% 24.21/13.21  tff(c_31463, plain, (![A_2383, B_2384]: (r1_lattices('#skF_5', '#skF_2'(A_2383, B_2384, a_2_1_lattice3('#skF_5', '#skF_7')), '#skF_6') | ~r2_hidden('#skF_2'(A_2383, B_2384, a_2_1_lattice3('#skF_5', '#skF_7')), a_2_1_lattice3('#skF_5', '#skF_7')) | r4_lattice3(A_2383, B_2384, a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_2384, u1_struct_0(A_2383)) | ~l3_lattices(A_2383) | v2_struct_0(A_2383))), inference(negUnitSimplification, [status(thm)], [c_64, c_31195])).
% 24.21/13.21  tff(c_31476, plain, (![A_2385, B_2386]: (r1_lattices('#skF_5', '#skF_2'(A_2385, B_2386, a_2_1_lattice3('#skF_5', '#skF_7')), '#skF_6') | r4_lattice3(A_2385, B_2386, a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_2386, u1_struct_0(A_2385)) | ~l3_lattices(A_2385) | v2_struct_0(A_2385))), inference(resolution, [status(thm)], [c_32, c_31463])).
% 24.21/13.21  tff(c_31480, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_31476, c_30])).
% 24.21/13.21  tff(c_31483, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_31480])).
% 24.21/13.21  tff(c_31484, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_64, c_31483])).
% 24.21/13.21  tff(c_30715, plain, (![A_2299, D_2300, B_2301, C_2302]: (r1_lattices(A_2299, D_2300, B_2301) | ~r2_hidden(D_2300, C_2302) | ~m1_subset_1(D_2300, u1_struct_0(A_2299)) | ~r4_lattice3(A_2299, B_2301, C_2302) | ~m1_subset_1(B_2301, u1_struct_0(A_2299)) | ~l3_lattices(A_2299) | v2_struct_0(A_2299))), inference(cnfTransformation, [status(thm)], [f_102])).
% 24.21/13.21  tff(c_31596, plain, (![C_2404, D_2407, A_2406, B_2405, B_2403]: (r1_lattices(A_2406, D_2407, B_2405) | ~m1_subset_1(D_2407, u1_struct_0(A_2406)) | ~r4_lattice3(A_2406, B_2405, a_2_1_lattice3(B_2403, C_2404)) | ~m1_subset_1(B_2405, u1_struct_0(A_2406)) | ~l3_lattices(A_2406) | v2_struct_0(A_2406) | ~r3_lattice3(B_2403, D_2407, C_2404) | ~m1_subset_1(D_2407, u1_struct_0(B_2403)) | ~l3_lattices(B_2403) | v2_struct_0(B_2403))), inference(resolution, [status(thm)], [c_48, c_30715])).
% 24.21/13.21  tff(c_31606, plain, (![B_2405, B_2403, C_2404]: (r1_lattices('#skF_5', '#skF_6', B_2405) | ~r4_lattice3('#skF_5', B_2405, a_2_1_lattice3(B_2403, C_2404)) | ~m1_subset_1(B_2405, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r3_lattice3(B_2403, '#skF_6', C_2404) | ~m1_subset_1('#skF_6', u1_struct_0(B_2403)) | ~l3_lattices(B_2403) | v2_struct_0(B_2403))), inference(resolution, [status(thm)], [c_56, c_31596])).
% 24.21/13.21  tff(c_31613, plain, (![B_2405, B_2403, C_2404]: (r1_lattices('#skF_5', '#skF_6', B_2405) | ~r4_lattice3('#skF_5', B_2405, a_2_1_lattice3(B_2403, C_2404)) | ~m1_subset_1(B_2405, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5') | ~r3_lattice3(B_2403, '#skF_6', C_2404) | ~m1_subset_1('#skF_6', u1_struct_0(B_2403)) | ~l3_lattices(B_2403) | v2_struct_0(B_2403))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_31606])).
% 24.21/13.21  tff(c_31615, plain, (![B_2408, B_2409, C_2410]: (r1_lattices('#skF_5', '#skF_6', B_2408) | ~r4_lattice3('#skF_5', B_2408, a_2_1_lattice3(B_2409, C_2410)) | ~m1_subset_1(B_2408, u1_struct_0('#skF_5')) | ~r3_lattice3(B_2409, '#skF_6', C_2410) | ~m1_subset_1('#skF_6', u1_struct_0(B_2409)) | ~l3_lattices(B_2409) | v2_struct_0(B_2409))), inference(negUnitSimplification, [status(thm)], [c_64, c_31613])).
% 24.21/13.21  tff(c_31633, plain, (![B_2409, C_2410, C_57]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3(B_2409, C_2410), C_57)) | ~m1_subset_1('#skF_3'('#skF_5', a_2_1_lattice3(B_2409, C_2410), C_57), u1_struct_0('#skF_5')) | ~r3_lattice3(B_2409, '#skF_6', C_2410) | ~m1_subset_1('#skF_6', u1_struct_0(B_2409)) | ~l3_lattices(B_2409) | v2_struct_0(B_2409) | k15_lattice3('#skF_5', a_2_1_lattice3(B_2409, C_2410))=C_57 | ~r4_lattice3('#skF_5', C_57, a_2_1_lattice3(B_2409, C_2410)) | ~m1_subset_1(C_57, u1_struct_0('#skF_5')) | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_31615])).
% 24.21/13.21  tff(c_31652, plain, (![B_2409, C_2410, C_57]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3(B_2409, C_2410), C_57)) | ~m1_subset_1('#skF_3'('#skF_5', a_2_1_lattice3(B_2409, C_2410), C_57), u1_struct_0('#skF_5')) | ~r3_lattice3(B_2409, '#skF_6', C_2410) | ~m1_subset_1('#skF_6', u1_struct_0(B_2409)) | ~l3_lattices(B_2409) | v2_struct_0(B_2409) | k15_lattice3('#skF_5', a_2_1_lattice3(B_2409, C_2410))=C_57 | ~r4_lattice3('#skF_5', C_57, a_2_1_lattice3(B_2409, C_2410)) | ~m1_subset_1(C_57, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_60, c_31633])).
% 24.21/13.21  tff(c_39614, plain, (![B_2824, C_2825, C_2826]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3(B_2824, C_2825), C_2826)) | ~m1_subset_1('#skF_3'('#skF_5', a_2_1_lattice3(B_2824, C_2825), C_2826), u1_struct_0('#skF_5')) | ~r3_lattice3(B_2824, '#skF_6', C_2825) | ~m1_subset_1('#skF_6', u1_struct_0(B_2824)) | ~l3_lattices(B_2824) | v2_struct_0(B_2824) | k15_lattice3('#skF_5', a_2_1_lattice3(B_2824, C_2825))=C_2826 | ~r4_lattice3('#skF_5', C_2826, a_2_1_lattice3(B_2824, C_2825)) | ~m1_subset_1(C_2826, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_31652])).
% 24.21/13.21  tff(c_39618, plain, (![B_2824, C_2825, C_57]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3(B_2824, C_2825), C_57)) | ~r3_lattice3(B_2824, '#skF_6', C_2825) | ~m1_subset_1('#skF_6', u1_struct_0(B_2824)) | ~l3_lattices(B_2824) | v2_struct_0(B_2824) | k15_lattice3('#skF_5', a_2_1_lattice3(B_2824, C_2825))=C_57 | ~r4_lattice3('#skF_5', C_57, a_2_1_lattice3(B_2824, C_2825)) | ~m1_subset_1(C_57, u1_struct_0('#skF_5')) | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_39614])).
% 24.21/13.21  tff(c_39621, plain, (![B_2824, C_2825, C_57]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3(B_2824, C_2825), C_57)) | ~r3_lattice3(B_2824, '#skF_6', C_2825) | ~m1_subset_1('#skF_6', u1_struct_0(B_2824)) | ~l3_lattices(B_2824) | v2_struct_0(B_2824) | k15_lattice3('#skF_5', a_2_1_lattice3(B_2824, C_2825))=C_57 | ~r4_lattice3('#skF_5', C_57, a_2_1_lattice3(B_2824, C_2825)) | ~m1_subset_1(C_57, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_60, c_39618])).
% 24.21/13.21  tff(c_46107, plain, (![B_3091, C_3092, C_3093]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3(B_3091, C_3092), C_3093)) | ~r3_lattice3(B_3091, '#skF_6', C_3092) | ~m1_subset_1('#skF_6', u1_struct_0(B_3091)) | ~l3_lattices(B_3091) | v2_struct_0(B_3091) | k15_lattice3('#skF_5', a_2_1_lattice3(B_3091, C_3092))=C_3093 | ~r4_lattice3('#skF_5', C_3093, a_2_1_lattice3(B_3091, C_3092)) | ~m1_subset_1(C_3093, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_39621])).
% 24.21/13.21  tff(c_46111, plain, (![B_3091, C_3092]: (~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r3_lattice3(B_3091, '#skF_6', C_3092) | ~m1_subset_1('#skF_6', u1_struct_0(B_3091)) | ~l3_lattices(B_3091) | v2_struct_0(B_3091) | k15_lattice3('#skF_5', a_2_1_lattice3(B_3091, C_3092))='#skF_6' | ~r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3(B_3091, C_3092)) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_46107, c_36])).
% 24.21/13.21  tff(c_46114, plain, (![B_3091, C_3092]: (v2_struct_0('#skF_5') | ~r3_lattice3(B_3091, '#skF_6', C_3092) | ~m1_subset_1('#skF_6', u1_struct_0(B_3091)) | ~l3_lattices(B_3091) | v2_struct_0(B_3091) | k15_lattice3('#skF_5', a_2_1_lattice3(B_3091, C_3092))='#skF_6' | ~r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3(B_3091, C_3092)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_62, c_60, c_46111])).
% 24.21/13.21  tff(c_46116, plain, (![B_3094, C_3095]: (~r3_lattice3(B_3094, '#skF_6', C_3095) | ~m1_subset_1('#skF_6', u1_struct_0(B_3094)) | ~l3_lattices(B_3094) | v2_struct_0(B_3094) | k15_lattice3('#skF_5', a_2_1_lattice3(B_3094, C_3095))='#skF_6' | ~r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3(B_3094, C_3095)))), inference(negUnitSimplification, [status(thm)], [c_64, c_46114])).
% 24.21/13.21  tff(c_46119, plain, (~r3_lattice3('#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_7'))='#skF_6'), inference(resolution, [status(thm)], [c_31484, c_46116])).
% 24.21/13.21  tff(c_46125, plain, (v2_struct_0('#skF_5') | k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_7'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_11623, c_46119])).
% 24.21/13.21  tff(c_46126, plain, (k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_7'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_64, c_46125])).
% 24.21/13.21  tff(c_46177, plain, (k16_lattice3('#skF_5', '#skF_7')='#skF_6' | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_46126, c_46])).
% 24.21/13.21  tff(c_46224, plain, (k16_lattice3('#skF_5', '#skF_7')='#skF_6' | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_46177])).
% 24.21/13.21  tff(c_46226, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_11626, c_46224])).
% 24.21/13.21  tff(c_46228, plain, (r3_lattices('#skF_5', '#skF_9', '#skF_6')), inference(splitRight, [status(thm)], [c_11628])).
% 24.21/13.21  tff(c_46418, plain, (![A_3151, B_3152, C_3153]: (r1_lattices(A_3151, B_3152, C_3153) | ~r3_lattices(A_3151, B_3152, C_3153) | ~m1_subset_1(C_3153, u1_struct_0(A_3151)) | ~m1_subset_1(B_3152, u1_struct_0(A_3151)) | ~l3_lattices(A_3151) | ~v9_lattices(A_3151) | ~v8_lattices(A_3151) | ~v6_lattices(A_3151) | v2_struct_0(A_3151))), inference(cnfTransformation, [status(thm)], [f_66])).
% 24.21/13.21  tff(c_46428, plain, (r1_lattices('#skF_5', '#skF_9', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_46228, c_46418])).
% 24.21/13.21  tff(c_46447, plain, (r1_lattices('#skF_5', '#skF_9', '#skF_6') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_46315, c_56, c_46428])).
% 24.21/13.21  tff(c_46448, plain, (r1_lattices('#skF_5', '#skF_9', '#skF_6') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_46447])).
% 24.21/13.21  tff(c_46449, plain, (~v6_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_46448])).
% 24.21/13.21  tff(c_46452, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_8, c_46449])).
% 24.21/13.21  tff(c_46455, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_46452])).
% 24.21/13.21  tff(c_46457, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_46455])).
% 24.21/13.21  tff(c_46459, plain, (v6_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_46448])).
% 24.21/13.21  tff(c_68, plain, (![D_87]: (r3_lattices('#skF_5', D_87, '#skF_6') | ~r3_lattice3('#skF_5', D_87, '#skF_7') | ~m1_subset_1(D_87, u1_struct_0('#skF_5')) | ~r3_lattices('#skF_5', '#skF_9', '#skF_6') | ~r3_lattice3('#skF_5', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_177])).
% 24.21/13.21  tff(c_46322, plain, (![D_3131]: (r3_lattices('#skF_5', D_3131, '#skF_6') | ~r3_lattice3('#skF_5', D_3131, '#skF_7') | ~m1_subset_1(D_3131, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_11622, c_46228, c_68])).
% 24.21/13.21  tff(c_46340, plain, (r3_lattices('#skF_5', '#skF_6', '#skF_6') | ~r3_lattice3('#skF_5', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_56, c_46322])).
% 24.21/13.21  tff(c_46357, plain, (r3_lattices('#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11623, c_46340])).
% 24.21/13.21  tff(c_46426, plain, (r1_lattices('#skF_5', '#skF_6', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_46357, c_46418])).
% 24.21/13.21  tff(c_46443, plain, (r1_lattices('#skF_5', '#skF_6', '#skF_6') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_46426])).
% 24.21/13.21  tff(c_46444, plain, (r1_lattices('#skF_5', '#skF_6', '#skF_6') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_46443])).
% 24.21/13.21  tff(c_46461, plain, (r1_lattices('#skF_5', '#skF_6', '#skF_6') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46459, c_46444])).
% 24.21/13.21  tff(c_46462, plain, (~v8_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_46461])).
% 24.21/13.21  tff(c_46465, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_4, c_46462])).
% 24.21/13.21  tff(c_46468, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_46465])).
% 24.21/13.21  tff(c_46470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_46468])).
% 24.21/13.21  tff(c_46472, plain, (v8_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_46461])).
% 24.21/13.21  tff(c_46471, plain, (~v9_lattices('#skF_5') | r1_lattices('#skF_5', '#skF_6', '#skF_6')), inference(splitRight, [status(thm)], [c_46461])).
% 24.21/13.21  tff(c_46473, plain, (~v9_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_46471])).
% 24.21/13.21  tff(c_46476, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_2, c_46473])).
% 24.21/13.21  tff(c_46479, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_46476])).
% 24.21/13.21  tff(c_46481, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_46479])).
% 24.21/13.21  tff(c_46483, plain, (v9_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_46471])).
% 24.21/13.21  tff(c_46337, plain, (![A_64, C_66]: (r3_lattices('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_7') | ~r2_hidden(A_64, a_2_1_lattice3('#skF_5', C_66)) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_46322])).
% 24.21/13.21  tff(c_46353, plain, (![A_64, C_66]: (r3_lattices('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_7') | ~r2_hidden(A_64, a_2_1_lattice3('#skF_5', C_66)) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_46337])).
% 24.21/13.21  tff(c_46354, plain, (![A_64, C_66]: (r3_lattices('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_7') | ~r2_hidden(A_64, a_2_1_lattice3('#skF_5', C_66)))), inference(negUnitSimplification, [status(thm)], [c_64, c_46353])).
% 24.21/13.21  tff(c_46424, plain, (![A_64, C_66]: (r1_lattices('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_4'(A_64, '#skF_5', C_66), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r3_lattice3('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_7') | ~r2_hidden(A_64, a_2_1_lattice3('#skF_5', C_66)))), inference(resolution, [status(thm)], [c_46354, c_46418])).
% 24.21/13.21  tff(c_46439, plain, (![A_64, C_66]: (r1_lattices('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_6') | ~m1_subset_1('#skF_4'(A_64, '#skF_5', C_66), u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r3_lattice3('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_7') | ~r2_hidden(A_64, a_2_1_lattice3('#skF_5', C_66)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_46424])).
% 24.21/13.21  tff(c_46440, plain, (![A_64, C_66]: (r1_lattices('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_6') | ~m1_subset_1('#skF_4'(A_64, '#skF_5', C_66), u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | ~r3_lattice3('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_7') | ~r2_hidden(A_64, a_2_1_lattice3('#skF_5', C_66)))), inference(negUnitSimplification, [status(thm)], [c_64, c_46439])).
% 24.21/13.21  tff(c_46881, plain, (![A_3206, C_3207]: (r1_lattices('#skF_5', '#skF_4'(A_3206, '#skF_5', C_3207), '#skF_6') | ~m1_subset_1('#skF_4'(A_3206, '#skF_5', C_3207), u1_struct_0('#skF_5')) | ~r3_lattice3('#skF_5', '#skF_4'(A_3206, '#skF_5', C_3207), '#skF_7') | ~r2_hidden(A_3206, a_2_1_lattice3('#skF_5', C_3207)))), inference(demodulation, [status(thm), theory('equality')], [c_46459, c_46472, c_46483, c_46440])).
% 24.21/13.21  tff(c_46897, plain, (![A_64, C_66]: (r1_lattices('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_7') | ~r2_hidden(A_64, a_2_1_lattice3('#skF_5', C_66)) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_46881])).
% 24.21/13.21  tff(c_46904, plain, (![A_64, C_66]: (r1_lattices('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_7') | ~r2_hidden(A_64, a_2_1_lattice3('#skF_5', C_66)) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_46897])).
% 24.21/13.21  tff(c_46906, plain, (![A_3208, C_3209]: (r1_lattices('#skF_5', '#skF_4'(A_3208, '#skF_5', C_3209), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'(A_3208, '#skF_5', C_3209), '#skF_7') | ~r2_hidden(A_3208, a_2_1_lattice3('#skF_5', C_3209)))), inference(negUnitSimplification, [status(thm)], [c_64, c_46904])).
% 24.21/13.21  tff(c_46922, plain, (![A_64]: (r1_lattices('#skF_5', '#skF_4'(A_64, '#skF_5', '#skF_7'), '#skF_6') | ~r2_hidden(A_64, a_2_1_lattice3('#skF_5', '#skF_7')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_46906])).
% 24.21/13.21  tff(c_46929, plain, (![A_64]: (r1_lattices('#skF_5', '#skF_4'(A_64, '#skF_5', '#skF_7'), '#skF_6') | ~r2_hidden(A_64, a_2_1_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_46922])).
% 24.21/13.21  tff(c_46930, plain, (![A_64]: (r1_lattices('#skF_5', '#skF_4'(A_64, '#skF_5', '#skF_7'), '#skF_6') | ~r2_hidden(A_64, a_2_1_lattice3('#skF_5', '#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_64, c_46929])).
% 24.21/13.21  tff(c_47258, plain, (![A_3241, B_3242]: (r1_lattices('#skF_5', '#skF_2'(A_3241, B_3242, a_2_1_lattice3('#skF_5', '#skF_7')), '#skF_6') | ~r2_hidden('#skF_2'(A_3241, B_3242, a_2_1_lattice3('#skF_5', '#skF_7')), a_2_1_lattice3('#skF_5', '#skF_7')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | r4_lattice3(A_3241, B_3242, a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_3242, u1_struct_0(A_3241)) | ~l3_lattices(A_3241) | v2_struct_0(A_3241))), inference(superposition, [status(thm), theory('equality')], [c_47248, c_46930])).
% 24.21/13.21  tff(c_47286, plain, (![A_3241, B_3242]: (r1_lattices('#skF_5', '#skF_2'(A_3241, B_3242, a_2_1_lattice3('#skF_5', '#skF_7')), '#skF_6') | ~r2_hidden('#skF_2'(A_3241, B_3242, a_2_1_lattice3('#skF_5', '#skF_7')), a_2_1_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5') | r4_lattice3(A_3241, B_3242, a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_3242, u1_struct_0(A_3241)) | ~l3_lattices(A_3241) | v2_struct_0(A_3241))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_47258])).
% 24.21/13.21  tff(c_47334, plain, (![A_3248, B_3249]: (r1_lattices('#skF_5', '#skF_2'(A_3248, B_3249, a_2_1_lattice3('#skF_5', '#skF_7')), '#skF_6') | ~r2_hidden('#skF_2'(A_3248, B_3249, a_2_1_lattice3('#skF_5', '#skF_7')), a_2_1_lattice3('#skF_5', '#skF_7')) | r4_lattice3(A_3248, B_3249, a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_3249, u1_struct_0(A_3248)) | ~l3_lattices(A_3248) | v2_struct_0(A_3248))), inference(negUnitSimplification, [status(thm)], [c_64, c_47286])).
% 24.21/13.21  tff(c_47347, plain, (![A_3250, B_3251]: (r1_lattices('#skF_5', '#skF_2'(A_3250, B_3251, a_2_1_lattice3('#skF_5', '#skF_7')), '#skF_6') | r4_lattice3(A_3250, B_3251, a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_3251, u1_struct_0(A_3250)) | ~l3_lattices(A_3250) | v2_struct_0(A_3250))), inference(resolution, [status(thm)], [c_32, c_47334])).
% 24.21/13.21  tff(c_47351, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_47347, c_30])).
% 24.21/13.21  tff(c_47354, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_47351])).
% 24.21/13.21  tff(c_47355, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_64, c_47354])).
% 24.21/13.21  tff(c_46376, plain, (![A_3140, D_3141, B_3142, C_3143]: (r1_lattices(A_3140, D_3141, B_3142) | ~r2_hidden(D_3141, C_3143) | ~m1_subset_1(D_3141, u1_struct_0(A_3140)) | ~r4_lattice3(A_3140, B_3142, C_3143) | ~m1_subset_1(B_3142, u1_struct_0(A_3140)) | ~l3_lattices(A_3140) | v2_struct_0(A_3140))), inference(cnfTransformation, [status(thm)], [f_102])).
% 24.21/13.21  tff(c_47485, plain, (![D_3264, C_3261, B_3260, B_3263, A_3262]: (r1_lattices(A_3262, D_3264, B_3263) | ~m1_subset_1(D_3264, u1_struct_0(A_3262)) | ~r4_lattice3(A_3262, B_3263, a_2_1_lattice3(B_3260, C_3261)) | ~m1_subset_1(B_3263, u1_struct_0(A_3262)) | ~l3_lattices(A_3262) | v2_struct_0(A_3262) | ~r3_lattice3(B_3260, D_3264, C_3261) | ~m1_subset_1(D_3264, u1_struct_0(B_3260)) | ~l3_lattices(B_3260) | v2_struct_0(B_3260))), inference(resolution, [status(thm)], [c_48, c_46376])).
% 24.21/13.21  tff(c_47497, plain, (![B_3263, B_3260, C_3261]: (r1_lattices('#skF_5', '#skF_6', B_3263) | ~r4_lattice3('#skF_5', B_3263, a_2_1_lattice3(B_3260, C_3261)) | ~m1_subset_1(B_3263, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r3_lattice3(B_3260, '#skF_6', C_3261) | ~m1_subset_1('#skF_6', u1_struct_0(B_3260)) | ~l3_lattices(B_3260) | v2_struct_0(B_3260))), inference(resolution, [status(thm)], [c_56, c_47485])).
% 24.21/13.21  tff(c_47508, plain, (![B_3263, B_3260, C_3261]: (r1_lattices('#skF_5', '#skF_6', B_3263) | ~r4_lattice3('#skF_5', B_3263, a_2_1_lattice3(B_3260, C_3261)) | ~m1_subset_1(B_3263, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5') | ~r3_lattice3(B_3260, '#skF_6', C_3261) | ~m1_subset_1('#skF_6', u1_struct_0(B_3260)) | ~l3_lattices(B_3260) | v2_struct_0(B_3260))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_47497])).
% 24.21/13.21  tff(c_47510, plain, (![B_3265, B_3266, C_3267]: (r1_lattices('#skF_5', '#skF_6', B_3265) | ~r4_lattice3('#skF_5', B_3265, a_2_1_lattice3(B_3266, C_3267)) | ~m1_subset_1(B_3265, u1_struct_0('#skF_5')) | ~r3_lattice3(B_3266, '#skF_6', C_3267) | ~m1_subset_1('#skF_6', u1_struct_0(B_3266)) | ~l3_lattices(B_3266) | v2_struct_0(B_3266))), inference(negUnitSimplification, [status(thm)], [c_64, c_47508])).
% 24.21/13.21  tff(c_47528, plain, (![B_3266, C_3267, C_57]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3(B_3266, C_3267), C_57)) | ~m1_subset_1('#skF_3'('#skF_5', a_2_1_lattice3(B_3266, C_3267), C_57), u1_struct_0('#skF_5')) | ~r3_lattice3(B_3266, '#skF_6', C_3267) | ~m1_subset_1('#skF_6', u1_struct_0(B_3266)) | ~l3_lattices(B_3266) | v2_struct_0(B_3266) | k15_lattice3('#skF_5', a_2_1_lattice3(B_3266, C_3267))=C_57 | ~r4_lattice3('#skF_5', C_57, a_2_1_lattice3(B_3266, C_3267)) | ~m1_subset_1(C_57, u1_struct_0('#skF_5')) | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_47510])).
% 24.21/13.21  tff(c_47547, plain, (![B_3266, C_3267, C_57]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3(B_3266, C_3267), C_57)) | ~m1_subset_1('#skF_3'('#skF_5', a_2_1_lattice3(B_3266, C_3267), C_57), u1_struct_0('#skF_5')) | ~r3_lattice3(B_3266, '#skF_6', C_3267) | ~m1_subset_1('#skF_6', u1_struct_0(B_3266)) | ~l3_lattices(B_3266) | v2_struct_0(B_3266) | k15_lattice3('#skF_5', a_2_1_lattice3(B_3266, C_3267))=C_57 | ~r4_lattice3('#skF_5', C_57, a_2_1_lattice3(B_3266, C_3267)) | ~m1_subset_1(C_57, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_60, c_47528])).
% 24.21/13.21  tff(c_56646, plain, (![B_3754, C_3755, C_3756]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3(B_3754, C_3755), C_3756)) | ~m1_subset_1('#skF_3'('#skF_5', a_2_1_lattice3(B_3754, C_3755), C_3756), u1_struct_0('#skF_5')) | ~r3_lattice3(B_3754, '#skF_6', C_3755) | ~m1_subset_1('#skF_6', u1_struct_0(B_3754)) | ~l3_lattices(B_3754) | v2_struct_0(B_3754) | k15_lattice3('#skF_5', a_2_1_lattice3(B_3754, C_3755))=C_3756 | ~r4_lattice3('#skF_5', C_3756, a_2_1_lattice3(B_3754, C_3755)) | ~m1_subset_1(C_3756, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_47547])).
% 24.21/13.21  tff(c_56650, plain, (![B_3754, C_3755, C_57]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3(B_3754, C_3755), C_57)) | ~r3_lattice3(B_3754, '#skF_6', C_3755) | ~m1_subset_1('#skF_6', u1_struct_0(B_3754)) | ~l3_lattices(B_3754) | v2_struct_0(B_3754) | k15_lattice3('#skF_5', a_2_1_lattice3(B_3754, C_3755))=C_57 | ~r4_lattice3('#skF_5', C_57, a_2_1_lattice3(B_3754, C_3755)) | ~m1_subset_1(C_57, u1_struct_0('#skF_5')) | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_56646])).
% 24.21/13.21  tff(c_56653, plain, (![B_3754, C_3755, C_57]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3(B_3754, C_3755), C_57)) | ~r3_lattice3(B_3754, '#skF_6', C_3755) | ~m1_subset_1('#skF_6', u1_struct_0(B_3754)) | ~l3_lattices(B_3754) | v2_struct_0(B_3754) | k15_lattice3('#skF_5', a_2_1_lattice3(B_3754, C_3755))=C_57 | ~r4_lattice3('#skF_5', C_57, a_2_1_lattice3(B_3754, C_3755)) | ~m1_subset_1(C_57, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_60, c_56650])).
% 24.21/13.21  tff(c_64045, plain, (![B_4068, C_4069, C_4070]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3(B_4068, C_4069), C_4070)) | ~r3_lattice3(B_4068, '#skF_6', C_4069) | ~m1_subset_1('#skF_6', u1_struct_0(B_4068)) | ~l3_lattices(B_4068) | v2_struct_0(B_4068) | k15_lattice3('#skF_5', a_2_1_lattice3(B_4068, C_4069))=C_4070 | ~r4_lattice3('#skF_5', C_4070, a_2_1_lattice3(B_4068, C_4069)) | ~m1_subset_1(C_4070, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_56653])).
% 24.21/13.21  tff(c_64049, plain, (![B_4068, C_4069]: (~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r3_lattice3(B_4068, '#skF_6', C_4069) | ~m1_subset_1('#skF_6', u1_struct_0(B_4068)) | ~l3_lattices(B_4068) | v2_struct_0(B_4068) | k15_lattice3('#skF_5', a_2_1_lattice3(B_4068, C_4069))='#skF_6' | ~r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3(B_4068, C_4069)) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_64045, c_36])).
% 24.21/13.21  tff(c_64052, plain, (![B_4068, C_4069]: (v2_struct_0('#skF_5') | ~r3_lattice3(B_4068, '#skF_6', C_4069) | ~m1_subset_1('#skF_6', u1_struct_0(B_4068)) | ~l3_lattices(B_4068) | v2_struct_0(B_4068) | k15_lattice3('#skF_5', a_2_1_lattice3(B_4068, C_4069))='#skF_6' | ~r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3(B_4068, C_4069)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_62, c_60, c_64049])).
% 24.21/13.21  tff(c_64054, plain, (![B_4071, C_4072]: (~r3_lattice3(B_4071, '#skF_6', C_4072) | ~m1_subset_1('#skF_6', u1_struct_0(B_4071)) | ~l3_lattices(B_4071) | v2_struct_0(B_4071) | k15_lattice3('#skF_5', a_2_1_lattice3(B_4071, C_4072))='#skF_6' | ~r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3(B_4071, C_4072)))), inference(negUnitSimplification, [status(thm)], [c_64, c_64052])).
% 24.21/13.21  tff(c_64057, plain, (~r3_lattice3('#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_7'))='#skF_6'), inference(resolution, [status(thm)], [c_47355, c_64054])).
% 24.21/13.21  tff(c_64063, plain, (v2_struct_0('#skF_5') | k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_7'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_11623, c_64057])).
% 24.21/13.21  tff(c_64064, plain, (k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_7'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_64, c_64063])).
% 24.21/13.21  tff(c_64118, plain, (k16_lattice3('#skF_5', '#skF_7')='#skF_6' | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_64064, c_46])).
% 24.21/13.21  tff(c_64166, plain, (k16_lattice3('#skF_5', '#skF_7')='#skF_6' | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_64118])).
% 24.21/13.21  tff(c_64168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_11626, c_64166])).
% 24.21/13.21  tff(c_64170, plain, (k16_lattice3('#skF_5', '#skF_7')='#skF_6'), inference(splitRight, [status(thm)], [c_11625])).
% 24.21/13.21  tff(c_64176, plain, (~r3_lattices('#skF_5', '#skF_9', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11622, c_64170, c_66])).
% 24.21/13.21  tff(c_78, plain, (k16_lattice3('#skF_5', '#skF_7')!='#skF_6' | m1_subset_1('#skF_9', u1_struct_0('#skF_5')) | ~r3_lattice3('#skF_5', '#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_177])).
% 24.21/13.21  tff(c_64191, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_11622, c_64170, c_78])).
% 24.21/13.21  tff(c_64317, plain, (![A_4121, B_4122, C_4123]: (r3_lattices(A_4121, B_4122, C_4123) | ~r1_lattices(A_4121, B_4122, C_4123) | ~m1_subset_1(C_4123, u1_struct_0(A_4121)) | ~m1_subset_1(B_4122, u1_struct_0(A_4121)) | ~l3_lattices(A_4121) | ~v9_lattices(A_4121) | ~v8_lattices(A_4121) | ~v6_lattices(A_4121) | v2_struct_0(A_4121))), inference(cnfTransformation, [status(thm)], [f_66])).
% 24.21/13.21  tff(c_64327, plain, (![B_4122]: (r3_lattices('#skF_5', B_4122, '#skF_6') | ~r1_lattices('#skF_5', B_4122, '#skF_6') | ~m1_subset_1(B_4122, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_64317])).
% 24.21/13.21  tff(c_64337, plain, (![B_4122]: (r3_lattices('#skF_5', B_4122, '#skF_6') | ~r1_lattices('#skF_5', B_4122, '#skF_6') | ~m1_subset_1(B_4122, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_64327])).
% 24.21/13.21  tff(c_64338, plain, (![B_4122]: (r3_lattices('#skF_5', B_4122, '#skF_6') | ~r1_lattices('#skF_5', B_4122, '#skF_6') | ~m1_subset_1(B_4122, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_64337])).
% 24.21/13.21  tff(c_64339, plain, (~v6_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_64338])).
% 24.21/13.21  tff(c_64342, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_8, c_64339])).
% 24.21/13.21  tff(c_64345, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_64342])).
% 24.21/13.21  tff(c_64347, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_64345])).
% 24.21/13.21  tff(c_64349, plain, (v6_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_64338])).
% 24.21/13.21  tff(c_64348, plain, (![B_4122]: (~v8_lattices('#skF_5') | ~v9_lattices('#skF_5') | r3_lattices('#skF_5', B_4122, '#skF_6') | ~r1_lattices('#skF_5', B_4122, '#skF_6') | ~m1_subset_1(B_4122, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_64338])).
% 24.21/13.21  tff(c_64354, plain, (~v9_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_64348])).
% 24.21/13.21  tff(c_64357, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_2, c_64354])).
% 24.21/13.21  tff(c_64360, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_64357])).
% 24.21/13.21  tff(c_64362, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_64360])).
% 24.21/13.21  tff(c_64364, plain, (v9_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_64348])).
% 24.21/13.21  tff(c_64325, plain, (![B_4122]: (r3_lattices('#skF_5', B_4122, '#skF_9') | ~r1_lattices('#skF_5', B_4122, '#skF_9') | ~m1_subset_1(B_4122, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_64191, c_64317])).
% 24.21/13.21  tff(c_64333, plain, (![B_4122]: (r3_lattices('#skF_5', B_4122, '#skF_9') | ~r1_lattices('#skF_5', B_4122, '#skF_9') | ~m1_subset_1(B_4122, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_64325])).
% 24.21/13.21  tff(c_64334, plain, (![B_4122]: (r3_lattices('#skF_5', B_4122, '#skF_9') | ~r1_lattices('#skF_5', B_4122, '#skF_9') | ~m1_subset_1(B_4122, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_64333])).
% 24.21/13.21  tff(c_64366, plain, (![B_4122]: (r3_lattices('#skF_5', B_4122, '#skF_9') | ~r1_lattices('#skF_5', B_4122, '#skF_9') | ~m1_subset_1(B_4122, u1_struct_0('#skF_5')) | ~v8_lattices('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64349, c_64364, c_64334])).
% 24.21/13.21  tff(c_64367, plain, (~v8_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_64366])).
% 24.21/13.21  tff(c_64370, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_4, c_64367])).
% 24.21/13.21  tff(c_64373, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_64370])).
% 24.21/13.21  tff(c_64375, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_64373])).
% 24.21/13.21  tff(c_64377, plain, (v8_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_64366])).
% 24.21/13.21  tff(c_64363, plain, (![B_4122]: (~v8_lattices('#skF_5') | r3_lattices('#skF_5', B_4122, '#skF_6') | ~r1_lattices('#skF_5', B_4122, '#skF_6') | ~m1_subset_1(B_4122, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_64348])).
% 24.21/13.21  tff(c_64424, plain, (![B_4131]: (r3_lattices('#skF_5', B_4131, '#skF_6') | ~r1_lattices('#skF_5', B_4131, '#skF_6') | ~m1_subset_1(B_4131, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_64377, c_64363])).
% 24.21/13.21  tff(c_64443, plain, (r3_lattices('#skF_5', '#skF_9', '#skF_6') | ~r1_lattices('#skF_5', '#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_64191, c_64424])).
% 24.21/13.21  tff(c_64465, plain, (~r1_lattices('#skF_5', '#skF_9', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_64176, c_64443])).
% 24.21/13.21  tff(c_64169, plain, (r3_lattice3('#skF_5', '#skF_9', '#skF_8')), inference(splitRight, [status(thm)], [c_11625])).
% 24.21/13.21  tff(c_64293, plain, (![A_4108, B_4109]: (r4_lattice3(A_4108, k15_lattice3(A_4108, B_4109), B_4109) | ~m1_subset_1(k15_lattice3(A_4108, B_4109), u1_struct_0(A_4108)) | ~v4_lattice3(A_4108) | ~v10_lattices(A_4108) | ~l3_lattices(A_4108) | v2_struct_0(A_4108))), inference(cnfTransformation, [status(thm)], [f_130])).
% 24.21/13.21  tff(c_65447, plain, (![A_4248, B_4249]: (r4_lattice3(A_4248, k15_lattice3(A_4248, a_2_1_lattice3(A_4248, B_4249)), a_2_1_lattice3(A_4248, B_4249)) | ~m1_subset_1(k16_lattice3(A_4248, B_4249), u1_struct_0(A_4248)) | ~v4_lattice3(A_4248) | ~v10_lattices(A_4248) | ~l3_lattices(A_4248) | v2_struct_0(A_4248) | ~l3_lattices(A_4248) | v2_struct_0(A_4248))), inference(superposition, [status(thm), theory('equality')], [c_46, c_64293])).
% 24.21/13.21  tff(c_65498, plain, (![A_4254, B_4255]: (r4_lattice3(A_4254, k16_lattice3(A_4254, B_4255), a_2_1_lattice3(A_4254, B_4255)) | ~m1_subset_1(k16_lattice3(A_4254, B_4255), u1_struct_0(A_4254)) | ~v4_lattice3(A_4254) | ~v10_lattices(A_4254) | ~l3_lattices(A_4254) | v2_struct_0(A_4254) | ~l3_lattices(A_4254) | v2_struct_0(A_4254) | ~l3_lattices(A_4254) | v2_struct_0(A_4254))), inference(superposition, [status(thm), theory('equality')], [c_46, c_65447])).
% 24.21/13.21  tff(c_65504, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_8')) | ~m1_subset_1(k16_lattice3('#skF_5', '#skF_8'), u1_struct_0('#skF_5')) | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_90, c_65498])).
% 24.21/13.21  tff(c_65509, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_8')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_58, c_58, c_62, c_60, c_56, c_90, c_65504])).
% 24.21/13.21  tff(c_65510, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_64, c_65509])).
% 24.21/13.21  tff(c_64306, plain, (![A_4114, D_4115, B_4116, C_4117]: (r1_lattices(A_4114, D_4115, B_4116) | ~r2_hidden(D_4115, C_4117) | ~m1_subset_1(D_4115, u1_struct_0(A_4114)) | ~r4_lattice3(A_4114, B_4116, C_4117) | ~m1_subset_1(B_4116, u1_struct_0(A_4114)) | ~l3_lattices(A_4114) | v2_struct_0(A_4114))), inference(cnfTransformation, [status(thm)], [f_102])).
% 24.21/13.21  tff(c_65803, plain, (![B_4284, A_4286, C_4285, B_4283, D_4287]: (r1_lattices(A_4286, D_4287, B_4284) | ~m1_subset_1(D_4287, u1_struct_0(A_4286)) | ~r4_lattice3(A_4286, B_4284, a_2_1_lattice3(B_4283, C_4285)) | ~m1_subset_1(B_4284, u1_struct_0(A_4286)) | ~l3_lattices(A_4286) | v2_struct_0(A_4286) | ~r3_lattice3(B_4283, D_4287, C_4285) | ~m1_subset_1(D_4287, u1_struct_0(B_4283)) | ~l3_lattices(B_4283) | v2_struct_0(B_4283))), inference(resolution, [status(thm)], [c_48, c_64306])).
% 24.21/13.21  tff(c_65813, plain, (![B_4284, B_4283, C_4285]: (r1_lattices('#skF_5', '#skF_9', B_4284) | ~r4_lattice3('#skF_5', B_4284, a_2_1_lattice3(B_4283, C_4285)) | ~m1_subset_1(B_4284, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r3_lattice3(B_4283, '#skF_9', C_4285) | ~m1_subset_1('#skF_9', u1_struct_0(B_4283)) | ~l3_lattices(B_4283) | v2_struct_0(B_4283))), inference(resolution, [status(thm)], [c_64191, c_65803])).
% 24.21/13.21  tff(c_65822, plain, (![B_4284, B_4283, C_4285]: (r1_lattices('#skF_5', '#skF_9', B_4284) | ~r4_lattice3('#skF_5', B_4284, a_2_1_lattice3(B_4283, C_4285)) | ~m1_subset_1(B_4284, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5') | ~r3_lattice3(B_4283, '#skF_9', C_4285) | ~m1_subset_1('#skF_9', u1_struct_0(B_4283)) | ~l3_lattices(B_4283) | v2_struct_0(B_4283))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_65813])).
% 24.21/13.21  tff(c_65912, plain, (![B_4300, B_4301, C_4302]: (r1_lattices('#skF_5', '#skF_9', B_4300) | ~r4_lattice3('#skF_5', B_4300, a_2_1_lattice3(B_4301, C_4302)) | ~m1_subset_1(B_4300, u1_struct_0('#skF_5')) | ~r3_lattice3(B_4301, '#skF_9', C_4302) | ~m1_subset_1('#skF_9', u1_struct_0(B_4301)) | ~l3_lattices(B_4301) | v2_struct_0(B_4301))), inference(negUnitSimplification, [status(thm)], [c_64, c_65822])).
% 24.21/13.21  tff(c_65918, plain, (r1_lattices('#skF_5', '#skF_9', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~r3_lattice3('#skF_5', '#skF_9', '#skF_8') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_65510, c_65912])).
% 24.21/13.21  tff(c_65937, plain, (r1_lattices('#skF_5', '#skF_9', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_64191, c_64169, c_56, c_65918])).
% 24.21/13.21  tff(c_65939, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_64465, c_65937])).
% 24.21/13.21  tff(c_65941, plain, (~r3_lattice3('#skF_5', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_11621])).
% 24.21/13.21  tff(c_70, plain, (r3_lattice3('#skF_5', '#skF_6', '#skF_7') | ~r3_lattices('#skF_5', '#skF_9', '#skF_6') | ~r3_lattice3('#skF_5', '#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_177])).
% 24.21/13.21  tff(c_65951, plain, (r3_lattice3('#skF_5', '#skF_6', '#skF_7') | ~r3_lattices('#skF_5', '#skF_9', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11622, c_70])).
% 24.21/13.21  tff(c_65952, plain, (~r3_lattices('#skF_5', '#skF_9', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_65941, c_65951])).
% 24.21/13.21  tff(c_65940, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_11621])).
% 24.21/13.21  tff(c_66067, plain, (![A_4351, B_4352, C_4353]: (r3_lattices(A_4351, B_4352, C_4353) | ~r1_lattices(A_4351, B_4352, C_4353) | ~m1_subset_1(C_4353, u1_struct_0(A_4351)) | ~m1_subset_1(B_4352, u1_struct_0(A_4351)) | ~l3_lattices(A_4351) | ~v9_lattices(A_4351) | ~v8_lattices(A_4351) | ~v6_lattices(A_4351) | v2_struct_0(A_4351))), inference(cnfTransformation, [status(thm)], [f_66])).
% 24.21/13.21  tff(c_66077, plain, (![B_4352]: (r3_lattices('#skF_5', B_4352, '#skF_6') | ~r1_lattices('#skF_5', B_4352, '#skF_6') | ~m1_subset_1(B_4352, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_66067])).
% 24.21/13.21  tff(c_66087, plain, (![B_4352]: (r3_lattices('#skF_5', B_4352, '#skF_6') | ~r1_lattices('#skF_5', B_4352, '#skF_6') | ~m1_subset_1(B_4352, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_66077])).
% 24.21/13.21  tff(c_66088, plain, (![B_4352]: (r3_lattices('#skF_5', B_4352, '#skF_6') | ~r1_lattices('#skF_5', B_4352, '#skF_6') | ~m1_subset_1(B_4352, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_66087])).
% 24.21/13.21  tff(c_66089, plain, (~v6_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_66088])).
% 24.21/13.21  tff(c_66092, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_8, c_66089])).
% 24.21/13.21  tff(c_66095, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_66092])).
% 24.21/13.21  tff(c_66097, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_66095])).
% 24.21/13.21  tff(c_66098, plain, (![B_4352]: (~v8_lattices('#skF_5') | ~v9_lattices('#skF_5') | r3_lattices('#skF_5', B_4352, '#skF_6') | ~r1_lattices('#skF_5', B_4352, '#skF_6') | ~m1_subset_1(B_4352, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_66088])).
% 24.21/13.21  tff(c_66100, plain, (~v9_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_66098])).
% 24.21/13.21  tff(c_66104, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_2, c_66100])).
% 24.21/13.21  tff(c_66107, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_66104])).
% 24.21/13.21  tff(c_66109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_66107])).
% 24.21/13.21  tff(c_66110, plain, (![B_4352]: (~v8_lattices('#skF_5') | r3_lattices('#skF_5', B_4352, '#skF_6') | ~r1_lattices('#skF_5', B_4352, '#skF_6') | ~m1_subset_1(B_4352, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_66098])).
% 24.21/13.21  tff(c_66112, plain, (~v8_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_66110])).
% 24.21/13.21  tff(c_66118, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_4, c_66112])).
% 24.21/13.21  tff(c_66121, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_66118])).
% 24.21/13.21  tff(c_66123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_66121])).
% 24.21/13.21  tff(c_66126, plain, (![B_4357]: (r3_lattices('#skF_5', B_4357, '#skF_6') | ~r1_lattices('#skF_5', B_4357, '#skF_6') | ~m1_subset_1(B_4357, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_66110])).
% 24.21/13.21  tff(c_66141, plain, (r3_lattices('#skF_5', '#skF_9', '#skF_6') | ~r1_lattices('#skF_5', '#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_65940, c_66126])).
% 24.21/13.21  tff(c_66159, plain, (~r1_lattices('#skF_5', '#skF_9', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_65952, c_66141])).
% 24.21/13.21  tff(c_76, plain, (r3_lattice3('#skF_5', '#skF_6', '#skF_7') | r3_lattice3('#skF_5', '#skF_9', '#skF_8') | ~r3_lattice3('#skF_5', '#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_177])).
% 24.21/13.21  tff(c_65948, plain, (r3_lattice3('#skF_5', '#skF_6', '#skF_7') | r3_lattice3('#skF_5', '#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_11622, c_76])).
% 24.21/13.21  tff(c_65949, plain, (r3_lattice3('#skF_5', '#skF_9', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_65941, c_65948])).
% 24.21/13.21  tff(c_66039, plain, (![A_4338, B_4339]: (r4_lattice3(A_4338, k15_lattice3(A_4338, B_4339), B_4339) | ~m1_subset_1(k15_lattice3(A_4338, B_4339), u1_struct_0(A_4338)) | ~v4_lattice3(A_4338) | ~v10_lattices(A_4338) | ~l3_lattices(A_4338) | v2_struct_0(A_4338))), inference(cnfTransformation, [status(thm)], [f_130])).
% 24.21/13.21  tff(c_67193, plain, (![A_4499, B_4500]: (r4_lattice3(A_4499, k15_lattice3(A_4499, a_2_1_lattice3(A_4499, B_4500)), a_2_1_lattice3(A_4499, B_4500)) | ~m1_subset_1(k16_lattice3(A_4499, B_4500), u1_struct_0(A_4499)) | ~v4_lattice3(A_4499) | ~v10_lattices(A_4499) | ~l3_lattices(A_4499) | v2_struct_0(A_4499) | ~l3_lattices(A_4499) | v2_struct_0(A_4499))), inference(superposition, [status(thm), theory('equality')], [c_46, c_66039])).
% 24.21/13.21  tff(c_67271, plain, (![A_4512, B_4513]: (r4_lattice3(A_4512, k16_lattice3(A_4512, B_4513), a_2_1_lattice3(A_4512, B_4513)) | ~m1_subset_1(k16_lattice3(A_4512, B_4513), u1_struct_0(A_4512)) | ~v4_lattice3(A_4512) | ~v10_lattices(A_4512) | ~l3_lattices(A_4512) | v2_struct_0(A_4512) | ~l3_lattices(A_4512) | v2_struct_0(A_4512) | ~l3_lattices(A_4512) | v2_struct_0(A_4512))), inference(superposition, [status(thm), theory('equality')], [c_46, c_67193])).
% 24.21/13.21  tff(c_67274, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_8')) | ~m1_subset_1(k16_lattice3('#skF_5', '#skF_8'), u1_struct_0('#skF_5')) | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_90, c_67271])).
% 24.21/13.21  tff(c_67276, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_8')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_58, c_58, c_62, c_60, c_56, c_90, c_67274])).
% 24.21/13.21  tff(c_67277, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_64, c_67276])).
% 24.21/13.21  tff(c_66056, plain, (![A_4344, D_4345, B_4346, C_4347]: (r1_lattices(A_4344, D_4345, B_4346) | ~r2_hidden(D_4345, C_4347) | ~m1_subset_1(D_4345, u1_struct_0(A_4344)) | ~r4_lattice3(A_4344, B_4346, C_4347) | ~m1_subset_1(B_4346, u1_struct_0(A_4344)) | ~l3_lattices(A_4344) | v2_struct_0(A_4344))), inference(cnfTransformation, [status(thm)], [f_102])).
% 24.21/13.21  tff(c_67549, plain, (![A_4548, B_4545, C_4546, B_4547, D_4549]: (r1_lattices(A_4548, D_4549, B_4547) | ~m1_subset_1(D_4549, u1_struct_0(A_4548)) | ~r4_lattice3(A_4548, B_4547, a_2_1_lattice3(B_4545, C_4546)) | ~m1_subset_1(B_4547, u1_struct_0(A_4548)) | ~l3_lattices(A_4548) | v2_struct_0(A_4548) | ~r3_lattice3(B_4545, D_4549, C_4546) | ~m1_subset_1(D_4549, u1_struct_0(B_4545)) | ~l3_lattices(B_4545) | v2_struct_0(B_4545))), inference(resolution, [status(thm)], [c_48, c_66056])).
% 24.21/13.21  tff(c_67559, plain, (![B_4547, B_4545, C_4546]: (r1_lattices('#skF_5', '#skF_9', B_4547) | ~r4_lattice3('#skF_5', B_4547, a_2_1_lattice3(B_4545, C_4546)) | ~m1_subset_1(B_4547, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r3_lattice3(B_4545, '#skF_9', C_4546) | ~m1_subset_1('#skF_9', u1_struct_0(B_4545)) | ~l3_lattices(B_4545) | v2_struct_0(B_4545))), inference(resolution, [status(thm)], [c_65940, c_67549])).
% 24.21/13.21  tff(c_67568, plain, (![B_4547, B_4545, C_4546]: (r1_lattices('#skF_5', '#skF_9', B_4547) | ~r4_lattice3('#skF_5', B_4547, a_2_1_lattice3(B_4545, C_4546)) | ~m1_subset_1(B_4547, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5') | ~r3_lattice3(B_4545, '#skF_9', C_4546) | ~m1_subset_1('#skF_9', u1_struct_0(B_4545)) | ~l3_lattices(B_4545) | v2_struct_0(B_4545))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_67559])).
% 24.21/13.21  tff(c_67612, plain, (![B_4554, B_4555, C_4556]: (r1_lattices('#skF_5', '#skF_9', B_4554) | ~r4_lattice3('#skF_5', B_4554, a_2_1_lattice3(B_4555, C_4556)) | ~m1_subset_1(B_4554, u1_struct_0('#skF_5')) | ~r3_lattice3(B_4555, '#skF_9', C_4556) | ~m1_subset_1('#skF_9', u1_struct_0(B_4555)) | ~l3_lattices(B_4555) | v2_struct_0(B_4555))), inference(negUnitSimplification, [status(thm)], [c_64, c_67568])).
% 24.21/13.21  tff(c_67615, plain, (r1_lattices('#skF_5', '#skF_9', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~r3_lattice3('#skF_5', '#skF_9', '#skF_8') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_67277, c_67612])).
% 24.21/13.21  tff(c_67630, plain, (r1_lattices('#skF_5', '#skF_9', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_65940, c_65949, c_56, c_67615])).
% 24.21/13.21  tff(c_67632, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_66159, c_67630])).
% 24.21/13.21  tff(c_67634, plain, (k16_lattice3('#skF_5', '#skF_8')!='#skF_6'), inference(splitRight, [status(thm)], [c_88])).
% 24.21/13.21  tff(c_84, plain, (k16_lattice3('#skF_5', '#skF_7')!='#skF_6' | k16_lattice3('#skF_5', '#skF_8')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_177])).
% 24.21/13.21  tff(c_67635, plain, (k16_lattice3('#skF_5', '#skF_7')!='#skF_6'), inference(splitLeft, [status(thm)], [c_84])).
% 24.21/13.21  tff(c_67633, plain, (r3_lattice3('#skF_5', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_88])).
% 24.21/13.21  tff(c_67703, plain, (![A_4580, B_4581, C_4582]: (r2_hidden('#skF_2'(A_4580, B_4581, C_4582), C_4582) | r4_lattice3(A_4580, B_4581, C_4582) | ~m1_subset_1(B_4581, u1_struct_0(A_4580)) | ~l3_lattices(A_4580) | v2_struct_0(A_4580))), inference(cnfTransformation, [status(thm)], [f_102])).
% 24.21/13.21  tff(c_68228, plain, (![A_4683, B_4684, B_4685, C_4686]: ('#skF_4'('#skF_2'(A_4683, B_4684, a_2_1_lattice3(B_4685, C_4686)), B_4685, C_4686)='#skF_2'(A_4683, B_4684, a_2_1_lattice3(B_4685, C_4686)) | ~l3_lattices(B_4685) | v2_struct_0(B_4685) | r4_lattice3(A_4683, B_4684, a_2_1_lattice3(B_4685, C_4686)) | ~m1_subset_1(B_4684, u1_struct_0(A_4683)) | ~l3_lattices(A_4683) | v2_struct_0(A_4683))), inference(resolution, [status(thm)], [c_67703, c_52])).
% 24.21/13.21  tff(c_67766, plain, (![A_4614, B_4615, C_4616]: (r3_lattices(A_4614, B_4615, C_4616) | ~r1_lattices(A_4614, B_4615, C_4616) | ~m1_subset_1(C_4616, u1_struct_0(A_4614)) | ~m1_subset_1(B_4615, u1_struct_0(A_4614)) | ~l3_lattices(A_4614) | ~v9_lattices(A_4614) | ~v8_lattices(A_4614) | ~v6_lattices(A_4614) | v2_struct_0(A_4614))), inference(cnfTransformation, [status(thm)], [f_66])).
% 24.21/13.21  tff(c_67774, plain, (![B_4615]: (r3_lattices('#skF_5', B_4615, '#skF_6') | ~r1_lattices('#skF_5', B_4615, '#skF_6') | ~m1_subset_1(B_4615, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_67766])).
% 24.21/13.21  tff(c_67780, plain, (![B_4615]: (r3_lattices('#skF_5', B_4615, '#skF_6') | ~r1_lattices('#skF_5', B_4615, '#skF_6') | ~m1_subset_1(B_4615, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_67774])).
% 24.21/13.21  tff(c_67781, plain, (![B_4615]: (r3_lattices('#skF_5', B_4615, '#skF_6') | ~r1_lattices('#skF_5', B_4615, '#skF_6') | ~m1_subset_1(B_4615, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_67780])).
% 24.21/13.21  tff(c_67782, plain, (~v6_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_67781])).
% 24.21/13.21  tff(c_67785, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_8, c_67782])).
% 24.21/13.21  tff(c_67788, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_67785])).
% 24.21/13.21  tff(c_67790, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_67788])).
% 24.21/13.21  tff(c_67792, plain, (v6_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_67781])).
% 24.21/13.21  tff(c_67791, plain, (![B_4615]: (~v8_lattices('#skF_5') | ~v9_lattices('#skF_5') | r3_lattices('#skF_5', B_4615, '#skF_6') | ~r1_lattices('#skF_5', B_4615, '#skF_6') | ~m1_subset_1(B_4615, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_67781])).
% 24.21/13.21  tff(c_67793, plain, (~v9_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_67791])).
% 24.21/13.21  tff(c_67796, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_2, c_67793])).
% 24.21/13.21  tff(c_67799, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_67796])).
% 24.21/13.21  tff(c_67801, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_67799])).
% 24.21/13.21  tff(c_67803, plain, (v9_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_67791])).
% 24.21/13.21  tff(c_86, plain, (![D_87]: (r3_lattices('#skF_5', D_87, '#skF_6') | ~r3_lattice3('#skF_5', D_87, '#skF_7') | ~m1_subset_1(D_87, u1_struct_0('#skF_5')) | k16_lattice3('#skF_5', '#skF_8')='#skF_6')), inference(cnfTransformation, [status(thm)], [f_177])).
% 24.21/13.21  tff(c_67656, plain, (![D_4570]: (r3_lattices('#skF_5', D_4570, '#skF_6') | ~r3_lattice3('#skF_5', D_4570, '#skF_7') | ~m1_subset_1(D_4570, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_67634, c_86])).
% 24.21/13.21  tff(c_67659, plain, (r3_lattices('#skF_5', '#skF_6', '#skF_6') | ~r3_lattice3('#skF_5', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_56, c_67656])).
% 24.21/13.21  tff(c_67662, plain, (r3_lattices('#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_67633, c_67659])).
% 24.21/13.21  tff(c_67804, plain, (![A_4617, B_4618, C_4619]: (r1_lattices(A_4617, B_4618, C_4619) | ~r3_lattices(A_4617, B_4618, C_4619) | ~m1_subset_1(C_4619, u1_struct_0(A_4617)) | ~m1_subset_1(B_4618, u1_struct_0(A_4617)) | ~l3_lattices(A_4617) | ~v9_lattices(A_4617) | ~v8_lattices(A_4617) | ~v6_lattices(A_4617) | v2_struct_0(A_4617))), inference(cnfTransformation, [status(thm)], [f_66])).
% 24.21/13.21  tff(c_67812, plain, (r1_lattices('#skF_5', '#skF_6', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_67662, c_67804])).
% 24.21/13.21  tff(c_67827, plain, (r1_lattices('#skF_5', '#skF_6', '#skF_6') | ~v8_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_67792, c_67803, c_58, c_56, c_67812])).
% 24.21/13.21  tff(c_67828, plain, (r1_lattices('#skF_5', '#skF_6', '#skF_6') | ~v8_lattices('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_67827])).
% 24.21/13.21  tff(c_67829, plain, (~v8_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_67828])).
% 24.21/13.21  tff(c_67832, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_4, c_67829])).
% 24.21/13.21  tff(c_67835, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_67832])).
% 24.21/13.21  tff(c_67837, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_67835])).
% 24.21/13.21  tff(c_67839, plain, (v8_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_67828])).
% 24.21/13.21  tff(c_67663, plain, (![A_4571, B_4572, C_4573]: (m1_subset_1('#skF_4'(A_4571, B_4572, C_4573), u1_struct_0(B_4572)) | ~r2_hidden(A_4571, a_2_1_lattice3(B_4572, C_4573)) | ~l3_lattices(B_4572) | v2_struct_0(B_4572))), inference(cnfTransformation, [status(thm)], [f_152])).
% 24.21/13.21  tff(c_67655, plain, (![D_87]: (r3_lattices('#skF_5', D_87, '#skF_6') | ~r3_lattice3('#skF_5', D_87, '#skF_7') | ~m1_subset_1(D_87, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_67634, c_86])).
% 24.21/13.21  tff(c_67667, plain, (![A_4571, C_4573]: (r3_lattices('#skF_5', '#skF_4'(A_4571, '#skF_5', C_4573), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'(A_4571, '#skF_5', C_4573), '#skF_7') | ~r2_hidden(A_4571, a_2_1_lattice3('#skF_5', C_4573)) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_67663, c_67655])).
% 24.21/13.21  tff(c_67670, plain, (![A_4571, C_4573]: (r3_lattices('#skF_5', '#skF_4'(A_4571, '#skF_5', C_4573), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'(A_4571, '#skF_5', C_4573), '#skF_7') | ~r2_hidden(A_4571, a_2_1_lattice3('#skF_5', C_4573)) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_67667])).
% 24.21/13.21  tff(c_67671, plain, (![A_4571, C_4573]: (r3_lattices('#skF_5', '#skF_4'(A_4571, '#skF_5', C_4573), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'(A_4571, '#skF_5', C_4573), '#skF_7') | ~r2_hidden(A_4571, a_2_1_lattice3('#skF_5', C_4573)))), inference(negUnitSimplification, [status(thm)], [c_64, c_67670])).
% 24.21/13.21  tff(c_67810, plain, (![A_4571, C_4573]: (r1_lattices('#skF_5', '#skF_4'(A_4571, '#skF_5', C_4573), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_4'(A_4571, '#skF_5', C_4573), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r3_lattice3('#skF_5', '#skF_4'(A_4571, '#skF_5', C_4573), '#skF_7') | ~r2_hidden(A_4571, a_2_1_lattice3('#skF_5', C_4573)))), inference(resolution, [status(thm)], [c_67671, c_67804])).
% 24.21/13.21  tff(c_67823, plain, (![A_4571, C_4573]: (r1_lattices('#skF_5', '#skF_4'(A_4571, '#skF_5', C_4573), '#skF_6') | ~m1_subset_1('#skF_4'(A_4571, '#skF_5', C_4573), u1_struct_0('#skF_5')) | ~v8_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r3_lattice3('#skF_5', '#skF_4'(A_4571, '#skF_5', C_4573), '#skF_7') | ~r2_hidden(A_4571, a_2_1_lattice3('#skF_5', C_4573)))), inference(demodulation, [status(thm), theory('equality')], [c_67792, c_67803, c_58, c_56, c_67810])).
% 24.21/13.21  tff(c_67824, plain, (![A_4571, C_4573]: (r1_lattices('#skF_5', '#skF_4'(A_4571, '#skF_5', C_4573), '#skF_6') | ~m1_subset_1('#skF_4'(A_4571, '#skF_5', C_4573), u1_struct_0('#skF_5')) | ~v8_lattices('#skF_5') | ~r3_lattice3('#skF_5', '#skF_4'(A_4571, '#skF_5', C_4573), '#skF_7') | ~r2_hidden(A_4571, a_2_1_lattice3('#skF_5', C_4573)))), inference(negUnitSimplification, [status(thm)], [c_64, c_67823])).
% 24.21/13.21  tff(c_67842, plain, (![A_4620, C_4621]: (r1_lattices('#skF_5', '#skF_4'(A_4620, '#skF_5', C_4621), '#skF_6') | ~m1_subset_1('#skF_4'(A_4620, '#skF_5', C_4621), u1_struct_0('#skF_5')) | ~r3_lattice3('#skF_5', '#skF_4'(A_4620, '#skF_5', C_4621), '#skF_7') | ~r2_hidden(A_4620, a_2_1_lattice3('#skF_5', C_4621)))), inference(demodulation, [status(thm), theory('equality')], [c_67839, c_67824])).
% 24.21/13.21  tff(c_67849, plain, (![A_64, C_66]: (r1_lattices('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_7') | ~r2_hidden(A_64, a_2_1_lattice3('#skF_5', C_66)) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_67842])).
% 24.21/13.21  tff(c_67854, plain, (![A_64, C_66]: (r1_lattices('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'(A_64, '#skF_5', C_66), '#skF_7') | ~r2_hidden(A_64, a_2_1_lattice3('#skF_5', C_66)) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_67849])).
% 24.21/13.21  tff(c_67890, plain, (![A_4623, C_4624]: (r1_lattices('#skF_5', '#skF_4'(A_4623, '#skF_5', C_4624), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'(A_4623, '#skF_5', C_4624), '#skF_7') | ~r2_hidden(A_4623, a_2_1_lattice3('#skF_5', C_4624)))), inference(negUnitSimplification, [status(thm)], [c_64, c_67854])).
% 24.21/13.21  tff(c_67897, plain, (![A_64]: (r1_lattices('#skF_5', '#skF_4'(A_64, '#skF_5', '#skF_7'), '#skF_6') | ~r2_hidden(A_64, a_2_1_lattice3('#skF_5', '#skF_7')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_67890])).
% 24.21/13.21  tff(c_67902, plain, (![A_64]: (r1_lattices('#skF_5', '#skF_4'(A_64, '#skF_5', '#skF_7'), '#skF_6') | ~r2_hidden(A_64, a_2_1_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_67897])).
% 24.21/13.21  tff(c_67903, plain, (![A_64]: (r1_lattices('#skF_5', '#skF_4'(A_64, '#skF_5', '#skF_7'), '#skF_6') | ~r2_hidden(A_64, a_2_1_lattice3('#skF_5', '#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_64, c_67902])).
% 24.21/13.21  tff(c_68242, plain, (![A_4683, B_4684]: (r1_lattices('#skF_5', '#skF_2'(A_4683, B_4684, a_2_1_lattice3('#skF_5', '#skF_7')), '#skF_6') | ~r2_hidden('#skF_2'(A_4683, B_4684, a_2_1_lattice3('#skF_5', '#skF_7')), a_2_1_lattice3('#skF_5', '#skF_7')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | r4_lattice3(A_4683, B_4684, a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_4684, u1_struct_0(A_4683)) | ~l3_lattices(A_4683) | v2_struct_0(A_4683))), inference(superposition, [status(thm), theory('equality')], [c_68228, c_67903])).
% 24.21/13.21  tff(c_68265, plain, (![A_4683, B_4684]: (r1_lattices('#skF_5', '#skF_2'(A_4683, B_4684, a_2_1_lattice3('#skF_5', '#skF_7')), '#skF_6') | ~r2_hidden('#skF_2'(A_4683, B_4684, a_2_1_lattice3('#skF_5', '#skF_7')), a_2_1_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5') | r4_lattice3(A_4683, B_4684, a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_4684, u1_struct_0(A_4683)) | ~l3_lattices(A_4683) | v2_struct_0(A_4683))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_68242])).
% 24.21/13.21  tff(c_68330, plain, (![A_4695, B_4696]: (r1_lattices('#skF_5', '#skF_2'(A_4695, B_4696, a_2_1_lattice3('#skF_5', '#skF_7')), '#skF_6') | ~r2_hidden('#skF_2'(A_4695, B_4696, a_2_1_lattice3('#skF_5', '#skF_7')), a_2_1_lattice3('#skF_5', '#skF_7')) | r4_lattice3(A_4695, B_4696, a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_4696, u1_struct_0(A_4695)) | ~l3_lattices(A_4695) | v2_struct_0(A_4695))), inference(negUnitSimplification, [status(thm)], [c_64, c_68265])).
% 24.21/13.21  tff(c_68343, plain, (![A_4697, B_4698]: (r1_lattices('#skF_5', '#skF_2'(A_4697, B_4698, a_2_1_lattice3('#skF_5', '#skF_7')), '#skF_6') | r4_lattice3(A_4697, B_4698, a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_4698, u1_struct_0(A_4697)) | ~l3_lattices(A_4697) | v2_struct_0(A_4697))), inference(resolution, [status(thm)], [c_32, c_68330])).
% 24.21/13.21  tff(c_68347, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_68343, c_30])).
% 24.21/13.21  tff(c_68350, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_68347])).
% 24.21/13.21  tff(c_68351, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_64, c_68350])).
% 24.21/13.21  tff(c_67745, plain, (![A_4604, D_4605, B_4606, C_4607]: (r1_lattices(A_4604, D_4605, B_4606) | ~r2_hidden(D_4605, C_4607) | ~m1_subset_1(D_4605, u1_struct_0(A_4604)) | ~r4_lattice3(A_4604, B_4606, C_4607) | ~m1_subset_1(B_4606, u1_struct_0(A_4604)) | ~l3_lattices(A_4604) | v2_struct_0(A_4604))), inference(cnfTransformation, [status(thm)], [f_102])).
% 24.21/13.21  tff(c_68603, plain, (![C_4726, A_4728, D_4729, B_4727, B_4725]: (r1_lattices(A_4728, D_4729, B_4727) | ~m1_subset_1(D_4729, u1_struct_0(A_4728)) | ~r4_lattice3(A_4728, B_4727, a_2_1_lattice3(B_4725, C_4726)) | ~m1_subset_1(B_4727, u1_struct_0(A_4728)) | ~l3_lattices(A_4728) | v2_struct_0(A_4728) | ~r3_lattice3(B_4725, D_4729, C_4726) | ~m1_subset_1(D_4729, u1_struct_0(B_4725)) | ~l3_lattices(B_4725) | v2_struct_0(B_4725))), inference(resolution, [status(thm)], [c_48, c_67745])).
% 24.21/13.21  tff(c_68613, plain, (![B_4727, B_4725, C_4726]: (r1_lattices('#skF_5', '#skF_6', B_4727) | ~r4_lattice3('#skF_5', B_4727, a_2_1_lattice3(B_4725, C_4726)) | ~m1_subset_1(B_4727, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r3_lattice3(B_4725, '#skF_6', C_4726) | ~m1_subset_1('#skF_6', u1_struct_0(B_4725)) | ~l3_lattices(B_4725) | v2_struct_0(B_4725))), inference(resolution, [status(thm)], [c_56, c_68603])).
% 24.21/13.21  tff(c_68620, plain, (![B_4727, B_4725, C_4726]: (r1_lattices('#skF_5', '#skF_6', B_4727) | ~r4_lattice3('#skF_5', B_4727, a_2_1_lattice3(B_4725, C_4726)) | ~m1_subset_1(B_4727, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5') | ~r3_lattice3(B_4725, '#skF_6', C_4726) | ~m1_subset_1('#skF_6', u1_struct_0(B_4725)) | ~l3_lattices(B_4725) | v2_struct_0(B_4725))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_68613])).
% 24.21/13.21  tff(c_68622, plain, (![B_4730, B_4731, C_4732]: (r1_lattices('#skF_5', '#skF_6', B_4730) | ~r4_lattice3('#skF_5', B_4730, a_2_1_lattice3(B_4731, C_4732)) | ~m1_subset_1(B_4730, u1_struct_0('#skF_5')) | ~r3_lattice3(B_4731, '#skF_6', C_4732) | ~m1_subset_1('#skF_6', u1_struct_0(B_4731)) | ~l3_lattices(B_4731) | v2_struct_0(B_4731))), inference(negUnitSimplification, [status(thm)], [c_64, c_68620])).
% 24.21/13.21  tff(c_68637, plain, (![B_4731, C_4732, C_57]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3(B_4731, C_4732), C_57)) | ~m1_subset_1('#skF_3'('#skF_5', a_2_1_lattice3(B_4731, C_4732), C_57), u1_struct_0('#skF_5')) | ~r3_lattice3(B_4731, '#skF_6', C_4732) | ~m1_subset_1('#skF_6', u1_struct_0(B_4731)) | ~l3_lattices(B_4731) | v2_struct_0(B_4731) | k15_lattice3('#skF_5', a_2_1_lattice3(B_4731, C_4732))=C_57 | ~r4_lattice3('#skF_5', C_57, a_2_1_lattice3(B_4731, C_4732)) | ~m1_subset_1(C_57, u1_struct_0('#skF_5')) | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_68622])).
% 24.21/13.21  tff(c_68652, plain, (![B_4731, C_4732, C_57]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3(B_4731, C_4732), C_57)) | ~m1_subset_1('#skF_3'('#skF_5', a_2_1_lattice3(B_4731, C_4732), C_57), u1_struct_0('#skF_5')) | ~r3_lattice3(B_4731, '#skF_6', C_4732) | ~m1_subset_1('#skF_6', u1_struct_0(B_4731)) | ~l3_lattices(B_4731) | v2_struct_0(B_4731) | k15_lattice3('#skF_5', a_2_1_lattice3(B_4731, C_4732))=C_57 | ~r4_lattice3('#skF_5', C_57, a_2_1_lattice3(B_4731, C_4732)) | ~m1_subset_1(C_57, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_60, c_68637])).
% 24.21/13.21  tff(c_72273, plain, (![B_5128, C_5129, C_5130]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3(B_5128, C_5129), C_5130)) | ~m1_subset_1('#skF_3'('#skF_5', a_2_1_lattice3(B_5128, C_5129), C_5130), u1_struct_0('#skF_5')) | ~r3_lattice3(B_5128, '#skF_6', C_5129) | ~m1_subset_1('#skF_6', u1_struct_0(B_5128)) | ~l3_lattices(B_5128) | v2_struct_0(B_5128) | k15_lattice3('#skF_5', a_2_1_lattice3(B_5128, C_5129))=C_5130 | ~r4_lattice3('#skF_5', C_5130, a_2_1_lattice3(B_5128, C_5129)) | ~m1_subset_1(C_5130, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_68652])).
% 24.21/13.21  tff(c_72277, plain, (![B_5128, C_5129, C_57]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3(B_5128, C_5129), C_57)) | ~r3_lattice3(B_5128, '#skF_6', C_5129) | ~m1_subset_1('#skF_6', u1_struct_0(B_5128)) | ~l3_lattices(B_5128) | v2_struct_0(B_5128) | k15_lattice3('#skF_5', a_2_1_lattice3(B_5128, C_5129))=C_57 | ~r4_lattice3('#skF_5', C_57, a_2_1_lattice3(B_5128, C_5129)) | ~m1_subset_1(C_57, u1_struct_0('#skF_5')) | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_72273])).
% 24.21/13.21  tff(c_72280, plain, (![B_5128, C_5129, C_57]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3(B_5128, C_5129), C_57)) | ~r3_lattice3(B_5128, '#skF_6', C_5129) | ~m1_subset_1('#skF_6', u1_struct_0(B_5128)) | ~l3_lattices(B_5128) | v2_struct_0(B_5128) | k15_lattice3('#skF_5', a_2_1_lattice3(B_5128, C_5129))=C_57 | ~r4_lattice3('#skF_5', C_57, a_2_1_lattice3(B_5128, C_5129)) | ~m1_subset_1(C_57, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_60, c_72277])).
% 24.21/13.21  tff(c_72282, plain, (![B_5131, C_5132, C_5133]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3(B_5131, C_5132), C_5133)) | ~r3_lattice3(B_5131, '#skF_6', C_5132) | ~m1_subset_1('#skF_6', u1_struct_0(B_5131)) | ~l3_lattices(B_5131) | v2_struct_0(B_5131) | k15_lattice3('#skF_5', a_2_1_lattice3(B_5131, C_5132))=C_5133 | ~r4_lattice3('#skF_5', C_5133, a_2_1_lattice3(B_5131, C_5132)) | ~m1_subset_1(C_5133, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_72280])).
% 24.21/13.21  tff(c_72286, plain, (![B_5131, C_5132]: (~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r3_lattice3(B_5131, '#skF_6', C_5132) | ~m1_subset_1('#skF_6', u1_struct_0(B_5131)) | ~l3_lattices(B_5131) | v2_struct_0(B_5131) | k15_lattice3('#skF_5', a_2_1_lattice3(B_5131, C_5132))='#skF_6' | ~r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3(B_5131, C_5132)) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_72282, c_36])).
% 24.21/13.21  tff(c_72289, plain, (![B_5131, C_5132]: (v2_struct_0('#skF_5') | ~r3_lattice3(B_5131, '#skF_6', C_5132) | ~m1_subset_1('#skF_6', u1_struct_0(B_5131)) | ~l3_lattices(B_5131) | v2_struct_0(B_5131) | k15_lattice3('#skF_5', a_2_1_lattice3(B_5131, C_5132))='#skF_6' | ~r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3(B_5131, C_5132)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_62, c_60, c_72286])).
% 24.21/13.21  tff(c_72291, plain, (![B_5134, C_5135]: (~r3_lattice3(B_5134, '#skF_6', C_5135) | ~m1_subset_1('#skF_6', u1_struct_0(B_5134)) | ~l3_lattices(B_5134) | v2_struct_0(B_5134) | k15_lattice3('#skF_5', a_2_1_lattice3(B_5134, C_5135))='#skF_6' | ~r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3(B_5134, C_5135)))), inference(negUnitSimplification, [status(thm)], [c_64, c_72289])).
% 24.21/13.21  tff(c_72297, plain, (~r3_lattice3('#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_7'))='#skF_6'), inference(resolution, [status(thm)], [c_68351, c_72291])).
% 24.21/13.21  tff(c_72304, plain, (v2_struct_0('#skF_5') | k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_7'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_67633, c_72297])).
% 24.21/13.21  tff(c_72305, plain, (k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_7'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_64, c_72304])).
% 24.21/13.21  tff(c_72331, plain, (k16_lattice3('#skF_5', '#skF_7')='#skF_6' | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_72305, c_46])).
% 24.21/13.21  tff(c_72361, plain, (k16_lattice3('#skF_5', '#skF_7')='#skF_6' | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_72331])).
% 24.21/13.21  tff(c_72363, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_67635, c_72361])).
% 24.21/13.21  tff(c_72364, plain, (k16_lattice3('#skF_5', '#skF_8')='#skF_6'), inference(splitRight, [status(thm)], [c_84])).
% 24.21/13.21  tff(c_72366, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67634, c_72364])).
% 24.21/13.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.21/13.21  
% 24.21/13.21  Inference rules
% 24.21/13.21  ----------------------
% 24.21/13.21  #Ref     : 0
% 24.21/13.21  #Sup     : 13545
% 24.21/13.21  #Fact    : 0
% 24.21/13.21  #Define  : 0
% 24.21/13.21  #Split   : 109
% 24.21/13.21  #Chain   : 0
% 24.21/13.21  #Close   : 0
% 24.21/13.21  
% 24.21/13.21  Ordering : KBO
% 24.21/13.21  
% 24.21/13.21  Simplification rules
% 24.21/13.21  ----------------------
% 24.21/13.21  #Subsume      : 4583
% 24.21/13.21  #Demod        : 25205
% 24.21/13.21  #Tautology    : 3349
% 24.21/13.21  #SimpNegUnit  : 5361
% 24.21/13.21  #BackRed      : 350
% 24.21/13.21  
% 24.21/13.21  #Partial instantiations: 0
% 24.21/13.21  #Strategies tried      : 1
% 24.21/13.21  
% 24.21/13.21  Timing (in seconds)
% 24.21/13.21  ----------------------
% 24.21/13.22  Preprocessing        : 0.37
% 24.21/13.22  Parsing              : 0.18
% 24.21/13.22  CNF conversion       : 0.03
% 24.21/13.22  Main loop            : 11.93
% 24.21/13.22  Inferencing          : 4.07
% 24.21/13.22  Reduction            : 3.87
% 24.21/13.22  Demodulation         : 2.80
% 24.21/13.22  BG Simplification    : 0.27
% 24.21/13.22  Subsumption          : 3.05
% 24.21/13.22  Abstraction          : 0.47
% 24.21/13.22  MUC search           : 0.00
% 24.21/13.22  Cooper               : 0.00
% 24.21/13.22  Total                : 12.48
% 24.21/13.22  Index Insertion      : 0.00
% 24.21/13.22  Index Deletion       : 0.00
% 24.21/13.22  Index Matching       : 0.00
% 24.21/13.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
