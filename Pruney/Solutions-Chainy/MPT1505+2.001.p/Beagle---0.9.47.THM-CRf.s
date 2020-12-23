%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:45 EST 2020

% Result     : Theorem 5.05s
% Output     : CNFRefutation 5.19s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 366 expanded)
%              Number of leaves         :   41 ( 144 expanded)
%              Depth                    :   13
%              Number of atoms          :  425 (1653 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_4 > #skF_6 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k16_lattice3,type,(
    k16_lattice3: ( $i * $i ) > $i )).

tff(k15_lattice3,type,(
    k15_lattice3: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

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

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r3_lattice3,type,(
    r3_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_201,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( r2_hidden(B,C)
               => ( r3_lattices(A,B,k15_lattice3(A,C))
                  & r3_lattices(A,k16_lattice3(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).

tff(f_157,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k16_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).

tff(f_181,axiom,(
    ! [A] :
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

tff(f_122,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v4_lattice3(A)
      <=> ! [B] :
          ? [C] :
            ( m1_subset_1(C,u1_struct_0(A))
            & r4_lattice3(A,C,B)
            & ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r4_lattice3(A,D,B)
                 => r1_lattices(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_lattice3)).

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

tff(f_150,axiom,(
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

tff(c_82,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_76,plain,(
    l3_lattices('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_80,plain,(
    v10_lattices('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_78,plain,(
    v4_lattice3('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_58,plain,(
    ! [A_87,B_88] :
      ( m1_subset_1(k16_lattice3(A_87,B_88),u1_struct_0(A_87))
      | ~ l3_lattices(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_762,plain,(
    ! [A_355,C_356] :
      ( r3_lattice3(A_355,k16_lattice3(A_355,C_356),C_356)
      | ~ m1_subset_1(k16_lattice3(A_355,C_356),u1_struct_0(A_355))
      | ~ l3_lattices(A_355)
      | ~ v4_lattice3(A_355)
      | ~ v10_lattices(A_355)
      | v2_struct_0(A_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_765,plain,(
    ! [A_87,B_88] :
      ( r3_lattice3(A_87,k16_lattice3(A_87,B_88),B_88)
      | ~ v4_lattice3(A_87)
      | ~ v10_lattices(A_87)
      | ~ l3_lattices(A_87)
      | v2_struct_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_58,c_762])).

tff(c_74,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_72,plain,(
    r2_hidden('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_774,plain,(
    ! [A_365,B_366,D_367,C_368] :
      ( r1_lattices(A_365,B_366,D_367)
      | ~ r2_hidden(D_367,C_368)
      | ~ m1_subset_1(D_367,u1_struct_0(A_365))
      | ~ r3_lattice3(A_365,B_366,C_368)
      | ~ m1_subset_1(B_366,u1_struct_0(A_365))
      | ~ l3_lattices(A_365)
      | v2_struct_0(A_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_784,plain,(
    ! [A_369,B_370] :
      ( r1_lattices(A_369,B_370,'#skF_9')
      | ~ m1_subset_1('#skF_9',u1_struct_0(A_369))
      | ~ r3_lattice3(A_369,B_370,'#skF_10')
      | ~ m1_subset_1(B_370,u1_struct_0(A_369))
      | ~ l3_lattices(A_369)
      | v2_struct_0(A_369) ) ),
    inference(resolution,[status(thm)],[c_72,c_774])).

tff(c_786,plain,(
    ! [B_370] :
      ( r1_lattices('#skF_8',B_370,'#skF_9')
      | ~ r3_lattice3('#skF_8',B_370,'#skF_10')
      | ~ m1_subset_1(B_370,u1_struct_0('#skF_8'))
      | ~ l3_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_74,c_784])).

tff(c_789,plain,(
    ! [B_370] :
      ( r1_lattices('#skF_8',B_370,'#skF_9')
      | ~ r3_lattice3('#skF_8',B_370,'#skF_10')
      | ~ m1_subset_1(B_370,u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_786])).

tff(c_791,plain,(
    ! [B_371] :
      ( r1_lattices('#skF_8',B_371,'#skF_9')
      | ~ r3_lattice3('#skF_8',B_371,'#skF_10')
      | ~ m1_subset_1(B_371,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_789])).

tff(c_811,plain,(
    ! [B_88] :
      ( r1_lattices('#skF_8',k16_lattice3('#skF_8',B_88),'#skF_9')
      | ~ r3_lattice3('#skF_8',k16_lattice3('#skF_8',B_88),'#skF_10')
      | ~ l3_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_58,c_791])).

tff(c_833,plain,(
    ! [B_88] :
      ( r1_lattices('#skF_8',k16_lattice3('#skF_8',B_88),'#skF_9')
      | ~ r3_lattice3('#skF_8',k16_lattice3('#skF_8',B_88),'#skF_10')
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_811])).

tff(c_847,plain,(
    ! [B_376] :
      ( r1_lattices('#skF_8',k16_lattice3('#skF_8',B_376),'#skF_9')
      | ~ r3_lattice3('#skF_8',k16_lattice3('#skF_8',B_376),'#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_833])).

tff(c_851,plain,
    ( r1_lattices('#skF_8',k16_lattice3('#skF_8','#skF_10'),'#skF_9')
    | ~ v4_lattice3('#skF_8')
    | ~ v10_lattices('#skF_8')
    | ~ l3_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_765,c_847])).

tff(c_854,plain,
    ( r1_lattices('#skF_8',k16_lattice3('#skF_8','#skF_10'),'#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_80,c_78,c_851])).

tff(c_855,plain,(
    r1_lattices('#skF_8',k16_lattice3('#skF_8','#skF_10'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_854])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_910,plain,(
    ! [A_381,B_382,C_383] :
      ( r3_lattices(A_381,B_382,C_383)
      | ~ r1_lattices(A_381,B_382,C_383)
      | ~ m1_subset_1(C_383,u1_struct_0(A_381))
      | ~ m1_subset_1(B_382,u1_struct_0(A_381))
      | ~ l3_lattices(A_381)
      | ~ v9_lattices(A_381)
      | ~ v8_lattices(A_381)
      | ~ v6_lattices(A_381)
      | v2_struct_0(A_381) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_922,plain,(
    ! [B_382] :
      ( r3_lattices('#skF_8',B_382,'#skF_9')
      | ~ r1_lattices('#skF_8',B_382,'#skF_9')
      | ~ m1_subset_1(B_382,u1_struct_0('#skF_8'))
      | ~ l3_lattices('#skF_8')
      | ~ v9_lattices('#skF_8')
      | ~ v8_lattices('#skF_8')
      | ~ v6_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_74,c_910])).

tff(c_930,plain,(
    ! [B_382] :
      ( r3_lattices('#skF_8',B_382,'#skF_9')
      | ~ r1_lattices('#skF_8',B_382,'#skF_9')
      | ~ m1_subset_1(B_382,u1_struct_0('#skF_8'))
      | ~ v9_lattices('#skF_8')
      | ~ v8_lattices('#skF_8')
      | ~ v6_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_922])).

tff(c_931,plain,(
    ! [B_382] :
      ( r3_lattices('#skF_8',B_382,'#skF_9')
      | ~ r1_lattices('#skF_8',B_382,'#skF_9')
      | ~ m1_subset_1(B_382,u1_struct_0('#skF_8'))
      | ~ v9_lattices('#skF_8')
      | ~ v8_lattices('#skF_8')
      | ~ v6_lattices('#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_930])).

tff(c_942,plain,(
    ~ v6_lattices('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_931])).

tff(c_945,plain,
    ( ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ l3_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_8,c_942])).

tff(c_948,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_80,c_945])).

tff(c_950,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_948])).

tff(c_951,plain,(
    ! [B_382] :
      ( ~ v8_lattices('#skF_8')
      | ~ v9_lattices('#skF_8')
      | r3_lattices('#skF_8',B_382,'#skF_9')
      | ~ r1_lattices('#skF_8',B_382,'#skF_9')
      | ~ m1_subset_1(B_382,u1_struct_0('#skF_8')) ) ),
    inference(splitRight,[status(thm)],[c_931])).

tff(c_953,plain,(
    ~ v9_lattices('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_951])).

tff(c_956,plain,
    ( ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ l3_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_2,c_953])).

tff(c_959,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_80,c_956])).

tff(c_961,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_959])).

tff(c_962,plain,(
    ! [B_382] :
      ( ~ v8_lattices('#skF_8')
      | r3_lattices('#skF_8',B_382,'#skF_9')
      | ~ r1_lattices('#skF_8',B_382,'#skF_9')
      | ~ m1_subset_1(B_382,u1_struct_0('#skF_8')) ) ),
    inference(splitRight,[status(thm)],[c_951])).

tff(c_971,plain,(
    ~ v8_lattices('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_962])).

tff(c_974,plain,
    ( ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ l3_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_971])).

tff(c_977,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_80,c_974])).

tff(c_979,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_977])).

tff(c_985,plain,(
    ! [B_389] :
      ( r3_lattices('#skF_8',B_389,'#skF_9')
      | ~ r1_lattices('#skF_8',B_389,'#skF_9')
      | ~ m1_subset_1(B_389,u1_struct_0('#skF_8')) ) ),
    inference(splitRight,[status(thm)],[c_962])).

tff(c_1005,plain,(
    ! [B_88] :
      ( r3_lattices('#skF_8',k16_lattice3('#skF_8',B_88),'#skF_9')
      | ~ r1_lattices('#skF_8',k16_lattice3('#skF_8',B_88),'#skF_9')
      | ~ l3_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_58,c_985])).

tff(c_1027,plain,(
    ! [B_88] :
      ( r3_lattices('#skF_8',k16_lattice3('#skF_8',B_88),'#skF_9')
      | ~ r1_lattices('#skF_8',k16_lattice3('#skF_8',B_88),'#skF_9')
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1005])).

tff(c_1066,plain,(
    ! [B_394] :
      ( r3_lattices('#skF_8',k16_lattice3('#skF_8',B_394),'#skF_9')
      | ~ r1_lattices('#skF_8',k16_lattice3('#skF_8',B_394),'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1027])).

tff(c_269,plain,(
    ! [A_189,B_190,C_191] :
      ( r3_lattices(A_189,B_190,C_191)
      | ~ r1_lattices(A_189,B_190,C_191)
      | ~ m1_subset_1(C_191,u1_struct_0(A_189))
      | ~ m1_subset_1(B_190,u1_struct_0(A_189))
      | ~ l3_lattices(A_189)
      | ~ v9_lattices(A_189)
      | ~ v8_lattices(A_189)
      | ~ v6_lattices(A_189)
      | v2_struct_0(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_281,plain,(
    ! [B_190] :
      ( r3_lattices('#skF_8',B_190,'#skF_9')
      | ~ r1_lattices('#skF_8',B_190,'#skF_9')
      | ~ m1_subset_1(B_190,u1_struct_0('#skF_8'))
      | ~ l3_lattices('#skF_8')
      | ~ v9_lattices('#skF_8')
      | ~ v8_lattices('#skF_8')
      | ~ v6_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_74,c_269])).

tff(c_289,plain,(
    ! [B_190] :
      ( r3_lattices('#skF_8',B_190,'#skF_9')
      | ~ r1_lattices('#skF_8',B_190,'#skF_9')
      | ~ m1_subset_1(B_190,u1_struct_0('#skF_8'))
      | ~ v9_lattices('#skF_8')
      | ~ v8_lattices('#skF_8')
      | ~ v6_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_281])).

tff(c_290,plain,(
    ! [B_190] :
      ( r3_lattices('#skF_8',B_190,'#skF_9')
      | ~ r1_lattices('#skF_8',B_190,'#skF_9')
      | ~ m1_subset_1(B_190,u1_struct_0('#skF_8'))
      | ~ v9_lattices('#skF_8')
      | ~ v8_lattices('#skF_8')
      | ~ v6_lattices('#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_289])).

tff(c_291,plain,(
    ~ v6_lattices('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_290])).

tff(c_294,plain,
    ( ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ l3_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_8,c_291])).

tff(c_297,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_80,c_294])).

tff(c_299,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_297])).

tff(c_301,plain,(
    v6_lattices('#skF_8') ),
    inference(splitRight,[status(thm)],[c_290])).

tff(c_300,plain,(
    ! [B_190] :
      ( ~ v8_lattices('#skF_8')
      | ~ v9_lattices('#skF_8')
      | r3_lattices('#skF_8',B_190,'#skF_9')
      | ~ r1_lattices('#skF_8',B_190,'#skF_9')
      | ~ m1_subset_1(B_190,u1_struct_0('#skF_8')) ) ),
    inference(splitRight,[status(thm)],[c_290])).

tff(c_322,plain,(
    ~ v9_lattices('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_300])).

tff(c_325,plain,
    ( ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ l3_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_2,c_322])).

tff(c_328,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_80,c_325])).

tff(c_330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_328])).

tff(c_331,plain,(
    ! [B_190] :
      ( ~ v8_lattices('#skF_8')
      | r3_lattices('#skF_8',B_190,'#skF_9')
      | ~ r1_lattices('#skF_8',B_190,'#skF_9')
      | ~ m1_subset_1(B_190,u1_struct_0('#skF_8')) ) ),
    inference(splitRight,[status(thm)],[c_300])).

tff(c_334,plain,(
    ~ v8_lattices('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_331])).

tff(c_337,plain,
    ( ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ l3_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_334])).

tff(c_340,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_80,c_337])).

tff(c_342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_340])).

tff(c_344,plain,(
    v8_lattices('#skF_8') ),
    inference(splitRight,[status(thm)],[c_331])).

tff(c_332,plain,(
    v9_lattices('#skF_8') ),
    inference(splitRight,[status(thm)],[c_300])).

tff(c_44,plain,(
    ! [A_49,B_64] :
      ( r4_lattice3(A_49,'#skF_3'(A_49,B_64),B_64)
      | ~ v4_lattice3(A_49)
      | ~ l3_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_46,plain,(
    ! [A_49,B_64] :
      ( m1_subset_1('#skF_3'(A_49,B_64),u1_struct_0(A_49))
      | ~ v4_lattice3(A_49)
      | ~ l3_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_118,plain,(
    ! [A_160,D_161,B_162,C_163] :
      ( r1_lattices(A_160,D_161,B_162)
      | ~ r2_hidden(D_161,C_163)
      | ~ m1_subset_1(D_161,u1_struct_0(A_160))
      | ~ r4_lattice3(A_160,B_162,C_163)
      | ~ m1_subset_1(B_162,u1_struct_0(A_160))
      | ~ l3_lattices(A_160)
      | v2_struct_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_128,plain,(
    ! [A_164,B_165] :
      ( r1_lattices(A_164,'#skF_9',B_165)
      | ~ m1_subset_1('#skF_9',u1_struct_0(A_164))
      | ~ r4_lattice3(A_164,B_165,'#skF_10')
      | ~ m1_subset_1(B_165,u1_struct_0(A_164))
      | ~ l3_lattices(A_164)
      | v2_struct_0(A_164) ) ),
    inference(resolution,[status(thm)],[c_72,c_118])).

tff(c_130,plain,(
    ! [B_165] :
      ( r1_lattices('#skF_8','#skF_9',B_165)
      | ~ r4_lattice3('#skF_8',B_165,'#skF_10')
      | ~ m1_subset_1(B_165,u1_struct_0('#skF_8'))
      | ~ l3_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_74,c_128])).

tff(c_133,plain,(
    ! [B_165] :
      ( r1_lattices('#skF_8','#skF_9',B_165)
      | ~ r4_lattice3('#skF_8',B_165,'#skF_10')
      | ~ m1_subset_1(B_165,u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_130])).

tff(c_135,plain,(
    ! [B_166] :
      ( r1_lattices('#skF_8','#skF_9',B_166)
      | ~ r4_lattice3('#skF_8',B_166,'#skF_10')
      | ~ m1_subset_1(B_166,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_133])).

tff(c_151,plain,(
    ! [B_64] :
      ( r1_lattices('#skF_8','#skF_9','#skF_3'('#skF_8',B_64))
      | ~ r4_lattice3('#skF_8','#skF_3'('#skF_8',B_64),'#skF_10')
      | ~ v4_lattice3('#skF_8')
      | ~ l3_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_46,c_135])).

tff(c_173,plain,(
    ! [B_64] :
      ( r1_lattices('#skF_8','#skF_9','#skF_3'('#skF_8',B_64))
      | ~ r4_lattice3('#skF_8','#skF_3'('#skF_8',B_64),'#skF_10')
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_78,c_151])).

tff(c_191,plain,(
    ! [B_171] :
      ( r1_lattices('#skF_8','#skF_9','#skF_3'('#skF_8',B_171))
      | ~ r4_lattice3('#skF_8','#skF_3'('#skF_8',B_171),'#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_173])).

tff(c_195,plain,
    ( r1_lattices('#skF_8','#skF_9','#skF_3'('#skF_8','#skF_10'))
    | ~ v4_lattice3('#skF_8')
    | ~ l3_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_44,c_191])).

tff(c_198,plain,
    ( r1_lattices('#skF_8','#skF_9','#skF_3'('#skF_8','#skF_10'))
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_78,c_195])).

tff(c_199,plain,(
    r1_lattices('#skF_8','#skF_9','#skF_3'('#skF_8','#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_198])).

tff(c_285,plain,(
    ! [A_49,B_190,B_64] :
      ( r3_lattices(A_49,B_190,'#skF_3'(A_49,B_64))
      | ~ r1_lattices(A_49,B_190,'#skF_3'(A_49,B_64))
      | ~ m1_subset_1(B_190,u1_struct_0(A_49))
      | ~ v9_lattices(A_49)
      | ~ v8_lattices(A_49)
      | ~ v6_lattices(A_49)
      | ~ v4_lattice3(A_49)
      | ~ l3_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_46,c_269])).

tff(c_52,plain,(
    ! [A_75,B_82,C_83] :
      ( m1_subset_1('#skF_6'(A_75,B_82,C_83),u1_struct_0(A_75))
      | k15_lattice3(A_75,B_82) = C_83
      | ~ r4_lattice3(A_75,C_83,B_82)
      | ~ m1_subset_1(C_83,u1_struct_0(A_75))
      | ~ v4_lattice3(A_75)
      | ~ v10_lattices(A_75)
      | ~ l3_lattices(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_50,plain,(
    ! [A_75,B_82,C_83] :
      ( r4_lattice3(A_75,'#skF_6'(A_75,B_82,C_83),B_82)
      | k15_lattice3(A_75,B_82) = C_83
      | ~ r4_lattice3(A_75,C_83,B_82)
      | ~ m1_subset_1(C_83,u1_struct_0(A_75))
      | ~ v4_lattice3(A_75)
      | ~ v10_lattices(A_75)
      | ~ l3_lattices(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_42,plain,(
    ! [A_49,B_64,D_69] :
      ( r1_lattices(A_49,'#skF_3'(A_49,B_64),D_69)
      | ~ r4_lattice3(A_49,D_69,B_64)
      | ~ m1_subset_1(D_69,u1_struct_0(A_49))
      | ~ v4_lattice3(A_49)
      | ~ l3_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_445,plain,(
    ! [A_214,C_215,B_216] :
      ( ~ r1_lattices(A_214,C_215,'#skF_6'(A_214,B_216,C_215))
      | k15_lattice3(A_214,B_216) = C_215
      | ~ r4_lattice3(A_214,C_215,B_216)
      | ~ m1_subset_1(C_215,u1_struct_0(A_214))
      | ~ v4_lattice3(A_214)
      | ~ v10_lattices(A_214)
      | ~ l3_lattices(A_214)
      | v2_struct_0(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_673,plain,(
    ! [A_307,B_308,B_309] :
      ( k15_lattice3(A_307,B_308) = '#skF_3'(A_307,B_309)
      | ~ r4_lattice3(A_307,'#skF_3'(A_307,B_309),B_308)
      | ~ m1_subset_1('#skF_3'(A_307,B_309),u1_struct_0(A_307))
      | ~ v10_lattices(A_307)
      | ~ r4_lattice3(A_307,'#skF_6'(A_307,B_308,'#skF_3'(A_307,B_309)),B_309)
      | ~ m1_subset_1('#skF_6'(A_307,B_308,'#skF_3'(A_307,B_309)),u1_struct_0(A_307))
      | ~ v4_lattice3(A_307)
      | ~ l3_lattices(A_307)
      | v2_struct_0(A_307) ) ),
    inference(resolution,[status(thm)],[c_42,c_445])).

tff(c_678,plain,(
    ! [A_310,B_311] :
      ( ~ m1_subset_1('#skF_6'(A_310,B_311,'#skF_3'(A_310,B_311)),u1_struct_0(A_310))
      | k15_lattice3(A_310,B_311) = '#skF_3'(A_310,B_311)
      | ~ r4_lattice3(A_310,'#skF_3'(A_310,B_311),B_311)
      | ~ m1_subset_1('#skF_3'(A_310,B_311),u1_struct_0(A_310))
      | ~ v4_lattice3(A_310)
      | ~ v10_lattices(A_310)
      | ~ l3_lattices(A_310)
      | v2_struct_0(A_310) ) ),
    inference(resolution,[status(thm)],[c_50,c_673])).

tff(c_693,plain,(
    ! [A_316,B_317] :
      ( k15_lattice3(A_316,B_317) = '#skF_3'(A_316,B_317)
      | ~ r4_lattice3(A_316,'#skF_3'(A_316,B_317),B_317)
      | ~ m1_subset_1('#skF_3'(A_316,B_317),u1_struct_0(A_316))
      | ~ v4_lattice3(A_316)
      | ~ v10_lattices(A_316)
      | ~ l3_lattices(A_316)
      | v2_struct_0(A_316) ) ),
    inference(resolution,[status(thm)],[c_52,c_678])).

tff(c_697,plain,(
    ! [A_318,B_319] :
      ( k15_lattice3(A_318,B_319) = '#skF_3'(A_318,B_319)
      | ~ m1_subset_1('#skF_3'(A_318,B_319),u1_struct_0(A_318))
      | ~ v10_lattices(A_318)
      | ~ v4_lattice3(A_318)
      | ~ l3_lattices(A_318)
      | v2_struct_0(A_318) ) ),
    inference(resolution,[status(thm)],[c_44,c_693])).

tff(c_702,plain,(
    ! [A_320,B_321] :
      ( k15_lattice3(A_320,B_321) = '#skF_3'(A_320,B_321)
      | ~ v10_lattices(A_320)
      | ~ v4_lattice3(A_320)
      | ~ l3_lattices(A_320)
      | v2_struct_0(A_320) ) ),
    inference(resolution,[status(thm)],[c_46,c_697])).

tff(c_704,plain,(
    ! [B_321] :
      ( k15_lattice3('#skF_8',B_321) = '#skF_3'('#skF_8',B_321)
      | ~ v10_lattices('#skF_8')
      | ~ l3_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_78,c_702])).

tff(c_707,plain,(
    ! [B_321] :
      ( k15_lattice3('#skF_8',B_321) = '#skF_3'('#skF_8',B_321)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_80,c_704])).

tff(c_708,plain,(
    ! [B_321] : k15_lattice3('#skF_8',B_321) = '#skF_3'('#skF_8',B_321) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_707])).

tff(c_70,plain,
    ( ~ r3_lattices('#skF_8',k16_lattice3('#skF_8','#skF_10'),'#skF_9')
    | ~ r3_lattices('#skF_8','#skF_9',k15_lattice3('#skF_8','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_86,plain,(
    ~ r3_lattices('#skF_8','#skF_9',k15_lattice3('#skF_8','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_713,plain,(
    ~ r3_lattices('#skF_8','#skF_9','#skF_3'('#skF_8','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_708,c_86])).

tff(c_735,plain,
    ( ~ r1_lattices('#skF_8','#skF_9','#skF_3'('#skF_8','#skF_10'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_8'))
    | ~ v9_lattices('#skF_8')
    | ~ v8_lattices('#skF_8')
    | ~ v6_lattices('#skF_8')
    | ~ v4_lattice3('#skF_8')
    | ~ l3_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_285,c_713])).

tff(c_738,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_78,c_301,c_344,c_332,c_74,c_199,c_735])).

tff(c_740,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_738])).

tff(c_741,plain,(
    ~ r3_lattices('#skF_8',k16_lattice3('#skF_8','#skF_10'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_1071,plain,(
    ~ r1_lattices('#skF_8',k16_lattice3('#skF_8','#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_1066,c_741])).

tff(c_1079,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_855,c_1071])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:54:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.05/2.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.19/2.16  
% 5.19/2.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.19/2.17  %$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_4 > #skF_6 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_5
% 5.19/2.17  
% 5.19/2.17  %Foreground sorts:
% 5.19/2.17  
% 5.19/2.17  
% 5.19/2.17  %Background operators:
% 5.19/2.17  
% 5.19/2.17  
% 5.19/2.17  %Foreground operators:
% 5.19/2.17  tff(l3_lattices, type, l3_lattices: $i > $o).
% 5.19/2.17  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.19/2.17  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.19/2.17  tff('#skF_4', type, '#skF_4': $i > $i).
% 5.19/2.17  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 5.19/2.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.19/2.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.19/2.17  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 5.19/2.17  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 5.19/2.17  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 5.19/2.17  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.19/2.17  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 5.19/2.17  tff('#skF_10', type, '#skF_10': $i).
% 5.19/2.17  tff(v4_lattices, type, v4_lattices: $i > $o).
% 5.19/2.17  tff(v6_lattices, type, v6_lattices: $i > $o).
% 5.19/2.17  tff(v9_lattices, type, v9_lattices: $i > $o).
% 5.19/2.17  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 5.19/2.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.19/2.17  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 5.19/2.17  tff(v5_lattices, type, v5_lattices: $i > $o).
% 5.19/2.17  tff(v10_lattices, type, v10_lattices: $i > $o).
% 5.19/2.17  tff('#skF_9', type, '#skF_9': $i).
% 5.19/2.17  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 5.19/2.17  tff('#skF_8', type, '#skF_8': $i).
% 5.19/2.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.19/2.17  tff(v8_lattices, type, v8_lattices: $i > $o).
% 5.19/2.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.19/2.17  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.19/2.17  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 5.19/2.17  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.19/2.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.19/2.17  tff(v7_lattices, type, v7_lattices: $i > $o).
% 5.19/2.17  
% 5.19/2.19  tff(f_201, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r2_hidden(B, C) => (r3_lattices(A, B, k15_lattice3(A, C)) & r3_lattices(A, k16_lattice3(A, C), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_lattice3)).
% 5.19/2.19  tff(f_157, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k16_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k16_lattice3)).
% 5.19/2.19  tff(f_181, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((B = k16_lattice3(A, C)) <=> (r3_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_lattice3(A, D, C) => r3_lattices(A, D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_lattice3)).
% 5.19/2.19  tff(f_84, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattice3)).
% 5.19/2.19  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 5.19/2.19  tff(f_66, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 5.19/2.19  tff(f_122, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v4_lattice3(A) <=> (![B]: (?[C]: ((m1_subset_1(C, u1_struct_0(A)) & r4_lattice3(A, C, B)) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_lattice3)).
% 5.19/2.19  tff(f_102, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 5.19/2.19  tff(f_150, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k15_lattice3(A, B)) <=> (r4_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d21_lattice3)).
% 5.19/2.19  tff(c_82, plain, (~v2_struct_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.19/2.19  tff(c_76, plain, (l3_lattices('#skF_8')), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.19/2.19  tff(c_80, plain, (v10_lattices('#skF_8')), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.19/2.19  tff(c_78, plain, (v4_lattice3('#skF_8')), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.19/2.19  tff(c_58, plain, (![A_87, B_88]: (m1_subset_1(k16_lattice3(A_87, B_88), u1_struct_0(A_87)) | ~l3_lattices(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.19/2.19  tff(c_762, plain, (![A_355, C_356]: (r3_lattice3(A_355, k16_lattice3(A_355, C_356), C_356) | ~m1_subset_1(k16_lattice3(A_355, C_356), u1_struct_0(A_355)) | ~l3_lattices(A_355) | ~v4_lattice3(A_355) | ~v10_lattices(A_355) | v2_struct_0(A_355))), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.19/2.19  tff(c_765, plain, (![A_87, B_88]: (r3_lattice3(A_87, k16_lattice3(A_87, B_88), B_88) | ~v4_lattice3(A_87) | ~v10_lattices(A_87) | ~l3_lattices(A_87) | v2_struct_0(A_87))), inference(resolution, [status(thm)], [c_58, c_762])).
% 5.19/2.19  tff(c_74, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.19/2.19  tff(c_72, plain, (r2_hidden('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.19/2.19  tff(c_774, plain, (![A_365, B_366, D_367, C_368]: (r1_lattices(A_365, B_366, D_367) | ~r2_hidden(D_367, C_368) | ~m1_subset_1(D_367, u1_struct_0(A_365)) | ~r3_lattice3(A_365, B_366, C_368) | ~m1_subset_1(B_366, u1_struct_0(A_365)) | ~l3_lattices(A_365) | v2_struct_0(A_365))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.19/2.19  tff(c_784, plain, (![A_369, B_370]: (r1_lattices(A_369, B_370, '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0(A_369)) | ~r3_lattice3(A_369, B_370, '#skF_10') | ~m1_subset_1(B_370, u1_struct_0(A_369)) | ~l3_lattices(A_369) | v2_struct_0(A_369))), inference(resolution, [status(thm)], [c_72, c_774])).
% 5.19/2.19  tff(c_786, plain, (![B_370]: (r1_lattices('#skF_8', B_370, '#skF_9') | ~r3_lattice3('#skF_8', B_370, '#skF_10') | ~m1_subset_1(B_370, u1_struct_0('#skF_8')) | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_74, c_784])).
% 5.19/2.19  tff(c_789, plain, (![B_370]: (r1_lattices('#skF_8', B_370, '#skF_9') | ~r3_lattice3('#skF_8', B_370, '#skF_10') | ~m1_subset_1(B_370, u1_struct_0('#skF_8')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_786])).
% 5.19/2.19  tff(c_791, plain, (![B_371]: (r1_lattices('#skF_8', B_371, '#skF_9') | ~r3_lattice3('#skF_8', B_371, '#skF_10') | ~m1_subset_1(B_371, u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_82, c_789])).
% 5.19/2.19  tff(c_811, plain, (![B_88]: (r1_lattices('#skF_8', k16_lattice3('#skF_8', B_88), '#skF_9') | ~r3_lattice3('#skF_8', k16_lattice3('#skF_8', B_88), '#skF_10') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_58, c_791])).
% 5.19/2.19  tff(c_833, plain, (![B_88]: (r1_lattices('#skF_8', k16_lattice3('#skF_8', B_88), '#skF_9') | ~r3_lattice3('#skF_8', k16_lattice3('#skF_8', B_88), '#skF_10') | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_811])).
% 5.19/2.19  tff(c_847, plain, (![B_376]: (r1_lattices('#skF_8', k16_lattice3('#skF_8', B_376), '#skF_9') | ~r3_lattice3('#skF_8', k16_lattice3('#skF_8', B_376), '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_82, c_833])).
% 5.19/2.19  tff(c_851, plain, (r1_lattices('#skF_8', k16_lattice3('#skF_8', '#skF_10'), '#skF_9') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_765, c_847])).
% 5.19/2.19  tff(c_854, plain, (r1_lattices('#skF_8', k16_lattice3('#skF_8', '#skF_10'), '#skF_9') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_80, c_78, c_851])).
% 5.19/2.19  tff(c_855, plain, (r1_lattices('#skF_8', k16_lattice3('#skF_8', '#skF_10'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_82, c_854])).
% 5.19/2.19  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.19/2.19  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.19/2.19  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.19/2.19  tff(c_910, plain, (![A_381, B_382, C_383]: (r3_lattices(A_381, B_382, C_383) | ~r1_lattices(A_381, B_382, C_383) | ~m1_subset_1(C_383, u1_struct_0(A_381)) | ~m1_subset_1(B_382, u1_struct_0(A_381)) | ~l3_lattices(A_381) | ~v9_lattices(A_381) | ~v8_lattices(A_381) | ~v6_lattices(A_381) | v2_struct_0(A_381))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.19/2.19  tff(c_922, plain, (![B_382]: (r3_lattices('#skF_8', B_382, '#skF_9') | ~r1_lattices('#skF_8', B_382, '#skF_9') | ~m1_subset_1(B_382, u1_struct_0('#skF_8')) | ~l3_lattices('#skF_8') | ~v9_lattices('#skF_8') | ~v8_lattices('#skF_8') | ~v6_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_74, c_910])).
% 5.19/2.19  tff(c_930, plain, (![B_382]: (r3_lattices('#skF_8', B_382, '#skF_9') | ~r1_lattices('#skF_8', B_382, '#skF_9') | ~m1_subset_1(B_382, u1_struct_0('#skF_8')) | ~v9_lattices('#skF_8') | ~v8_lattices('#skF_8') | ~v6_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_922])).
% 5.19/2.19  tff(c_931, plain, (![B_382]: (r3_lattices('#skF_8', B_382, '#skF_9') | ~r1_lattices('#skF_8', B_382, '#skF_9') | ~m1_subset_1(B_382, u1_struct_0('#skF_8')) | ~v9_lattices('#skF_8') | ~v8_lattices('#skF_8') | ~v6_lattices('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_82, c_930])).
% 5.19/2.19  tff(c_942, plain, (~v6_lattices('#skF_8')), inference(splitLeft, [status(thm)], [c_931])).
% 5.19/2.19  tff(c_945, plain, (~v10_lattices('#skF_8') | v2_struct_0('#skF_8') | ~l3_lattices('#skF_8')), inference(resolution, [status(thm)], [c_8, c_942])).
% 5.19/2.19  tff(c_948, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_80, c_945])).
% 5.19/2.19  tff(c_950, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_948])).
% 5.19/2.19  tff(c_951, plain, (![B_382]: (~v8_lattices('#skF_8') | ~v9_lattices('#skF_8') | r3_lattices('#skF_8', B_382, '#skF_9') | ~r1_lattices('#skF_8', B_382, '#skF_9') | ~m1_subset_1(B_382, u1_struct_0('#skF_8')))), inference(splitRight, [status(thm)], [c_931])).
% 5.19/2.19  tff(c_953, plain, (~v9_lattices('#skF_8')), inference(splitLeft, [status(thm)], [c_951])).
% 5.19/2.19  tff(c_956, plain, (~v10_lattices('#skF_8') | v2_struct_0('#skF_8') | ~l3_lattices('#skF_8')), inference(resolution, [status(thm)], [c_2, c_953])).
% 5.19/2.19  tff(c_959, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_80, c_956])).
% 5.19/2.19  tff(c_961, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_959])).
% 5.19/2.19  tff(c_962, plain, (![B_382]: (~v8_lattices('#skF_8') | r3_lattices('#skF_8', B_382, '#skF_9') | ~r1_lattices('#skF_8', B_382, '#skF_9') | ~m1_subset_1(B_382, u1_struct_0('#skF_8')))), inference(splitRight, [status(thm)], [c_951])).
% 5.19/2.19  tff(c_971, plain, (~v8_lattices('#skF_8')), inference(splitLeft, [status(thm)], [c_962])).
% 5.19/2.19  tff(c_974, plain, (~v10_lattices('#skF_8') | v2_struct_0('#skF_8') | ~l3_lattices('#skF_8')), inference(resolution, [status(thm)], [c_4, c_971])).
% 5.19/2.19  tff(c_977, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_80, c_974])).
% 5.19/2.19  tff(c_979, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_977])).
% 5.19/2.19  tff(c_985, plain, (![B_389]: (r3_lattices('#skF_8', B_389, '#skF_9') | ~r1_lattices('#skF_8', B_389, '#skF_9') | ~m1_subset_1(B_389, u1_struct_0('#skF_8')))), inference(splitRight, [status(thm)], [c_962])).
% 5.19/2.19  tff(c_1005, plain, (![B_88]: (r3_lattices('#skF_8', k16_lattice3('#skF_8', B_88), '#skF_9') | ~r1_lattices('#skF_8', k16_lattice3('#skF_8', B_88), '#skF_9') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_58, c_985])).
% 5.19/2.19  tff(c_1027, plain, (![B_88]: (r3_lattices('#skF_8', k16_lattice3('#skF_8', B_88), '#skF_9') | ~r1_lattices('#skF_8', k16_lattice3('#skF_8', B_88), '#skF_9') | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1005])).
% 5.19/2.19  tff(c_1066, plain, (![B_394]: (r3_lattices('#skF_8', k16_lattice3('#skF_8', B_394), '#skF_9') | ~r1_lattices('#skF_8', k16_lattice3('#skF_8', B_394), '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_82, c_1027])).
% 5.19/2.19  tff(c_269, plain, (![A_189, B_190, C_191]: (r3_lattices(A_189, B_190, C_191) | ~r1_lattices(A_189, B_190, C_191) | ~m1_subset_1(C_191, u1_struct_0(A_189)) | ~m1_subset_1(B_190, u1_struct_0(A_189)) | ~l3_lattices(A_189) | ~v9_lattices(A_189) | ~v8_lattices(A_189) | ~v6_lattices(A_189) | v2_struct_0(A_189))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.19/2.19  tff(c_281, plain, (![B_190]: (r3_lattices('#skF_8', B_190, '#skF_9') | ~r1_lattices('#skF_8', B_190, '#skF_9') | ~m1_subset_1(B_190, u1_struct_0('#skF_8')) | ~l3_lattices('#skF_8') | ~v9_lattices('#skF_8') | ~v8_lattices('#skF_8') | ~v6_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_74, c_269])).
% 5.19/2.19  tff(c_289, plain, (![B_190]: (r3_lattices('#skF_8', B_190, '#skF_9') | ~r1_lattices('#skF_8', B_190, '#skF_9') | ~m1_subset_1(B_190, u1_struct_0('#skF_8')) | ~v9_lattices('#skF_8') | ~v8_lattices('#skF_8') | ~v6_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_281])).
% 5.19/2.19  tff(c_290, plain, (![B_190]: (r3_lattices('#skF_8', B_190, '#skF_9') | ~r1_lattices('#skF_8', B_190, '#skF_9') | ~m1_subset_1(B_190, u1_struct_0('#skF_8')) | ~v9_lattices('#skF_8') | ~v8_lattices('#skF_8') | ~v6_lattices('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_82, c_289])).
% 5.19/2.19  tff(c_291, plain, (~v6_lattices('#skF_8')), inference(splitLeft, [status(thm)], [c_290])).
% 5.19/2.19  tff(c_294, plain, (~v10_lattices('#skF_8') | v2_struct_0('#skF_8') | ~l3_lattices('#skF_8')), inference(resolution, [status(thm)], [c_8, c_291])).
% 5.19/2.19  tff(c_297, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_80, c_294])).
% 5.19/2.19  tff(c_299, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_297])).
% 5.19/2.19  tff(c_301, plain, (v6_lattices('#skF_8')), inference(splitRight, [status(thm)], [c_290])).
% 5.19/2.19  tff(c_300, plain, (![B_190]: (~v8_lattices('#skF_8') | ~v9_lattices('#skF_8') | r3_lattices('#skF_8', B_190, '#skF_9') | ~r1_lattices('#skF_8', B_190, '#skF_9') | ~m1_subset_1(B_190, u1_struct_0('#skF_8')))), inference(splitRight, [status(thm)], [c_290])).
% 5.19/2.19  tff(c_322, plain, (~v9_lattices('#skF_8')), inference(splitLeft, [status(thm)], [c_300])).
% 5.19/2.19  tff(c_325, plain, (~v10_lattices('#skF_8') | v2_struct_0('#skF_8') | ~l3_lattices('#skF_8')), inference(resolution, [status(thm)], [c_2, c_322])).
% 5.19/2.19  tff(c_328, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_80, c_325])).
% 5.19/2.19  tff(c_330, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_328])).
% 5.19/2.19  tff(c_331, plain, (![B_190]: (~v8_lattices('#skF_8') | r3_lattices('#skF_8', B_190, '#skF_9') | ~r1_lattices('#skF_8', B_190, '#skF_9') | ~m1_subset_1(B_190, u1_struct_0('#skF_8')))), inference(splitRight, [status(thm)], [c_300])).
% 5.19/2.19  tff(c_334, plain, (~v8_lattices('#skF_8')), inference(splitLeft, [status(thm)], [c_331])).
% 5.19/2.19  tff(c_337, plain, (~v10_lattices('#skF_8') | v2_struct_0('#skF_8') | ~l3_lattices('#skF_8')), inference(resolution, [status(thm)], [c_4, c_334])).
% 5.19/2.19  tff(c_340, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_80, c_337])).
% 5.19/2.19  tff(c_342, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_340])).
% 5.19/2.19  tff(c_344, plain, (v8_lattices('#skF_8')), inference(splitRight, [status(thm)], [c_331])).
% 5.19/2.19  tff(c_332, plain, (v9_lattices('#skF_8')), inference(splitRight, [status(thm)], [c_300])).
% 5.19/2.19  tff(c_44, plain, (![A_49, B_64]: (r4_lattice3(A_49, '#skF_3'(A_49, B_64), B_64) | ~v4_lattice3(A_49) | ~l3_lattices(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.19/2.19  tff(c_46, plain, (![A_49, B_64]: (m1_subset_1('#skF_3'(A_49, B_64), u1_struct_0(A_49)) | ~v4_lattice3(A_49) | ~l3_lattices(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.19/2.19  tff(c_118, plain, (![A_160, D_161, B_162, C_163]: (r1_lattices(A_160, D_161, B_162) | ~r2_hidden(D_161, C_163) | ~m1_subset_1(D_161, u1_struct_0(A_160)) | ~r4_lattice3(A_160, B_162, C_163) | ~m1_subset_1(B_162, u1_struct_0(A_160)) | ~l3_lattices(A_160) | v2_struct_0(A_160))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.19/2.19  tff(c_128, plain, (![A_164, B_165]: (r1_lattices(A_164, '#skF_9', B_165) | ~m1_subset_1('#skF_9', u1_struct_0(A_164)) | ~r4_lattice3(A_164, B_165, '#skF_10') | ~m1_subset_1(B_165, u1_struct_0(A_164)) | ~l3_lattices(A_164) | v2_struct_0(A_164))), inference(resolution, [status(thm)], [c_72, c_118])).
% 5.19/2.19  tff(c_130, plain, (![B_165]: (r1_lattices('#skF_8', '#skF_9', B_165) | ~r4_lattice3('#skF_8', B_165, '#skF_10') | ~m1_subset_1(B_165, u1_struct_0('#skF_8')) | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_74, c_128])).
% 5.19/2.19  tff(c_133, plain, (![B_165]: (r1_lattices('#skF_8', '#skF_9', B_165) | ~r4_lattice3('#skF_8', B_165, '#skF_10') | ~m1_subset_1(B_165, u1_struct_0('#skF_8')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_130])).
% 5.19/2.19  tff(c_135, plain, (![B_166]: (r1_lattices('#skF_8', '#skF_9', B_166) | ~r4_lattice3('#skF_8', B_166, '#skF_10') | ~m1_subset_1(B_166, u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_82, c_133])).
% 5.19/2.19  tff(c_151, plain, (![B_64]: (r1_lattices('#skF_8', '#skF_9', '#skF_3'('#skF_8', B_64)) | ~r4_lattice3('#skF_8', '#skF_3'('#skF_8', B_64), '#skF_10') | ~v4_lattice3('#skF_8') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_46, c_135])).
% 5.19/2.19  tff(c_173, plain, (![B_64]: (r1_lattices('#skF_8', '#skF_9', '#skF_3'('#skF_8', B_64)) | ~r4_lattice3('#skF_8', '#skF_3'('#skF_8', B_64), '#skF_10') | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_78, c_151])).
% 5.19/2.19  tff(c_191, plain, (![B_171]: (r1_lattices('#skF_8', '#skF_9', '#skF_3'('#skF_8', B_171)) | ~r4_lattice3('#skF_8', '#skF_3'('#skF_8', B_171), '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_82, c_173])).
% 5.19/2.19  tff(c_195, plain, (r1_lattices('#skF_8', '#skF_9', '#skF_3'('#skF_8', '#skF_10')) | ~v4_lattice3('#skF_8') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_44, c_191])).
% 5.19/2.19  tff(c_198, plain, (r1_lattices('#skF_8', '#skF_9', '#skF_3'('#skF_8', '#skF_10')) | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_78, c_195])).
% 5.19/2.19  tff(c_199, plain, (r1_lattices('#skF_8', '#skF_9', '#skF_3'('#skF_8', '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_82, c_198])).
% 5.19/2.19  tff(c_285, plain, (![A_49, B_190, B_64]: (r3_lattices(A_49, B_190, '#skF_3'(A_49, B_64)) | ~r1_lattices(A_49, B_190, '#skF_3'(A_49, B_64)) | ~m1_subset_1(B_190, u1_struct_0(A_49)) | ~v9_lattices(A_49) | ~v8_lattices(A_49) | ~v6_lattices(A_49) | ~v4_lattice3(A_49) | ~l3_lattices(A_49) | v2_struct_0(A_49))), inference(resolution, [status(thm)], [c_46, c_269])).
% 5.19/2.19  tff(c_52, plain, (![A_75, B_82, C_83]: (m1_subset_1('#skF_6'(A_75, B_82, C_83), u1_struct_0(A_75)) | k15_lattice3(A_75, B_82)=C_83 | ~r4_lattice3(A_75, C_83, B_82) | ~m1_subset_1(C_83, u1_struct_0(A_75)) | ~v4_lattice3(A_75) | ~v10_lattices(A_75) | ~l3_lattices(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.19/2.19  tff(c_50, plain, (![A_75, B_82, C_83]: (r4_lattice3(A_75, '#skF_6'(A_75, B_82, C_83), B_82) | k15_lattice3(A_75, B_82)=C_83 | ~r4_lattice3(A_75, C_83, B_82) | ~m1_subset_1(C_83, u1_struct_0(A_75)) | ~v4_lattice3(A_75) | ~v10_lattices(A_75) | ~l3_lattices(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.19/2.19  tff(c_42, plain, (![A_49, B_64, D_69]: (r1_lattices(A_49, '#skF_3'(A_49, B_64), D_69) | ~r4_lattice3(A_49, D_69, B_64) | ~m1_subset_1(D_69, u1_struct_0(A_49)) | ~v4_lattice3(A_49) | ~l3_lattices(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.19/2.19  tff(c_445, plain, (![A_214, C_215, B_216]: (~r1_lattices(A_214, C_215, '#skF_6'(A_214, B_216, C_215)) | k15_lattice3(A_214, B_216)=C_215 | ~r4_lattice3(A_214, C_215, B_216) | ~m1_subset_1(C_215, u1_struct_0(A_214)) | ~v4_lattice3(A_214) | ~v10_lattices(A_214) | ~l3_lattices(A_214) | v2_struct_0(A_214))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.19/2.19  tff(c_673, plain, (![A_307, B_308, B_309]: (k15_lattice3(A_307, B_308)='#skF_3'(A_307, B_309) | ~r4_lattice3(A_307, '#skF_3'(A_307, B_309), B_308) | ~m1_subset_1('#skF_3'(A_307, B_309), u1_struct_0(A_307)) | ~v10_lattices(A_307) | ~r4_lattice3(A_307, '#skF_6'(A_307, B_308, '#skF_3'(A_307, B_309)), B_309) | ~m1_subset_1('#skF_6'(A_307, B_308, '#skF_3'(A_307, B_309)), u1_struct_0(A_307)) | ~v4_lattice3(A_307) | ~l3_lattices(A_307) | v2_struct_0(A_307))), inference(resolution, [status(thm)], [c_42, c_445])).
% 5.19/2.19  tff(c_678, plain, (![A_310, B_311]: (~m1_subset_1('#skF_6'(A_310, B_311, '#skF_3'(A_310, B_311)), u1_struct_0(A_310)) | k15_lattice3(A_310, B_311)='#skF_3'(A_310, B_311) | ~r4_lattice3(A_310, '#skF_3'(A_310, B_311), B_311) | ~m1_subset_1('#skF_3'(A_310, B_311), u1_struct_0(A_310)) | ~v4_lattice3(A_310) | ~v10_lattices(A_310) | ~l3_lattices(A_310) | v2_struct_0(A_310))), inference(resolution, [status(thm)], [c_50, c_673])).
% 5.19/2.19  tff(c_693, plain, (![A_316, B_317]: (k15_lattice3(A_316, B_317)='#skF_3'(A_316, B_317) | ~r4_lattice3(A_316, '#skF_3'(A_316, B_317), B_317) | ~m1_subset_1('#skF_3'(A_316, B_317), u1_struct_0(A_316)) | ~v4_lattice3(A_316) | ~v10_lattices(A_316) | ~l3_lattices(A_316) | v2_struct_0(A_316))), inference(resolution, [status(thm)], [c_52, c_678])).
% 5.19/2.19  tff(c_697, plain, (![A_318, B_319]: (k15_lattice3(A_318, B_319)='#skF_3'(A_318, B_319) | ~m1_subset_1('#skF_3'(A_318, B_319), u1_struct_0(A_318)) | ~v10_lattices(A_318) | ~v4_lattice3(A_318) | ~l3_lattices(A_318) | v2_struct_0(A_318))), inference(resolution, [status(thm)], [c_44, c_693])).
% 5.19/2.19  tff(c_702, plain, (![A_320, B_321]: (k15_lattice3(A_320, B_321)='#skF_3'(A_320, B_321) | ~v10_lattices(A_320) | ~v4_lattice3(A_320) | ~l3_lattices(A_320) | v2_struct_0(A_320))), inference(resolution, [status(thm)], [c_46, c_697])).
% 5.19/2.19  tff(c_704, plain, (![B_321]: (k15_lattice3('#skF_8', B_321)='#skF_3'('#skF_8', B_321) | ~v10_lattices('#skF_8') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_78, c_702])).
% 5.19/2.19  tff(c_707, plain, (![B_321]: (k15_lattice3('#skF_8', B_321)='#skF_3'('#skF_8', B_321) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_80, c_704])).
% 5.19/2.19  tff(c_708, plain, (![B_321]: (k15_lattice3('#skF_8', B_321)='#skF_3'('#skF_8', B_321))), inference(negUnitSimplification, [status(thm)], [c_82, c_707])).
% 5.19/2.19  tff(c_70, plain, (~r3_lattices('#skF_8', k16_lattice3('#skF_8', '#skF_10'), '#skF_9') | ~r3_lattices('#skF_8', '#skF_9', k15_lattice3('#skF_8', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.19/2.19  tff(c_86, plain, (~r3_lattices('#skF_8', '#skF_9', k15_lattice3('#skF_8', '#skF_10'))), inference(splitLeft, [status(thm)], [c_70])).
% 5.19/2.19  tff(c_713, plain, (~r3_lattices('#skF_8', '#skF_9', '#skF_3'('#skF_8', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_708, c_86])).
% 5.19/2.19  tff(c_735, plain, (~r1_lattices('#skF_8', '#skF_9', '#skF_3'('#skF_8', '#skF_10')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_8')) | ~v9_lattices('#skF_8') | ~v8_lattices('#skF_8') | ~v6_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_285, c_713])).
% 5.19/2.19  tff(c_738, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_78, c_301, c_344, c_332, c_74, c_199, c_735])).
% 5.19/2.19  tff(c_740, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_738])).
% 5.19/2.19  tff(c_741, plain, (~r3_lattices('#skF_8', k16_lattice3('#skF_8', '#skF_10'), '#skF_9')), inference(splitRight, [status(thm)], [c_70])).
% 5.19/2.19  tff(c_1071, plain, (~r1_lattices('#skF_8', k16_lattice3('#skF_8', '#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_1066, c_741])).
% 5.19/2.19  tff(c_1079, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_855, c_1071])).
% 5.19/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.19/2.19  
% 5.19/2.19  Inference rules
% 5.19/2.19  ----------------------
% 5.19/2.19  #Ref     : 0
% 5.19/2.19  #Sup     : 152
% 5.19/2.19  #Fact    : 0
% 5.19/2.19  #Define  : 0
% 5.19/2.19  #Split   : 14
% 5.19/2.19  #Chain   : 0
% 5.19/2.19  #Close   : 0
% 5.19/2.19  
% 5.19/2.19  Ordering : KBO
% 5.19/2.19  
% 5.19/2.19  Simplification rules
% 5.19/2.19  ----------------------
% 5.19/2.19  #Subsume      : 9
% 5.19/2.19  #Demod        : 180
% 5.19/2.19  #Tautology    : 29
% 5.19/2.19  #SimpNegUnit  : 72
% 5.19/2.19  #BackRed      : 5
% 5.19/2.19  
% 5.19/2.19  #Partial instantiations: 0
% 5.19/2.19  #Strategies tried      : 1
% 5.19/2.19  
% 5.19/2.19  Timing (in seconds)
% 5.19/2.19  ----------------------
% 5.19/2.19  Preprocessing        : 0.55
% 5.19/2.19  Parsing              : 0.28
% 5.19/2.19  CNF conversion       : 0.06
% 5.19/2.19  Main loop            : 0.71
% 5.19/2.19  Inferencing          : 0.29
% 5.19/2.19  Reduction            : 0.19
% 5.19/2.19  Demodulation         : 0.13
% 5.19/2.19  BG Simplification    : 0.05
% 5.19/2.19  Subsumption          : 0.13
% 5.19/2.19  Abstraction          : 0.03
% 5.19/2.19  MUC search           : 0.00
% 5.19/2.19  Cooper               : 0.00
% 5.19/2.19  Total                : 1.32
% 5.19/2.19  Index Insertion      : 0.00
% 5.19/2.19  Index Deletion       : 0.00
% 5.19/2.20  Index Matching       : 0.00
% 5.19/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
