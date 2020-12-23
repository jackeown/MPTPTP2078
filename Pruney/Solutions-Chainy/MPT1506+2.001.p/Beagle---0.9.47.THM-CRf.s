%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:46 EST 2020

% Result     : Theorem 10.97s
% Output     : CNFRefutation 11.28s
% Verified   : 
% Statistics : Number of formulae       :  282 (63560 expanded)
%              Number of leaves         :   40 (23018 expanded)
%              Depth                    :  101
%              Number of atoms          : 1236 (341441 expanded)
%              Number of equality atoms :   72 (15187 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > a_2_9_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_4 > #skF_6 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_5

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

tff(a_2_9_lattice3,type,(
    a_2_9_lattice3: ( $i * $i ) > $i )).

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

tff(f_182,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( r3_lattice3(A,B,C)
               => r3_lattices(A,B,k16_lattice3(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).

tff(f_140,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v10_lattices(B)
        & v4_lattice3(B)
        & l3_lattices(B) )
     => ( r2_hidden(A,a_2_9_lattice3(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & r3_lattice3(B,D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_9_lattice3)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

tff(f_164,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).

tff(c_70,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_68,plain,(
    r3_lattice3('#skF_8','#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_76,plain,(
    v10_lattices('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_74,plain,(
    v4_lattice3('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_72,plain,(
    l3_lattices('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_46,plain,(
    ! [A_49,B_64] :
      ( m1_subset_1('#skF_3'(A_49,B_64),u1_struct_0(A_49))
      | ~ v4_lattice3(A_49)
      | ~ l3_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_26,plain,(
    ! [A_5,B_17,C_23] :
      ( m1_subset_1('#skF_1'(A_5,B_17,C_23),u1_struct_0(A_5))
      | r3_lattice3(A_5,B_17,C_23)
      | ~ m1_subset_1(B_17,u1_struct_0(A_5))
      | ~ l3_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_34,plain,(
    ! [A_27,B_39,C_45] :
      ( m1_subset_1('#skF_2'(A_27,B_39,C_45),u1_struct_0(A_27))
      | r4_lattice3(A_27,B_39,C_45)
      | ~ m1_subset_1(B_39,u1_struct_0(A_27))
      | ~ l3_lattices(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_32,plain,(
    ! [A_27,B_39,C_45] :
      ( r2_hidden('#skF_2'(A_27,B_39,C_45),C_45)
      | r4_lattice3(A_27,B_39,C_45)
      | ~ m1_subset_1(B_39,u1_struct_0(A_27))
      | ~ l3_lattices(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_89,plain,(
    ! [A_123,B_124,C_125] :
      ( '#skF_6'(A_123,B_124,C_125) = A_123
      | ~ r2_hidden(A_123,a_2_9_lattice3(B_124,C_125))
      | ~ l3_lattices(B_124)
      | ~ v4_lattice3(B_124)
      | ~ v10_lattices(B_124)
      | v2_struct_0(B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_654,plain,(
    ! [A_251,B_252,B_253,C_254] :
      ( '#skF_6'('#skF_2'(A_251,B_252,a_2_9_lattice3(B_253,C_254)),B_253,C_254) = '#skF_2'(A_251,B_252,a_2_9_lattice3(B_253,C_254))
      | ~ l3_lattices(B_253)
      | ~ v4_lattice3(B_253)
      | ~ v10_lattices(B_253)
      | v2_struct_0(B_253)
      | r4_lattice3(A_251,B_252,a_2_9_lattice3(B_253,C_254))
      | ~ m1_subset_1(B_252,u1_struct_0(A_251))
      | ~ l3_lattices(A_251)
      | v2_struct_0(A_251) ) ),
    inference(resolution,[status(thm)],[c_32,c_89])).

tff(c_50,plain,(
    ! [B_76,A_75,C_77] :
      ( r3_lattice3(B_76,'#skF_6'(A_75,B_76,C_77),C_77)
      | ~ r2_hidden(A_75,a_2_9_lattice3(B_76,C_77))
      | ~ l3_lattices(B_76)
      | ~ v4_lattice3(B_76)
      | ~ v10_lattices(B_76)
      | v2_struct_0(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_2032,plain,(
    ! [B_454,A_455,B_456,C_457] :
      ( r3_lattice3(B_454,'#skF_2'(A_455,B_456,a_2_9_lattice3(B_454,C_457)),C_457)
      | ~ r2_hidden('#skF_2'(A_455,B_456,a_2_9_lattice3(B_454,C_457)),a_2_9_lattice3(B_454,C_457))
      | ~ l3_lattices(B_454)
      | ~ v4_lattice3(B_454)
      | ~ v10_lattices(B_454)
      | v2_struct_0(B_454)
      | ~ l3_lattices(B_454)
      | ~ v4_lattice3(B_454)
      | ~ v10_lattices(B_454)
      | v2_struct_0(B_454)
      | r4_lattice3(A_455,B_456,a_2_9_lattice3(B_454,C_457))
      | ~ m1_subset_1(B_456,u1_struct_0(A_455))
      | ~ l3_lattices(A_455)
      | v2_struct_0(A_455) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_654,c_50])).

tff(c_2042,plain,(
    ! [B_454,A_27,B_39,C_457] :
      ( r3_lattice3(B_454,'#skF_2'(A_27,B_39,a_2_9_lattice3(B_454,C_457)),C_457)
      | ~ l3_lattices(B_454)
      | ~ v4_lattice3(B_454)
      | ~ v10_lattices(B_454)
      | v2_struct_0(B_454)
      | r4_lattice3(A_27,B_39,a_2_9_lattice3(B_454,C_457))
      | ~ m1_subset_1(B_39,u1_struct_0(A_27))
      | ~ l3_lattices(A_27)
      | v2_struct_0(A_27) ) ),
    inference(resolution,[status(thm)],[c_32,c_2032])).

tff(c_24,plain,(
    ! [A_5,B_17,C_23] :
      ( r2_hidden('#skF_1'(A_5,B_17,C_23),C_23)
      | r3_lattice3(A_5,B_17,C_23)
      | ~ m1_subset_1(B_17,u1_struct_0(A_5))
      | ~ l3_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_161,plain,(
    ! [A_165,B_166,D_167,C_168] :
      ( r1_lattices(A_165,B_166,D_167)
      | ~ r2_hidden(D_167,C_168)
      | ~ m1_subset_1(D_167,u1_struct_0(A_165))
      | ~ r3_lattice3(A_165,B_166,C_168)
      | ~ m1_subset_1(B_166,u1_struct_0(A_165))
      | ~ l3_lattices(A_165)
      | v2_struct_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_895,plain,(
    ! [B_302,A_306,B_304,C_303,A_305] :
      ( r1_lattices(A_305,B_302,'#skF_1'(A_306,B_304,C_303))
      | ~ m1_subset_1('#skF_1'(A_306,B_304,C_303),u1_struct_0(A_305))
      | ~ r3_lattice3(A_305,B_302,C_303)
      | ~ m1_subset_1(B_302,u1_struct_0(A_305))
      | ~ l3_lattices(A_305)
      | v2_struct_0(A_305)
      | r3_lattice3(A_306,B_304,C_303)
      | ~ m1_subset_1(B_304,u1_struct_0(A_306))
      | ~ l3_lattices(A_306)
      | v2_struct_0(A_306) ) ),
    inference(resolution,[status(thm)],[c_24,c_161])).

tff(c_903,plain,(
    ! [A_312,B_313,B_314,C_315] :
      ( r1_lattices(A_312,B_313,'#skF_1'(A_312,B_314,C_315))
      | ~ r3_lattice3(A_312,B_313,C_315)
      | ~ m1_subset_1(B_313,u1_struct_0(A_312))
      | r3_lattice3(A_312,B_314,C_315)
      | ~ m1_subset_1(B_314,u1_struct_0(A_312))
      | ~ l3_lattices(A_312)
      | v2_struct_0(A_312) ) ),
    inference(resolution,[status(thm)],[c_26,c_895])).

tff(c_30,plain,(
    ! [A_27,B_39,C_45] :
      ( ~ r1_lattices(A_27,'#skF_2'(A_27,B_39,C_45),B_39)
      | r4_lattice3(A_27,B_39,C_45)
      | ~ m1_subset_1(B_39,u1_struct_0(A_27))
      | ~ l3_lattices(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3293,plain,(
    ! [A_579,B_580,C_581,C_582] :
      ( r4_lattice3(A_579,'#skF_1'(A_579,B_580,C_581),C_582)
      | ~ m1_subset_1('#skF_1'(A_579,B_580,C_581),u1_struct_0(A_579))
      | ~ r3_lattice3(A_579,'#skF_2'(A_579,'#skF_1'(A_579,B_580,C_581),C_582),C_581)
      | ~ m1_subset_1('#skF_2'(A_579,'#skF_1'(A_579,B_580,C_581),C_582),u1_struct_0(A_579))
      | r3_lattice3(A_579,B_580,C_581)
      | ~ m1_subset_1(B_580,u1_struct_0(A_579))
      | ~ l3_lattices(A_579)
      | v2_struct_0(A_579) ) ),
    inference(resolution,[status(thm)],[c_903,c_30])).

tff(c_3298,plain,(
    ! [A_583,B_584,C_585] :
      ( ~ m1_subset_1('#skF_2'(A_583,'#skF_1'(A_583,B_584,C_585),a_2_9_lattice3(A_583,C_585)),u1_struct_0(A_583))
      | r3_lattice3(A_583,B_584,C_585)
      | ~ m1_subset_1(B_584,u1_struct_0(A_583))
      | ~ v4_lattice3(A_583)
      | ~ v10_lattices(A_583)
      | r4_lattice3(A_583,'#skF_1'(A_583,B_584,C_585),a_2_9_lattice3(A_583,C_585))
      | ~ m1_subset_1('#skF_1'(A_583,B_584,C_585),u1_struct_0(A_583))
      | ~ l3_lattices(A_583)
      | v2_struct_0(A_583) ) ),
    inference(resolution,[status(thm)],[c_2042,c_3293])).

tff(c_3320,plain,(
    ! [A_588,B_589,C_590] :
      ( r3_lattice3(A_588,B_589,C_590)
      | ~ m1_subset_1(B_589,u1_struct_0(A_588))
      | ~ v4_lattice3(A_588)
      | ~ v10_lattices(A_588)
      | r4_lattice3(A_588,'#skF_1'(A_588,B_589,C_590),a_2_9_lattice3(A_588,C_590))
      | ~ m1_subset_1('#skF_1'(A_588,B_589,C_590),u1_struct_0(A_588))
      | ~ l3_lattices(A_588)
      | v2_struct_0(A_588) ) ),
    inference(resolution,[status(thm)],[c_34,c_3298])).

tff(c_106,plain,(
    ! [A_143,B_144,D_145] :
      ( r1_lattices(A_143,'#skF_3'(A_143,B_144),D_145)
      | ~ r4_lattice3(A_143,D_145,B_144)
      | ~ m1_subset_1(D_145,u1_struct_0(A_143))
      | ~ v4_lattice3(A_143)
      | ~ l3_lattices(A_143)
      | v2_struct_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_22,plain,(
    ! [A_5,B_17,C_23] :
      ( ~ r1_lattices(A_5,B_17,'#skF_1'(A_5,B_17,C_23))
      | r3_lattice3(A_5,B_17,C_23)
      | ~ m1_subset_1(B_17,u1_struct_0(A_5))
      | ~ l3_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_111,plain,(
    ! [A_143,B_144,C_23] :
      ( r3_lattice3(A_143,'#skF_3'(A_143,B_144),C_23)
      | ~ m1_subset_1('#skF_3'(A_143,B_144),u1_struct_0(A_143))
      | ~ r4_lattice3(A_143,'#skF_1'(A_143,'#skF_3'(A_143,B_144),C_23),B_144)
      | ~ m1_subset_1('#skF_1'(A_143,'#skF_3'(A_143,B_144),C_23),u1_struct_0(A_143))
      | ~ v4_lattice3(A_143)
      | ~ l3_lattices(A_143)
      | v2_struct_0(A_143) ) ),
    inference(resolution,[status(thm)],[c_106,c_22])).

tff(c_3616,plain,(
    ! [A_608,C_609] :
      ( r3_lattice3(A_608,'#skF_3'(A_608,a_2_9_lattice3(A_608,C_609)),C_609)
      | ~ m1_subset_1('#skF_3'(A_608,a_2_9_lattice3(A_608,C_609)),u1_struct_0(A_608))
      | ~ v4_lattice3(A_608)
      | ~ v10_lattices(A_608)
      | ~ m1_subset_1('#skF_1'(A_608,'#skF_3'(A_608,a_2_9_lattice3(A_608,C_609)),C_609),u1_struct_0(A_608))
      | ~ l3_lattices(A_608)
      | v2_struct_0(A_608) ) ),
    inference(resolution,[status(thm)],[c_3320,c_111])).

tff(c_3627,plain,(
    ! [A_610,C_611] :
      ( ~ v4_lattice3(A_610)
      | ~ v10_lattices(A_610)
      | r3_lattice3(A_610,'#skF_3'(A_610,a_2_9_lattice3(A_610,C_611)),C_611)
      | ~ m1_subset_1('#skF_3'(A_610,a_2_9_lattice3(A_610,C_611)),u1_struct_0(A_610))
      | ~ l3_lattices(A_610)
      | v2_struct_0(A_610) ) ),
    inference(resolution,[status(thm)],[c_26,c_3616])).

tff(c_3631,plain,(
    ! [A_49,C_611] :
      ( ~ v10_lattices(A_49)
      | r3_lattice3(A_49,'#skF_3'(A_49,a_2_9_lattice3(A_49,C_611)),C_611)
      | ~ v4_lattice3(A_49)
      | ~ l3_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_46,c_3627])).

tff(c_48,plain,(
    ! [D_80,B_76,C_77] :
      ( r2_hidden(D_80,a_2_9_lattice3(B_76,C_77))
      | ~ r3_lattice3(B_76,D_80,C_77)
      | ~ m1_subset_1(D_80,u1_struct_0(B_76))
      | ~ l3_lattices(B_76)
      | ~ v4_lattice3(B_76)
      | ~ v10_lattices(B_76)
      | v2_struct_0(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_54,plain,(
    ! [A_75,B_76,C_77] :
      ( m1_subset_1('#skF_6'(A_75,B_76,C_77),u1_struct_0(B_76))
      | ~ r2_hidden(A_75,a_2_9_lattice3(B_76,C_77))
      | ~ l3_lattices(B_76)
      | ~ v4_lattice3(B_76)
      | ~ v10_lattices(B_76)
      | v2_struct_0(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_3632,plain,(
    ! [A_612,C_613] :
      ( ~ v10_lattices(A_612)
      | r3_lattice3(A_612,'#skF_3'(A_612,a_2_9_lattice3(A_612,C_613)),C_613)
      | ~ v4_lattice3(A_612)
      | ~ l3_lattices(A_612)
      | v2_struct_0(A_612) ) ),
    inference(resolution,[status(thm)],[c_46,c_3627])).

tff(c_114,plain,(
    ! [D_151,B_152,C_153] :
      ( r2_hidden(D_151,a_2_9_lattice3(B_152,C_153))
      | ~ r3_lattice3(B_152,D_151,C_153)
      | ~ m1_subset_1(D_151,u1_struct_0(B_152))
      | ~ l3_lattices(B_152)
      | ~ v4_lattice3(B_152)
      | ~ v10_lattices(B_152)
      | v2_struct_0(B_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_52,plain,(
    ! [A_75,B_76,C_77] :
      ( '#skF_6'(A_75,B_76,C_77) = A_75
      | ~ r2_hidden(A_75,a_2_9_lattice3(B_76,C_77))
      | ~ l3_lattices(B_76)
      | ~ v4_lattice3(B_76)
      | ~ v10_lattices(B_76)
      | v2_struct_0(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_118,plain,(
    ! [D_151,B_152,C_153] :
      ( '#skF_6'(D_151,B_152,C_153) = D_151
      | ~ r3_lattice3(B_152,D_151,C_153)
      | ~ m1_subset_1(D_151,u1_struct_0(B_152))
      | ~ l3_lattices(B_152)
      | ~ v4_lattice3(B_152)
      | ~ v10_lattices(B_152)
      | v2_struct_0(B_152) ) ),
    inference(resolution,[status(thm)],[c_114,c_52])).

tff(c_3755,plain,(
    ! [A_621,C_622] :
      ( '#skF_6'('#skF_3'(A_621,a_2_9_lattice3(A_621,C_622)),A_621,C_622) = '#skF_3'(A_621,a_2_9_lattice3(A_621,C_622))
      | ~ m1_subset_1('#skF_3'(A_621,a_2_9_lattice3(A_621,C_622)),u1_struct_0(A_621))
      | ~ v10_lattices(A_621)
      | ~ v4_lattice3(A_621)
      | ~ l3_lattices(A_621)
      | v2_struct_0(A_621) ) ),
    inference(resolution,[status(thm)],[c_3632,c_118])).

tff(c_3765,plain,(
    ! [A_49,C_622] :
      ( '#skF_6'('#skF_3'(A_49,a_2_9_lattice3(A_49,C_622)),A_49,C_622) = '#skF_3'(A_49,a_2_9_lattice3(A_49,C_622))
      | ~ v10_lattices(A_49)
      | ~ v4_lattice3(A_49)
      | ~ l3_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_46,c_3755])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_171,plain,(
    ! [A_169,B_170,C_171] :
      ( r3_lattices(A_169,B_170,C_171)
      | ~ r1_lattices(A_169,B_170,C_171)
      | ~ m1_subset_1(C_171,u1_struct_0(A_169))
      | ~ m1_subset_1(B_170,u1_struct_0(A_169))
      | ~ l3_lattices(A_169)
      | ~ v9_lattices(A_169)
      | ~ v8_lattices(A_169)
      | ~ v6_lattices(A_169)
      | v2_struct_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_183,plain,(
    ! [B_170] :
      ( r3_lattices('#skF_8',B_170,'#skF_9')
      | ~ r1_lattices('#skF_8',B_170,'#skF_9')
      | ~ m1_subset_1(B_170,u1_struct_0('#skF_8'))
      | ~ l3_lattices('#skF_8')
      | ~ v9_lattices('#skF_8')
      | ~ v8_lattices('#skF_8')
      | ~ v6_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_70,c_171])).

tff(c_191,plain,(
    ! [B_170] :
      ( r3_lattices('#skF_8',B_170,'#skF_9')
      | ~ r1_lattices('#skF_8',B_170,'#skF_9')
      | ~ m1_subset_1(B_170,u1_struct_0('#skF_8'))
      | ~ v9_lattices('#skF_8')
      | ~ v8_lattices('#skF_8')
      | ~ v6_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_183])).

tff(c_192,plain,(
    ! [B_170] :
      ( r3_lattices('#skF_8',B_170,'#skF_9')
      | ~ r1_lattices('#skF_8',B_170,'#skF_9')
      | ~ m1_subset_1(B_170,u1_struct_0('#skF_8'))
      | ~ v9_lattices('#skF_8')
      | ~ v8_lattices('#skF_8')
      | ~ v6_lattices('#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_191])).

tff(c_194,plain,(
    ~ v6_lattices('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_192])).

tff(c_197,plain,
    ( ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ l3_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_8,c_194])).

tff(c_200,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76,c_197])).

tff(c_202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_200])).

tff(c_204,plain,(
    v6_lattices('#skF_8') ),
    inference(splitRight,[status(thm)],[c_192])).

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

tff(c_203,plain,(
    ! [B_170] :
      ( ~ v8_lattices('#skF_8')
      | ~ v9_lattices('#skF_8')
      | r3_lattices('#skF_8',B_170,'#skF_9')
      | ~ r1_lattices('#skF_8',B_170,'#skF_9')
      | ~ m1_subset_1(B_170,u1_struct_0('#skF_8')) ) ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_205,plain,(
    ~ v9_lattices('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_203])).

tff(c_208,plain,
    ( ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ l3_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_2,c_205])).

tff(c_211,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76,c_208])).

tff(c_213,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_211])).

tff(c_214,plain,(
    ! [B_170] :
      ( ~ v8_lattices('#skF_8')
      | r3_lattices('#skF_8',B_170,'#skF_9')
      | ~ r1_lattices('#skF_8',B_170,'#skF_9')
      | ~ m1_subset_1(B_170,u1_struct_0('#skF_8')) ) ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_216,plain,(
    ~ v8_lattices('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_214])).

tff(c_219,plain,
    ( ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ l3_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_216])).

tff(c_222,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76,c_219])).

tff(c_224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_222])).

tff(c_226,plain,(
    v8_lattices('#skF_8') ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_215,plain,(
    v9_lattices('#skF_8') ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_125,plain,(
    ! [D_158,B_159,C_160] :
      ( '#skF_6'(D_158,B_159,C_160) = D_158
      | ~ r3_lattice3(B_159,D_158,C_160)
      | ~ m1_subset_1(D_158,u1_struct_0(B_159))
      | ~ l3_lattices(B_159)
      | ~ v4_lattice3(B_159)
      | ~ v10_lattices(B_159)
      | v2_struct_0(B_159) ) ),
    inference(resolution,[status(thm)],[c_114,c_52])).

tff(c_129,plain,
    ( '#skF_6'('#skF_9','#skF_8','#skF_10') = '#skF_9'
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_8'))
    | ~ l3_lattices('#skF_8')
    | ~ v4_lattice3('#skF_8')
    | ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_68,c_125])).

tff(c_133,plain,
    ( '#skF_6'('#skF_9','#skF_8','#skF_10') = '#skF_9'
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_129])).

tff(c_134,plain,(
    '#skF_6'('#skF_9','#skF_8','#skF_10') = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_133])).

tff(c_348,plain,(
    ! [A_201,B_202,C_203] :
      ( '#skF_6'('#skF_6'(A_201,B_202,C_203),B_202,C_203) = '#skF_6'(A_201,B_202,C_203)
      | ~ m1_subset_1('#skF_6'(A_201,B_202,C_203),u1_struct_0(B_202))
      | ~ r2_hidden(A_201,a_2_9_lattice3(B_202,C_203))
      | ~ l3_lattices(B_202)
      | ~ v4_lattice3(B_202)
      | ~ v10_lattices(B_202)
      | v2_struct_0(B_202) ) ),
    inference(resolution,[status(thm)],[c_50,c_125])).

tff(c_357,plain,(
    ! [A_204,B_205,C_206] :
      ( '#skF_6'('#skF_6'(A_204,B_205,C_206),B_205,C_206) = '#skF_6'(A_204,B_205,C_206)
      | ~ r2_hidden(A_204,a_2_9_lattice3(B_205,C_206))
      | ~ l3_lattices(B_205)
      | ~ v4_lattice3(B_205)
      | ~ v10_lattices(B_205)
      | v2_struct_0(B_205) ) ),
    inference(resolution,[status(thm)],[c_54,c_348])).

tff(c_369,plain,(
    ! [D_207,B_208,C_209] :
      ( '#skF_6'('#skF_6'(D_207,B_208,C_209),B_208,C_209) = '#skF_6'(D_207,B_208,C_209)
      | ~ r3_lattice3(B_208,D_207,C_209)
      | ~ m1_subset_1(D_207,u1_struct_0(B_208))
      | ~ l3_lattices(B_208)
      | ~ v4_lattice3(B_208)
      | ~ v10_lattices(B_208)
      | v2_struct_0(B_208) ) ),
    inference(resolution,[status(thm)],[c_48,c_357])).

tff(c_383,plain,(
    ! [C_209] :
      ( '#skF_6'('#skF_6'('#skF_9','#skF_8',C_209),'#skF_8',C_209) = '#skF_6'('#skF_9','#skF_8',C_209)
      | ~ r3_lattice3('#skF_8','#skF_9',C_209)
      | ~ l3_lattices('#skF_8')
      | ~ v4_lattice3('#skF_8')
      | ~ v10_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_70,c_369])).

tff(c_392,plain,(
    ! [C_209] :
      ( '#skF_6'('#skF_6'('#skF_9','#skF_8',C_209),'#skF_8',C_209) = '#skF_6'('#skF_9','#skF_8',C_209)
      | ~ r3_lattice3('#skF_8','#skF_9',C_209)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_383])).

tff(c_393,plain,(
    ! [C_209] :
      ( '#skF_6'('#skF_6'('#skF_9','#skF_8',C_209),'#skF_8',C_209) = '#skF_6'('#skF_9','#skF_8',C_209)
      | ~ r3_lattice3('#skF_8','#skF_9',C_209) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_392])).

tff(c_687,plain,(
    ! [A_258,B_259,C_260,C_261] :
      ( '#skF_6'('#skF_6'('#skF_6'(A_258,B_259,C_260),B_259,C_261),B_259,C_261) = '#skF_6'('#skF_6'(A_258,B_259,C_260),B_259,C_261)
      | ~ r3_lattice3(B_259,'#skF_6'(A_258,B_259,C_260),C_261)
      | ~ r2_hidden(A_258,a_2_9_lattice3(B_259,C_260))
      | ~ l3_lattices(B_259)
      | ~ v4_lattice3(B_259)
      | ~ v10_lattices(B_259)
      | v2_struct_0(B_259) ) ),
    inference(resolution,[status(thm)],[c_54,c_369])).

tff(c_733,plain,(
    ! [C_209,C_261] :
      ( '#skF_6'('#skF_6'('#skF_6'('#skF_9','#skF_8',C_209),'#skF_8',C_261),'#skF_8',C_261) = '#skF_6'('#skF_6'('#skF_6'('#skF_9','#skF_8',C_209),'#skF_8',C_209),'#skF_8',C_261)
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_6'('#skF_9','#skF_8',C_209),'#skF_8',C_209),C_261)
      | ~ r2_hidden('#skF_6'('#skF_9','#skF_8',C_209),a_2_9_lattice3('#skF_8',C_209))
      | ~ l3_lattices('#skF_8')
      | ~ v4_lattice3('#skF_8')
      | ~ v10_lattices('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ r3_lattice3('#skF_8','#skF_9',C_209) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_687])).

tff(c_749,plain,(
    ! [C_209,C_261] :
      ( '#skF_6'('#skF_6'('#skF_6'('#skF_9','#skF_8',C_209),'#skF_8',C_261),'#skF_8',C_261) = '#skF_6'('#skF_6'('#skF_6'('#skF_9','#skF_8',C_209),'#skF_8',C_209),'#skF_8',C_261)
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_6'('#skF_9','#skF_8',C_209),'#skF_8',C_209),C_261)
      | ~ r2_hidden('#skF_6'('#skF_9','#skF_8',C_209),a_2_9_lattice3('#skF_8',C_209))
      | v2_struct_0('#skF_8')
      | ~ r3_lattice3('#skF_8','#skF_9',C_209) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_733])).

tff(c_811,plain,(
    ! [C_283,C_284] :
      ( '#skF_6'('#skF_6'('#skF_6'('#skF_9','#skF_8',C_283),'#skF_8',C_284),'#skF_8',C_284) = '#skF_6'('#skF_6'('#skF_6'('#skF_9','#skF_8',C_283),'#skF_8',C_283),'#skF_8',C_284)
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_6'('#skF_9','#skF_8',C_283),'#skF_8',C_283),C_284)
      | ~ r2_hidden('#skF_6'('#skF_9','#skF_8',C_283),a_2_9_lattice3('#skF_8',C_283))
      | ~ r3_lattice3('#skF_8','#skF_9',C_283) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_749])).

tff(c_1494,plain,(
    ! [C_396,C_397] :
      ( '#skF_6'('#skF_6'('#skF_6'('#skF_9','#skF_8',C_396),'#skF_8',C_397),'#skF_8',C_397) = '#skF_6'('#skF_6'('#skF_6'('#skF_9','#skF_8',C_396),'#skF_8',C_396),'#skF_8',C_397)
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_9','#skF_8',C_396),C_397)
      | ~ r2_hidden('#skF_6'('#skF_9','#skF_8',C_396),a_2_9_lattice3('#skF_8',C_396))
      | ~ r3_lattice3('#skF_8','#skF_9',C_396)
      | ~ r3_lattice3('#skF_8','#skF_9',C_396) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_811])).

tff(c_1499,plain,(
    ! [C_77,C_397] :
      ( '#skF_6'('#skF_6'('#skF_6'('#skF_9','#skF_8',C_77),'#skF_8',C_77),'#skF_8',C_397) = '#skF_6'('#skF_6'('#skF_6'('#skF_9','#skF_8',C_77),'#skF_8',C_397),'#skF_8',C_397)
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_9','#skF_8',C_77),C_397)
      | ~ r3_lattice3('#skF_8','#skF_9',C_77)
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_9','#skF_8',C_77),C_77)
      | ~ m1_subset_1('#skF_6'('#skF_9','#skF_8',C_77),u1_struct_0('#skF_8'))
      | ~ l3_lattices('#skF_8')
      | ~ v4_lattice3('#skF_8')
      | ~ v10_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_48,c_1494])).

tff(c_1504,plain,(
    ! [C_77,C_397] :
      ( '#skF_6'('#skF_6'('#skF_6'('#skF_9','#skF_8',C_77),'#skF_8',C_77),'#skF_8',C_397) = '#skF_6'('#skF_6'('#skF_6'('#skF_9','#skF_8',C_77),'#skF_8',C_397),'#skF_8',C_397)
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_9','#skF_8',C_77),C_397)
      | ~ r3_lattice3('#skF_8','#skF_9',C_77)
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_9','#skF_8',C_77),C_77)
      | ~ m1_subset_1('#skF_6'('#skF_9','#skF_8',C_77),u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_1499])).

tff(c_1770,plain,(
    ! [C_441,C_442] :
      ( '#skF_6'('#skF_6'('#skF_6'('#skF_9','#skF_8',C_441),'#skF_8',C_442),'#skF_8',C_442) = '#skF_6'('#skF_6'('#skF_6'('#skF_9','#skF_8',C_441),'#skF_8',C_441),'#skF_8',C_442)
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_9','#skF_8',C_441),C_442)
      | ~ r3_lattice3('#skF_8','#skF_9',C_441)
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_9','#skF_8',C_441),C_441)
      | ~ m1_subset_1('#skF_6'('#skF_9','#skF_8',C_441),u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1504])).

tff(c_1775,plain,(
    ! [C_77,C_442] :
      ( '#skF_6'('#skF_6'('#skF_6'('#skF_9','#skF_8',C_77),'#skF_8',C_77),'#skF_8',C_442) = '#skF_6'('#skF_6'('#skF_6'('#skF_9','#skF_8',C_77),'#skF_8',C_442),'#skF_8',C_442)
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_9','#skF_8',C_77),C_442)
      | ~ r3_lattice3('#skF_8','#skF_9',C_77)
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_9','#skF_8',C_77),C_77)
      | ~ r2_hidden('#skF_9',a_2_9_lattice3('#skF_8',C_77))
      | ~ l3_lattices('#skF_8')
      | ~ v4_lattice3('#skF_8')
      | ~ v10_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_54,c_1770])).

tff(c_1780,plain,(
    ! [C_77,C_442] :
      ( '#skF_6'('#skF_6'('#skF_6'('#skF_9','#skF_8',C_77),'#skF_8',C_77),'#skF_8',C_442) = '#skF_6'('#skF_6'('#skF_6'('#skF_9','#skF_8',C_77),'#skF_8',C_442),'#skF_8',C_442)
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_9','#skF_8',C_77),C_442)
      | ~ r3_lattice3('#skF_8','#skF_9',C_77)
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_9','#skF_8',C_77),C_77)
      | ~ r2_hidden('#skF_9',a_2_9_lattice3('#skF_8',C_77))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_1775])).

tff(c_1808,plain,(
    ! [C_448,C_449] :
      ( '#skF_6'('#skF_6'('#skF_6'('#skF_9','#skF_8',C_448),'#skF_8',C_449),'#skF_8',C_449) = '#skF_6'('#skF_6'('#skF_6'('#skF_9','#skF_8',C_448),'#skF_8',C_448),'#skF_8',C_449)
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_9','#skF_8',C_448),C_449)
      | ~ r3_lattice3('#skF_8','#skF_9',C_448)
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_9','#skF_8',C_448),C_448)
      | ~ r2_hidden('#skF_9',a_2_9_lattice3('#skF_8',C_448)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1780])).

tff(c_386,plain,(
    ! [A_75,B_76,C_77,C_209] :
      ( '#skF_6'('#skF_6'('#skF_6'(A_75,B_76,C_77),B_76,C_209),B_76,C_209) = '#skF_6'('#skF_6'(A_75,B_76,C_77),B_76,C_209)
      | ~ r3_lattice3(B_76,'#skF_6'(A_75,B_76,C_77),C_209)
      | ~ r2_hidden(A_75,a_2_9_lattice3(B_76,C_77))
      | ~ l3_lattices(B_76)
      | ~ v4_lattice3(B_76)
      | ~ v10_lattices(B_76)
      | v2_struct_0(B_76) ) ),
    inference(resolution,[status(thm)],[c_54,c_369])).

tff(c_1843,plain,(
    ! [C_448,C_449] :
      ( '#skF_6'('#skF_6'('#skF_6'('#skF_9','#skF_8',C_448),'#skF_8',C_448),'#skF_8',C_449) = '#skF_6'('#skF_6'('#skF_9','#skF_8',C_448),'#skF_8',C_449)
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_9','#skF_8',C_448),C_449)
      | ~ r2_hidden('#skF_9',a_2_9_lattice3('#skF_8',C_448))
      | ~ l3_lattices('#skF_8')
      | ~ v4_lattice3('#skF_8')
      | ~ v10_lattices('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_9','#skF_8',C_448),C_449)
      | ~ r3_lattice3('#skF_8','#skF_9',C_448)
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_9','#skF_8',C_448),C_448)
      | ~ r2_hidden('#skF_9',a_2_9_lattice3('#skF_8',C_448)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1808,c_386])).

tff(c_1908,plain,(
    ! [C_448,C_449] :
      ( '#skF_6'('#skF_6'('#skF_6'('#skF_9','#skF_8',C_448),'#skF_8',C_448),'#skF_8',C_449) = '#skF_6'('#skF_6'('#skF_9','#skF_8',C_448),'#skF_8',C_449)
      | v2_struct_0('#skF_8')
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_9','#skF_8',C_448),C_449)
      | ~ r3_lattice3('#skF_8','#skF_9',C_448)
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_9','#skF_8',C_448),C_448)
      | ~ r2_hidden('#skF_9',a_2_9_lattice3('#skF_8',C_448)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_1843])).

tff(c_1937,plain,(
    ! [C_450,C_451] :
      ( '#skF_6'('#skF_6'('#skF_6'('#skF_9','#skF_8',C_450),'#skF_8',C_450),'#skF_8',C_451) = '#skF_6'('#skF_6'('#skF_9','#skF_8',C_450),'#skF_8',C_451)
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_9','#skF_8',C_450),C_451)
      | ~ r3_lattice3('#skF_8','#skF_9',C_450)
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_9','#skF_8',C_450),C_450)
      | ~ r2_hidden('#skF_9',a_2_9_lattice3('#skF_8',C_450)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1908])).

tff(c_1969,plain,(
    ! [C_450,C_451] :
      ( r3_lattice3('#skF_8','#skF_6'('#skF_6'('#skF_9','#skF_8',C_450),'#skF_8',C_451),C_451)
      | ~ r2_hidden('#skF_6'('#skF_6'('#skF_9','#skF_8',C_450),'#skF_8',C_450),a_2_9_lattice3('#skF_8',C_451))
      | ~ l3_lattices('#skF_8')
      | ~ v4_lattice3('#skF_8')
      | ~ v10_lattices('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_9','#skF_8',C_450),C_451)
      | ~ r3_lattice3('#skF_8','#skF_9',C_450)
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_9','#skF_8',C_450),C_450)
      | ~ r2_hidden('#skF_9',a_2_9_lattice3('#skF_8',C_450)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1937,c_50])).

tff(c_2007,plain,(
    ! [C_450,C_451] :
      ( r3_lattice3('#skF_8','#skF_6'('#skF_6'('#skF_9','#skF_8',C_450),'#skF_8',C_451),C_451)
      | ~ r2_hidden('#skF_6'('#skF_6'('#skF_9','#skF_8',C_450),'#skF_8',C_450),a_2_9_lattice3('#skF_8',C_451))
      | v2_struct_0('#skF_8')
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_9','#skF_8',C_450),C_451)
      | ~ r3_lattice3('#skF_8','#skF_9',C_450)
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_9','#skF_8',C_450),C_450)
      | ~ r2_hidden('#skF_9',a_2_9_lattice3('#skF_8',C_450)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_1969])).

tff(c_2259,plain,(
    ! [C_470,C_471] :
      ( r3_lattice3('#skF_8','#skF_6'('#skF_6'('#skF_9','#skF_8',C_470),'#skF_8',C_471),C_471)
      | ~ r2_hidden('#skF_6'('#skF_6'('#skF_9','#skF_8',C_470),'#skF_8',C_470),a_2_9_lattice3('#skF_8',C_471))
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_9','#skF_8',C_470),C_471)
      | ~ r3_lattice3('#skF_8','#skF_9',C_470)
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_9','#skF_8',C_470),C_470)
      | ~ r2_hidden('#skF_9',a_2_9_lattice3('#skF_8',C_470)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2007])).

tff(c_2263,plain,(
    ! [C_471] :
      ( r3_lattice3('#skF_8','#skF_6'('#skF_6'('#skF_9','#skF_8','#skF_10'),'#skF_8',C_471),C_471)
      | ~ r2_hidden('#skF_6'('#skF_9','#skF_8','#skF_10'),a_2_9_lattice3('#skF_8',C_471))
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_9','#skF_8','#skF_10'),C_471)
      | ~ r3_lattice3('#skF_8','#skF_9','#skF_10')
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_9','#skF_8','#skF_10'),'#skF_10')
      | ~ r2_hidden('#skF_9',a_2_9_lattice3('#skF_8','#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_2259])).

tff(c_2268,plain,(
    ! [C_471] :
      ( r3_lattice3('#skF_8','#skF_6'('#skF_9','#skF_8',C_471),C_471)
      | ~ r2_hidden('#skF_9',a_2_9_lattice3('#skF_8',C_471))
      | ~ r3_lattice3('#skF_8','#skF_9',C_471)
      | ~ r2_hidden('#skF_9',a_2_9_lattice3('#skF_8','#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_134,c_68,c_134,c_134,c_134,c_2263])).

tff(c_2273,plain,(
    ~ r2_hidden('#skF_9',a_2_9_lattice3('#skF_8','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_2268])).

tff(c_2276,plain,
    ( ~ r3_lattice3('#skF_8','#skF_9','#skF_10')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_8'))
    | ~ l3_lattices('#skF_8')
    | ~ v4_lattice3('#skF_8')
    | ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_2273])).

tff(c_2279,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_68,c_2276])).

tff(c_2281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2279])).

tff(c_2283,plain,(
    r2_hidden('#skF_9',a_2_9_lattice3('#skF_8','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_2268])).

tff(c_20,plain,(
    ! [A_5,B_17,D_26,C_23] :
      ( r1_lattices(A_5,B_17,D_26)
      | ~ r2_hidden(D_26,C_23)
      | ~ m1_subset_1(D_26,u1_struct_0(A_5))
      | ~ r3_lattice3(A_5,B_17,C_23)
      | ~ m1_subset_1(B_17,u1_struct_0(A_5))
      | ~ l3_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2341,plain,(
    ! [A_477,B_478] :
      ( r1_lattices(A_477,B_478,'#skF_9')
      | ~ m1_subset_1('#skF_9',u1_struct_0(A_477))
      | ~ r3_lattice3(A_477,B_478,a_2_9_lattice3('#skF_8','#skF_10'))
      | ~ m1_subset_1(B_478,u1_struct_0(A_477))
      | ~ l3_lattices(A_477)
      | v2_struct_0(A_477) ) ),
    inference(resolution,[status(thm)],[c_2283,c_20])).

tff(c_2449,plain,(
    ! [B_495,A_496] :
      ( r1_lattices(B_495,'#skF_6'(A_496,B_495,a_2_9_lattice3('#skF_8','#skF_10')),'#skF_9')
      | ~ m1_subset_1('#skF_9',u1_struct_0(B_495))
      | ~ m1_subset_1('#skF_6'(A_496,B_495,a_2_9_lattice3('#skF_8','#skF_10')),u1_struct_0(B_495))
      | ~ r2_hidden(A_496,a_2_9_lattice3(B_495,a_2_9_lattice3('#skF_8','#skF_10')))
      | ~ l3_lattices(B_495)
      | ~ v4_lattice3(B_495)
      | ~ v10_lattices(B_495)
      | v2_struct_0(B_495) ) ),
    inference(resolution,[status(thm)],[c_50,c_2341])).

tff(c_2549,plain,(
    ! [B_497,A_498] :
      ( r1_lattices(B_497,'#skF_6'(A_498,B_497,a_2_9_lattice3('#skF_8','#skF_10')),'#skF_9')
      | ~ m1_subset_1('#skF_9',u1_struct_0(B_497))
      | ~ r2_hidden(A_498,a_2_9_lattice3(B_497,a_2_9_lattice3('#skF_8','#skF_10')))
      | ~ l3_lattices(B_497)
      | ~ v4_lattice3(B_497)
      | ~ v10_lattices(B_497)
      | v2_struct_0(B_497) ) ),
    inference(resolution,[status(thm)],[c_54,c_2449])).

tff(c_231,plain,(
    ! [B_178] :
      ( r3_lattices('#skF_8',B_178,'#skF_9')
      | ~ r1_lattices('#skF_8',B_178,'#skF_9')
      | ~ m1_subset_1(B_178,u1_struct_0('#skF_8')) ) ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_239,plain,(
    ! [A_75,C_77] :
      ( r3_lattices('#skF_8','#skF_6'(A_75,'#skF_8',C_77),'#skF_9')
      | ~ r1_lattices('#skF_8','#skF_6'(A_75,'#skF_8',C_77),'#skF_9')
      | ~ r2_hidden(A_75,a_2_9_lattice3('#skF_8',C_77))
      | ~ l3_lattices('#skF_8')
      | ~ v4_lattice3('#skF_8')
      | ~ v10_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_54,c_231])).

tff(c_261,plain,(
    ! [A_75,C_77] :
      ( r3_lattices('#skF_8','#skF_6'(A_75,'#skF_8',C_77),'#skF_9')
      | ~ r1_lattices('#skF_8','#skF_6'(A_75,'#skF_8',C_77),'#skF_9')
      | ~ r2_hidden(A_75,a_2_9_lattice3('#skF_8',C_77))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_239])).

tff(c_262,plain,(
    ! [A_75,C_77] :
      ( r3_lattices('#skF_8','#skF_6'(A_75,'#skF_8',C_77),'#skF_9')
      | ~ r1_lattices('#skF_8','#skF_6'(A_75,'#skF_8',C_77),'#skF_9')
      | ~ r2_hidden(A_75,a_2_9_lattice3('#skF_8',C_77)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_261])).

tff(c_664,plain,(
    ! [A_251,B_252,C_254] :
      ( r3_lattices('#skF_8','#skF_2'(A_251,B_252,a_2_9_lattice3('#skF_8',C_254)),'#skF_9')
      | ~ r1_lattices('#skF_8','#skF_6'('#skF_2'(A_251,B_252,a_2_9_lattice3('#skF_8',C_254)),'#skF_8',C_254),'#skF_9')
      | ~ r2_hidden('#skF_2'(A_251,B_252,a_2_9_lattice3('#skF_8',C_254)),a_2_9_lattice3('#skF_8',C_254))
      | ~ l3_lattices('#skF_8')
      | ~ v4_lattice3('#skF_8')
      | ~ v10_lattices('#skF_8')
      | v2_struct_0('#skF_8')
      | r4_lattice3(A_251,B_252,a_2_9_lattice3('#skF_8',C_254))
      | ~ m1_subset_1(B_252,u1_struct_0(A_251))
      | ~ l3_lattices(A_251)
      | v2_struct_0(A_251) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_654,c_262])).

tff(c_676,plain,(
    ! [A_251,B_252,C_254] :
      ( r3_lattices('#skF_8','#skF_2'(A_251,B_252,a_2_9_lattice3('#skF_8',C_254)),'#skF_9')
      | ~ r1_lattices('#skF_8','#skF_6'('#skF_2'(A_251,B_252,a_2_9_lattice3('#skF_8',C_254)),'#skF_8',C_254),'#skF_9')
      | ~ r2_hidden('#skF_2'(A_251,B_252,a_2_9_lattice3('#skF_8',C_254)),a_2_9_lattice3('#skF_8',C_254))
      | v2_struct_0('#skF_8')
      | r4_lattice3(A_251,B_252,a_2_9_lattice3('#skF_8',C_254))
      | ~ m1_subset_1(B_252,u1_struct_0(A_251))
      | ~ l3_lattices(A_251)
      | v2_struct_0(A_251) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_664])).

tff(c_677,plain,(
    ! [A_251,B_252,C_254] :
      ( r3_lattices('#skF_8','#skF_2'(A_251,B_252,a_2_9_lattice3('#skF_8',C_254)),'#skF_9')
      | ~ r1_lattices('#skF_8','#skF_6'('#skF_2'(A_251,B_252,a_2_9_lattice3('#skF_8',C_254)),'#skF_8',C_254),'#skF_9')
      | ~ r2_hidden('#skF_2'(A_251,B_252,a_2_9_lattice3('#skF_8',C_254)),a_2_9_lattice3('#skF_8',C_254))
      | r4_lattice3(A_251,B_252,a_2_9_lattice3('#skF_8',C_254))
      | ~ m1_subset_1(B_252,u1_struct_0(A_251))
      | ~ l3_lattices(A_251)
      | v2_struct_0(A_251) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_676])).

tff(c_2553,plain,(
    ! [A_251,B_252] :
      ( r3_lattices('#skF_8','#skF_2'(A_251,B_252,a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),'#skF_9')
      | r4_lattice3(A_251,B_252,a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
      | ~ m1_subset_1(B_252,u1_struct_0(A_251))
      | ~ l3_lattices(A_251)
      | v2_struct_0(A_251)
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_8'))
      | ~ r2_hidden('#skF_2'(A_251,B_252,a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
      | ~ l3_lattices('#skF_8')
      | ~ v4_lattice3('#skF_8')
      | ~ v10_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2549,c_677])).

tff(c_2644,plain,(
    ! [A_251,B_252] :
      ( r3_lattices('#skF_8','#skF_2'(A_251,B_252,a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),'#skF_9')
      | r4_lattice3(A_251,B_252,a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
      | ~ m1_subset_1(B_252,u1_struct_0(A_251))
      | ~ l3_lattices(A_251)
      | v2_struct_0(A_251)
      | ~ r2_hidden('#skF_2'(A_251,B_252,a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_2553])).

tff(c_2781,plain,(
    ! [A_525,B_526] :
      ( r3_lattices('#skF_8','#skF_2'(A_525,B_526,a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),'#skF_9')
      | r4_lattice3(A_525,B_526,a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
      | ~ m1_subset_1(B_526,u1_struct_0(A_525))
      | ~ l3_lattices(A_525)
      | v2_struct_0(A_525)
      | ~ r2_hidden('#skF_2'(A_525,B_526,a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2644])).

tff(c_2794,plain,(
    ! [A_527,B_528] :
      ( r3_lattices('#skF_8','#skF_2'(A_527,B_528,a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),'#skF_9')
      | r4_lattice3(A_527,B_528,a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
      | ~ m1_subset_1(B_528,u1_struct_0(A_527))
      | ~ l3_lattices(A_527)
      | v2_struct_0(A_527) ) ),
    inference(resolution,[status(thm)],[c_32,c_2781])).

tff(c_18,plain,(
    ! [A_2,B_3,C_4] :
      ( r1_lattices(A_2,B_3,C_4)
      | ~ r3_lattices(A_2,B_3,C_4)
      | ~ m1_subset_1(C_4,u1_struct_0(A_2))
      | ~ m1_subset_1(B_3,u1_struct_0(A_2))
      | ~ l3_lattices(A_2)
      | ~ v9_lattices(A_2)
      | ~ v8_lattices(A_2)
      | ~ v6_lattices(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2796,plain,(
    ! [A_527,B_528] :
      ( r1_lattices('#skF_8','#skF_2'(A_527,B_528,a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),'#skF_9')
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_2'(A_527,B_528,a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),u1_struct_0('#skF_8'))
      | ~ l3_lattices('#skF_8')
      | ~ v9_lattices('#skF_8')
      | ~ v8_lattices('#skF_8')
      | ~ v6_lattices('#skF_8')
      | v2_struct_0('#skF_8')
      | r4_lattice3(A_527,B_528,a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
      | ~ m1_subset_1(B_528,u1_struct_0(A_527))
      | ~ l3_lattices(A_527)
      | v2_struct_0(A_527) ) ),
    inference(resolution,[status(thm)],[c_2794,c_18])).

tff(c_2799,plain,(
    ! [A_527,B_528] :
      ( r1_lattices('#skF_8','#skF_2'(A_527,B_528,a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),'#skF_9')
      | ~ m1_subset_1('#skF_2'(A_527,B_528,a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8')
      | r4_lattice3(A_527,B_528,a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
      | ~ m1_subset_1(B_528,u1_struct_0(A_527))
      | ~ l3_lattices(A_527)
      | v2_struct_0(A_527) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_226,c_215,c_72,c_70,c_2796])).

tff(c_2801,plain,(
    ! [A_529,B_530] :
      ( r1_lattices('#skF_8','#skF_2'(A_529,B_530,a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),'#skF_9')
      | ~ m1_subset_1('#skF_2'(A_529,B_530,a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),u1_struct_0('#skF_8'))
      | r4_lattice3(A_529,B_530,a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
      | ~ m1_subset_1(B_530,u1_struct_0(A_529))
      | ~ l3_lattices(A_529)
      | v2_struct_0(A_529) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2799])).

tff(c_2809,plain,(
    ! [B_39] :
      ( r1_lattices('#skF_8','#skF_2'('#skF_8',B_39,a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),'#skF_9')
      | r4_lattice3('#skF_8',B_39,a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
      | ~ m1_subset_1(B_39,u1_struct_0('#skF_8'))
      | ~ l3_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_34,c_2801])).

tff(c_2816,plain,(
    ! [B_39] :
      ( r1_lattices('#skF_8','#skF_2'('#skF_8',B_39,a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),'#skF_9')
      | r4_lattice3('#skF_8',B_39,a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
      | ~ m1_subset_1(B_39,u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2809])).

tff(c_2818,plain,(
    ! [B_531] :
      ( r1_lattices('#skF_8','#skF_2'('#skF_8',B_531,a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),'#skF_9')
      | r4_lattice3('#skF_8',B_531,a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
      | ~ m1_subset_1(B_531,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2816])).

tff(c_2822,plain,
    ( ~ l3_lattices('#skF_8')
    | v2_struct_0('#skF_8')
    | r4_lattice3('#skF_8','#skF_9',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_8')) ),
    inference(resolution,[status(thm)],[c_2818,c_30])).

tff(c_2825,plain,
    ( v2_struct_0('#skF_8')
    | r4_lattice3('#skF_8','#skF_9',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_72,c_2822])).

tff(c_2826,plain,(
    r4_lattice3('#skF_8','#skF_9',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2825])).

tff(c_151,plain,(
    ! [A_161,D_162,B_163,C_164] :
      ( r1_lattices(A_161,D_162,B_163)
      | ~ r2_hidden(D_162,C_164)
      | ~ m1_subset_1(D_162,u1_struct_0(A_161))
      | ~ r4_lattice3(A_161,B_163,C_164)
      | ~ m1_subset_1(B_163,u1_struct_0(A_161))
      | ~ l3_lattices(A_161)
      | v2_struct_0(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_758,plain,(
    ! [C_266,A_265,D_262,B_264,B_263] :
      ( r1_lattices(A_265,D_262,B_263)
      | ~ m1_subset_1(D_262,u1_struct_0(A_265))
      | ~ r4_lattice3(A_265,B_263,a_2_9_lattice3(B_264,C_266))
      | ~ m1_subset_1(B_263,u1_struct_0(A_265))
      | ~ l3_lattices(A_265)
      | v2_struct_0(A_265)
      | ~ r3_lattice3(B_264,D_262,C_266)
      | ~ m1_subset_1(D_262,u1_struct_0(B_264))
      | ~ l3_lattices(B_264)
      | ~ v4_lattice3(B_264)
      | ~ v10_lattices(B_264)
      | v2_struct_0(B_264) ) ),
    inference(resolution,[status(thm)],[c_48,c_151])).

tff(c_778,plain,(
    ! [C_266,B_64,A_49,B_264,B_263] :
      ( r1_lattices(A_49,'#skF_3'(A_49,B_64),B_263)
      | ~ r4_lattice3(A_49,B_263,a_2_9_lattice3(B_264,C_266))
      | ~ m1_subset_1(B_263,u1_struct_0(A_49))
      | ~ r3_lattice3(B_264,'#skF_3'(A_49,B_64),C_266)
      | ~ m1_subset_1('#skF_3'(A_49,B_64),u1_struct_0(B_264))
      | ~ l3_lattices(B_264)
      | ~ v4_lattice3(B_264)
      | ~ v10_lattices(B_264)
      | v2_struct_0(B_264)
      | ~ v4_lattice3(A_49)
      | ~ l3_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_46,c_758])).

tff(c_2830,plain,(
    ! [B_64] :
      ( r1_lattices('#skF_8','#skF_3'('#skF_8',B_64),'#skF_9')
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_8'))
      | ~ r3_lattice3('#skF_8','#skF_3'('#skF_8',B_64),a_2_9_lattice3('#skF_8','#skF_10'))
      | ~ m1_subset_1('#skF_3'('#skF_8',B_64),u1_struct_0('#skF_8'))
      | ~ v10_lattices('#skF_8')
      | ~ v4_lattice3('#skF_8')
      | ~ l3_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2826,c_778])).

tff(c_2840,plain,(
    ! [B_64] :
      ( r1_lattices('#skF_8','#skF_3'('#skF_8',B_64),'#skF_9')
      | ~ r3_lattice3('#skF_8','#skF_3'('#skF_8',B_64),a_2_9_lattice3('#skF_8','#skF_10'))
      | ~ m1_subset_1('#skF_3'('#skF_8',B_64),u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_74,c_76,c_70,c_2830])).

tff(c_2841,plain,(
    ! [B_64] :
      ( r1_lattices('#skF_8','#skF_3'('#skF_8',B_64),'#skF_9')
      | ~ r3_lattice3('#skF_8','#skF_3'('#skF_8',B_64),a_2_9_lattice3('#skF_8','#skF_10'))
      | ~ m1_subset_1('#skF_3'('#skF_8',B_64),u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2840])).

tff(c_3645,plain,
    ( r1_lattices('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),'#skF_9')
    | ~ m1_subset_1('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),u1_struct_0('#skF_8'))
    | ~ v10_lattices('#skF_8')
    | ~ v4_lattice3('#skF_8')
    | ~ l3_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_3632,c_2841])).

tff(c_3664,plain,
    ( r1_lattices('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),'#skF_9')
    | ~ m1_subset_1('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),u1_struct_0('#skF_8'))
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_74,c_76,c_3645])).

tff(c_3665,plain,
    ( r1_lattices('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),'#skF_9')
    | ~ m1_subset_1('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),u1_struct_0('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3664])).

tff(c_3673,plain,(
    ~ m1_subset_1('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),u1_struct_0('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_3665])).

tff(c_3676,plain,
    ( ~ v4_lattice3('#skF_8')
    | ~ l3_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_46,c_3673])).

tff(c_3679,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_74,c_3676])).

tff(c_3681,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3679])).

tff(c_3683,plain,(
    m1_subset_1('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),u1_struct_0('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_3665])).

tff(c_3757,plain,
    ( '#skF_6'('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),'#skF_8',a_2_9_lattice3('#skF_8','#skF_10')) = '#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
    | ~ v10_lattices('#skF_8')
    | ~ v4_lattice3('#skF_8')
    | ~ l3_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_3683,c_3755])).

tff(c_3763,plain,
    ( '#skF_6'('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),'#skF_8',a_2_9_lattice3('#skF_8','#skF_10')) = '#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_74,c_76,c_3757])).

tff(c_3764,plain,(
    '#skF_6'('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),'#skF_8',a_2_9_lattice3('#skF_8','#skF_10')) = '#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3763])).

tff(c_3817,plain,
    ( r3_lattice3('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),a_2_9_lattice3('#skF_8','#skF_10'))
    | ~ r2_hidden('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
    | ~ l3_lattices('#skF_8')
    | ~ v4_lattice3('#skF_8')
    | ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_3764,c_50])).

tff(c_3860,plain,
    ( r3_lattice3('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),a_2_9_lattice3('#skF_8','#skF_10'))
    | ~ r2_hidden('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_3817])).

tff(c_3861,plain,
    ( r3_lattice3('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),a_2_9_lattice3('#skF_8','#skF_10'))
    | ~ r2_hidden('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3860])).

tff(c_3981,plain,(
    ~ r2_hidden('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_3861])).

tff(c_3984,plain,
    ( ~ r3_lattice3('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),a_2_9_lattice3('#skF_8','#skF_10'))
    | ~ m1_subset_1('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),u1_struct_0('#skF_8'))
    | ~ l3_lattices('#skF_8')
    | ~ v4_lattice3('#skF_8')
    | ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_3981])).

tff(c_3987,plain,
    ( ~ r3_lattice3('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),a_2_9_lattice3('#skF_8','#skF_10'))
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_3683,c_3984])).

tff(c_3988,plain,(
    ~ r3_lattice3('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),a_2_9_lattice3('#skF_8','#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3987])).

tff(c_4005,plain,
    ( ~ v10_lattices('#skF_8')
    | ~ v4_lattice3('#skF_8')
    | ~ l3_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_3631,c_3988])).

tff(c_4008,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_74,c_76,c_4005])).

tff(c_4010,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4008])).

tff(c_4011,plain,(
    r3_lattice3('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),a_2_9_lattice3('#skF_8','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_3861])).

tff(c_64,plain,(
    ! [A_81,B_93,C_99] :
      ( m1_subset_1('#skF_7'(A_81,B_93,C_99),u1_struct_0(A_81))
      | k16_lattice3(A_81,C_99) = B_93
      | ~ r3_lattice3(A_81,B_93,C_99)
      | ~ m1_subset_1(B_93,u1_struct_0(A_81))
      | ~ l3_lattices(A_81)
      | ~ v4_lattice3(A_81)
      | ~ v10_lattices(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_227,plain,(
    ! [A_175,B_176,C_177] :
      ( r3_lattice3(A_175,'#skF_7'(A_175,B_176,C_177),C_177)
      | k16_lattice3(A_175,C_177) = B_176
      | ~ r3_lattice3(A_175,B_176,C_177)
      | ~ m1_subset_1(B_176,u1_struct_0(A_175))
      | ~ l3_lattices(A_175)
      | ~ v4_lattice3(A_175)
      | ~ v10_lattices(A_175)
      | v2_struct_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_932,plain,(
    ! [A_320,B_321,C_322] :
      ( '#skF_6'('#skF_7'(A_320,B_321,C_322),A_320,C_322) = '#skF_7'(A_320,B_321,C_322)
      | ~ m1_subset_1('#skF_7'(A_320,B_321,C_322),u1_struct_0(A_320))
      | k16_lattice3(A_320,C_322) = B_321
      | ~ r3_lattice3(A_320,B_321,C_322)
      | ~ m1_subset_1(B_321,u1_struct_0(A_320))
      | ~ l3_lattices(A_320)
      | ~ v4_lattice3(A_320)
      | ~ v10_lattices(A_320)
      | v2_struct_0(A_320) ) ),
    inference(resolution,[status(thm)],[c_227,c_118])).

tff(c_935,plain,(
    ! [A_81,B_93,C_99] :
      ( '#skF_6'('#skF_7'(A_81,B_93,C_99),A_81,C_99) = '#skF_7'(A_81,B_93,C_99)
      | k16_lattice3(A_81,C_99) = B_93
      | ~ r3_lattice3(A_81,B_93,C_99)
      | ~ m1_subset_1(B_93,u1_struct_0(A_81))
      | ~ l3_lattices(A_81)
      | ~ v4_lattice3(A_81)
      | ~ v10_lattices(A_81)
      | v2_struct_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_64,c_932])).

tff(c_3699,plain,(
    ! [C_99] :
      ( '#skF_6'('#skF_7'('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),C_99),'#skF_8',C_99) = '#skF_7'('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),C_99)
      | k16_lattice3('#skF_8',C_99) = '#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
      | ~ r3_lattice3('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),C_99)
      | ~ l3_lattices('#skF_8')
      | ~ v4_lattice3('#skF_8')
      | ~ v10_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_3683,c_935])).

tff(c_3713,plain,(
    ! [C_99] :
      ( '#skF_6'('#skF_7'('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),C_99),'#skF_8',C_99) = '#skF_7'('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),C_99)
      | k16_lattice3('#skF_8',C_99) = '#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
      | ~ r3_lattice3('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),C_99)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_3699])).

tff(c_6114,plain,(
    ! [C_717] :
      ( '#skF_6'('#skF_7'('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),C_717),'#skF_8',C_717) = '#skF_7'('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),C_717)
      | k16_lattice3('#skF_8',C_717) = '#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
      | ~ r3_lattice3('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),C_717) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3713])).

tff(c_4139,plain,(
    ! [B_638,A_639,C_637,B_640,C_642,B_641] :
      ( r1_lattices(B_638,'#skF_6'(A_639,B_638,C_642),B_641)
      | ~ r4_lattice3(B_638,B_641,a_2_9_lattice3(B_640,C_637))
      | ~ m1_subset_1(B_641,u1_struct_0(B_638))
      | ~ r3_lattice3(B_640,'#skF_6'(A_639,B_638,C_642),C_637)
      | ~ m1_subset_1('#skF_6'(A_639,B_638,C_642),u1_struct_0(B_640))
      | ~ l3_lattices(B_640)
      | ~ v4_lattice3(B_640)
      | ~ v10_lattices(B_640)
      | v2_struct_0(B_640)
      | ~ r2_hidden(A_639,a_2_9_lattice3(B_638,C_642))
      | ~ l3_lattices(B_638)
      | ~ v4_lattice3(B_638)
      | ~ v10_lattices(B_638)
      | v2_struct_0(B_638) ) ),
    inference(resolution,[status(thm)],[c_54,c_758])).

tff(c_4143,plain,(
    ! [A_639,C_642] :
      ( r1_lattices('#skF_8','#skF_6'(A_639,'#skF_8',C_642),'#skF_9')
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_8'))
      | ~ r3_lattice3('#skF_8','#skF_6'(A_639,'#skF_8',C_642),a_2_9_lattice3('#skF_8','#skF_10'))
      | ~ m1_subset_1('#skF_6'(A_639,'#skF_8',C_642),u1_struct_0('#skF_8'))
      | ~ r2_hidden(A_639,a_2_9_lattice3('#skF_8',C_642))
      | ~ l3_lattices('#skF_8')
      | ~ v4_lattice3('#skF_8')
      | ~ v10_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2826,c_4139])).

tff(c_4150,plain,(
    ! [A_639,C_642] :
      ( r1_lattices('#skF_8','#skF_6'(A_639,'#skF_8',C_642),'#skF_9')
      | ~ r3_lattice3('#skF_8','#skF_6'(A_639,'#skF_8',C_642),a_2_9_lattice3('#skF_8','#skF_10'))
      | ~ m1_subset_1('#skF_6'(A_639,'#skF_8',C_642),u1_struct_0('#skF_8'))
      | ~ r2_hidden(A_639,a_2_9_lattice3('#skF_8',C_642))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_4143])).

tff(c_4153,plain,(
    ! [A_643,C_644] :
      ( r1_lattices('#skF_8','#skF_6'(A_643,'#skF_8',C_644),'#skF_9')
      | ~ r3_lattice3('#skF_8','#skF_6'(A_643,'#skF_8',C_644),a_2_9_lattice3('#skF_8','#skF_10'))
      | ~ m1_subset_1('#skF_6'(A_643,'#skF_8',C_644),u1_struct_0('#skF_8'))
      | ~ r2_hidden(A_643,a_2_9_lattice3('#skF_8',C_644)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4150])).

tff(c_4240,plain,(
    ! [A_75] :
      ( r1_lattices('#skF_8','#skF_6'(A_75,'#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),'#skF_9')
      | ~ m1_subset_1('#skF_6'(A_75,'#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),u1_struct_0('#skF_8'))
      | ~ r2_hidden(A_75,a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
      | ~ l3_lattices('#skF_8')
      | ~ v4_lattice3('#skF_8')
      | ~ v10_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_50,c_4153])).

tff(c_4286,plain,(
    ! [A_75] :
      ( r1_lattices('#skF_8','#skF_6'(A_75,'#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),'#skF_9')
      | ~ m1_subset_1('#skF_6'(A_75,'#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),u1_struct_0('#skF_8'))
      | ~ r2_hidden(A_75,a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_4240])).

tff(c_4288,plain,(
    ! [A_645] :
      ( r1_lattices('#skF_8','#skF_6'(A_645,'#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),'#skF_9')
      | ~ m1_subset_1('#skF_6'(A_645,'#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),u1_struct_0('#skF_8'))
      | ~ r2_hidden(A_645,a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4286])).

tff(c_4379,plain,(
    ! [A_75] :
      ( r1_lattices('#skF_8','#skF_6'(A_75,'#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),'#skF_9')
      | ~ r2_hidden(A_75,a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
      | ~ l3_lattices('#skF_8')
      | ~ v4_lattice3('#skF_8')
      | ~ v10_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_54,c_4288])).

tff(c_4422,plain,(
    ! [A_75] :
      ( r1_lattices('#skF_8','#skF_6'(A_75,'#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),'#skF_9')
      | ~ r2_hidden(A_75,a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_4379])).

tff(c_4423,plain,(
    ! [A_75] :
      ( r1_lattices('#skF_8','#skF_6'(A_75,'#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),'#skF_9')
      | ~ r2_hidden(A_75,a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4422])).

tff(c_6139,plain,
    ( r1_lattices('#skF_8','#skF_7'('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),a_2_9_lattice3('#skF_8','#skF_10')),'#skF_9')
    | ~ r2_hidden('#skF_7'('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),a_2_9_lattice3('#skF_8','#skF_10')),a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
    | '#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))) = k16_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))
    | ~ r3_lattice3('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),a_2_9_lattice3('#skF_8','#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6114,c_4423])).

tff(c_6196,plain,
    ( r1_lattices('#skF_8','#skF_7'('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),a_2_9_lattice3('#skF_8','#skF_10')),'#skF_9')
    | ~ r2_hidden('#skF_7'('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),a_2_9_lattice3('#skF_8','#skF_10')),a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
    | '#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))) = k16_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4011,c_6139])).

tff(c_6309,plain,(
    ~ r2_hidden('#skF_7'('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),a_2_9_lattice3('#skF_8','#skF_10')),a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_6196])).

tff(c_6312,plain,
    ( ~ r3_lattice3('#skF_8','#skF_7'('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),a_2_9_lattice3('#skF_8','#skF_10')),a_2_9_lattice3('#skF_8','#skF_10'))
    | ~ m1_subset_1('#skF_7'('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),a_2_9_lattice3('#skF_8','#skF_10')),u1_struct_0('#skF_8'))
    | ~ l3_lattices('#skF_8')
    | ~ v4_lattice3('#skF_8')
    | ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_6309])).

tff(c_6315,plain,
    ( ~ r3_lattice3('#skF_8','#skF_7'('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),a_2_9_lattice3('#skF_8','#skF_10')),a_2_9_lattice3('#skF_8','#skF_10'))
    | ~ m1_subset_1('#skF_7'('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),a_2_9_lattice3('#skF_8','#skF_10')),u1_struct_0('#skF_8'))
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_6312])).

tff(c_6316,plain,
    ( ~ r3_lattice3('#skF_8','#skF_7'('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),a_2_9_lattice3('#skF_8','#skF_10')),a_2_9_lattice3('#skF_8','#skF_10'))
    | ~ m1_subset_1('#skF_7'('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),a_2_9_lattice3('#skF_8','#skF_10')),u1_struct_0('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_6315])).

tff(c_6317,plain,(
    ~ m1_subset_1('#skF_7'('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),a_2_9_lattice3('#skF_8','#skF_10')),u1_struct_0('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_6316])).

tff(c_6320,plain,
    ( '#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))) = k16_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))
    | ~ r3_lattice3('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),a_2_9_lattice3('#skF_8','#skF_10'))
    | ~ m1_subset_1('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),u1_struct_0('#skF_8'))
    | ~ l3_lattices('#skF_8')
    | ~ v4_lattice3('#skF_8')
    | ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_64,c_6317])).

tff(c_6323,plain,
    ( '#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))) = k16_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_3683,c_4011,c_6320])).

tff(c_6324,plain,(
    '#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))) = k16_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_6323])).

tff(c_826,plain,(
    ! [D_285,A_288,C_289,B_286,B_287] :
      ( r1_lattices(A_288,B_286,D_285)
      | ~ m1_subset_1(D_285,u1_struct_0(A_288))
      | ~ r3_lattice3(A_288,B_286,a_2_9_lattice3(B_287,C_289))
      | ~ m1_subset_1(B_286,u1_struct_0(A_288))
      | ~ l3_lattices(A_288)
      | v2_struct_0(A_288)
      | ~ r3_lattice3(B_287,D_285,C_289)
      | ~ m1_subset_1(D_285,u1_struct_0(B_287))
      | ~ l3_lattices(B_287)
      | ~ v4_lattice3(B_287)
      | ~ v10_lattices(B_287)
      | v2_struct_0(B_287) ) ),
    inference(resolution,[status(thm)],[c_48,c_161])).

tff(c_4837,plain,(
    ! [B_670,C_673,C_672,B_671,B_668,A_669] :
      ( r1_lattices(B_668,B_671,'#skF_6'(A_669,B_668,C_672))
      | ~ r3_lattice3(B_668,B_671,a_2_9_lattice3(B_670,C_673))
      | ~ m1_subset_1(B_671,u1_struct_0(B_668))
      | ~ r3_lattice3(B_670,'#skF_6'(A_669,B_668,C_672),C_673)
      | ~ m1_subset_1('#skF_6'(A_669,B_668,C_672),u1_struct_0(B_670))
      | ~ l3_lattices(B_670)
      | ~ v4_lattice3(B_670)
      | ~ v10_lattices(B_670)
      | v2_struct_0(B_670)
      | ~ r2_hidden(A_669,a_2_9_lattice3(B_668,C_672))
      | ~ l3_lattices(B_668)
      | ~ v4_lattice3(B_668)
      | ~ v10_lattices(B_668)
      | v2_struct_0(B_668) ) ),
    inference(resolution,[status(thm)],[c_54,c_826])).

tff(c_4839,plain,(
    ! [A_669,C_672] :
      ( r1_lattices('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),'#skF_6'(A_669,'#skF_8',C_672))
      | ~ m1_subset_1('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),u1_struct_0('#skF_8'))
      | ~ r3_lattice3('#skF_8','#skF_6'(A_669,'#skF_8',C_672),'#skF_10')
      | ~ m1_subset_1('#skF_6'(A_669,'#skF_8',C_672),u1_struct_0('#skF_8'))
      | ~ r2_hidden(A_669,a_2_9_lattice3('#skF_8',C_672))
      | ~ l3_lattices('#skF_8')
      | ~ v4_lattice3('#skF_8')
      | ~ v10_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_4011,c_4837])).

tff(c_4863,plain,(
    ! [A_669,C_672] :
      ( r1_lattices('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),'#skF_6'(A_669,'#skF_8',C_672))
      | ~ r3_lattice3('#skF_8','#skF_6'(A_669,'#skF_8',C_672),'#skF_10')
      | ~ m1_subset_1('#skF_6'(A_669,'#skF_8',C_672),u1_struct_0('#skF_8'))
      | ~ r2_hidden(A_669,a_2_9_lattice3('#skF_8',C_672))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_3683,c_4839])).

tff(c_4864,plain,(
    ! [A_669,C_672] :
      ( r1_lattices('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))),'#skF_6'(A_669,'#skF_8',C_672))
      | ~ r3_lattice3('#skF_8','#skF_6'(A_669,'#skF_8',C_672),'#skF_10')
      | ~ m1_subset_1('#skF_6'(A_669,'#skF_8',C_672),u1_struct_0('#skF_8'))
      | ~ r2_hidden(A_669,a_2_9_lattice3('#skF_8',C_672)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4863])).

tff(c_7274,plain,(
    ! [A_764,C_765] :
      ( r1_lattices('#skF_8',k16_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),'#skF_6'(A_764,'#skF_8',C_765))
      | ~ r3_lattice3('#skF_8','#skF_6'(A_764,'#skF_8',C_765),'#skF_10')
      | ~ m1_subset_1('#skF_6'(A_764,'#skF_8',C_765),u1_struct_0('#skF_8'))
      | ~ r2_hidden(A_764,a_2_9_lattice3('#skF_8',C_765)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6324,c_4864])).

tff(c_7300,plain,(
    ! [C_622] :
      ( r1_lattices('#skF_8',k16_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),'#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',C_622)))
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',C_622)),'#skF_8',C_622),'#skF_10')
      | ~ m1_subset_1('#skF_6'('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',C_622)),'#skF_8',C_622),u1_struct_0('#skF_8'))
      | ~ r2_hidden('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',C_622)),a_2_9_lattice3('#skF_8',C_622))
      | ~ v10_lattices('#skF_8')
      | ~ v4_lattice3('#skF_8')
      | ~ l3_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3765,c_7274])).

tff(c_7386,plain,(
    ! [C_622] :
      ( r1_lattices('#skF_8',k16_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),'#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',C_622)))
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',C_622)),'#skF_8',C_622),'#skF_10')
      | ~ m1_subset_1('#skF_6'('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',C_622)),'#skF_8',C_622),u1_struct_0('#skF_8'))
      | ~ r2_hidden('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',C_622)),a_2_9_lattice3('#skF_8',C_622))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_74,c_76,c_7300])).

tff(c_8324,plain,(
    ! [C_840] :
      ( r1_lattices('#skF_8',k16_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),'#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',C_840)))
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',C_840)),'#skF_8',C_840),'#skF_10')
      | ~ m1_subset_1('#skF_6'('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',C_840)),'#skF_8',C_840),u1_struct_0('#skF_8'))
      | ~ r2_hidden('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',C_840)),a_2_9_lattice3('#skF_8',C_840)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_7386])).

tff(c_8332,plain,(
    ! [C_77] :
      ( r1_lattices('#skF_8',k16_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),'#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',C_77)))
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',C_77)),'#skF_8',C_77),'#skF_10')
      | ~ r2_hidden('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',C_77)),a_2_9_lattice3('#skF_8',C_77))
      | ~ l3_lattices('#skF_8')
      | ~ v4_lattice3('#skF_8')
      | ~ v10_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_54,c_8324])).

tff(c_8340,plain,(
    ! [C_77] :
      ( r1_lattices('#skF_8',k16_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),'#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',C_77)))
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',C_77)),'#skF_8',C_77),'#skF_10')
      | ~ r2_hidden('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',C_77)),a_2_9_lattice3('#skF_8',C_77))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_8332])).

tff(c_8342,plain,(
    ! [C_841] :
      ( r1_lattices('#skF_8',k16_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),'#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',C_841)))
      | ~ r3_lattice3('#skF_8','#skF_6'('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',C_841)),'#skF_8',C_841),'#skF_10')
      | ~ r2_hidden('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8',C_841)),a_2_9_lattice3('#skF_8',C_841)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_8340])).

tff(c_8350,plain,
    ( r1_lattices('#skF_8',k16_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),'#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
    | ~ r2_hidden('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),a_2_9_lattice3('#skF_8','#skF_10'))
    | ~ l3_lattices('#skF_8')
    | ~ v4_lattice3('#skF_8')
    | ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_50,c_8342])).

tff(c_8358,plain,
    ( r1_lattices('#skF_8',k16_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),'#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
    | ~ r2_hidden('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),a_2_9_lattice3('#skF_8','#skF_10'))
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_8350])).

tff(c_8359,plain,
    ( r1_lattices('#skF_8',k16_lattice3('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),'#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
    | ~ r2_hidden('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),a_2_9_lattice3('#skF_8','#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_8358])).

tff(c_8360,plain,(
    ~ r2_hidden('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),a_2_9_lattice3('#skF_8','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_8359])).

tff(c_8363,plain,
    ( ~ r3_lattice3('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),'#skF_10')
    | ~ m1_subset_1('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),u1_struct_0('#skF_8'))
    | ~ l3_lattices('#skF_8')
    | ~ v4_lattice3('#skF_8')
    | ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_8360])).

tff(c_8366,plain,
    ( ~ r3_lattice3('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),'#skF_10')
    | ~ m1_subset_1('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),u1_struct_0('#skF_8'))
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_8363])).

tff(c_8367,plain,
    ( ~ r3_lattice3('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),'#skF_10')
    | ~ m1_subset_1('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),u1_struct_0('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_8366])).

tff(c_8368,plain,(
    ~ m1_subset_1('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),u1_struct_0('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_8367])).

tff(c_8371,plain,
    ( ~ v4_lattice3('#skF_8')
    | ~ l3_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_46,c_8368])).

tff(c_8374,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_74,c_8371])).

tff(c_8376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_8374])).

tff(c_8377,plain,(
    ~ r3_lattice3('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_8367])).

tff(c_8415,plain,
    ( ~ v10_lattices('#skF_8')
    | ~ v4_lattice3('#skF_8')
    | ~ l3_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_3631,c_8377])).

tff(c_8418,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_74,c_76,c_8415])).

tff(c_8420,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_8418])).

tff(c_8422,plain,(
    r2_hidden('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),a_2_9_lattice3('#skF_8','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_8359])).

tff(c_8443,plain,
    ( '#skF_6'('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),'#skF_8','#skF_10') = '#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))
    | ~ l3_lattices('#skF_8')
    | ~ v4_lattice3('#skF_8')
    | ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_8422,c_52])).

tff(c_8452,plain,
    ( '#skF_6'('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),'#skF_8','#skF_10') = '#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_8443])).

tff(c_8453,plain,(
    '#skF_6'('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),'#skF_8','#skF_10') = '#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_8452])).

tff(c_8522,plain,
    ( m1_subset_1('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),u1_struct_0('#skF_8'))
    | ~ r2_hidden('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),a_2_9_lattice3('#skF_8','#skF_10'))
    | ~ l3_lattices('#skF_8')
    | ~ v4_lattice3('#skF_8')
    | ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_8453,c_54])).

tff(c_8585,plain,
    ( m1_subset_1('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),u1_struct_0('#skF_8'))
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_8422,c_8522])).

tff(c_8586,plain,(
    m1_subset_1('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),u1_struct_0('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_8585])).

tff(c_8519,plain,
    ( r3_lattice3('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),'#skF_10')
    | ~ r2_hidden('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),a_2_9_lattice3('#skF_8','#skF_10'))
    | ~ l3_lattices('#skF_8')
    | ~ v4_lattice3('#skF_8')
    | ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_8453,c_50])).

tff(c_8582,plain,
    ( r3_lattice3('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),'#skF_10')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_8422,c_8519])).

tff(c_8583,plain,(
    r3_lattice3('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),'#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_8582])).

tff(c_62,plain,(
    ! [A_81,B_93,C_99] :
      ( r3_lattice3(A_81,'#skF_7'(A_81,B_93,C_99),C_99)
      | k16_lattice3(A_81,C_99) = B_93
      | ~ r3_lattice3(A_81,B_93,C_99)
      | ~ m1_subset_1(B_93,u1_struct_0(A_81))
      | ~ l3_lattices(A_81)
      | ~ v4_lattice3(A_81)
      | ~ v10_lattices(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_44,plain,(
    ! [A_49,B_64] :
      ( r4_lattice3(A_49,'#skF_3'(A_49,B_64),B_64)
      | ~ v4_lattice3(A_49)
      | ~ l3_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_5384,plain,(
    ! [B_697,B_696,C_692,A_693,B_695,C_694] :
      ( r1_lattices(A_693,'#skF_7'(A_693,B_697,C_694),B_696)
      | ~ r4_lattice3(A_693,B_696,a_2_9_lattice3(B_695,C_692))
      | ~ m1_subset_1(B_696,u1_struct_0(A_693))
      | ~ r3_lattice3(B_695,'#skF_7'(A_693,B_697,C_694),C_692)
      | ~ m1_subset_1('#skF_7'(A_693,B_697,C_694),u1_struct_0(B_695))
      | ~ l3_lattices(B_695)
      | ~ v4_lattice3(B_695)
      | ~ v10_lattices(B_695)
      | v2_struct_0(B_695)
      | k16_lattice3(A_693,C_694) = B_697
      | ~ r3_lattice3(A_693,B_697,C_694)
      | ~ m1_subset_1(B_697,u1_struct_0(A_693))
      | ~ l3_lattices(A_693)
      | ~ v4_lattice3(A_693)
      | ~ v10_lattices(A_693)
      | v2_struct_0(A_693) ) ),
    inference(resolution,[status(thm)],[c_64,c_758])).

tff(c_5403,plain,(
    ! [B_697,C_692,B_695,C_694,A_49] :
      ( r1_lattices(A_49,'#skF_7'(A_49,B_697,C_694),'#skF_3'(A_49,a_2_9_lattice3(B_695,C_692)))
      | ~ m1_subset_1('#skF_3'(A_49,a_2_9_lattice3(B_695,C_692)),u1_struct_0(A_49))
      | ~ r3_lattice3(B_695,'#skF_7'(A_49,B_697,C_694),C_692)
      | ~ m1_subset_1('#skF_7'(A_49,B_697,C_694),u1_struct_0(B_695))
      | ~ l3_lattices(B_695)
      | ~ v4_lattice3(B_695)
      | ~ v10_lattices(B_695)
      | v2_struct_0(B_695)
      | k16_lattice3(A_49,C_694) = B_697
      | ~ r3_lattice3(A_49,B_697,C_694)
      | ~ m1_subset_1(B_697,u1_struct_0(A_49))
      | ~ v10_lattices(A_49)
      | ~ v4_lattice3(A_49)
      | ~ l3_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_44,c_5384])).

tff(c_185,plain,(
    ! [B_76,B_170,A_75,C_77] :
      ( r3_lattices(B_76,B_170,'#skF_6'(A_75,B_76,C_77))
      | ~ r1_lattices(B_76,B_170,'#skF_6'(A_75,B_76,C_77))
      | ~ m1_subset_1(B_170,u1_struct_0(B_76))
      | ~ v9_lattices(B_76)
      | ~ v8_lattices(B_76)
      | ~ v6_lattices(B_76)
      | ~ r2_hidden(A_75,a_2_9_lattice3(B_76,C_77))
      | ~ l3_lattices(B_76)
      | ~ v4_lattice3(B_76)
      | ~ v10_lattices(B_76)
      | v2_struct_0(B_76) ) ),
    inference(resolution,[status(thm)],[c_54,c_171])).

tff(c_8504,plain,(
    ! [B_170] :
      ( r3_lattices('#skF_8',B_170,'#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
      | ~ r1_lattices('#skF_8',B_170,'#skF_6'('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),'#skF_8','#skF_10'))
      | ~ m1_subset_1(B_170,u1_struct_0('#skF_8'))
      | ~ v9_lattices('#skF_8')
      | ~ v8_lattices('#skF_8')
      | ~ v6_lattices('#skF_8')
      | ~ r2_hidden('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),a_2_9_lattice3('#skF_8','#skF_10'))
      | ~ l3_lattices('#skF_8')
      | ~ v4_lattice3('#skF_8')
      | ~ v10_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8453,c_185])).

tff(c_8570,plain,(
    ! [B_170] :
      ( r3_lattices('#skF_8',B_170,'#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
      | ~ r1_lattices('#skF_8',B_170,'#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
      | ~ m1_subset_1(B_170,u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_8422,c_204,c_226,c_215,c_8453,c_8504])).

tff(c_8635,plain,(
    ! [B_847] :
      ( r3_lattices('#skF_8',B_847,'#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
      | ~ r1_lattices('#skF_8',B_847,'#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
      | ~ m1_subset_1(B_847,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_8570])).

tff(c_60,plain,(
    ! [A_81,B_93,C_99] :
      ( ~ r3_lattices(A_81,'#skF_7'(A_81,B_93,C_99),B_93)
      | k16_lattice3(A_81,C_99) = B_93
      | ~ r3_lattice3(A_81,B_93,C_99)
      | ~ m1_subset_1(B_93,u1_struct_0(A_81))
      | ~ l3_lattices(A_81)
      | ~ v4_lattice3(A_81)
      | ~ v10_lattices(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_8639,plain,(
    ! [C_99] :
      ( k16_lattice3('#skF_8',C_99) = '#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))
      | ~ r3_lattice3('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),C_99)
      | ~ m1_subset_1('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),u1_struct_0('#skF_8'))
      | ~ l3_lattices('#skF_8')
      | ~ v4_lattice3('#skF_8')
      | ~ v10_lattices('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ r1_lattices('#skF_8','#skF_7'('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),C_99),'#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
      | ~ m1_subset_1('#skF_7'('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),C_99),u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_8635,c_60])).

tff(c_8644,plain,(
    ! [C_99] :
      ( k16_lattice3('#skF_8',C_99) = '#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))
      | ~ r3_lattice3('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),C_99)
      | v2_struct_0('#skF_8')
      | ~ r1_lattices('#skF_8','#skF_7'('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),C_99),'#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
      | ~ m1_subset_1('#skF_7'('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),C_99),u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_8586,c_8639])).

tff(c_9502,plain,(
    ! [C_878] :
      ( k16_lattice3('#skF_8',C_878) = '#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))
      | ~ r3_lattice3('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),C_878)
      | ~ r1_lattices('#skF_8','#skF_7'('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),C_878),'#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')))
      | ~ m1_subset_1('#skF_7'('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),C_878),u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_8644])).

tff(c_9509,plain,(
    ! [C_694] :
      ( ~ r3_lattice3('#skF_8','#skF_7'('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),C_694),'#skF_10')
      | ~ m1_subset_1('#skF_7'('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),C_694),u1_struct_0('#skF_8'))
      | k16_lattice3('#skF_8',C_694) = '#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))
      | ~ r3_lattice3('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),C_694)
      | ~ m1_subset_1('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),u1_struct_0('#skF_8'))
      | ~ v10_lattices('#skF_8')
      | ~ v4_lattice3('#skF_8')
      | ~ l3_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_5403,c_9502])).

tff(c_9513,plain,(
    ! [C_694] :
      ( ~ r3_lattice3('#skF_8','#skF_7'('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),C_694),'#skF_10')
      | ~ m1_subset_1('#skF_7'('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),C_694),u1_struct_0('#skF_8'))
      | k16_lattice3('#skF_8',C_694) = '#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))
      | ~ r3_lattice3('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),C_694)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_74,c_76,c_8586,c_9509])).

tff(c_9515,plain,(
    ! [C_879] :
      ( ~ r3_lattice3('#skF_8','#skF_7'('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),C_879),'#skF_10')
      | ~ m1_subset_1('#skF_7'('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),C_879),u1_struct_0('#skF_8'))
      | k16_lattice3('#skF_8',C_879) = '#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))
      | ~ r3_lattice3('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),C_879) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_9513])).

tff(c_9519,plain,(
    ! [C_99] :
      ( ~ r3_lattice3('#skF_8','#skF_7'('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),C_99),'#skF_10')
      | k16_lattice3('#skF_8',C_99) = '#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))
      | ~ r3_lattice3('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),C_99)
      | ~ m1_subset_1('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),u1_struct_0('#skF_8'))
      | ~ l3_lattices('#skF_8')
      | ~ v4_lattice3('#skF_8')
      | ~ v10_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_64,c_9515])).

tff(c_9522,plain,(
    ! [C_99] :
      ( ~ r3_lattice3('#skF_8','#skF_7'('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),C_99),'#skF_10')
      | k16_lattice3('#skF_8',C_99) = '#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))
      | ~ r3_lattice3('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),C_99)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_8586,c_9519])).

tff(c_9544,plain,(
    ! [C_885] :
      ( ~ r3_lattice3('#skF_8','#skF_7'('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),C_885),'#skF_10')
      | k16_lattice3('#skF_8',C_885) = '#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10'))
      | ~ r3_lattice3('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),C_885) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_9522])).

tff(c_9548,plain,
    ( '#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')) = k16_lattice3('#skF_8','#skF_10')
    | ~ r3_lattice3('#skF_8','#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),'#skF_10')
    | ~ m1_subset_1('#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')),u1_struct_0('#skF_8'))
    | ~ l3_lattices('#skF_8')
    | ~ v4_lattice3('#skF_8')
    | ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_62,c_9544])).

tff(c_9551,plain,
    ( '#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')) = k16_lattice3('#skF_8','#skF_10')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_8586,c_8583,c_9548])).

tff(c_9552,plain,(
    '#skF_3'('#skF_8',a_2_9_lattice3('#skF_8','#skF_10')) = k16_lattice3('#skF_8','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_9551])).

tff(c_9572,plain,(
    m1_subset_1(k16_lattice3('#skF_8','#skF_10'),u1_struct_0('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9552,c_8586])).

tff(c_56,plain,(
    ! [A_81,D_102,C_99] :
      ( r3_lattices(A_81,D_102,k16_lattice3(A_81,C_99))
      | ~ r3_lattice3(A_81,D_102,C_99)
      | ~ m1_subset_1(D_102,u1_struct_0(A_81))
      | ~ m1_subset_1(k16_lattice3(A_81,C_99),u1_struct_0(A_81))
      | ~ l3_lattices(A_81)
      | ~ v4_lattice3(A_81)
      | ~ v10_lattices(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_9796,plain,(
    ! [D_102] :
      ( r3_lattices('#skF_8',D_102,k16_lattice3('#skF_8','#skF_10'))
      | ~ r3_lattice3('#skF_8',D_102,'#skF_10')
      | ~ m1_subset_1(D_102,u1_struct_0('#skF_8'))
      | ~ l3_lattices('#skF_8')
      | ~ v4_lattice3('#skF_8')
      | ~ v10_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_9572,c_56])).

tff(c_9822,plain,(
    ! [D_102] :
      ( r3_lattices('#skF_8',D_102,k16_lattice3('#skF_8','#skF_10'))
      | ~ r3_lattice3('#skF_8',D_102,'#skF_10')
      | ~ m1_subset_1(D_102,u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_9796])).

tff(c_10326,plain,(
    ! [D_898] :
      ( r3_lattices('#skF_8',D_898,k16_lattice3('#skF_8','#skF_10'))
      | ~ r3_lattice3('#skF_8',D_898,'#skF_10')
      | ~ m1_subset_1(D_898,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_9822])).

tff(c_66,plain,(
    ~ r3_lattices('#skF_8','#skF_9',k16_lattice3('#skF_8','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_10335,plain,
    ( ~ r3_lattice3('#skF_8','#skF_9','#skF_10')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_8')) ),
    inference(resolution,[status(thm)],[c_10326,c_66])).

tff(c_10347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_10335])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:33:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.97/3.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.97/4.02  
% 10.97/4.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.97/4.02  %$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > a_2_9_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_4 > #skF_6 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_5
% 10.97/4.02  
% 10.97/4.02  %Foreground sorts:
% 10.97/4.02  
% 10.97/4.02  
% 10.97/4.02  %Background operators:
% 10.97/4.02  
% 10.97/4.02  
% 10.97/4.02  %Foreground operators:
% 10.97/4.02  tff(l3_lattices, type, l3_lattices: $i > $o).
% 10.97/4.02  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.97/4.02  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.97/4.02  tff('#skF_4', type, '#skF_4': $i > $i).
% 10.97/4.02  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 10.97/4.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.97/4.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.97/4.02  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 10.97/4.02  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 10.97/4.02  tff(a_2_9_lattice3, type, a_2_9_lattice3: ($i * $i) > $i).
% 10.97/4.02  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.97/4.02  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 10.97/4.02  tff('#skF_10', type, '#skF_10': $i).
% 10.97/4.02  tff(v4_lattices, type, v4_lattices: $i > $o).
% 10.97/4.02  tff(v6_lattices, type, v6_lattices: $i > $o).
% 10.97/4.02  tff(v9_lattices, type, v9_lattices: $i > $o).
% 10.97/4.02  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 10.97/4.02  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.97/4.02  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 10.97/4.02  tff(v5_lattices, type, v5_lattices: $i > $o).
% 10.97/4.02  tff(v10_lattices, type, v10_lattices: $i > $o).
% 10.97/4.02  tff('#skF_9', type, '#skF_9': $i).
% 10.97/4.02  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 10.97/4.02  tff('#skF_8', type, '#skF_8': $i).
% 10.97/4.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.97/4.02  tff(v8_lattices, type, v8_lattices: $i > $o).
% 10.97/4.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.97/4.02  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.97/4.02  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 10.97/4.02  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 10.97/4.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.97/4.02  tff(v7_lattices, type, v7_lattices: $i > $o).
% 10.97/4.02  
% 11.28/4.07  tff(f_182, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) => r3_lattices(A, B, k16_lattice3(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_lattice3)).
% 11.28/4.07  tff(f_122, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v4_lattice3(A) <=> (![B]: (?[C]: ((m1_subset_1(C, u1_struct_0(A)) & r4_lattice3(A, C, B)) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_lattice3)).
% 11.28/4.07  tff(f_84, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattice3)).
% 11.28/4.07  tff(f_102, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_lattice3)).
% 11.28/4.07  tff(f_140, axiom, (![A, B, C]: ((((~v2_struct_0(B) & v10_lattices(B)) & v4_lattice3(B)) & l3_lattices(B)) => (r2_hidden(A, a_2_9_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & r3_lattice3(B, D, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_9_lattice3)).
% 11.28/4.07  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 11.28/4.07  tff(f_66, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 11.28/4.07  tff(f_164, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((B = k16_lattice3(A, C)) <=> (r3_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_lattice3(A, D, C) => r3_lattices(A, D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_lattice3)).
% 11.28/4.07  tff(c_70, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 11.28/4.07  tff(c_68, plain, (r3_lattice3('#skF_8', '#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_182])).
% 11.28/4.07  tff(c_78, plain, (~v2_struct_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_182])).
% 11.28/4.07  tff(c_76, plain, (v10_lattices('#skF_8')), inference(cnfTransformation, [status(thm)], [f_182])).
% 11.28/4.07  tff(c_74, plain, (v4_lattice3('#skF_8')), inference(cnfTransformation, [status(thm)], [f_182])).
% 11.28/4.07  tff(c_72, plain, (l3_lattices('#skF_8')), inference(cnfTransformation, [status(thm)], [f_182])).
% 11.28/4.07  tff(c_46, plain, (![A_49, B_64]: (m1_subset_1('#skF_3'(A_49, B_64), u1_struct_0(A_49)) | ~v4_lattice3(A_49) | ~l3_lattices(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_122])).
% 11.28/4.07  tff(c_26, plain, (![A_5, B_17, C_23]: (m1_subset_1('#skF_1'(A_5, B_17, C_23), u1_struct_0(A_5)) | r3_lattice3(A_5, B_17, C_23) | ~m1_subset_1(B_17, u1_struct_0(A_5)) | ~l3_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.28/4.07  tff(c_34, plain, (![A_27, B_39, C_45]: (m1_subset_1('#skF_2'(A_27, B_39, C_45), u1_struct_0(A_27)) | r4_lattice3(A_27, B_39, C_45) | ~m1_subset_1(B_39, u1_struct_0(A_27)) | ~l3_lattices(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_102])).
% 11.28/4.07  tff(c_32, plain, (![A_27, B_39, C_45]: (r2_hidden('#skF_2'(A_27, B_39, C_45), C_45) | r4_lattice3(A_27, B_39, C_45) | ~m1_subset_1(B_39, u1_struct_0(A_27)) | ~l3_lattices(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_102])).
% 11.28/4.07  tff(c_89, plain, (![A_123, B_124, C_125]: ('#skF_6'(A_123, B_124, C_125)=A_123 | ~r2_hidden(A_123, a_2_9_lattice3(B_124, C_125)) | ~l3_lattices(B_124) | ~v4_lattice3(B_124) | ~v10_lattices(B_124) | v2_struct_0(B_124))), inference(cnfTransformation, [status(thm)], [f_140])).
% 11.28/4.07  tff(c_654, plain, (![A_251, B_252, B_253, C_254]: ('#skF_6'('#skF_2'(A_251, B_252, a_2_9_lattice3(B_253, C_254)), B_253, C_254)='#skF_2'(A_251, B_252, a_2_9_lattice3(B_253, C_254)) | ~l3_lattices(B_253) | ~v4_lattice3(B_253) | ~v10_lattices(B_253) | v2_struct_0(B_253) | r4_lattice3(A_251, B_252, a_2_9_lattice3(B_253, C_254)) | ~m1_subset_1(B_252, u1_struct_0(A_251)) | ~l3_lattices(A_251) | v2_struct_0(A_251))), inference(resolution, [status(thm)], [c_32, c_89])).
% 11.28/4.07  tff(c_50, plain, (![B_76, A_75, C_77]: (r3_lattice3(B_76, '#skF_6'(A_75, B_76, C_77), C_77) | ~r2_hidden(A_75, a_2_9_lattice3(B_76, C_77)) | ~l3_lattices(B_76) | ~v4_lattice3(B_76) | ~v10_lattices(B_76) | v2_struct_0(B_76))), inference(cnfTransformation, [status(thm)], [f_140])).
% 11.28/4.07  tff(c_2032, plain, (![B_454, A_455, B_456, C_457]: (r3_lattice3(B_454, '#skF_2'(A_455, B_456, a_2_9_lattice3(B_454, C_457)), C_457) | ~r2_hidden('#skF_2'(A_455, B_456, a_2_9_lattice3(B_454, C_457)), a_2_9_lattice3(B_454, C_457)) | ~l3_lattices(B_454) | ~v4_lattice3(B_454) | ~v10_lattices(B_454) | v2_struct_0(B_454) | ~l3_lattices(B_454) | ~v4_lattice3(B_454) | ~v10_lattices(B_454) | v2_struct_0(B_454) | r4_lattice3(A_455, B_456, a_2_9_lattice3(B_454, C_457)) | ~m1_subset_1(B_456, u1_struct_0(A_455)) | ~l3_lattices(A_455) | v2_struct_0(A_455))), inference(superposition, [status(thm), theory('equality')], [c_654, c_50])).
% 11.28/4.07  tff(c_2042, plain, (![B_454, A_27, B_39, C_457]: (r3_lattice3(B_454, '#skF_2'(A_27, B_39, a_2_9_lattice3(B_454, C_457)), C_457) | ~l3_lattices(B_454) | ~v4_lattice3(B_454) | ~v10_lattices(B_454) | v2_struct_0(B_454) | r4_lattice3(A_27, B_39, a_2_9_lattice3(B_454, C_457)) | ~m1_subset_1(B_39, u1_struct_0(A_27)) | ~l3_lattices(A_27) | v2_struct_0(A_27))), inference(resolution, [status(thm)], [c_32, c_2032])).
% 11.28/4.07  tff(c_24, plain, (![A_5, B_17, C_23]: (r2_hidden('#skF_1'(A_5, B_17, C_23), C_23) | r3_lattice3(A_5, B_17, C_23) | ~m1_subset_1(B_17, u1_struct_0(A_5)) | ~l3_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.28/4.07  tff(c_161, plain, (![A_165, B_166, D_167, C_168]: (r1_lattices(A_165, B_166, D_167) | ~r2_hidden(D_167, C_168) | ~m1_subset_1(D_167, u1_struct_0(A_165)) | ~r3_lattice3(A_165, B_166, C_168) | ~m1_subset_1(B_166, u1_struct_0(A_165)) | ~l3_lattices(A_165) | v2_struct_0(A_165))), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.28/4.07  tff(c_895, plain, (![B_302, A_306, B_304, C_303, A_305]: (r1_lattices(A_305, B_302, '#skF_1'(A_306, B_304, C_303)) | ~m1_subset_1('#skF_1'(A_306, B_304, C_303), u1_struct_0(A_305)) | ~r3_lattice3(A_305, B_302, C_303) | ~m1_subset_1(B_302, u1_struct_0(A_305)) | ~l3_lattices(A_305) | v2_struct_0(A_305) | r3_lattice3(A_306, B_304, C_303) | ~m1_subset_1(B_304, u1_struct_0(A_306)) | ~l3_lattices(A_306) | v2_struct_0(A_306))), inference(resolution, [status(thm)], [c_24, c_161])).
% 11.28/4.07  tff(c_903, plain, (![A_312, B_313, B_314, C_315]: (r1_lattices(A_312, B_313, '#skF_1'(A_312, B_314, C_315)) | ~r3_lattice3(A_312, B_313, C_315) | ~m1_subset_1(B_313, u1_struct_0(A_312)) | r3_lattice3(A_312, B_314, C_315) | ~m1_subset_1(B_314, u1_struct_0(A_312)) | ~l3_lattices(A_312) | v2_struct_0(A_312))), inference(resolution, [status(thm)], [c_26, c_895])).
% 11.28/4.07  tff(c_30, plain, (![A_27, B_39, C_45]: (~r1_lattices(A_27, '#skF_2'(A_27, B_39, C_45), B_39) | r4_lattice3(A_27, B_39, C_45) | ~m1_subset_1(B_39, u1_struct_0(A_27)) | ~l3_lattices(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_102])).
% 11.28/4.07  tff(c_3293, plain, (![A_579, B_580, C_581, C_582]: (r4_lattice3(A_579, '#skF_1'(A_579, B_580, C_581), C_582) | ~m1_subset_1('#skF_1'(A_579, B_580, C_581), u1_struct_0(A_579)) | ~r3_lattice3(A_579, '#skF_2'(A_579, '#skF_1'(A_579, B_580, C_581), C_582), C_581) | ~m1_subset_1('#skF_2'(A_579, '#skF_1'(A_579, B_580, C_581), C_582), u1_struct_0(A_579)) | r3_lattice3(A_579, B_580, C_581) | ~m1_subset_1(B_580, u1_struct_0(A_579)) | ~l3_lattices(A_579) | v2_struct_0(A_579))), inference(resolution, [status(thm)], [c_903, c_30])).
% 11.28/4.07  tff(c_3298, plain, (![A_583, B_584, C_585]: (~m1_subset_1('#skF_2'(A_583, '#skF_1'(A_583, B_584, C_585), a_2_9_lattice3(A_583, C_585)), u1_struct_0(A_583)) | r3_lattice3(A_583, B_584, C_585) | ~m1_subset_1(B_584, u1_struct_0(A_583)) | ~v4_lattice3(A_583) | ~v10_lattices(A_583) | r4_lattice3(A_583, '#skF_1'(A_583, B_584, C_585), a_2_9_lattice3(A_583, C_585)) | ~m1_subset_1('#skF_1'(A_583, B_584, C_585), u1_struct_0(A_583)) | ~l3_lattices(A_583) | v2_struct_0(A_583))), inference(resolution, [status(thm)], [c_2042, c_3293])).
% 11.28/4.07  tff(c_3320, plain, (![A_588, B_589, C_590]: (r3_lattice3(A_588, B_589, C_590) | ~m1_subset_1(B_589, u1_struct_0(A_588)) | ~v4_lattice3(A_588) | ~v10_lattices(A_588) | r4_lattice3(A_588, '#skF_1'(A_588, B_589, C_590), a_2_9_lattice3(A_588, C_590)) | ~m1_subset_1('#skF_1'(A_588, B_589, C_590), u1_struct_0(A_588)) | ~l3_lattices(A_588) | v2_struct_0(A_588))), inference(resolution, [status(thm)], [c_34, c_3298])).
% 11.28/4.07  tff(c_106, plain, (![A_143, B_144, D_145]: (r1_lattices(A_143, '#skF_3'(A_143, B_144), D_145) | ~r4_lattice3(A_143, D_145, B_144) | ~m1_subset_1(D_145, u1_struct_0(A_143)) | ~v4_lattice3(A_143) | ~l3_lattices(A_143) | v2_struct_0(A_143))), inference(cnfTransformation, [status(thm)], [f_122])).
% 11.28/4.07  tff(c_22, plain, (![A_5, B_17, C_23]: (~r1_lattices(A_5, B_17, '#skF_1'(A_5, B_17, C_23)) | r3_lattice3(A_5, B_17, C_23) | ~m1_subset_1(B_17, u1_struct_0(A_5)) | ~l3_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.28/4.07  tff(c_111, plain, (![A_143, B_144, C_23]: (r3_lattice3(A_143, '#skF_3'(A_143, B_144), C_23) | ~m1_subset_1('#skF_3'(A_143, B_144), u1_struct_0(A_143)) | ~r4_lattice3(A_143, '#skF_1'(A_143, '#skF_3'(A_143, B_144), C_23), B_144) | ~m1_subset_1('#skF_1'(A_143, '#skF_3'(A_143, B_144), C_23), u1_struct_0(A_143)) | ~v4_lattice3(A_143) | ~l3_lattices(A_143) | v2_struct_0(A_143))), inference(resolution, [status(thm)], [c_106, c_22])).
% 11.28/4.07  tff(c_3616, plain, (![A_608, C_609]: (r3_lattice3(A_608, '#skF_3'(A_608, a_2_9_lattice3(A_608, C_609)), C_609) | ~m1_subset_1('#skF_3'(A_608, a_2_9_lattice3(A_608, C_609)), u1_struct_0(A_608)) | ~v4_lattice3(A_608) | ~v10_lattices(A_608) | ~m1_subset_1('#skF_1'(A_608, '#skF_3'(A_608, a_2_9_lattice3(A_608, C_609)), C_609), u1_struct_0(A_608)) | ~l3_lattices(A_608) | v2_struct_0(A_608))), inference(resolution, [status(thm)], [c_3320, c_111])).
% 11.28/4.07  tff(c_3627, plain, (![A_610, C_611]: (~v4_lattice3(A_610) | ~v10_lattices(A_610) | r3_lattice3(A_610, '#skF_3'(A_610, a_2_9_lattice3(A_610, C_611)), C_611) | ~m1_subset_1('#skF_3'(A_610, a_2_9_lattice3(A_610, C_611)), u1_struct_0(A_610)) | ~l3_lattices(A_610) | v2_struct_0(A_610))), inference(resolution, [status(thm)], [c_26, c_3616])).
% 11.28/4.07  tff(c_3631, plain, (![A_49, C_611]: (~v10_lattices(A_49) | r3_lattice3(A_49, '#skF_3'(A_49, a_2_9_lattice3(A_49, C_611)), C_611) | ~v4_lattice3(A_49) | ~l3_lattices(A_49) | v2_struct_0(A_49))), inference(resolution, [status(thm)], [c_46, c_3627])).
% 11.28/4.07  tff(c_48, plain, (![D_80, B_76, C_77]: (r2_hidden(D_80, a_2_9_lattice3(B_76, C_77)) | ~r3_lattice3(B_76, D_80, C_77) | ~m1_subset_1(D_80, u1_struct_0(B_76)) | ~l3_lattices(B_76) | ~v4_lattice3(B_76) | ~v10_lattices(B_76) | v2_struct_0(B_76))), inference(cnfTransformation, [status(thm)], [f_140])).
% 11.28/4.07  tff(c_54, plain, (![A_75, B_76, C_77]: (m1_subset_1('#skF_6'(A_75, B_76, C_77), u1_struct_0(B_76)) | ~r2_hidden(A_75, a_2_9_lattice3(B_76, C_77)) | ~l3_lattices(B_76) | ~v4_lattice3(B_76) | ~v10_lattices(B_76) | v2_struct_0(B_76))), inference(cnfTransformation, [status(thm)], [f_140])).
% 11.28/4.07  tff(c_3632, plain, (![A_612, C_613]: (~v10_lattices(A_612) | r3_lattice3(A_612, '#skF_3'(A_612, a_2_9_lattice3(A_612, C_613)), C_613) | ~v4_lattice3(A_612) | ~l3_lattices(A_612) | v2_struct_0(A_612))), inference(resolution, [status(thm)], [c_46, c_3627])).
% 11.28/4.07  tff(c_114, plain, (![D_151, B_152, C_153]: (r2_hidden(D_151, a_2_9_lattice3(B_152, C_153)) | ~r3_lattice3(B_152, D_151, C_153) | ~m1_subset_1(D_151, u1_struct_0(B_152)) | ~l3_lattices(B_152) | ~v4_lattice3(B_152) | ~v10_lattices(B_152) | v2_struct_0(B_152))), inference(cnfTransformation, [status(thm)], [f_140])).
% 11.28/4.07  tff(c_52, plain, (![A_75, B_76, C_77]: ('#skF_6'(A_75, B_76, C_77)=A_75 | ~r2_hidden(A_75, a_2_9_lattice3(B_76, C_77)) | ~l3_lattices(B_76) | ~v4_lattice3(B_76) | ~v10_lattices(B_76) | v2_struct_0(B_76))), inference(cnfTransformation, [status(thm)], [f_140])).
% 11.28/4.07  tff(c_118, plain, (![D_151, B_152, C_153]: ('#skF_6'(D_151, B_152, C_153)=D_151 | ~r3_lattice3(B_152, D_151, C_153) | ~m1_subset_1(D_151, u1_struct_0(B_152)) | ~l3_lattices(B_152) | ~v4_lattice3(B_152) | ~v10_lattices(B_152) | v2_struct_0(B_152))), inference(resolution, [status(thm)], [c_114, c_52])).
% 11.28/4.07  tff(c_3755, plain, (![A_621, C_622]: ('#skF_6'('#skF_3'(A_621, a_2_9_lattice3(A_621, C_622)), A_621, C_622)='#skF_3'(A_621, a_2_9_lattice3(A_621, C_622)) | ~m1_subset_1('#skF_3'(A_621, a_2_9_lattice3(A_621, C_622)), u1_struct_0(A_621)) | ~v10_lattices(A_621) | ~v4_lattice3(A_621) | ~l3_lattices(A_621) | v2_struct_0(A_621))), inference(resolution, [status(thm)], [c_3632, c_118])).
% 11.28/4.07  tff(c_3765, plain, (![A_49, C_622]: ('#skF_6'('#skF_3'(A_49, a_2_9_lattice3(A_49, C_622)), A_49, C_622)='#skF_3'(A_49, a_2_9_lattice3(A_49, C_622)) | ~v10_lattices(A_49) | ~v4_lattice3(A_49) | ~l3_lattices(A_49) | v2_struct_0(A_49))), inference(resolution, [status(thm)], [c_46, c_3755])).
% 11.28/4.07  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.28/4.07  tff(c_171, plain, (![A_169, B_170, C_171]: (r3_lattices(A_169, B_170, C_171) | ~r1_lattices(A_169, B_170, C_171) | ~m1_subset_1(C_171, u1_struct_0(A_169)) | ~m1_subset_1(B_170, u1_struct_0(A_169)) | ~l3_lattices(A_169) | ~v9_lattices(A_169) | ~v8_lattices(A_169) | ~v6_lattices(A_169) | v2_struct_0(A_169))), inference(cnfTransformation, [status(thm)], [f_66])).
% 11.28/4.07  tff(c_183, plain, (![B_170]: (r3_lattices('#skF_8', B_170, '#skF_9') | ~r1_lattices('#skF_8', B_170, '#skF_9') | ~m1_subset_1(B_170, u1_struct_0('#skF_8')) | ~l3_lattices('#skF_8') | ~v9_lattices('#skF_8') | ~v8_lattices('#skF_8') | ~v6_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_70, c_171])).
% 11.28/4.07  tff(c_191, plain, (![B_170]: (r3_lattices('#skF_8', B_170, '#skF_9') | ~r1_lattices('#skF_8', B_170, '#skF_9') | ~m1_subset_1(B_170, u1_struct_0('#skF_8')) | ~v9_lattices('#skF_8') | ~v8_lattices('#skF_8') | ~v6_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_183])).
% 11.28/4.07  tff(c_192, plain, (![B_170]: (r3_lattices('#skF_8', B_170, '#skF_9') | ~r1_lattices('#skF_8', B_170, '#skF_9') | ~m1_subset_1(B_170, u1_struct_0('#skF_8')) | ~v9_lattices('#skF_8') | ~v8_lattices('#skF_8') | ~v6_lattices('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_78, c_191])).
% 11.28/4.07  tff(c_194, plain, (~v6_lattices('#skF_8')), inference(splitLeft, [status(thm)], [c_192])).
% 11.28/4.07  tff(c_197, plain, (~v10_lattices('#skF_8') | v2_struct_0('#skF_8') | ~l3_lattices('#skF_8')), inference(resolution, [status(thm)], [c_8, c_194])).
% 11.28/4.07  tff(c_200, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76, c_197])).
% 11.28/4.07  tff(c_202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_200])).
% 11.28/4.07  tff(c_204, plain, (v6_lattices('#skF_8')), inference(splitRight, [status(thm)], [c_192])).
% 11.28/4.07  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.28/4.07  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.28/4.07  tff(c_203, plain, (![B_170]: (~v8_lattices('#skF_8') | ~v9_lattices('#skF_8') | r3_lattices('#skF_8', B_170, '#skF_9') | ~r1_lattices('#skF_8', B_170, '#skF_9') | ~m1_subset_1(B_170, u1_struct_0('#skF_8')))), inference(splitRight, [status(thm)], [c_192])).
% 11.28/4.07  tff(c_205, plain, (~v9_lattices('#skF_8')), inference(splitLeft, [status(thm)], [c_203])).
% 11.28/4.07  tff(c_208, plain, (~v10_lattices('#skF_8') | v2_struct_0('#skF_8') | ~l3_lattices('#skF_8')), inference(resolution, [status(thm)], [c_2, c_205])).
% 11.28/4.07  tff(c_211, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76, c_208])).
% 11.28/4.07  tff(c_213, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_211])).
% 11.28/4.07  tff(c_214, plain, (![B_170]: (~v8_lattices('#skF_8') | r3_lattices('#skF_8', B_170, '#skF_9') | ~r1_lattices('#skF_8', B_170, '#skF_9') | ~m1_subset_1(B_170, u1_struct_0('#skF_8')))), inference(splitRight, [status(thm)], [c_203])).
% 11.28/4.07  tff(c_216, plain, (~v8_lattices('#skF_8')), inference(splitLeft, [status(thm)], [c_214])).
% 11.28/4.07  tff(c_219, plain, (~v10_lattices('#skF_8') | v2_struct_0('#skF_8') | ~l3_lattices('#skF_8')), inference(resolution, [status(thm)], [c_4, c_216])).
% 11.28/4.07  tff(c_222, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76, c_219])).
% 11.28/4.07  tff(c_224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_222])).
% 11.28/4.07  tff(c_226, plain, (v8_lattices('#skF_8')), inference(splitRight, [status(thm)], [c_214])).
% 11.28/4.07  tff(c_215, plain, (v9_lattices('#skF_8')), inference(splitRight, [status(thm)], [c_203])).
% 11.28/4.07  tff(c_125, plain, (![D_158, B_159, C_160]: ('#skF_6'(D_158, B_159, C_160)=D_158 | ~r3_lattice3(B_159, D_158, C_160) | ~m1_subset_1(D_158, u1_struct_0(B_159)) | ~l3_lattices(B_159) | ~v4_lattice3(B_159) | ~v10_lattices(B_159) | v2_struct_0(B_159))), inference(resolution, [status(thm)], [c_114, c_52])).
% 11.28/4.07  tff(c_129, plain, ('#skF_6'('#skF_9', '#skF_8', '#skF_10')='#skF_9' | ~m1_subset_1('#skF_9', u1_struct_0('#skF_8')) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_68, c_125])).
% 11.28/4.07  tff(c_133, plain, ('#skF_6'('#skF_9', '#skF_8', '#skF_10')='#skF_9' | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_129])).
% 11.28/4.07  tff(c_134, plain, ('#skF_6'('#skF_9', '#skF_8', '#skF_10')='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_78, c_133])).
% 11.28/4.07  tff(c_348, plain, (![A_201, B_202, C_203]: ('#skF_6'('#skF_6'(A_201, B_202, C_203), B_202, C_203)='#skF_6'(A_201, B_202, C_203) | ~m1_subset_1('#skF_6'(A_201, B_202, C_203), u1_struct_0(B_202)) | ~r2_hidden(A_201, a_2_9_lattice3(B_202, C_203)) | ~l3_lattices(B_202) | ~v4_lattice3(B_202) | ~v10_lattices(B_202) | v2_struct_0(B_202))), inference(resolution, [status(thm)], [c_50, c_125])).
% 11.28/4.07  tff(c_357, plain, (![A_204, B_205, C_206]: ('#skF_6'('#skF_6'(A_204, B_205, C_206), B_205, C_206)='#skF_6'(A_204, B_205, C_206) | ~r2_hidden(A_204, a_2_9_lattice3(B_205, C_206)) | ~l3_lattices(B_205) | ~v4_lattice3(B_205) | ~v10_lattices(B_205) | v2_struct_0(B_205))), inference(resolution, [status(thm)], [c_54, c_348])).
% 11.28/4.07  tff(c_369, plain, (![D_207, B_208, C_209]: ('#skF_6'('#skF_6'(D_207, B_208, C_209), B_208, C_209)='#skF_6'(D_207, B_208, C_209) | ~r3_lattice3(B_208, D_207, C_209) | ~m1_subset_1(D_207, u1_struct_0(B_208)) | ~l3_lattices(B_208) | ~v4_lattice3(B_208) | ~v10_lattices(B_208) | v2_struct_0(B_208))), inference(resolution, [status(thm)], [c_48, c_357])).
% 11.28/4.07  tff(c_383, plain, (![C_209]: ('#skF_6'('#skF_6'('#skF_9', '#skF_8', C_209), '#skF_8', C_209)='#skF_6'('#skF_9', '#skF_8', C_209) | ~r3_lattice3('#skF_8', '#skF_9', C_209) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_70, c_369])).
% 11.28/4.07  tff(c_392, plain, (![C_209]: ('#skF_6'('#skF_6'('#skF_9', '#skF_8', C_209), '#skF_8', C_209)='#skF_6'('#skF_9', '#skF_8', C_209) | ~r3_lattice3('#skF_8', '#skF_9', C_209) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_383])).
% 11.28/4.07  tff(c_393, plain, (![C_209]: ('#skF_6'('#skF_6'('#skF_9', '#skF_8', C_209), '#skF_8', C_209)='#skF_6'('#skF_9', '#skF_8', C_209) | ~r3_lattice3('#skF_8', '#skF_9', C_209))), inference(negUnitSimplification, [status(thm)], [c_78, c_392])).
% 11.28/4.07  tff(c_687, plain, (![A_258, B_259, C_260, C_261]: ('#skF_6'('#skF_6'('#skF_6'(A_258, B_259, C_260), B_259, C_261), B_259, C_261)='#skF_6'('#skF_6'(A_258, B_259, C_260), B_259, C_261) | ~r3_lattice3(B_259, '#skF_6'(A_258, B_259, C_260), C_261) | ~r2_hidden(A_258, a_2_9_lattice3(B_259, C_260)) | ~l3_lattices(B_259) | ~v4_lattice3(B_259) | ~v10_lattices(B_259) | v2_struct_0(B_259))), inference(resolution, [status(thm)], [c_54, c_369])).
% 11.28/4.07  tff(c_733, plain, (![C_209, C_261]: ('#skF_6'('#skF_6'('#skF_6'('#skF_9', '#skF_8', C_209), '#skF_8', C_261), '#skF_8', C_261)='#skF_6'('#skF_6'('#skF_6'('#skF_9', '#skF_8', C_209), '#skF_8', C_209), '#skF_8', C_261) | ~r3_lattice3('#skF_8', '#skF_6'('#skF_6'('#skF_9', '#skF_8', C_209), '#skF_8', C_209), C_261) | ~r2_hidden('#skF_6'('#skF_9', '#skF_8', C_209), a_2_9_lattice3('#skF_8', C_209)) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8') | ~r3_lattice3('#skF_8', '#skF_9', C_209))), inference(superposition, [status(thm), theory('equality')], [c_393, c_687])).
% 11.28/4.07  tff(c_749, plain, (![C_209, C_261]: ('#skF_6'('#skF_6'('#skF_6'('#skF_9', '#skF_8', C_209), '#skF_8', C_261), '#skF_8', C_261)='#skF_6'('#skF_6'('#skF_6'('#skF_9', '#skF_8', C_209), '#skF_8', C_209), '#skF_8', C_261) | ~r3_lattice3('#skF_8', '#skF_6'('#skF_6'('#skF_9', '#skF_8', C_209), '#skF_8', C_209), C_261) | ~r2_hidden('#skF_6'('#skF_9', '#skF_8', C_209), a_2_9_lattice3('#skF_8', C_209)) | v2_struct_0('#skF_8') | ~r3_lattice3('#skF_8', '#skF_9', C_209))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_733])).
% 11.28/4.07  tff(c_811, plain, (![C_283, C_284]: ('#skF_6'('#skF_6'('#skF_6'('#skF_9', '#skF_8', C_283), '#skF_8', C_284), '#skF_8', C_284)='#skF_6'('#skF_6'('#skF_6'('#skF_9', '#skF_8', C_283), '#skF_8', C_283), '#skF_8', C_284) | ~r3_lattice3('#skF_8', '#skF_6'('#skF_6'('#skF_9', '#skF_8', C_283), '#skF_8', C_283), C_284) | ~r2_hidden('#skF_6'('#skF_9', '#skF_8', C_283), a_2_9_lattice3('#skF_8', C_283)) | ~r3_lattice3('#skF_8', '#skF_9', C_283))), inference(negUnitSimplification, [status(thm)], [c_78, c_749])).
% 11.28/4.07  tff(c_1494, plain, (![C_396, C_397]: ('#skF_6'('#skF_6'('#skF_6'('#skF_9', '#skF_8', C_396), '#skF_8', C_397), '#skF_8', C_397)='#skF_6'('#skF_6'('#skF_6'('#skF_9', '#skF_8', C_396), '#skF_8', C_396), '#skF_8', C_397) | ~r3_lattice3('#skF_8', '#skF_6'('#skF_9', '#skF_8', C_396), C_397) | ~r2_hidden('#skF_6'('#skF_9', '#skF_8', C_396), a_2_9_lattice3('#skF_8', C_396)) | ~r3_lattice3('#skF_8', '#skF_9', C_396) | ~r3_lattice3('#skF_8', '#skF_9', C_396))), inference(superposition, [status(thm), theory('equality')], [c_393, c_811])).
% 11.28/4.07  tff(c_1499, plain, (![C_77, C_397]: ('#skF_6'('#skF_6'('#skF_6'('#skF_9', '#skF_8', C_77), '#skF_8', C_77), '#skF_8', C_397)='#skF_6'('#skF_6'('#skF_6'('#skF_9', '#skF_8', C_77), '#skF_8', C_397), '#skF_8', C_397) | ~r3_lattice3('#skF_8', '#skF_6'('#skF_9', '#skF_8', C_77), C_397) | ~r3_lattice3('#skF_8', '#skF_9', C_77) | ~r3_lattice3('#skF_8', '#skF_6'('#skF_9', '#skF_8', C_77), C_77) | ~m1_subset_1('#skF_6'('#skF_9', '#skF_8', C_77), u1_struct_0('#skF_8')) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_48, c_1494])).
% 11.28/4.07  tff(c_1504, plain, (![C_77, C_397]: ('#skF_6'('#skF_6'('#skF_6'('#skF_9', '#skF_8', C_77), '#skF_8', C_77), '#skF_8', C_397)='#skF_6'('#skF_6'('#skF_6'('#skF_9', '#skF_8', C_77), '#skF_8', C_397), '#skF_8', C_397) | ~r3_lattice3('#skF_8', '#skF_6'('#skF_9', '#skF_8', C_77), C_397) | ~r3_lattice3('#skF_8', '#skF_9', C_77) | ~r3_lattice3('#skF_8', '#skF_6'('#skF_9', '#skF_8', C_77), C_77) | ~m1_subset_1('#skF_6'('#skF_9', '#skF_8', C_77), u1_struct_0('#skF_8')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_1499])).
% 11.28/4.07  tff(c_1770, plain, (![C_441, C_442]: ('#skF_6'('#skF_6'('#skF_6'('#skF_9', '#skF_8', C_441), '#skF_8', C_442), '#skF_8', C_442)='#skF_6'('#skF_6'('#skF_6'('#skF_9', '#skF_8', C_441), '#skF_8', C_441), '#skF_8', C_442) | ~r3_lattice3('#skF_8', '#skF_6'('#skF_9', '#skF_8', C_441), C_442) | ~r3_lattice3('#skF_8', '#skF_9', C_441) | ~r3_lattice3('#skF_8', '#skF_6'('#skF_9', '#skF_8', C_441), C_441) | ~m1_subset_1('#skF_6'('#skF_9', '#skF_8', C_441), u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_78, c_1504])).
% 11.28/4.07  tff(c_1775, plain, (![C_77, C_442]: ('#skF_6'('#skF_6'('#skF_6'('#skF_9', '#skF_8', C_77), '#skF_8', C_77), '#skF_8', C_442)='#skF_6'('#skF_6'('#skF_6'('#skF_9', '#skF_8', C_77), '#skF_8', C_442), '#skF_8', C_442) | ~r3_lattice3('#skF_8', '#skF_6'('#skF_9', '#skF_8', C_77), C_442) | ~r3_lattice3('#skF_8', '#skF_9', C_77) | ~r3_lattice3('#skF_8', '#skF_6'('#skF_9', '#skF_8', C_77), C_77) | ~r2_hidden('#skF_9', a_2_9_lattice3('#skF_8', C_77)) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_54, c_1770])).
% 11.28/4.07  tff(c_1780, plain, (![C_77, C_442]: ('#skF_6'('#skF_6'('#skF_6'('#skF_9', '#skF_8', C_77), '#skF_8', C_77), '#skF_8', C_442)='#skF_6'('#skF_6'('#skF_6'('#skF_9', '#skF_8', C_77), '#skF_8', C_442), '#skF_8', C_442) | ~r3_lattice3('#skF_8', '#skF_6'('#skF_9', '#skF_8', C_77), C_442) | ~r3_lattice3('#skF_8', '#skF_9', C_77) | ~r3_lattice3('#skF_8', '#skF_6'('#skF_9', '#skF_8', C_77), C_77) | ~r2_hidden('#skF_9', a_2_9_lattice3('#skF_8', C_77)) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_1775])).
% 11.28/4.07  tff(c_1808, plain, (![C_448, C_449]: ('#skF_6'('#skF_6'('#skF_6'('#skF_9', '#skF_8', C_448), '#skF_8', C_449), '#skF_8', C_449)='#skF_6'('#skF_6'('#skF_6'('#skF_9', '#skF_8', C_448), '#skF_8', C_448), '#skF_8', C_449) | ~r3_lattice3('#skF_8', '#skF_6'('#skF_9', '#skF_8', C_448), C_449) | ~r3_lattice3('#skF_8', '#skF_9', C_448) | ~r3_lattice3('#skF_8', '#skF_6'('#skF_9', '#skF_8', C_448), C_448) | ~r2_hidden('#skF_9', a_2_9_lattice3('#skF_8', C_448)))), inference(negUnitSimplification, [status(thm)], [c_78, c_1780])).
% 11.28/4.07  tff(c_386, plain, (![A_75, B_76, C_77, C_209]: ('#skF_6'('#skF_6'('#skF_6'(A_75, B_76, C_77), B_76, C_209), B_76, C_209)='#skF_6'('#skF_6'(A_75, B_76, C_77), B_76, C_209) | ~r3_lattice3(B_76, '#skF_6'(A_75, B_76, C_77), C_209) | ~r2_hidden(A_75, a_2_9_lattice3(B_76, C_77)) | ~l3_lattices(B_76) | ~v4_lattice3(B_76) | ~v10_lattices(B_76) | v2_struct_0(B_76))), inference(resolution, [status(thm)], [c_54, c_369])).
% 11.28/4.07  tff(c_1843, plain, (![C_448, C_449]: ('#skF_6'('#skF_6'('#skF_6'('#skF_9', '#skF_8', C_448), '#skF_8', C_448), '#skF_8', C_449)='#skF_6'('#skF_6'('#skF_9', '#skF_8', C_448), '#skF_8', C_449) | ~r3_lattice3('#skF_8', '#skF_6'('#skF_9', '#skF_8', C_448), C_449) | ~r2_hidden('#skF_9', a_2_9_lattice3('#skF_8', C_448)) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8') | ~r3_lattice3('#skF_8', '#skF_6'('#skF_9', '#skF_8', C_448), C_449) | ~r3_lattice3('#skF_8', '#skF_9', C_448) | ~r3_lattice3('#skF_8', '#skF_6'('#skF_9', '#skF_8', C_448), C_448) | ~r2_hidden('#skF_9', a_2_9_lattice3('#skF_8', C_448)))), inference(superposition, [status(thm), theory('equality')], [c_1808, c_386])).
% 11.28/4.07  tff(c_1908, plain, (![C_448, C_449]: ('#skF_6'('#skF_6'('#skF_6'('#skF_9', '#skF_8', C_448), '#skF_8', C_448), '#skF_8', C_449)='#skF_6'('#skF_6'('#skF_9', '#skF_8', C_448), '#skF_8', C_449) | v2_struct_0('#skF_8') | ~r3_lattice3('#skF_8', '#skF_6'('#skF_9', '#skF_8', C_448), C_449) | ~r3_lattice3('#skF_8', '#skF_9', C_448) | ~r3_lattice3('#skF_8', '#skF_6'('#skF_9', '#skF_8', C_448), C_448) | ~r2_hidden('#skF_9', a_2_9_lattice3('#skF_8', C_448)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_1843])).
% 11.28/4.07  tff(c_1937, plain, (![C_450, C_451]: ('#skF_6'('#skF_6'('#skF_6'('#skF_9', '#skF_8', C_450), '#skF_8', C_450), '#skF_8', C_451)='#skF_6'('#skF_6'('#skF_9', '#skF_8', C_450), '#skF_8', C_451) | ~r3_lattice3('#skF_8', '#skF_6'('#skF_9', '#skF_8', C_450), C_451) | ~r3_lattice3('#skF_8', '#skF_9', C_450) | ~r3_lattice3('#skF_8', '#skF_6'('#skF_9', '#skF_8', C_450), C_450) | ~r2_hidden('#skF_9', a_2_9_lattice3('#skF_8', C_450)))), inference(negUnitSimplification, [status(thm)], [c_78, c_1908])).
% 11.28/4.07  tff(c_1969, plain, (![C_450, C_451]: (r3_lattice3('#skF_8', '#skF_6'('#skF_6'('#skF_9', '#skF_8', C_450), '#skF_8', C_451), C_451) | ~r2_hidden('#skF_6'('#skF_6'('#skF_9', '#skF_8', C_450), '#skF_8', C_450), a_2_9_lattice3('#skF_8', C_451)) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8') | ~r3_lattice3('#skF_8', '#skF_6'('#skF_9', '#skF_8', C_450), C_451) | ~r3_lattice3('#skF_8', '#skF_9', C_450) | ~r3_lattice3('#skF_8', '#skF_6'('#skF_9', '#skF_8', C_450), C_450) | ~r2_hidden('#skF_9', a_2_9_lattice3('#skF_8', C_450)))), inference(superposition, [status(thm), theory('equality')], [c_1937, c_50])).
% 11.28/4.07  tff(c_2007, plain, (![C_450, C_451]: (r3_lattice3('#skF_8', '#skF_6'('#skF_6'('#skF_9', '#skF_8', C_450), '#skF_8', C_451), C_451) | ~r2_hidden('#skF_6'('#skF_6'('#skF_9', '#skF_8', C_450), '#skF_8', C_450), a_2_9_lattice3('#skF_8', C_451)) | v2_struct_0('#skF_8') | ~r3_lattice3('#skF_8', '#skF_6'('#skF_9', '#skF_8', C_450), C_451) | ~r3_lattice3('#skF_8', '#skF_9', C_450) | ~r3_lattice3('#skF_8', '#skF_6'('#skF_9', '#skF_8', C_450), C_450) | ~r2_hidden('#skF_9', a_2_9_lattice3('#skF_8', C_450)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_1969])).
% 11.28/4.07  tff(c_2259, plain, (![C_470, C_471]: (r3_lattice3('#skF_8', '#skF_6'('#skF_6'('#skF_9', '#skF_8', C_470), '#skF_8', C_471), C_471) | ~r2_hidden('#skF_6'('#skF_6'('#skF_9', '#skF_8', C_470), '#skF_8', C_470), a_2_9_lattice3('#skF_8', C_471)) | ~r3_lattice3('#skF_8', '#skF_6'('#skF_9', '#skF_8', C_470), C_471) | ~r3_lattice3('#skF_8', '#skF_9', C_470) | ~r3_lattice3('#skF_8', '#skF_6'('#skF_9', '#skF_8', C_470), C_470) | ~r2_hidden('#skF_9', a_2_9_lattice3('#skF_8', C_470)))), inference(negUnitSimplification, [status(thm)], [c_78, c_2007])).
% 11.28/4.07  tff(c_2263, plain, (![C_471]: (r3_lattice3('#skF_8', '#skF_6'('#skF_6'('#skF_9', '#skF_8', '#skF_10'), '#skF_8', C_471), C_471) | ~r2_hidden('#skF_6'('#skF_9', '#skF_8', '#skF_10'), a_2_9_lattice3('#skF_8', C_471)) | ~r3_lattice3('#skF_8', '#skF_6'('#skF_9', '#skF_8', '#skF_10'), C_471) | ~r3_lattice3('#skF_8', '#skF_9', '#skF_10') | ~r3_lattice3('#skF_8', '#skF_6'('#skF_9', '#skF_8', '#skF_10'), '#skF_10') | ~r2_hidden('#skF_9', a_2_9_lattice3('#skF_8', '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_134, c_2259])).
% 11.28/4.07  tff(c_2268, plain, (![C_471]: (r3_lattice3('#skF_8', '#skF_6'('#skF_9', '#skF_8', C_471), C_471) | ~r2_hidden('#skF_9', a_2_9_lattice3('#skF_8', C_471)) | ~r3_lattice3('#skF_8', '#skF_9', C_471) | ~r2_hidden('#skF_9', a_2_9_lattice3('#skF_8', '#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_134, c_68, c_134, c_134, c_134, c_2263])).
% 11.28/4.07  tff(c_2273, plain, (~r2_hidden('#skF_9', a_2_9_lattice3('#skF_8', '#skF_10'))), inference(splitLeft, [status(thm)], [c_2268])).
% 11.28/4.07  tff(c_2276, plain, (~r3_lattice3('#skF_8', '#skF_9', '#skF_10') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_8')) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_48, c_2273])).
% 11.28/4.07  tff(c_2279, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_68, c_2276])).
% 11.28/4.07  tff(c_2281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_2279])).
% 11.28/4.07  tff(c_2283, plain, (r2_hidden('#skF_9', a_2_9_lattice3('#skF_8', '#skF_10'))), inference(splitRight, [status(thm)], [c_2268])).
% 11.28/4.07  tff(c_20, plain, (![A_5, B_17, D_26, C_23]: (r1_lattices(A_5, B_17, D_26) | ~r2_hidden(D_26, C_23) | ~m1_subset_1(D_26, u1_struct_0(A_5)) | ~r3_lattice3(A_5, B_17, C_23) | ~m1_subset_1(B_17, u1_struct_0(A_5)) | ~l3_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.28/4.07  tff(c_2341, plain, (![A_477, B_478]: (r1_lattices(A_477, B_478, '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0(A_477)) | ~r3_lattice3(A_477, B_478, a_2_9_lattice3('#skF_8', '#skF_10')) | ~m1_subset_1(B_478, u1_struct_0(A_477)) | ~l3_lattices(A_477) | v2_struct_0(A_477))), inference(resolution, [status(thm)], [c_2283, c_20])).
% 11.28/4.07  tff(c_2449, plain, (![B_495, A_496]: (r1_lattices(B_495, '#skF_6'(A_496, B_495, a_2_9_lattice3('#skF_8', '#skF_10')), '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0(B_495)) | ~m1_subset_1('#skF_6'(A_496, B_495, a_2_9_lattice3('#skF_8', '#skF_10')), u1_struct_0(B_495)) | ~r2_hidden(A_496, a_2_9_lattice3(B_495, a_2_9_lattice3('#skF_8', '#skF_10'))) | ~l3_lattices(B_495) | ~v4_lattice3(B_495) | ~v10_lattices(B_495) | v2_struct_0(B_495))), inference(resolution, [status(thm)], [c_50, c_2341])).
% 11.28/4.07  tff(c_2549, plain, (![B_497, A_498]: (r1_lattices(B_497, '#skF_6'(A_498, B_497, a_2_9_lattice3('#skF_8', '#skF_10')), '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0(B_497)) | ~r2_hidden(A_498, a_2_9_lattice3(B_497, a_2_9_lattice3('#skF_8', '#skF_10'))) | ~l3_lattices(B_497) | ~v4_lattice3(B_497) | ~v10_lattices(B_497) | v2_struct_0(B_497))), inference(resolution, [status(thm)], [c_54, c_2449])).
% 11.28/4.07  tff(c_231, plain, (![B_178]: (r3_lattices('#skF_8', B_178, '#skF_9') | ~r1_lattices('#skF_8', B_178, '#skF_9') | ~m1_subset_1(B_178, u1_struct_0('#skF_8')))), inference(splitRight, [status(thm)], [c_214])).
% 11.28/4.07  tff(c_239, plain, (![A_75, C_77]: (r3_lattices('#skF_8', '#skF_6'(A_75, '#skF_8', C_77), '#skF_9') | ~r1_lattices('#skF_8', '#skF_6'(A_75, '#skF_8', C_77), '#skF_9') | ~r2_hidden(A_75, a_2_9_lattice3('#skF_8', C_77)) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_54, c_231])).
% 11.28/4.07  tff(c_261, plain, (![A_75, C_77]: (r3_lattices('#skF_8', '#skF_6'(A_75, '#skF_8', C_77), '#skF_9') | ~r1_lattices('#skF_8', '#skF_6'(A_75, '#skF_8', C_77), '#skF_9') | ~r2_hidden(A_75, a_2_9_lattice3('#skF_8', C_77)) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_239])).
% 11.28/4.07  tff(c_262, plain, (![A_75, C_77]: (r3_lattices('#skF_8', '#skF_6'(A_75, '#skF_8', C_77), '#skF_9') | ~r1_lattices('#skF_8', '#skF_6'(A_75, '#skF_8', C_77), '#skF_9') | ~r2_hidden(A_75, a_2_9_lattice3('#skF_8', C_77)))), inference(negUnitSimplification, [status(thm)], [c_78, c_261])).
% 11.28/4.07  tff(c_664, plain, (![A_251, B_252, C_254]: (r3_lattices('#skF_8', '#skF_2'(A_251, B_252, a_2_9_lattice3('#skF_8', C_254)), '#skF_9') | ~r1_lattices('#skF_8', '#skF_6'('#skF_2'(A_251, B_252, a_2_9_lattice3('#skF_8', C_254)), '#skF_8', C_254), '#skF_9') | ~r2_hidden('#skF_2'(A_251, B_252, a_2_9_lattice3('#skF_8', C_254)), a_2_9_lattice3('#skF_8', C_254)) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8') | r4_lattice3(A_251, B_252, a_2_9_lattice3('#skF_8', C_254)) | ~m1_subset_1(B_252, u1_struct_0(A_251)) | ~l3_lattices(A_251) | v2_struct_0(A_251))), inference(superposition, [status(thm), theory('equality')], [c_654, c_262])).
% 11.28/4.07  tff(c_676, plain, (![A_251, B_252, C_254]: (r3_lattices('#skF_8', '#skF_2'(A_251, B_252, a_2_9_lattice3('#skF_8', C_254)), '#skF_9') | ~r1_lattices('#skF_8', '#skF_6'('#skF_2'(A_251, B_252, a_2_9_lattice3('#skF_8', C_254)), '#skF_8', C_254), '#skF_9') | ~r2_hidden('#skF_2'(A_251, B_252, a_2_9_lattice3('#skF_8', C_254)), a_2_9_lattice3('#skF_8', C_254)) | v2_struct_0('#skF_8') | r4_lattice3(A_251, B_252, a_2_9_lattice3('#skF_8', C_254)) | ~m1_subset_1(B_252, u1_struct_0(A_251)) | ~l3_lattices(A_251) | v2_struct_0(A_251))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_664])).
% 11.28/4.07  tff(c_677, plain, (![A_251, B_252, C_254]: (r3_lattices('#skF_8', '#skF_2'(A_251, B_252, a_2_9_lattice3('#skF_8', C_254)), '#skF_9') | ~r1_lattices('#skF_8', '#skF_6'('#skF_2'(A_251, B_252, a_2_9_lattice3('#skF_8', C_254)), '#skF_8', C_254), '#skF_9') | ~r2_hidden('#skF_2'(A_251, B_252, a_2_9_lattice3('#skF_8', C_254)), a_2_9_lattice3('#skF_8', C_254)) | r4_lattice3(A_251, B_252, a_2_9_lattice3('#skF_8', C_254)) | ~m1_subset_1(B_252, u1_struct_0(A_251)) | ~l3_lattices(A_251) | v2_struct_0(A_251))), inference(negUnitSimplification, [status(thm)], [c_78, c_676])).
% 11.28/4.07  tff(c_2553, plain, (![A_251, B_252]: (r3_lattices('#skF_8', '#skF_2'(A_251, B_252, a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), '#skF_9') | r4_lattice3(A_251, B_252, a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | ~m1_subset_1(B_252, u1_struct_0(A_251)) | ~l3_lattices(A_251) | v2_struct_0(A_251) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_8')) | ~r2_hidden('#skF_2'(A_251, B_252, a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_2549, c_677])).
% 11.28/4.07  tff(c_2644, plain, (![A_251, B_252]: (r3_lattices('#skF_8', '#skF_2'(A_251, B_252, a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), '#skF_9') | r4_lattice3(A_251, B_252, a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | ~m1_subset_1(B_252, u1_struct_0(A_251)) | ~l3_lattices(A_251) | v2_struct_0(A_251) | ~r2_hidden('#skF_2'(A_251, B_252, a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_2553])).
% 11.28/4.07  tff(c_2781, plain, (![A_525, B_526]: (r3_lattices('#skF_8', '#skF_2'(A_525, B_526, a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), '#skF_9') | r4_lattice3(A_525, B_526, a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | ~m1_subset_1(B_526, u1_struct_0(A_525)) | ~l3_lattices(A_525) | v2_struct_0(A_525) | ~r2_hidden('#skF_2'(A_525, B_526, a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))))), inference(negUnitSimplification, [status(thm)], [c_78, c_2644])).
% 11.28/4.07  tff(c_2794, plain, (![A_527, B_528]: (r3_lattices('#skF_8', '#skF_2'(A_527, B_528, a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), '#skF_9') | r4_lattice3(A_527, B_528, a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | ~m1_subset_1(B_528, u1_struct_0(A_527)) | ~l3_lattices(A_527) | v2_struct_0(A_527))), inference(resolution, [status(thm)], [c_32, c_2781])).
% 11.28/4.07  tff(c_18, plain, (![A_2, B_3, C_4]: (r1_lattices(A_2, B_3, C_4) | ~r3_lattices(A_2, B_3, C_4) | ~m1_subset_1(C_4, u1_struct_0(A_2)) | ~m1_subset_1(B_3, u1_struct_0(A_2)) | ~l3_lattices(A_2) | ~v9_lattices(A_2) | ~v8_lattices(A_2) | ~v6_lattices(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_66])).
% 11.28/4.07  tff(c_2796, plain, (![A_527, B_528]: (r1_lattices('#skF_8', '#skF_2'(A_527, B_528, a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_2'(A_527, B_528, a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), u1_struct_0('#skF_8')) | ~l3_lattices('#skF_8') | ~v9_lattices('#skF_8') | ~v8_lattices('#skF_8') | ~v6_lattices('#skF_8') | v2_struct_0('#skF_8') | r4_lattice3(A_527, B_528, a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | ~m1_subset_1(B_528, u1_struct_0(A_527)) | ~l3_lattices(A_527) | v2_struct_0(A_527))), inference(resolution, [status(thm)], [c_2794, c_18])).
% 11.28/4.07  tff(c_2799, plain, (![A_527, B_528]: (r1_lattices('#skF_8', '#skF_2'(A_527, B_528, a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), '#skF_9') | ~m1_subset_1('#skF_2'(A_527, B_528, a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), u1_struct_0('#skF_8')) | v2_struct_0('#skF_8') | r4_lattice3(A_527, B_528, a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | ~m1_subset_1(B_528, u1_struct_0(A_527)) | ~l3_lattices(A_527) | v2_struct_0(A_527))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_226, c_215, c_72, c_70, c_2796])).
% 11.28/4.07  tff(c_2801, plain, (![A_529, B_530]: (r1_lattices('#skF_8', '#skF_2'(A_529, B_530, a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), '#skF_9') | ~m1_subset_1('#skF_2'(A_529, B_530, a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), u1_struct_0('#skF_8')) | r4_lattice3(A_529, B_530, a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | ~m1_subset_1(B_530, u1_struct_0(A_529)) | ~l3_lattices(A_529) | v2_struct_0(A_529))), inference(negUnitSimplification, [status(thm)], [c_78, c_2799])).
% 11.28/4.07  tff(c_2809, plain, (![B_39]: (r1_lattices('#skF_8', '#skF_2'('#skF_8', B_39, a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), '#skF_9') | r4_lattice3('#skF_8', B_39, a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | ~m1_subset_1(B_39, u1_struct_0('#skF_8')) | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_34, c_2801])).
% 11.28/4.07  tff(c_2816, plain, (![B_39]: (r1_lattices('#skF_8', '#skF_2'('#skF_8', B_39, a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), '#skF_9') | r4_lattice3('#skF_8', B_39, a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | ~m1_subset_1(B_39, u1_struct_0('#skF_8')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2809])).
% 11.28/4.07  tff(c_2818, plain, (![B_531]: (r1_lattices('#skF_8', '#skF_2'('#skF_8', B_531, a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), '#skF_9') | r4_lattice3('#skF_8', B_531, a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | ~m1_subset_1(B_531, u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_78, c_2816])).
% 11.28/4.07  tff(c_2822, plain, (~l3_lattices('#skF_8') | v2_struct_0('#skF_8') | r4_lattice3('#skF_8', '#skF_9', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_2818, c_30])).
% 11.28/4.07  tff(c_2825, plain, (v2_struct_0('#skF_8') | r4_lattice3('#skF_8', '#skF_9', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_72, c_2822])).
% 11.28/4.07  tff(c_2826, plain, (r4_lattice3('#skF_8', '#skF_9', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_78, c_2825])).
% 11.28/4.07  tff(c_151, plain, (![A_161, D_162, B_163, C_164]: (r1_lattices(A_161, D_162, B_163) | ~r2_hidden(D_162, C_164) | ~m1_subset_1(D_162, u1_struct_0(A_161)) | ~r4_lattice3(A_161, B_163, C_164) | ~m1_subset_1(B_163, u1_struct_0(A_161)) | ~l3_lattices(A_161) | v2_struct_0(A_161))), inference(cnfTransformation, [status(thm)], [f_102])).
% 11.28/4.07  tff(c_758, plain, (![C_266, A_265, D_262, B_264, B_263]: (r1_lattices(A_265, D_262, B_263) | ~m1_subset_1(D_262, u1_struct_0(A_265)) | ~r4_lattice3(A_265, B_263, a_2_9_lattice3(B_264, C_266)) | ~m1_subset_1(B_263, u1_struct_0(A_265)) | ~l3_lattices(A_265) | v2_struct_0(A_265) | ~r3_lattice3(B_264, D_262, C_266) | ~m1_subset_1(D_262, u1_struct_0(B_264)) | ~l3_lattices(B_264) | ~v4_lattice3(B_264) | ~v10_lattices(B_264) | v2_struct_0(B_264))), inference(resolution, [status(thm)], [c_48, c_151])).
% 11.28/4.07  tff(c_778, plain, (![C_266, B_64, A_49, B_264, B_263]: (r1_lattices(A_49, '#skF_3'(A_49, B_64), B_263) | ~r4_lattice3(A_49, B_263, a_2_9_lattice3(B_264, C_266)) | ~m1_subset_1(B_263, u1_struct_0(A_49)) | ~r3_lattice3(B_264, '#skF_3'(A_49, B_64), C_266) | ~m1_subset_1('#skF_3'(A_49, B_64), u1_struct_0(B_264)) | ~l3_lattices(B_264) | ~v4_lattice3(B_264) | ~v10_lattices(B_264) | v2_struct_0(B_264) | ~v4_lattice3(A_49) | ~l3_lattices(A_49) | v2_struct_0(A_49))), inference(resolution, [status(thm)], [c_46, c_758])).
% 11.28/4.07  tff(c_2830, plain, (![B_64]: (r1_lattices('#skF_8', '#skF_3'('#skF_8', B_64), '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_8')) | ~r3_lattice3('#skF_8', '#skF_3'('#skF_8', B_64), a_2_9_lattice3('#skF_8', '#skF_10')) | ~m1_subset_1('#skF_3'('#skF_8', B_64), u1_struct_0('#skF_8')) | ~v10_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_2826, c_778])).
% 11.28/4.07  tff(c_2840, plain, (![B_64]: (r1_lattices('#skF_8', '#skF_3'('#skF_8', B_64), '#skF_9') | ~r3_lattice3('#skF_8', '#skF_3'('#skF_8', B_64), a_2_9_lattice3('#skF_8', '#skF_10')) | ~m1_subset_1('#skF_3'('#skF_8', B_64), u1_struct_0('#skF_8')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_74, c_76, c_70, c_2830])).
% 11.28/4.07  tff(c_2841, plain, (![B_64]: (r1_lattices('#skF_8', '#skF_3'('#skF_8', B_64), '#skF_9') | ~r3_lattice3('#skF_8', '#skF_3'('#skF_8', B_64), a_2_9_lattice3('#skF_8', '#skF_10')) | ~m1_subset_1('#skF_3'('#skF_8', B_64), u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_78, c_2840])).
% 11.28/4.07  tff(c_3645, plain, (r1_lattices('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), '#skF_9') | ~m1_subset_1('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), u1_struct_0('#skF_8')) | ~v10_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_3632, c_2841])).
% 11.28/4.07  tff(c_3664, plain, (r1_lattices('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), '#skF_9') | ~m1_subset_1('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), u1_struct_0('#skF_8')) | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_74, c_76, c_3645])).
% 11.28/4.07  tff(c_3665, plain, (r1_lattices('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), '#skF_9') | ~m1_subset_1('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), u1_struct_0('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_78, c_3664])).
% 11.28/4.07  tff(c_3673, plain, (~m1_subset_1('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), u1_struct_0('#skF_8'))), inference(splitLeft, [status(thm)], [c_3665])).
% 11.28/4.07  tff(c_3676, plain, (~v4_lattice3('#skF_8') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_46, c_3673])).
% 11.28/4.07  tff(c_3679, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_74, c_3676])).
% 11.28/4.07  tff(c_3681, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_3679])).
% 11.28/4.07  tff(c_3683, plain, (m1_subset_1('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), u1_struct_0('#skF_8'))), inference(splitRight, [status(thm)], [c_3665])).
% 11.28/4.07  tff(c_3757, plain, ('#skF_6'('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), '#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))='#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | ~v10_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_3683, c_3755])).
% 11.28/4.07  tff(c_3763, plain, ('#skF_6'('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), '#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))='#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_74, c_76, c_3757])).
% 11.28/4.07  tff(c_3764, plain, ('#skF_6'('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), '#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))='#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_78, c_3763])).
% 11.28/4.07  tff(c_3817, plain, (r3_lattice3('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), a_2_9_lattice3('#skF_8', '#skF_10')) | ~r2_hidden('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_3764, c_50])).
% 11.28/4.07  tff(c_3860, plain, (r3_lattice3('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), a_2_9_lattice3('#skF_8', '#skF_10')) | ~r2_hidden('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_3817])).
% 11.28/4.07  tff(c_3861, plain, (r3_lattice3('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), a_2_9_lattice3('#skF_8', '#skF_10')) | ~r2_hidden('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_78, c_3860])).
% 11.28/4.07  tff(c_3981, plain, (~r2_hidden('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')))), inference(splitLeft, [status(thm)], [c_3861])).
% 11.28/4.07  tff(c_3984, plain, (~r3_lattice3('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), a_2_9_lattice3('#skF_8', '#skF_10')) | ~m1_subset_1('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), u1_struct_0('#skF_8')) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_48, c_3981])).
% 11.28/4.07  tff(c_3987, plain, (~r3_lattice3('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), a_2_9_lattice3('#skF_8', '#skF_10')) | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_3683, c_3984])).
% 11.28/4.07  tff(c_3988, plain, (~r3_lattice3('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), a_2_9_lattice3('#skF_8', '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_78, c_3987])).
% 11.28/4.07  tff(c_4005, plain, (~v10_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_3631, c_3988])).
% 11.28/4.07  tff(c_4008, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_74, c_76, c_4005])).
% 11.28/4.07  tff(c_4010, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_4008])).
% 11.28/4.07  tff(c_4011, plain, (r3_lattice3('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), a_2_9_lattice3('#skF_8', '#skF_10'))), inference(splitRight, [status(thm)], [c_3861])).
% 11.28/4.07  tff(c_64, plain, (![A_81, B_93, C_99]: (m1_subset_1('#skF_7'(A_81, B_93, C_99), u1_struct_0(A_81)) | k16_lattice3(A_81, C_99)=B_93 | ~r3_lattice3(A_81, B_93, C_99) | ~m1_subset_1(B_93, u1_struct_0(A_81)) | ~l3_lattices(A_81) | ~v4_lattice3(A_81) | ~v10_lattices(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_164])).
% 11.28/4.07  tff(c_227, plain, (![A_175, B_176, C_177]: (r3_lattice3(A_175, '#skF_7'(A_175, B_176, C_177), C_177) | k16_lattice3(A_175, C_177)=B_176 | ~r3_lattice3(A_175, B_176, C_177) | ~m1_subset_1(B_176, u1_struct_0(A_175)) | ~l3_lattices(A_175) | ~v4_lattice3(A_175) | ~v10_lattices(A_175) | v2_struct_0(A_175))), inference(cnfTransformation, [status(thm)], [f_164])).
% 11.28/4.07  tff(c_932, plain, (![A_320, B_321, C_322]: ('#skF_6'('#skF_7'(A_320, B_321, C_322), A_320, C_322)='#skF_7'(A_320, B_321, C_322) | ~m1_subset_1('#skF_7'(A_320, B_321, C_322), u1_struct_0(A_320)) | k16_lattice3(A_320, C_322)=B_321 | ~r3_lattice3(A_320, B_321, C_322) | ~m1_subset_1(B_321, u1_struct_0(A_320)) | ~l3_lattices(A_320) | ~v4_lattice3(A_320) | ~v10_lattices(A_320) | v2_struct_0(A_320))), inference(resolution, [status(thm)], [c_227, c_118])).
% 11.28/4.07  tff(c_935, plain, (![A_81, B_93, C_99]: ('#skF_6'('#skF_7'(A_81, B_93, C_99), A_81, C_99)='#skF_7'(A_81, B_93, C_99) | k16_lattice3(A_81, C_99)=B_93 | ~r3_lattice3(A_81, B_93, C_99) | ~m1_subset_1(B_93, u1_struct_0(A_81)) | ~l3_lattices(A_81) | ~v4_lattice3(A_81) | ~v10_lattices(A_81) | v2_struct_0(A_81))), inference(resolution, [status(thm)], [c_64, c_932])).
% 11.28/4.07  tff(c_3699, plain, (![C_99]: ('#skF_6'('#skF_7'('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), C_99), '#skF_8', C_99)='#skF_7'('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), C_99) | k16_lattice3('#skF_8', C_99)='#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | ~r3_lattice3('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), C_99) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_3683, c_935])).
% 11.28/4.07  tff(c_3713, plain, (![C_99]: ('#skF_6'('#skF_7'('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), C_99), '#skF_8', C_99)='#skF_7'('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), C_99) | k16_lattice3('#skF_8', C_99)='#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | ~r3_lattice3('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), C_99) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_3699])).
% 11.28/4.07  tff(c_6114, plain, (![C_717]: ('#skF_6'('#skF_7'('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), C_717), '#skF_8', C_717)='#skF_7'('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), C_717) | k16_lattice3('#skF_8', C_717)='#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | ~r3_lattice3('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), C_717))), inference(negUnitSimplification, [status(thm)], [c_78, c_3713])).
% 11.28/4.07  tff(c_4139, plain, (![B_638, A_639, C_637, B_640, C_642, B_641]: (r1_lattices(B_638, '#skF_6'(A_639, B_638, C_642), B_641) | ~r4_lattice3(B_638, B_641, a_2_9_lattice3(B_640, C_637)) | ~m1_subset_1(B_641, u1_struct_0(B_638)) | ~r3_lattice3(B_640, '#skF_6'(A_639, B_638, C_642), C_637) | ~m1_subset_1('#skF_6'(A_639, B_638, C_642), u1_struct_0(B_640)) | ~l3_lattices(B_640) | ~v4_lattice3(B_640) | ~v10_lattices(B_640) | v2_struct_0(B_640) | ~r2_hidden(A_639, a_2_9_lattice3(B_638, C_642)) | ~l3_lattices(B_638) | ~v4_lattice3(B_638) | ~v10_lattices(B_638) | v2_struct_0(B_638))), inference(resolution, [status(thm)], [c_54, c_758])).
% 11.28/4.07  tff(c_4143, plain, (![A_639, C_642]: (r1_lattices('#skF_8', '#skF_6'(A_639, '#skF_8', C_642), '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_8')) | ~r3_lattice3('#skF_8', '#skF_6'(A_639, '#skF_8', C_642), a_2_9_lattice3('#skF_8', '#skF_10')) | ~m1_subset_1('#skF_6'(A_639, '#skF_8', C_642), u1_struct_0('#skF_8')) | ~r2_hidden(A_639, a_2_9_lattice3('#skF_8', C_642)) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_2826, c_4139])).
% 11.28/4.07  tff(c_4150, plain, (![A_639, C_642]: (r1_lattices('#skF_8', '#skF_6'(A_639, '#skF_8', C_642), '#skF_9') | ~r3_lattice3('#skF_8', '#skF_6'(A_639, '#skF_8', C_642), a_2_9_lattice3('#skF_8', '#skF_10')) | ~m1_subset_1('#skF_6'(A_639, '#skF_8', C_642), u1_struct_0('#skF_8')) | ~r2_hidden(A_639, a_2_9_lattice3('#skF_8', C_642)) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_4143])).
% 11.28/4.07  tff(c_4153, plain, (![A_643, C_644]: (r1_lattices('#skF_8', '#skF_6'(A_643, '#skF_8', C_644), '#skF_9') | ~r3_lattice3('#skF_8', '#skF_6'(A_643, '#skF_8', C_644), a_2_9_lattice3('#skF_8', '#skF_10')) | ~m1_subset_1('#skF_6'(A_643, '#skF_8', C_644), u1_struct_0('#skF_8')) | ~r2_hidden(A_643, a_2_9_lattice3('#skF_8', C_644)))), inference(negUnitSimplification, [status(thm)], [c_78, c_4150])).
% 11.28/4.07  tff(c_4240, plain, (![A_75]: (r1_lattices('#skF_8', '#skF_6'(A_75, '#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), '#skF_9') | ~m1_subset_1('#skF_6'(A_75, '#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), u1_struct_0('#skF_8')) | ~r2_hidden(A_75, a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_50, c_4153])).
% 11.28/4.07  tff(c_4286, plain, (![A_75]: (r1_lattices('#skF_8', '#skF_6'(A_75, '#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), '#skF_9') | ~m1_subset_1('#skF_6'(A_75, '#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), u1_struct_0('#skF_8')) | ~r2_hidden(A_75, a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_4240])).
% 11.28/4.07  tff(c_4288, plain, (![A_645]: (r1_lattices('#skF_8', '#skF_6'(A_645, '#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), '#skF_9') | ~m1_subset_1('#skF_6'(A_645, '#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), u1_struct_0('#skF_8')) | ~r2_hidden(A_645, a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))))), inference(negUnitSimplification, [status(thm)], [c_78, c_4286])).
% 11.28/4.07  tff(c_4379, plain, (![A_75]: (r1_lattices('#skF_8', '#skF_6'(A_75, '#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), '#skF_9') | ~r2_hidden(A_75, a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_54, c_4288])).
% 11.28/4.07  tff(c_4422, plain, (![A_75]: (r1_lattices('#skF_8', '#skF_6'(A_75, '#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), '#skF_9') | ~r2_hidden(A_75, a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_4379])).
% 11.28/4.07  tff(c_4423, plain, (![A_75]: (r1_lattices('#skF_8', '#skF_6'(A_75, '#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), '#skF_9') | ~r2_hidden(A_75, a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))))), inference(negUnitSimplification, [status(thm)], [c_78, c_4422])).
% 11.28/4.07  tff(c_6139, plain, (r1_lattices('#skF_8', '#skF_7'('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), a_2_9_lattice3('#skF_8', '#skF_10')), '#skF_9') | ~r2_hidden('#skF_7'('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), a_2_9_lattice3('#skF_8', '#skF_10')), a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')))=k16_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')) | ~r3_lattice3('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), a_2_9_lattice3('#skF_8', '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_6114, c_4423])).
% 11.28/4.07  tff(c_6196, plain, (r1_lattices('#skF_8', '#skF_7'('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), a_2_9_lattice3('#skF_8', '#skF_10')), '#skF_9') | ~r2_hidden('#skF_7'('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), a_2_9_lattice3('#skF_8', '#skF_10')), a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')))=k16_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_4011, c_6139])).
% 11.28/4.07  tff(c_6309, plain, (~r2_hidden('#skF_7'('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), a_2_9_lattice3('#skF_8', '#skF_10')), a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')))), inference(splitLeft, [status(thm)], [c_6196])).
% 11.28/4.07  tff(c_6312, plain, (~r3_lattice3('#skF_8', '#skF_7'('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), a_2_9_lattice3('#skF_8', '#skF_10')), a_2_9_lattice3('#skF_8', '#skF_10')) | ~m1_subset_1('#skF_7'('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), a_2_9_lattice3('#skF_8', '#skF_10')), u1_struct_0('#skF_8')) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_48, c_6309])).
% 11.28/4.07  tff(c_6315, plain, (~r3_lattice3('#skF_8', '#skF_7'('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), a_2_9_lattice3('#skF_8', '#skF_10')), a_2_9_lattice3('#skF_8', '#skF_10')) | ~m1_subset_1('#skF_7'('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), a_2_9_lattice3('#skF_8', '#skF_10')), u1_struct_0('#skF_8')) | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_6312])).
% 11.28/4.07  tff(c_6316, plain, (~r3_lattice3('#skF_8', '#skF_7'('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), a_2_9_lattice3('#skF_8', '#skF_10')), a_2_9_lattice3('#skF_8', '#skF_10')) | ~m1_subset_1('#skF_7'('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), a_2_9_lattice3('#skF_8', '#skF_10')), u1_struct_0('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_78, c_6315])).
% 11.28/4.07  tff(c_6317, plain, (~m1_subset_1('#skF_7'('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), a_2_9_lattice3('#skF_8', '#skF_10')), u1_struct_0('#skF_8'))), inference(splitLeft, [status(thm)], [c_6316])).
% 11.28/4.07  tff(c_6320, plain, ('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')))=k16_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')) | ~r3_lattice3('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), a_2_9_lattice3('#skF_8', '#skF_10')) | ~m1_subset_1('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), u1_struct_0('#skF_8')) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_64, c_6317])).
% 11.28/4.07  tff(c_6323, plain, ('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')))=k16_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')) | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_3683, c_4011, c_6320])).
% 11.28/4.07  tff(c_6324, plain, ('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')))=k16_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_78, c_6323])).
% 11.28/4.07  tff(c_826, plain, (![D_285, A_288, C_289, B_286, B_287]: (r1_lattices(A_288, B_286, D_285) | ~m1_subset_1(D_285, u1_struct_0(A_288)) | ~r3_lattice3(A_288, B_286, a_2_9_lattice3(B_287, C_289)) | ~m1_subset_1(B_286, u1_struct_0(A_288)) | ~l3_lattices(A_288) | v2_struct_0(A_288) | ~r3_lattice3(B_287, D_285, C_289) | ~m1_subset_1(D_285, u1_struct_0(B_287)) | ~l3_lattices(B_287) | ~v4_lattice3(B_287) | ~v10_lattices(B_287) | v2_struct_0(B_287))), inference(resolution, [status(thm)], [c_48, c_161])).
% 11.28/4.07  tff(c_4837, plain, (![B_670, C_673, C_672, B_671, B_668, A_669]: (r1_lattices(B_668, B_671, '#skF_6'(A_669, B_668, C_672)) | ~r3_lattice3(B_668, B_671, a_2_9_lattice3(B_670, C_673)) | ~m1_subset_1(B_671, u1_struct_0(B_668)) | ~r3_lattice3(B_670, '#skF_6'(A_669, B_668, C_672), C_673) | ~m1_subset_1('#skF_6'(A_669, B_668, C_672), u1_struct_0(B_670)) | ~l3_lattices(B_670) | ~v4_lattice3(B_670) | ~v10_lattices(B_670) | v2_struct_0(B_670) | ~r2_hidden(A_669, a_2_9_lattice3(B_668, C_672)) | ~l3_lattices(B_668) | ~v4_lattice3(B_668) | ~v10_lattices(B_668) | v2_struct_0(B_668))), inference(resolution, [status(thm)], [c_54, c_826])).
% 11.28/4.07  tff(c_4839, plain, (![A_669, C_672]: (r1_lattices('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), '#skF_6'(A_669, '#skF_8', C_672)) | ~m1_subset_1('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), u1_struct_0('#skF_8')) | ~r3_lattice3('#skF_8', '#skF_6'(A_669, '#skF_8', C_672), '#skF_10') | ~m1_subset_1('#skF_6'(A_669, '#skF_8', C_672), u1_struct_0('#skF_8')) | ~r2_hidden(A_669, a_2_9_lattice3('#skF_8', C_672)) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_4011, c_4837])).
% 11.28/4.07  tff(c_4863, plain, (![A_669, C_672]: (r1_lattices('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), '#skF_6'(A_669, '#skF_8', C_672)) | ~r3_lattice3('#skF_8', '#skF_6'(A_669, '#skF_8', C_672), '#skF_10') | ~m1_subset_1('#skF_6'(A_669, '#skF_8', C_672), u1_struct_0('#skF_8')) | ~r2_hidden(A_669, a_2_9_lattice3('#skF_8', C_672)) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_3683, c_4839])).
% 11.28/4.07  tff(c_4864, plain, (![A_669, C_672]: (r1_lattices('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), '#skF_6'(A_669, '#skF_8', C_672)) | ~r3_lattice3('#skF_8', '#skF_6'(A_669, '#skF_8', C_672), '#skF_10') | ~m1_subset_1('#skF_6'(A_669, '#skF_8', C_672), u1_struct_0('#skF_8')) | ~r2_hidden(A_669, a_2_9_lattice3('#skF_8', C_672)))), inference(negUnitSimplification, [status(thm)], [c_78, c_4863])).
% 11.28/4.07  tff(c_7274, plain, (![A_764, C_765]: (r1_lattices('#skF_8', k16_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), '#skF_6'(A_764, '#skF_8', C_765)) | ~r3_lattice3('#skF_8', '#skF_6'(A_764, '#skF_8', C_765), '#skF_10') | ~m1_subset_1('#skF_6'(A_764, '#skF_8', C_765), u1_struct_0('#skF_8')) | ~r2_hidden(A_764, a_2_9_lattice3('#skF_8', C_765)))), inference(demodulation, [status(thm), theory('equality')], [c_6324, c_4864])).
% 11.28/4.07  tff(c_7300, plain, (![C_622]: (r1_lattices('#skF_8', k16_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', C_622))) | ~r3_lattice3('#skF_8', '#skF_6'('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', C_622)), '#skF_8', C_622), '#skF_10') | ~m1_subset_1('#skF_6'('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', C_622)), '#skF_8', C_622), u1_struct_0('#skF_8')) | ~r2_hidden('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', C_622)), a_2_9_lattice3('#skF_8', C_622)) | ~v10_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_3765, c_7274])).
% 11.28/4.07  tff(c_7386, plain, (![C_622]: (r1_lattices('#skF_8', k16_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', C_622))) | ~r3_lattice3('#skF_8', '#skF_6'('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', C_622)), '#skF_8', C_622), '#skF_10') | ~m1_subset_1('#skF_6'('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', C_622)), '#skF_8', C_622), u1_struct_0('#skF_8')) | ~r2_hidden('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', C_622)), a_2_9_lattice3('#skF_8', C_622)) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_74, c_76, c_7300])).
% 11.28/4.07  tff(c_8324, plain, (![C_840]: (r1_lattices('#skF_8', k16_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', C_840))) | ~r3_lattice3('#skF_8', '#skF_6'('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', C_840)), '#skF_8', C_840), '#skF_10') | ~m1_subset_1('#skF_6'('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', C_840)), '#skF_8', C_840), u1_struct_0('#skF_8')) | ~r2_hidden('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', C_840)), a_2_9_lattice3('#skF_8', C_840)))), inference(negUnitSimplification, [status(thm)], [c_78, c_7386])).
% 11.28/4.07  tff(c_8332, plain, (![C_77]: (r1_lattices('#skF_8', k16_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', C_77))) | ~r3_lattice3('#skF_8', '#skF_6'('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', C_77)), '#skF_8', C_77), '#skF_10') | ~r2_hidden('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', C_77)), a_2_9_lattice3('#skF_8', C_77)) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_54, c_8324])).
% 11.28/4.07  tff(c_8340, plain, (![C_77]: (r1_lattices('#skF_8', k16_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', C_77))) | ~r3_lattice3('#skF_8', '#skF_6'('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', C_77)), '#skF_8', C_77), '#skF_10') | ~r2_hidden('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', C_77)), a_2_9_lattice3('#skF_8', C_77)) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_8332])).
% 11.28/4.07  tff(c_8342, plain, (![C_841]: (r1_lattices('#skF_8', k16_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', C_841))) | ~r3_lattice3('#skF_8', '#skF_6'('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', C_841)), '#skF_8', C_841), '#skF_10') | ~r2_hidden('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', C_841)), a_2_9_lattice3('#skF_8', C_841)))), inference(negUnitSimplification, [status(thm)], [c_78, c_8340])).
% 11.28/4.07  tff(c_8350, plain, (r1_lattices('#skF_8', k16_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | ~r2_hidden('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), a_2_9_lattice3('#skF_8', '#skF_10')) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_50, c_8342])).
% 11.28/4.07  tff(c_8358, plain, (r1_lattices('#skF_8', k16_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | ~r2_hidden('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), a_2_9_lattice3('#skF_8', '#skF_10')) | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_8350])).
% 11.28/4.07  tff(c_8359, plain, (r1_lattices('#skF_8', k16_lattice3('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | ~r2_hidden('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), a_2_9_lattice3('#skF_8', '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_78, c_8358])).
% 11.28/4.07  tff(c_8360, plain, (~r2_hidden('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), a_2_9_lattice3('#skF_8', '#skF_10'))), inference(splitLeft, [status(thm)], [c_8359])).
% 11.28/4.07  tff(c_8363, plain, (~r3_lattice3('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), '#skF_10') | ~m1_subset_1('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), u1_struct_0('#skF_8')) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_48, c_8360])).
% 11.28/4.07  tff(c_8366, plain, (~r3_lattice3('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), '#skF_10') | ~m1_subset_1('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), u1_struct_0('#skF_8')) | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_8363])).
% 11.28/4.07  tff(c_8367, plain, (~r3_lattice3('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), '#skF_10') | ~m1_subset_1('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), u1_struct_0('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_78, c_8366])).
% 11.28/4.07  tff(c_8368, plain, (~m1_subset_1('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), u1_struct_0('#skF_8'))), inference(splitLeft, [status(thm)], [c_8367])).
% 11.28/4.07  tff(c_8371, plain, (~v4_lattice3('#skF_8') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_46, c_8368])).
% 11.28/4.07  tff(c_8374, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_74, c_8371])).
% 11.28/4.07  tff(c_8376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_8374])).
% 11.28/4.07  tff(c_8377, plain, (~r3_lattice3('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), '#skF_10')), inference(splitRight, [status(thm)], [c_8367])).
% 11.28/4.07  tff(c_8415, plain, (~v10_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_3631, c_8377])).
% 11.28/4.07  tff(c_8418, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_74, c_76, c_8415])).
% 11.28/4.07  tff(c_8420, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_8418])).
% 11.28/4.07  tff(c_8422, plain, (r2_hidden('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), a_2_9_lattice3('#skF_8', '#skF_10'))), inference(splitRight, [status(thm)], [c_8359])).
% 11.28/4.07  tff(c_8443, plain, ('#skF_6'('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), '#skF_8', '#skF_10')='#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_8422, c_52])).
% 11.28/4.07  tff(c_8452, plain, ('#skF_6'('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), '#skF_8', '#skF_10')='#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')) | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_8443])).
% 11.28/4.07  tff(c_8453, plain, ('#skF_6'('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), '#skF_8', '#skF_10')='#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_78, c_8452])).
% 11.28/4.07  tff(c_8522, plain, (m1_subset_1('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), u1_struct_0('#skF_8')) | ~r2_hidden('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), a_2_9_lattice3('#skF_8', '#skF_10')) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_8453, c_54])).
% 11.28/4.07  tff(c_8585, plain, (m1_subset_1('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), u1_struct_0('#skF_8')) | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_8422, c_8522])).
% 11.28/4.07  tff(c_8586, plain, (m1_subset_1('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), u1_struct_0('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_78, c_8585])).
% 11.28/4.07  tff(c_8519, plain, (r3_lattice3('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), '#skF_10') | ~r2_hidden('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), a_2_9_lattice3('#skF_8', '#skF_10')) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_8453, c_50])).
% 11.28/4.07  tff(c_8582, plain, (r3_lattice3('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), '#skF_10') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_8422, c_8519])).
% 11.28/4.07  tff(c_8583, plain, (r3_lattice3('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_78, c_8582])).
% 11.28/4.07  tff(c_62, plain, (![A_81, B_93, C_99]: (r3_lattice3(A_81, '#skF_7'(A_81, B_93, C_99), C_99) | k16_lattice3(A_81, C_99)=B_93 | ~r3_lattice3(A_81, B_93, C_99) | ~m1_subset_1(B_93, u1_struct_0(A_81)) | ~l3_lattices(A_81) | ~v4_lattice3(A_81) | ~v10_lattices(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_164])).
% 11.28/4.07  tff(c_44, plain, (![A_49, B_64]: (r4_lattice3(A_49, '#skF_3'(A_49, B_64), B_64) | ~v4_lattice3(A_49) | ~l3_lattices(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_122])).
% 11.28/4.07  tff(c_5384, plain, (![B_697, B_696, C_692, A_693, B_695, C_694]: (r1_lattices(A_693, '#skF_7'(A_693, B_697, C_694), B_696) | ~r4_lattice3(A_693, B_696, a_2_9_lattice3(B_695, C_692)) | ~m1_subset_1(B_696, u1_struct_0(A_693)) | ~r3_lattice3(B_695, '#skF_7'(A_693, B_697, C_694), C_692) | ~m1_subset_1('#skF_7'(A_693, B_697, C_694), u1_struct_0(B_695)) | ~l3_lattices(B_695) | ~v4_lattice3(B_695) | ~v10_lattices(B_695) | v2_struct_0(B_695) | k16_lattice3(A_693, C_694)=B_697 | ~r3_lattice3(A_693, B_697, C_694) | ~m1_subset_1(B_697, u1_struct_0(A_693)) | ~l3_lattices(A_693) | ~v4_lattice3(A_693) | ~v10_lattices(A_693) | v2_struct_0(A_693))), inference(resolution, [status(thm)], [c_64, c_758])).
% 11.28/4.07  tff(c_5403, plain, (![B_697, C_692, B_695, C_694, A_49]: (r1_lattices(A_49, '#skF_7'(A_49, B_697, C_694), '#skF_3'(A_49, a_2_9_lattice3(B_695, C_692))) | ~m1_subset_1('#skF_3'(A_49, a_2_9_lattice3(B_695, C_692)), u1_struct_0(A_49)) | ~r3_lattice3(B_695, '#skF_7'(A_49, B_697, C_694), C_692) | ~m1_subset_1('#skF_7'(A_49, B_697, C_694), u1_struct_0(B_695)) | ~l3_lattices(B_695) | ~v4_lattice3(B_695) | ~v10_lattices(B_695) | v2_struct_0(B_695) | k16_lattice3(A_49, C_694)=B_697 | ~r3_lattice3(A_49, B_697, C_694) | ~m1_subset_1(B_697, u1_struct_0(A_49)) | ~v10_lattices(A_49) | ~v4_lattice3(A_49) | ~l3_lattices(A_49) | v2_struct_0(A_49))), inference(resolution, [status(thm)], [c_44, c_5384])).
% 11.28/4.07  tff(c_185, plain, (![B_76, B_170, A_75, C_77]: (r3_lattices(B_76, B_170, '#skF_6'(A_75, B_76, C_77)) | ~r1_lattices(B_76, B_170, '#skF_6'(A_75, B_76, C_77)) | ~m1_subset_1(B_170, u1_struct_0(B_76)) | ~v9_lattices(B_76) | ~v8_lattices(B_76) | ~v6_lattices(B_76) | ~r2_hidden(A_75, a_2_9_lattice3(B_76, C_77)) | ~l3_lattices(B_76) | ~v4_lattice3(B_76) | ~v10_lattices(B_76) | v2_struct_0(B_76))), inference(resolution, [status(thm)], [c_54, c_171])).
% 11.28/4.07  tff(c_8504, plain, (![B_170]: (r3_lattices('#skF_8', B_170, '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | ~r1_lattices('#skF_8', B_170, '#skF_6'('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), '#skF_8', '#skF_10')) | ~m1_subset_1(B_170, u1_struct_0('#skF_8')) | ~v9_lattices('#skF_8') | ~v8_lattices('#skF_8') | ~v6_lattices('#skF_8') | ~r2_hidden('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), a_2_9_lattice3('#skF_8', '#skF_10')) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_8453, c_185])).
% 11.28/4.07  tff(c_8570, plain, (![B_170]: (r3_lattices('#skF_8', B_170, '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | ~r1_lattices('#skF_8', B_170, '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | ~m1_subset_1(B_170, u1_struct_0('#skF_8')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_8422, c_204, c_226, c_215, c_8453, c_8504])).
% 11.28/4.07  tff(c_8635, plain, (![B_847]: (r3_lattices('#skF_8', B_847, '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | ~r1_lattices('#skF_8', B_847, '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | ~m1_subset_1(B_847, u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_78, c_8570])).
% 11.28/4.07  tff(c_60, plain, (![A_81, B_93, C_99]: (~r3_lattices(A_81, '#skF_7'(A_81, B_93, C_99), B_93) | k16_lattice3(A_81, C_99)=B_93 | ~r3_lattice3(A_81, B_93, C_99) | ~m1_subset_1(B_93, u1_struct_0(A_81)) | ~l3_lattices(A_81) | ~v4_lattice3(A_81) | ~v10_lattices(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_164])).
% 11.28/4.07  tff(c_8639, plain, (![C_99]: (k16_lattice3('#skF_8', C_99)='#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')) | ~r3_lattice3('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), C_99) | ~m1_subset_1('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), u1_struct_0('#skF_8')) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8') | ~r1_lattices('#skF_8', '#skF_7'('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), C_99), '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | ~m1_subset_1('#skF_7'('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), C_99), u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_8635, c_60])).
% 11.28/4.07  tff(c_8644, plain, (![C_99]: (k16_lattice3('#skF_8', C_99)='#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')) | ~r3_lattice3('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), C_99) | v2_struct_0('#skF_8') | ~r1_lattices('#skF_8', '#skF_7'('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), C_99), '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | ~m1_subset_1('#skF_7'('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), C_99), u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_8586, c_8639])).
% 11.28/4.07  tff(c_9502, plain, (![C_878]: (k16_lattice3('#skF_8', C_878)='#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')) | ~r3_lattice3('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), C_878) | ~r1_lattices('#skF_8', '#skF_7'('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), C_878), '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))) | ~m1_subset_1('#skF_7'('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), C_878), u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_78, c_8644])).
% 11.28/4.07  tff(c_9509, plain, (![C_694]: (~r3_lattice3('#skF_8', '#skF_7'('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), C_694), '#skF_10') | ~m1_subset_1('#skF_7'('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), C_694), u1_struct_0('#skF_8')) | k16_lattice3('#skF_8', C_694)='#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')) | ~r3_lattice3('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), C_694) | ~m1_subset_1('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), u1_struct_0('#skF_8')) | ~v10_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_5403, c_9502])).
% 11.28/4.07  tff(c_9513, plain, (![C_694]: (~r3_lattice3('#skF_8', '#skF_7'('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), C_694), '#skF_10') | ~m1_subset_1('#skF_7'('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), C_694), u1_struct_0('#skF_8')) | k16_lattice3('#skF_8', C_694)='#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')) | ~r3_lattice3('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), C_694) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_74, c_76, c_8586, c_9509])).
% 11.28/4.07  tff(c_9515, plain, (![C_879]: (~r3_lattice3('#skF_8', '#skF_7'('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), C_879), '#skF_10') | ~m1_subset_1('#skF_7'('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), C_879), u1_struct_0('#skF_8')) | k16_lattice3('#skF_8', C_879)='#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')) | ~r3_lattice3('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), C_879))), inference(negUnitSimplification, [status(thm)], [c_78, c_9513])).
% 11.28/4.07  tff(c_9519, plain, (![C_99]: (~r3_lattice3('#skF_8', '#skF_7'('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), C_99), '#skF_10') | k16_lattice3('#skF_8', C_99)='#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')) | ~r3_lattice3('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), C_99) | ~m1_subset_1('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), u1_struct_0('#skF_8')) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_64, c_9515])).
% 11.28/4.07  tff(c_9522, plain, (![C_99]: (~r3_lattice3('#skF_8', '#skF_7'('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), C_99), '#skF_10') | k16_lattice3('#skF_8', C_99)='#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')) | ~r3_lattice3('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), C_99) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_8586, c_9519])).
% 11.28/4.07  tff(c_9544, plain, (![C_885]: (~r3_lattice3('#skF_8', '#skF_7'('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), C_885), '#skF_10') | k16_lattice3('#skF_8', C_885)='#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')) | ~r3_lattice3('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), C_885))), inference(negUnitSimplification, [status(thm)], [c_78, c_9522])).
% 11.28/4.07  tff(c_9548, plain, ('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))=k16_lattice3('#skF_8', '#skF_10') | ~r3_lattice3('#skF_8', '#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), '#skF_10') | ~m1_subset_1('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10')), u1_struct_0('#skF_8')) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_62, c_9544])).
% 11.28/4.07  tff(c_9551, plain, ('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))=k16_lattice3('#skF_8', '#skF_10') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_8586, c_8583, c_9548])).
% 11.28/4.07  tff(c_9552, plain, ('#skF_3'('#skF_8', a_2_9_lattice3('#skF_8', '#skF_10'))=k16_lattice3('#skF_8', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_78, c_9551])).
% 11.28/4.07  tff(c_9572, plain, (m1_subset_1(k16_lattice3('#skF_8', '#skF_10'), u1_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_9552, c_8586])).
% 11.28/4.07  tff(c_56, plain, (![A_81, D_102, C_99]: (r3_lattices(A_81, D_102, k16_lattice3(A_81, C_99)) | ~r3_lattice3(A_81, D_102, C_99) | ~m1_subset_1(D_102, u1_struct_0(A_81)) | ~m1_subset_1(k16_lattice3(A_81, C_99), u1_struct_0(A_81)) | ~l3_lattices(A_81) | ~v4_lattice3(A_81) | ~v10_lattices(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_164])).
% 11.28/4.07  tff(c_9796, plain, (![D_102]: (r3_lattices('#skF_8', D_102, k16_lattice3('#skF_8', '#skF_10')) | ~r3_lattice3('#skF_8', D_102, '#skF_10') | ~m1_subset_1(D_102, u1_struct_0('#skF_8')) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_9572, c_56])).
% 11.28/4.07  tff(c_9822, plain, (![D_102]: (r3_lattices('#skF_8', D_102, k16_lattice3('#skF_8', '#skF_10')) | ~r3_lattice3('#skF_8', D_102, '#skF_10') | ~m1_subset_1(D_102, u1_struct_0('#skF_8')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_9796])).
% 11.28/4.07  tff(c_10326, plain, (![D_898]: (r3_lattices('#skF_8', D_898, k16_lattice3('#skF_8', '#skF_10')) | ~r3_lattice3('#skF_8', D_898, '#skF_10') | ~m1_subset_1(D_898, u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_78, c_9822])).
% 11.28/4.07  tff(c_66, plain, (~r3_lattices('#skF_8', '#skF_9', k16_lattice3('#skF_8', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 11.28/4.07  tff(c_10335, plain, (~r3_lattice3('#skF_8', '#skF_9', '#skF_10') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_10326, c_66])).
% 11.28/4.07  tff(c_10347, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_10335])).
% 11.28/4.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.28/4.07  
% 11.28/4.07  Inference rules
% 11.28/4.07  ----------------------
% 11.28/4.07  #Ref     : 0
% 11.28/4.07  #Sup     : 1843
% 11.28/4.07  #Fact    : 0
% 11.28/4.07  #Define  : 0
% 11.28/4.07  #Split   : 19
% 11.28/4.07  #Chain   : 0
% 11.28/4.07  #Close   : 0
% 11.28/4.07  
% 11.28/4.07  Ordering : KBO
% 11.28/4.07  
% 11.28/4.07  Simplification rules
% 11.28/4.07  ----------------------
% 11.28/4.07  #Subsume      : 340
% 11.28/4.07  #Demod        : 4297
% 11.28/4.07  #Tautology    : 358
% 11.28/4.07  #SimpNegUnit  : 936
% 11.28/4.07  #BackRed      : 52
% 11.28/4.07  
% 11.28/4.07  #Partial instantiations: 0
% 11.28/4.07  #Strategies tried      : 1
% 11.28/4.07  
% 11.28/4.07  Timing (in seconds)
% 11.28/4.07  ----------------------
% 11.28/4.07  Preprocessing        : 0.37
% 11.28/4.07  Parsing              : 0.20
% 11.28/4.07  CNF conversion       : 0.04
% 11.28/4.07  Main loop            : 2.82
% 11.28/4.07  Inferencing          : 1.00
% 11.28/4.07  Reduction            : 0.85
% 11.28/4.07  Demodulation         : 0.60
% 11.28/4.07  BG Simplification    : 0.10
% 11.28/4.07  Subsumption          : 0.72
% 11.28/4.07  Abstraction          : 0.13
% 11.28/4.07  MUC search           : 0.00
% 11.28/4.07  Cooper               : 0.00
% 11.28/4.07  Total                : 3.30
% 11.28/4.07  Index Insertion      : 0.00
% 11.28/4.07  Index Deletion       : 0.00
% 11.28/4.07  Index Matching       : 0.00
% 11.28/4.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
