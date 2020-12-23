%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:50 EST 2020

% Result     : Theorem 7.60s
% Output     : CNFRefutation 7.92s
% Verified   : 
% Statistics : Number of formulae       :  240 (2262 expanded)
%              Number of leaves         :   48 ( 831 expanded)
%              Depth                    :   29
%              Number of atoms          :  957 (12775 expanded)
%              Number of equality atoms :   39 ( 267 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k6_domain_1 > k16_lattice3 > k15_lattice3 > a_2_6_lattice3 > a_2_5_lattice3 > a_2_2_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_11 > #skF_6 > #skF_10 > #skF_5 > #skF_9 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_12 > #skF_4

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

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k16_lattice3,type,(
    k16_lattice3: ( $i * $i ) > $i )).

tff(k15_lattice3,type,(
    k15_lattice3: ( $i * $i ) > $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

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
    '#skF_9': $i )).

tff(a_2_2_lattice3,type,(
    a_2_2_lattice3: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(a_2_6_lattice3,type,(
    a_2_6_lattice3: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_261,negated_conjecture,(
    ~ ! [A] :
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

tff(f_185,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] : k15_lattice3(A,B) = k16_lattice3(A,a_2_2_lattice3(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).

tff(f_204,axiom,(
    ! [A] :
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

tff(f_234,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( k15_lattice3(A,B) = k15_lattice3(A,a_2_5_lattice3(A,B))
          & k16_lattice3(A,B) = k16_lattice3(A,a_2_6_lattice3(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_lattice3)).

tff(f_104,axiom,(
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

tff(f_173,axiom,(
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

tff(f_84,axiom,(
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
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v10_lattices(B)
        & v4_lattice3(B)
        & l3_lattices(B) )
     => ( r2_hidden(A,a_2_2_lattice3(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & r4_lattice3(B,D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).

tff(f_132,axiom,(
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

tff(c_92,plain,(
    ~ v2_struct_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_90,plain,(
    v10_lattices('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_88,plain,(
    v4_lattice3('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_86,plain,(
    l3_lattices('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_70,plain,(
    ! [A_84,B_86] :
      ( k16_lattice3(A_84,a_2_2_lattice3(A_84,B_86)) = k15_lattice3(A_84,B_86)
      | ~ l3_lattices(A_84)
      | ~ v4_lattice3(A_84)
      | ~ v10_lattices(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_191,plain,(
    ! [A_171,C_172,B_173] :
      ( r3_lattices(A_171,k16_lattice3(A_171,C_172),B_173)
      | ~ r2_hidden(B_173,C_172)
      | ~ m1_subset_1(B_173,u1_struct_0(A_171))
      | ~ l3_lattices(A_171)
      | ~ v4_lattice3(A_171)
      | ~ v10_lattices(A_171)
      | v2_struct_0(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_866,plain,(
    ! [A_278,B_279,B_280] :
      ( r3_lattices(A_278,k15_lattice3(A_278,B_279),B_280)
      | ~ r2_hidden(B_280,a_2_2_lattice3(A_278,B_279))
      | ~ m1_subset_1(B_280,u1_struct_0(A_278))
      | ~ l3_lattices(A_278)
      | ~ v4_lattice3(A_278)
      | ~ v10_lattices(A_278)
      | v2_struct_0(A_278)
      | ~ l3_lattices(A_278)
      | ~ v4_lattice3(A_278)
      | ~ v10_lattices(A_278)
      | v2_struct_0(A_278) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_191])).

tff(c_84,plain,(
    ~ r3_lattices('#skF_9',k15_lattice3('#skF_9','#skF_10'),k15_lattice3('#skF_9','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_874,plain,
    ( ~ r2_hidden(k15_lattice3('#skF_9','#skF_11'),a_2_2_lattice3('#skF_9','#skF_10'))
    | ~ m1_subset_1(k15_lattice3('#skF_9','#skF_11'),u1_struct_0('#skF_9'))
    | ~ l3_lattices('#skF_9')
    | ~ v4_lattice3('#skF_9')
    | ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_866,c_84])).

tff(c_885,plain,
    ( ~ r2_hidden(k15_lattice3('#skF_9','#skF_11'),a_2_2_lattice3('#skF_9','#skF_10'))
    | ~ m1_subset_1(k15_lattice3('#skF_9','#skF_11'),u1_struct_0('#skF_9'))
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_874])).

tff(c_886,plain,
    ( ~ r2_hidden(k15_lattice3('#skF_9','#skF_11'),a_2_2_lattice3('#skF_9','#skF_10'))
    | ~ m1_subset_1(k15_lattice3('#skF_9','#skF_11'),u1_struct_0('#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_885])).

tff(c_887,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_9','#skF_11'),u1_struct_0('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_886])).

tff(c_80,plain,(
    ! [A_97,B_99] :
      ( k15_lattice3(A_97,a_2_5_lattice3(A_97,B_99)) = k15_lattice3(A_97,B_99)
      | ~ l3_lattices(A_97)
      | ~ v4_lattice3(A_97)
      | ~ v10_lattices(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_38,plain,(
    ! [A_27,B_42] :
      ( m1_subset_1('#skF_2'(A_27,B_42),u1_struct_0(A_27))
      | ~ v4_lattice3(A_27)
      | ~ l3_lattices(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_36,plain,(
    ! [A_27,B_42] :
      ( r4_lattice3(A_27,'#skF_2'(A_27,B_42),B_42)
      | ~ v4_lattice3(A_27)
      | ~ l3_lattices(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_98,plain,(
    ! [D_111] :
      ( m1_subset_1('#skF_12'(D_111),u1_struct_0('#skF_9'))
      | ~ r2_hidden(D_111,'#skF_10')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_9')) ) ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_96,plain,(
    ! [D_111] :
      ( r3_lattices('#skF_9',D_111,'#skF_12'(D_111))
      | ~ r2_hidden(D_111,'#skF_10')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_9')) ) ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_94,plain,(
    ! [D_111] :
      ( r2_hidden('#skF_12'(D_111),'#skF_11')
      | ~ r2_hidden(D_111,'#skF_10')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_9')) ) ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_374,plain,(
    ! [D_219,B_220,C_221,E_222] :
      ( r2_hidden(D_219,a_2_5_lattice3(B_220,C_221))
      | ~ r2_hidden(E_222,C_221)
      | ~ r3_lattices(B_220,D_219,E_222)
      | ~ m1_subset_1(E_222,u1_struct_0(B_220))
      | ~ m1_subset_1(D_219,u1_struct_0(B_220))
      | ~ l3_lattices(B_220)
      | ~ v4_lattice3(B_220)
      | ~ v10_lattices(B_220)
      | v2_struct_0(B_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_419,plain,(
    ! [D_234,B_235,D_236] :
      ( r2_hidden(D_234,a_2_5_lattice3(B_235,'#skF_11'))
      | ~ r3_lattices(B_235,D_234,'#skF_12'(D_236))
      | ~ m1_subset_1('#skF_12'(D_236),u1_struct_0(B_235))
      | ~ m1_subset_1(D_234,u1_struct_0(B_235))
      | ~ l3_lattices(B_235)
      | ~ v4_lattice3(B_235)
      | ~ v10_lattices(B_235)
      | v2_struct_0(B_235)
      | ~ r2_hidden(D_236,'#skF_10')
      | ~ m1_subset_1(D_236,u1_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_94,c_374])).

tff(c_426,plain,(
    ! [D_111] :
      ( r2_hidden(D_111,a_2_5_lattice3('#skF_9','#skF_11'))
      | ~ m1_subset_1('#skF_12'(D_111),u1_struct_0('#skF_9'))
      | ~ l3_lattices('#skF_9')
      | ~ v4_lattice3('#skF_9')
      | ~ v10_lattices('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ r2_hidden(D_111,'#skF_10')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_96,c_419])).

tff(c_434,plain,(
    ! [D_111] :
      ( r2_hidden(D_111,a_2_5_lattice3('#skF_9','#skF_11'))
      | ~ m1_subset_1('#skF_12'(D_111),u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9')
      | ~ r2_hidden(D_111,'#skF_10')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_426])).

tff(c_436,plain,(
    ! [D_237] :
      ( r2_hidden(D_237,a_2_5_lattice3('#skF_9','#skF_11'))
      | ~ m1_subset_1('#skF_12'(D_237),u1_struct_0('#skF_9'))
      | ~ r2_hidden(D_237,'#skF_10')
      | ~ m1_subset_1(D_237,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_434])).

tff(c_441,plain,(
    ! [D_238] :
      ( r2_hidden(D_238,a_2_5_lattice3('#skF_9','#skF_11'))
      | ~ r2_hidden(D_238,'#skF_10')
      | ~ m1_subset_1(D_238,u1_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_98,c_436])).

tff(c_20,plain,(
    ! [A_5,D_26,B_17,C_23] :
      ( r1_lattices(A_5,D_26,B_17)
      | ~ r2_hidden(D_26,C_23)
      | ~ m1_subset_1(D_26,u1_struct_0(A_5))
      | ~ r4_lattice3(A_5,B_17,C_23)
      | ~ m1_subset_1(B_17,u1_struct_0(A_5))
      | ~ l3_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_736,plain,(
    ! [A_268,D_269,B_270] :
      ( r1_lattices(A_268,D_269,B_270)
      | ~ m1_subset_1(D_269,u1_struct_0(A_268))
      | ~ r4_lattice3(A_268,B_270,a_2_5_lattice3('#skF_9','#skF_11'))
      | ~ m1_subset_1(B_270,u1_struct_0(A_268))
      | ~ l3_lattices(A_268)
      | v2_struct_0(A_268)
      | ~ r2_hidden(D_269,'#skF_10')
      | ~ m1_subset_1(D_269,u1_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_441,c_20])).

tff(c_752,plain,(
    ! [D_111,B_270] :
      ( r1_lattices('#skF_9','#skF_12'(D_111),B_270)
      | ~ r4_lattice3('#skF_9',B_270,a_2_5_lattice3('#skF_9','#skF_11'))
      | ~ m1_subset_1(B_270,u1_struct_0('#skF_9'))
      | ~ l3_lattices('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ r2_hidden('#skF_12'(D_111),'#skF_10')
      | ~ m1_subset_1('#skF_12'(D_111),u1_struct_0('#skF_9'))
      | ~ r2_hidden(D_111,'#skF_10')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_98,c_736])).

tff(c_762,plain,(
    ! [D_111,B_270] :
      ( r1_lattices('#skF_9','#skF_12'(D_111),B_270)
      | ~ r4_lattice3('#skF_9',B_270,a_2_5_lattice3('#skF_9','#skF_11'))
      | ~ m1_subset_1(B_270,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9')
      | ~ r2_hidden('#skF_12'(D_111),'#skF_10')
      | ~ m1_subset_1('#skF_12'(D_111),u1_struct_0('#skF_9'))
      | ~ r2_hidden(D_111,'#skF_10')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_752])).

tff(c_889,plain,(
    ! [D_283,B_284] :
      ( r1_lattices('#skF_9','#skF_12'(D_283),B_284)
      | ~ r4_lattice3('#skF_9',B_284,a_2_5_lattice3('#skF_9','#skF_11'))
      | ~ m1_subset_1(B_284,u1_struct_0('#skF_9'))
      | ~ r2_hidden('#skF_12'(D_283),'#skF_10')
      | ~ m1_subset_1('#skF_12'(D_283),u1_struct_0('#skF_9'))
      | ~ r2_hidden(D_283,'#skF_10')
      | ~ m1_subset_1(D_283,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_762])).

tff(c_898,plain,(
    ! [D_283] :
      ( r1_lattices('#skF_9','#skF_12'(D_283),'#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')))
      | ~ m1_subset_1('#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),u1_struct_0('#skF_9'))
      | ~ r2_hidden('#skF_12'(D_283),'#skF_10')
      | ~ m1_subset_1('#skF_12'(D_283),u1_struct_0('#skF_9'))
      | ~ r2_hidden(D_283,'#skF_10')
      | ~ m1_subset_1(D_283,u1_struct_0('#skF_9'))
      | ~ v4_lattice3('#skF_9')
      | ~ l3_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_36,c_889])).

tff(c_909,plain,(
    ! [D_283] :
      ( r1_lattices('#skF_9','#skF_12'(D_283),'#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')))
      | ~ m1_subset_1('#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),u1_struct_0('#skF_9'))
      | ~ r2_hidden('#skF_12'(D_283),'#skF_10')
      | ~ m1_subset_1('#skF_12'(D_283),u1_struct_0('#skF_9'))
      | ~ r2_hidden(D_283,'#skF_10')
      | ~ m1_subset_1(D_283,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_88,c_898])).

tff(c_910,plain,(
    ! [D_283] :
      ( r1_lattices('#skF_9','#skF_12'(D_283),'#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')))
      | ~ m1_subset_1('#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),u1_struct_0('#skF_9'))
      | ~ r2_hidden('#skF_12'(D_283),'#skF_10')
      | ~ m1_subset_1('#skF_12'(D_283),u1_struct_0('#skF_9'))
      | ~ r2_hidden(D_283,'#skF_10')
      | ~ m1_subset_1(D_283,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_909])).

tff(c_1211,plain,(
    ~ m1_subset_1('#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),u1_struct_0('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_910])).

tff(c_1214,plain,
    ( ~ v4_lattice3('#skF_9')
    | ~ l3_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_38,c_1211])).

tff(c_1217,plain,(
    v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_88,c_1214])).

tff(c_1219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1217])).

tff(c_1221,plain,(
    m1_subset_1('#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),u1_struct_0('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_910])).

tff(c_201,plain,(
    ! [D_174,B_175,C_176] :
      ( r2_hidden(D_174,a_2_2_lattice3(B_175,C_176))
      | ~ r4_lattice3(B_175,D_174,C_176)
      | ~ m1_subset_1(D_174,u1_struct_0(B_175))
      | ~ l3_lattices(B_175)
      | ~ v4_lattice3(B_175)
      | ~ v10_lattices(B_175)
      | v2_struct_0(B_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_54,plain,(
    ! [A_65,B_66,C_67] :
      ( '#skF_6'(A_65,B_66,C_67) = A_65
      | ~ r2_hidden(A_65,a_2_2_lattice3(B_66,C_67))
      | ~ l3_lattices(B_66)
      | ~ v4_lattice3(B_66)
      | ~ v10_lattices(B_66)
      | v2_struct_0(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_227,plain,(
    ! [D_184,B_185,C_186] :
      ( '#skF_6'(D_184,B_185,C_186) = D_184
      | ~ r4_lattice3(B_185,D_184,C_186)
      | ~ m1_subset_1(D_184,u1_struct_0(B_185))
      | ~ l3_lattices(B_185)
      | ~ v4_lattice3(B_185)
      | ~ v10_lattices(B_185)
      | v2_struct_0(B_185) ) ),
    inference(resolution,[status(thm)],[c_201,c_54])).

tff(c_252,plain,(
    ! [A_196,B_197] :
      ( '#skF_6'('#skF_2'(A_196,B_197),A_196,B_197) = '#skF_2'(A_196,B_197)
      | ~ m1_subset_1('#skF_2'(A_196,B_197),u1_struct_0(A_196))
      | ~ v10_lattices(A_196)
      | ~ v4_lattice3(A_196)
      | ~ l3_lattices(A_196)
      | v2_struct_0(A_196) ) ),
    inference(resolution,[status(thm)],[c_36,c_227])).

tff(c_255,plain,(
    ! [A_27,B_42] :
      ( '#skF_6'('#skF_2'(A_27,B_42),A_27,B_42) = '#skF_2'(A_27,B_42)
      | ~ v10_lattices(A_27)
      | ~ v4_lattice3(A_27)
      | ~ l3_lattices(A_27)
      | v2_struct_0(A_27) ) ),
    inference(resolution,[status(thm)],[c_38,c_252])).

tff(c_50,plain,(
    ! [D_70,B_66,C_67] :
      ( r2_hidden(D_70,a_2_2_lattice3(B_66,C_67))
      | ~ r4_lattice3(B_66,D_70,C_67)
      | ~ m1_subset_1(D_70,u1_struct_0(B_66))
      | ~ l3_lattices(B_66)
      | ~ v4_lattice3(B_66)
      | ~ v10_lattices(B_66)
      | v2_struct_0(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_56,plain,(
    ! [A_65,B_66,C_67] :
      ( m1_subset_1('#skF_6'(A_65,B_66,C_67),u1_struct_0(B_66))
      | ~ r2_hidden(A_65,a_2_2_lattice3(B_66,C_67))
      | ~ l3_lattices(B_66)
      | ~ v4_lattice3(B_66)
      | ~ v10_lattices(B_66)
      | v2_struct_0(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_52,plain,(
    ! [B_66,A_65,C_67] :
      ( r4_lattice3(B_66,'#skF_6'(A_65,B_66,C_67),C_67)
      | ~ r2_hidden(A_65,a_2_2_lattice3(B_66,C_67))
      | ~ l3_lattices(B_66)
      | ~ v4_lattice3(B_66)
      | ~ v10_lattices(B_66)
      | v2_struct_0(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_911,plain,(
    ! [A_285,B_286,C_287] :
      ( '#skF_6'('#skF_6'(A_285,B_286,C_287),B_286,C_287) = '#skF_6'(A_285,B_286,C_287)
      | ~ m1_subset_1('#skF_6'(A_285,B_286,C_287),u1_struct_0(B_286))
      | ~ r2_hidden(A_285,a_2_2_lattice3(B_286,C_287))
      | ~ l3_lattices(B_286)
      | ~ v4_lattice3(B_286)
      | ~ v10_lattices(B_286)
      | v2_struct_0(B_286) ) ),
    inference(resolution,[status(thm)],[c_52,c_227])).

tff(c_917,plain,(
    ! [A_288,B_289,C_290] :
      ( '#skF_6'('#skF_6'(A_288,B_289,C_290),B_289,C_290) = '#skF_6'(A_288,B_289,C_290)
      | ~ r2_hidden(A_288,a_2_2_lattice3(B_289,C_290))
      | ~ l3_lattices(B_289)
      | ~ v4_lattice3(B_289)
      | ~ v10_lattices(B_289)
      | v2_struct_0(B_289) ) ),
    inference(resolution,[status(thm)],[c_56,c_911])).

tff(c_926,plain,(
    ! [D_70,B_66,C_67] :
      ( '#skF_6'('#skF_6'(D_70,B_66,C_67),B_66,C_67) = '#skF_6'(D_70,B_66,C_67)
      | ~ r4_lattice3(B_66,D_70,C_67)
      | ~ m1_subset_1(D_70,u1_struct_0(B_66))
      | ~ l3_lattices(B_66)
      | ~ v4_lattice3(B_66)
      | ~ v10_lattices(B_66)
      | v2_struct_0(B_66) ) ),
    inference(resolution,[status(thm)],[c_50,c_917])).

tff(c_1223,plain,(
    ! [C_67] :
      ( '#skF_6'('#skF_6'('#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),'#skF_9',C_67),'#skF_9',C_67) = '#skF_6'('#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),'#skF_9',C_67)
      | ~ r4_lattice3('#skF_9','#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),C_67)
      | ~ l3_lattices('#skF_9')
      | ~ v4_lattice3('#skF_9')
      | ~ v10_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1221,c_926])).

tff(c_1236,plain,(
    ! [C_67] :
      ( '#skF_6'('#skF_6'('#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),'#skF_9',C_67),'#skF_9',C_67) = '#skF_6'('#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),'#skF_9',C_67)
      | ~ r4_lattice3('#skF_9','#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),C_67)
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_1223])).

tff(c_1268,plain,(
    ! [C_328] :
      ( '#skF_6'('#skF_6'('#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),'#skF_9',C_328),'#skF_9',C_328) = '#skF_6'('#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),'#skF_9',C_328)
      | ~ r4_lattice3('#skF_9','#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),C_328) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1236])).

tff(c_1286,plain,(
    ! [C_328] :
      ( m1_subset_1('#skF_6'('#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),'#skF_9',C_328),u1_struct_0('#skF_9'))
      | ~ r2_hidden('#skF_6'('#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),'#skF_9',C_328),a_2_2_lattice3('#skF_9',C_328))
      | ~ l3_lattices('#skF_9')
      | ~ v4_lattice3('#skF_9')
      | ~ v10_lattices('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ r4_lattice3('#skF_9','#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),C_328) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1268,c_56])).

tff(c_1307,plain,(
    ! [C_328] :
      ( m1_subset_1('#skF_6'('#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),'#skF_9',C_328),u1_struct_0('#skF_9'))
      | ~ r2_hidden('#skF_6'('#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),'#skF_9',C_328),a_2_2_lattice3('#skF_9',C_328))
      | v2_struct_0('#skF_9')
      | ~ r4_lattice3('#skF_9','#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),C_328) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_1286])).

tff(c_1334,plain,(
    ! [C_330] :
      ( m1_subset_1('#skF_6'('#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),'#skF_9',C_330),u1_struct_0('#skF_9'))
      | ~ r2_hidden('#skF_6'('#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),'#skF_9',C_330),a_2_2_lattice3('#skF_9',C_330))
      | ~ r4_lattice3('#skF_9','#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),C_330) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1307])).

tff(c_1338,plain,
    ( m1_subset_1('#skF_6'('#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),'#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),u1_struct_0('#skF_9'))
    | ~ r2_hidden('#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),a_2_2_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')))
    | ~ r4_lattice3('#skF_9','#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),a_2_5_lattice3('#skF_9','#skF_11'))
    | ~ v10_lattices('#skF_9')
    | ~ v4_lattice3('#skF_9')
    | ~ l3_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_1334])).

tff(c_1344,plain,
    ( m1_subset_1('#skF_6'('#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),'#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),u1_struct_0('#skF_9'))
    | ~ r2_hidden('#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),a_2_2_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')))
    | ~ r4_lattice3('#skF_9','#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),a_2_5_lattice3('#skF_9','#skF_11'))
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_88,c_90,c_1338])).

tff(c_1345,plain,
    ( m1_subset_1('#skF_6'('#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),'#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),u1_struct_0('#skF_9'))
    | ~ r2_hidden('#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),a_2_2_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')))
    | ~ r4_lattice3('#skF_9','#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),a_2_5_lattice3('#skF_9','#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1344])).

tff(c_1560,plain,(
    ~ r4_lattice3('#skF_9','#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),a_2_5_lattice3('#skF_9','#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_1345])).

tff(c_1563,plain,
    ( ~ v4_lattice3('#skF_9')
    | ~ l3_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_36,c_1560])).

tff(c_1566,plain,(
    v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_88,c_1563])).

tff(c_1568,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1566])).

tff(c_1570,plain,(
    r4_lattice3('#skF_9','#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),a_2_5_lattice3('#skF_9','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_1345])).

tff(c_44,plain,(
    ! [A_53,B_60,C_61] :
      ( m1_subset_1('#skF_5'(A_53,B_60,C_61),u1_struct_0(A_53))
      | k15_lattice3(A_53,B_60) = C_61
      | ~ r4_lattice3(A_53,C_61,B_60)
      | ~ m1_subset_1(C_61,u1_struct_0(A_53))
      | ~ v4_lattice3(A_53)
      | ~ v10_lattices(A_53)
      | ~ l3_lattices(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_42,plain,(
    ! [A_53,B_60,C_61] :
      ( r4_lattice3(A_53,'#skF_5'(A_53,B_60,C_61),B_60)
      | k15_lattice3(A_53,B_60) = C_61
      | ~ r4_lattice3(A_53,C_61,B_60)
      | ~ m1_subset_1(C_61,u1_struct_0(A_53))
      | ~ v4_lattice3(A_53)
      | ~ v10_lattices(A_53)
      | ~ l3_lattices(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_34,plain,(
    ! [A_27,B_42,D_47] :
      ( r1_lattices(A_27,'#skF_2'(A_27,B_42),D_47)
      | ~ r4_lattice3(A_27,D_47,B_42)
      | ~ m1_subset_1(D_47,u1_struct_0(A_27))
      | ~ v4_lattice3(A_27)
      | ~ l3_lattices(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_364,plain,(
    ! [A_213,C_214,B_215] :
      ( ~ r1_lattices(A_213,C_214,'#skF_5'(A_213,B_215,C_214))
      | k15_lattice3(A_213,B_215) = C_214
      | ~ r4_lattice3(A_213,C_214,B_215)
      | ~ m1_subset_1(C_214,u1_struct_0(A_213))
      | ~ v4_lattice3(A_213)
      | ~ v10_lattices(A_213)
      | ~ l3_lattices(A_213)
      | v2_struct_0(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_3821,plain,(
    ! [A_579,B_580,B_581] :
      ( k15_lattice3(A_579,B_580) = '#skF_2'(A_579,B_581)
      | ~ r4_lattice3(A_579,'#skF_2'(A_579,B_581),B_580)
      | ~ m1_subset_1('#skF_2'(A_579,B_581),u1_struct_0(A_579))
      | ~ v10_lattices(A_579)
      | ~ r4_lattice3(A_579,'#skF_5'(A_579,B_580,'#skF_2'(A_579,B_581)),B_581)
      | ~ m1_subset_1('#skF_5'(A_579,B_580,'#skF_2'(A_579,B_581)),u1_struct_0(A_579))
      | ~ v4_lattice3(A_579)
      | ~ l3_lattices(A_579)
      | v2_struct_0(A_579) ) ),
    inference(resolution,[status(thm)],[c_34,c_364])).

tff(c_3827,plain,(
    ! [A_583,B_584] :
      ( ~ m1_subset_1('#skF_5'(A_583,B_584,'#skF_2'(A_583,B_584)),u1_struct_0(A_583))
      | k15_lattice3(A_583,B_584) = '#skF_2'(A_583,B_584)
      | ~ r4_lattice3(A_583,'#skF_2'(A_583,B_584),B_584)
      | ~ m1_subset_1('#skF_2'(A_583,B_584),u1_struct_0(A_583))
      | ~ v4_lattice3(A_583)
      | ~ v10_lattices(A_583)
      | ~ l3_lattices(A_583)
      | v2_struct_0(A_583) ) ),
    inference(resolution,[status(thm)],[c_42,c_3821])).

tff(c_3833,plain,(
    ! [A_585,B_586] :
      ( k15_lattice3(A_585,B_586) = '#skF_2'(A_585,B_586)
      | ~ r4_lattice3(A_585,'#skF_2'(A_585,B_586),B_586)
      | ~ m1_subset_1('#skF_2'(A_585,B_586),u1_struct_0(A_585))
      | ~ v4_lattice3(A_585)
      | ~ v10_lattices(A_585)
      | ~ l3_lattices(A_585)
      | v2_struct_0(A_585) ) ),
    inference(resolution,[status(thm)],[c_44,c_3827])).

tff(c_3835,plain,
    ( k15_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')) = '#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11'))
    | ~ m1_subset_1('#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),u1_struct_0('#skF_9'))
    | ~ v4_lattice3('#skF_9')
    | ~ v10_lattices('#skF_9')
    | ~ l3_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_1570,c_3833])).

tff(c_3840,plain,
    ( k15_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')) = '#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11'))
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_90,c_88,c_1221,c_3835])).

tff(c_3841,plain,(
    k15_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')) = '#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_3840])).

tff(c_184,plain,(
    ! [A_163,B_164] :
      ( r4_lattice3(A_163,k15_lattice3(A_163,B_164),B_164)
      | ~ m1_subset_1(k15_lattice3(A_163,B_164),u1_struct_0(A_163))
      | ~ v4_lattice3(A_163)
      | ~ v10_lattices(A_163)
      | ~ l3_lattices(A_163)
      | v2_struct_0(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1017,plain,(
    ! [A_299,B_300] :
      ( r4_lattice3(A_299,k15_lattice3(A_299,a_2_5_lattice3(A_299,B_300)),a_2_5_lattice3(A_299,B_300))
      | ~ m1_subset_1(k15_lattice3(A_299,B_300),u1_struct_0(A_299))
      | ~ v4_lattice3(A_299)
      | ~ v10_lattices(A_299)
      | ~ l3_lattices(A_299)
      | v2_struct_0(A_299)
      | ~ l3_lattices(A_299)
      | ~ v4_lattice3(A_299)
      | ~ v10_lattices(A_299)
      | v2_struct_0(A_299) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_184])).

tff(c_2786,plain,(
    ! [A_481,B_482] :
      ( r4_lattice3(A_481,k15_lattice3(A_481,B_482),a_2_5_lattice3(A_481,B_482))
      | ~ m1_subset_1(k15_lattice3(A_481,B_482),u1_struct_0(A_481))
      | ~ v4_lattice3(A_481)
      | ~ v10_lattices(A_481)
      | ~ l3_lattices(A_481)
      | v2_struct_0(A_481)
      | ~ l3_lattices(A_481)
      | ~ v4_lattice3(A_481)
      | ~ v10_lattices(A_481)
      | v2_struct_0(A_481)
      | ~ l3_lattices(A_481)
      | ~ v4_lattice3(A_481)
      | ~ v10_lattices(A_481)
      | v2_struct_0(A_481) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_1017])).

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

tff(c_296,plain,(
    ! [A_203,B_204,C_205] :
      ( r1_lattices(A_203,B_204,C_205)
      | ~ r3_lattices(A_203,B_204,C_205)
      | ~ m1_subset_1(C_205,u1_struct_0(A_203))
      | ~ m1_subset_1(B_204,u1_struct_0(A_203))
      | ~ l3_lattices(A_203)
      | ~ v9_lattices(A_203)
      | ~ v8_lattices(A_203)
      | ~ v6_lattices(A_203)
      | v2_struct_0(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_304,plain,(
    ! [D_111] :
      ( r1_lattices('#skF_9',D_111,'#skF_12'(D_111))
      | ~ m1_subset_1('#skF_12'(D_111),u1_struct_0('#skF_9'))
      | ~ l3_lattices('#skF_9')
      | ~ v9_lattices('#skF_9')
      | ~ v8_lattices('#skF_9')
      | ~ v6_lattices('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ r2_hidden(D_111,'#skF_10')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_96,c_296])).

tff(c_310,plain,(
    ! [D_111] :
      ( r1_lattices('#skF_9',D_111,'#skF_12'(D_111))
      | ~ m1_subset_1('#skF_12'(D_111),u1_struct_0('#skF_9'))
      | ~ v9_lattices('#skF_9')
      | ~ v8_lattices('#skF_9')
      | ~ v6_lattices('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ r2_hidden(D_111,'#skF_10')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_304])).

tff(c_311,plain,(
    ! [D_111] :
      ( r1_lattices('#skF_9',D_111,'#skF_12'(D_111))
      | ~ m1_subset_1('#skF_12'(D_111),u1_struct_0('#skF_9'))
      | ~ v9_lattices('#skF_9')
      | ~ v8_lattices('#skF_9')
      | ~ v6_lattices('#skF_9')
      | ~ r2_hidden(D_111,'#skF_10')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_310])).

tff(c_312,plain,(
    ~ v6_lattices('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_311])).

tff(c_316,plain,
    ( ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_8,c_312])).

tff(c_319,plain,(
    v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_90,c_316])).

tff(c_321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_319])).

tff(c_322,plain,(
    ! [D_111] :
      ( ~ v8_lattices('#skF_9')
      | ~ v9_lattices('#skF_9')
      | r1_lattices('#skF_9',D_111,'#skF_12'(D_111))
      | ~ m1_subset_1('#skF_12'(D_111),u1_struct_0('#skF_9'))
      | ~ r2_hidden(D_111,'#skF_10')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_9')) ) ),
    inference(splitRight,[status(thm)],[c_311])).

tff(c_324,plain,(
    ~ v9_lattices('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_322])).

tff(c_327,plain,
    ( ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_2,c_324])).

tff(c_330,plain,(
    v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_90,c_327])).

tff(c_332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_330])).

tff(c_333,plain,(
    ! [D_111] :
      ( ~ v8_lattices('#skF_9')
      | r1_lattices('#skF_9',D_111,'#skF_12'(D_111))
      | ~ m1_subset_1('#skF_12'(D_111),u1_struct_0('#skF_9'))
      | ~ r2_hidden(D_111,'#skF_10')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_9')) ) ),
    inference(splitRight,[status(thm)],[c_322])).

tff(c_339,plain,(
    ~ v8_lattices('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_333])).

tff(c_342,plain,
    ( ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_4,c_339])).

tff(c_345,plain,(
    v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_90,c_342])).

tff(c_347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_345])).

tff(c_359,plain,(
    ! [D_211] :
      ( r1_lattices('#skF_9',D_211,'#skF_12'(D_211))
      | ~ m1_subset_1('#skF_12'(D_211),u1_struct_0('#skF_9'))
      | ~ r2_hidden(D_211,'#skF_10')
      | ~ m1_subset_1(D_211,u1_struct_0('#skF_9')) ) ),
    inference(splitRight,[status(thm)],[c_333])).

tff(c_362,plain,(
    ! [D_111] :
      ( r1_lattices('#skF_9',D_111,'#skF_12'(D_111))
      | ~ r2_hidden(D_111,'#skF_10')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_98,c_359])).

tff(c_323,plain,(
    v6_lattices('#skF_9') ),
    inference(splitRight,[status(thm)],[c_311])).

tff(c_349,plain,(
    v8_lattices('#skF_9') ),
    inference(splitRight,[status(thm)],[c_333])).

tff(c_334,plain,(
    v9_lattices('#skF_9') ),
    inference(splitRight,[status(thm)],[c_322])).

tff(c_256,plain,(
    ! [A_198,B_199,C_200] :
      ( r3_lattices(A_198,B_199,C_200)
      | ~ r1_lattices(A_198,B_199,C_200)
      | ~ m1_subset_1(C_200,u1_struct_0(A_198))
      | ~ m1_subset_1(B_199,u1_struct_0(A_198))
      | ~ l3_lattices(A_198)
      | ~ v9_lattices(A_198)
      | ~ v8_lattices(A_198)
      | ~ v6_lattices(A_198)
      | v2_struct_0(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_270,plain,(
    ! [B_199,D_111] :
      ( r3_lattices('#skF_9',B_199,'#skF_12'(D_111))
      | ~ r1_lattices('#skF_9',B_199,'#skF_12'(D_111))
      | ~ m1_subset_1(B_199,u1_struct_0('#skF_9'))
      | ~ l3_lattices('#skF_9')
      | ~ v9_lattices('#skF_9')
      | ~ v8_lattices('#skF_9')
      | ~ v6_lattices('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ r2_hidden(D_111,'#skF_10')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_98,c_256])).

tff(c_279,plain,(
    ! [B_199,D_111] :
      ( r3_lattices('#skF_9',B_199,'#skF_12'(D_111))
      | ~ r1_lattices('#skF_9',B_199,'#skF_12'(D_111))
      | ~ m1_subset_1(B_199,u1_struct_0('#skF_9'))
      | ~ v9_lattices('#skF_9')
      | ~ v8_lattices('#skF_9')
      | ~ v6_lattices('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ r2_hidden(D_111,'#skF_10')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_270])).

tff(c_280,plain,(
    ! [B_199,D_111] :
      ( r3_lattices('#skF_9',B_199,'#skF_12'(D_111))
      | ~ r1_lattices('#skF_9',B_199,'#skF_12'(D_111))
      | ~ m1_subset_1(B_199,u1_struct_0('#skF_9'))
      | ~ v9_lattices('#skF_9')
      | ~ v8_lattices('#skF_9')
      | ~ v6_lattices('#skF_9')
      | ~ r2_hidden(D_111,'#skF_10')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_279])).

tff(c_351,plain,(
    ! [B_199,D_111] :
      ( r3_lattices('#skF_9',B_199,'#skF_12'(D_111))
      | ~ r1_lattices('#skF_9',B_199,'#skF_12'(D_111))
      | ~ m1_subset_1(B_199,u1_struct_0('#skF_9'))
      | ~ r2_hidden(D_111,'#skF_10')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_349,c_334,c_280])).

tff(c_58,plain,(
    ! [D_81,B_72,C_73,E_83] :
      ( r2_hidden(D_81,a_2_5_lattice3(B_72,C_73))
      | ~ r2_hidden(E_83,C_73)
      | ~ r3_lattices(B_72,D_81,E_83)
      | ~ m1_subset_1(E_83,u1_struct_0(B_72))
      | ~ m1_subset_1(D_81,u1_struct_0(B_72))
      | ~ l3_lattices(B_72)
      | ~ v4_lattice3(B_72)
      | ~ v10_lattices(B_72)
      | v2_struct_0(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_1428,plain,(
    ! [D_345,B_346,D_347] :
      ( r2_hidden(D_345,a_2_5_lattice3(B_346,a_2_5_lattice3('#skF_9','#skF_11')))
      | ~ r3_lattices(B_346,D_345,D_347)
      | ~ m1_subset_1(D_347,u1_struct_0(B_346))
      | ~ m1_subset_1(D_345,u1_struct_0(B_346))
      | ~ l3_lattices(B_346)
      | ~ v4_lattice3(B_346)
      | ~ v10_lattices(B_346)
      | v2_struct_0(B_346)
      | ~ r2_hidden(D_347,'#skF_10')
      | ~ m1_subset_1(D_347,u1_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_441,c_58])).

tff(c_1444,plain,(
    ! [B_199,D_111] :
      ( r2_hidden(B_199,a_2_5_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')))
      | ~ l3_lattices('#skF_9')
      | ~ v4_lattice3('#skF_9')
      | ~ v10_lattices('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ r2_hidden('#skF_12'(D_111),'#skF_10')
      | ~ m1_subset_1('#skF_12'(D_111),u1_struct_0('#skF_9'))
      | ~ r1_lattices('#skF_9',B_199,'#skF_12'(D_111))
      | ~ m1_subset_1(B_199,u1_struct_0('#skF_9'))
      | ~ r2_hidden(D_111,'#skF_10')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_351,c_1428])).

tff(c_1468,plain,(
    ! [B_199,D_111] :
      ( r2_hidden(B_199,a_2_5_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')))
      | v2_struct_0('#skF_9')
      | ~ r2_hidden('#skF_12'(D_111),'#skF_10')
      | ~ m1_subset_1('#skF_12'(D_111),u1_struct_0('#skF_9'))
      | ~ r1_lattices('#skF_9',B_199,'#skF_12'(D_111))
      | ~ m1_subset_1(B_199,u1_struct_0('#skF_9'))
      | ~ r2_hidden(D_111,'#skF_10')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_1444])).

tff(c_1497,plain,(
    ! [B_351,D_352] :
      ( r2_hidden(B_351,a_2_5_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')))
      | ~ r2_hidden('#skF_12'(D_352),'#skF_10')
      | ~ m1_subset_1('#skF_12'(D_352),u1_struct_0('#skF_9'))
      | ~ r1_lattices('#skF_9',B_351,'#skF_12'(D_352))
      | ~ m1_subset_1(B_351,u1_struct_0('#skF_9'))
      | ~ r2_hidden(D_352,'#skF_10')
      | ~ m1_subset_1(D_352,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1468])).

tff(c_1501,plain,(
    ! [B_353,D_354] :
      ( r2_hidden(B_353,a_2_5_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')))
      | ~ r2_hidden('#skF_12'(D_354),'#skF_10')
      | ~ r1_lattices('#skF_9',B_353,'#skF_12'(D_354))
      | ~ m1_subset_1(B_353,u1_struct_0('#skF_9'))
      | ~ r2_hidden(D_354,'#skF_10')
      | ~ m1_subset_1(D_354,u1_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_98,c_1497])).

tff(c_1516,plain,(
    ! [D_355] :
      ( r2_hidden(D_355,a_2_5_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')))
      | ~ r2_hidden('#skF_12'(D_355),'#skF_10')
      | ~ r2_hidden(D_355,'#skF_10')
      | ~ m1_subset_1(D_355,u1_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_362,c_1501])).

tff(c_1735,plain,(
    ! [A_382,D_383,B_384] :
      ( r1_lattices(A_382,D_383,B_384)
      | ~ m1_subset_1(D_383,u1_struct_0(A_382))
      | ~ r4_lattice3(A_382,B_384,a_2_5_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')))
      | ~ m1_subset_1(B_384,u1_struct_0(A_382))
      | ~ l3_lattices(A_382)
      | v2_struct_0(A_382)
      | ~ r2_hidden('#skF_12'(D_383),'#skF_10')
      | ~ r2_hidden(D_383,'#skF_10')
      | ~ m1_subset_1(D_383,u1_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_1516,c_20])).

tff(c_1755,plain,(
    ! [D_111,B_384] :
      ( r1_lattices('#skF_9','#skF_12'(D_111),B_384)
      | ~ r4_lattice3('#skF_9',B_384,a_2_5_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')))
      | ~ m1_subset_1(B_384,u1_struct_0('#skF_9'))
      | ~ l3_lattices('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ r2_hidden('#skF_12'('#skF_12'(D_111)),'#skF_10')
      | ~ r2_hidden('#skF_12'(D_111),'#skF_10')
      | ~ m1_subset_1('#skF_12'(D_111),u1_struct_0('#skF_9'))
      | ~ r2_hidden(D_111,'#skF_10')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_98,c_1735])).

tff(c_1773,plain,(
    ! [D_111,B_384] :
      ( r1_lattices('#skF_9','#skF_12'(D_111),B_384)
      | ~ r4_lattice3('#skF_9',B_384,a_2_5_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')))
      | ~ m1_subset_1(B_384,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9')
      | ~ r2_hidden('#skF_12'('#skF_12'(D_111)),'#skF_10')
      | ~ r2_hidden('#skF_12'(D_111),'#skF_10')
      | ~ m1_subset_1('#skF_12'(D_111),u1_struct_0('#skF_9'))
      | ~ r2_hidden(D_111,'#skF_10')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1755])).

tff(c_1774,plain,(
    ! [D_111,B_384] :
      ( r1_lattices('#skF_9','#skF_12'(D_111),B_384)
      | ~ r4_lattice3('#skF_9',B_384,a_2_5_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')))
      | ~ m1_subset_1(B_384,u1_struct_0('#skF_9'))
      | ~ r2_hidden('#skF_12'('#skF_12'(D_111)),'#skF_10')
      | ~ r2_hidden('#skF_12'(D_111),'#skF_10')
      | ~ m1_subset_1('#skF_12'(D_111),u1_struct_0('#skF_9'))
      | ~ r2_hidden(D_111,'#skF_10')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1773])).

tff(c_2789,plain,(
    ! [D_111] :
      ( r1_lattices('#skF_9','#skF_12'(D_111),k15_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')))
      | ~ r2_hidden('#skF_12'('#skF_12'(D_111)),'#skF_10')
      | ~ r2_hidden('#skF_12'(D_111),'#skF_10')
      | ~ m1_subset_1('#skF_12'(D_111),u1_struct_0('#skF_9'))
      | ~ r2_hidden(D_111,'#skF_10')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_9'))
      | ~ m1_subset_1(k15_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),u1_struct_0('#skF_9'))
      | ~ l3_lattices('#skF_9')
      | ~ v4_lattice3('#skF_9')
      | ~ v10_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2786,c_1774])).

tff(c_2806,plain,(
    ! [D_111] :
      ( r1_lattices('#skF_9','#skF_12'(D_111),k15_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')))
      | ~ r2_hidden('#skF_12'('#skF_12'(D_111)),'#skF_10')
      | ~ r2_hidden('#skF_12'(D_111),'#skF_10')
      | ~ m1_subset_1('#skF_12'(D_111),u1_struct_0('#skF_9'))
      | ~ r2_hidden(D_111,'#skF_10')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_9'))
      | ~ m1_subset_1(k15_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_2789])).

tff(c_2807,plain,(
    ! [D_111] :
      ( r1_lattices('#skF_9','#skF_12'(D_111),k15_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')))
      | ~ r2_hidden('#skF_12'('#skF_12'(D_111)),'#skF_10')
      | ~ r2_hidden('#skF_12'(D_111),'#skF_10')
      | ~ m1_subset_1('#skF_12'(D_111),u1_struct_0('#skF_9'))
      | ~ r2_hidden(D_111,'#skF_10')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_9'))
      | ~ m1_subset_1(k15_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_2806])).

tff(c_3302,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),u1_struct_0('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_2807])).

tff(c_3843,plain,(
    ~ m1_subset_1('#skF_2'('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),u1_struct_0('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3841,c_3302])).

tff(c_3846,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1221,c_3843])).

tff(c_3848,plain,(
    m1_subset_1(k15_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),u1_struct_0('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_2807])).

tff(c_3885,plain,
    ( m1_subset_1(k15_lattice3('#skF_9','#skF_11'),u1_struct_0('#skF_9'))
    | ~ l3_lattices('#skF_9')
    | ~ v4_lattice3('#skF_9')
    | ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_3848])).

tff(c_3942,plain,
    ( m1_subset_1(k15_lattice3('#skF_9','#skF_11'),u1_struct_0('#skF_9'))
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_3885])).

tff(c_3944,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_887,c_3942])).

tff(c_3946,plain,(
    m1_subset_1(k15_lattice3('#skF_9','#skF_11'),u1_struct_0('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_886])).

tff(c_3945,plain,(
    ~ r2_hidden(k15_lattice3('#skF_9','#skF_11'),a_2_2_lattice3('#skF_9','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_886])).

tff(c_3987,plain,
    ( ~ r4_lattice3('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10')
    | ~ m1_subset_1(k15_lattice3('#skF_9','#skF_11'),u1_struct_0('#skF_9'))
    | ~ l3_lattices('#skF_9')
    | ~ v4_lattice3('#skF_9')
    | ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_50,c_3945])).

tff(c_3990,plain,
    ( ~ r4_lattice3('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_3946,c_3987])).

tff(c_3991,plain,(
    ~ r4_lattice3('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_3990])).

tff(c_24,plain,(
    ! [A_5,B_17,C_23] :
      ( r2_hidden('#skF_1'(A_5,B_17,C_23),C_23)
      | r4_lattice3(A_5,B_17,C_23)
      | ~ m1_subset_1(B_17,u1_struct_0(A_5))
      | ~ l3_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_26,plain,(
    ! [A_5,B_17,C_23] :
      ( m1_subset_1('#skF_1'(A_5,B_17,C_23),u1_struct_0(A_5))
      | r4_lattice3(A_5,B_17,C_23)
      | ~ m1_subset_1(B_17,u1_struct_0(A_5))
      | ~ l3_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_440,plain,(
    ! [D_111] :
      ( r2_hidden(D_111,a_2_5_lattice3('#skF_9','#skF_11'))
      | ~ r2_hidden(D_111,'#skF_10')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_98,c_436])).

tff(c_66,plain,(
    ! [A_71,B_72,C_73] :
      ( '#skF_7'(A_71,B_72,C_73) = A_71
      | ~ r2_hidden(A_71,a_2_5_lattice3(B_72,C_73))
      | ~ l3_lattices(B_72)
      | ~ v4_lattice3(B_72)
      | ~ v10_lattices(B_72)
      | v2_struct_0(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_448,plain,(
    ! [D_238] :
      ( '#skF_7'(D_238,'#skF_9','#skF_11') = D_238
      | ~ l3_lattices('#skF_9')
      | ~ v4_lattice3('#skF_9')
      | ~ v10_lattices('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ r2_hidden(D_238,'#skF_10')
      | ~ m1_subset_1(D_238,u1_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_441,c_66])).

tff(c_453,plain,(
    ! [D_238] :
      ( '#skF_7'(D_238,'#skF_9','#skF_11') = D_238
      | v2_struct_0('#skF_9')
      | ~ r2_hidden(D_238,'#skF_10')
      | ~ m1_subset_1(D_238,u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_448])).

tff(c_455,plain,(
    ! [D_239] :
      ( '#skF_7'(D_239,'#skF_9','#skF_11') = D_239
      | ~ r2_hidden(D_239,'#skF_10')
      | ~ m1_subset_1(D_239,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_453])).

tff(c_479,plain,(
    ! [B_17,C_23] :
      ( '#skF_7'('#skF_1'('#skF_9',B_17,C_23),'#skF_9','#skF_11') = '#skF_1'('#skF_9',B_17,C_23)
      | ~ r2_hidden('#skF_1'('#skF_9',B_17,C_23),'#skF_10')
      | r4_lattice3('#skF_9',B_17,C_23)
      | ~ m1_subset_1(B_17,u1_struct_0('#skF_9'))
      | ~ l3_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_26,c_455])).

tff(c_509,plain,(
    ! [B_17,C_23] :
      ( '#skF_7'('#skF_1'('#skF_9',B_17,C_23),'#skF_9','#skF_11') = '#skF_1'('#skF_9',B_17,C_23)
      | ~ r2_hidden('#skF_1'('#skF_9',B_17,C_23),'#skF_10')
      | r4_lattice3('#skF_9',B_17,C_23)
      | ~ m1_subset_1(B_17,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_479])).

tff(c_564,plain,(
    ! [B_252,C_253] :
      ( '#skF_7'('#skF_1'('#skF_9',B_252,C_253),'#skF_9','#skF_11') = '#skF_1'('#skF_9',B_252,C_253)
      | ~ r2_hidden('#skF_1'('#skF_9',B_252,C_253),'#skF_10')
      | r4_lattice3('#skF_9',B_252,C_253)
      | ~ m1_subset_1(B_252,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_509])).

tff(c_568,plain,(
    ! [B_17] :
      ( '#skF_7'('#skF_1'('#skF_9',B_17,'#skF_10'),'#skF_9','#skF_11') = '#skF_1'('#skF_9',B_17,'#skF_10')
      | r4_lattice3('#skF_9',B_17,'#skF_10')
      | ~ m1_subset_1(B_17,u1_struct_0('#skF_9'))
      | ~ l3_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_24,c_564])).

tff(c_571,plain,(
    ! [B_17] :
      ( '#skF_7'('#skF_1'('#skF_9',B_17,'#skF_10'),'#skF_9','#skF_11') = '#skF_1'('#skF_9',B_17,'#skF_10')
      | r4_lattice3('#skF_9',B_17,'#skF_10')
      | ~ m1_subset_1(B_17,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_568])).

tff(c_572,plain,(
    ! [B_17] :
      ( '#skF_7'('#skF_1'('#skF_9',B_17,'#skF_10'),'#skF_9','#skF_11') = '#skF_1'('#skF_9',B_17,'#skF_10')
      | r4_lattice3('#skF_9',B_17,'#skF_10')
      | ~ m1_subset_1(B_17,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_571])).

tff(c_3965,plain,
    ( '#skF_7'('#skF_1'('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10'),'#skF_9','#skF_11') = '#skF_1'('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10')
    | r4_lattice3('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10') ),
    inference(resolution,[status(thm)],[c_3946,c_572])).

tff(c_4059,plain,(
    '#skF_7'('#skF_1'('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10'),'#skF_9','#skF_11') = '#skF_1'('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_3991,c_3965])).

tff(c_68,plain,(
    ! [A_71,B_72,C_73] :
      ( m1_subset_1('#skF_7'(A_71,B_72,C_73),u1_struct_0(B_72))
      | ~ r2_hidden(A_71,a_2_5_lattice3(B_72,C_73))
      | ~ l3_lattices(B_72)
      | ~ v4_lattice3(B_72)
      | ~ v10_lattices(B_72)
      | v2_struct_0(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_4072,plain,
    ( m1_subset_1('#skF_1'('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10'),u1_struct_0('#skF_9'))
    | ~ r2_hidden('#skF_1'('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10'),a_2_5_lattice3('#skF_9','#skF_11'))
    | ~ l3_lattices('#skF_9')
    | ~ v4_lattice3('#skF_9')
    | ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_4059,c_68])).

tff(c_4081,plain,
    ( m1_subset_1('#skF_1'('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10'),u1_struct_0('#skF_9'))
    | ~ r2_hidden('#skF_1'('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10'),a_2_5_lattice3('#skF_9','#skF_11'))
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_4072])).

tff(c_4082,plain,
    ( m1_subset_1('#skF_1'('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10'),u1_struct_0('#skF_9'))
    | ~ r2_hidden('#skF_1'('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10'),a_2_5_lattice3('#skF_9','#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_4081])).

tff(c_4084,plain,(
    ~ r2_hidden('#skF_1'('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10'),a_2_5_lattice3('#skF_9','#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_4082])).

tff(c_4095,plain,
    ( ~ r2_hidden('#skF_1'('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10'),'#skF_10')
    | ~ m1_subset_1('#skF_1'('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10'),u1_struct_0('#skF_9')) ),
    inference(resolution,[status(thm)],[c_440,c_4084])).

tff(c_4096,plain,(
    ~ m1_subset_1('#skF_1'('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10'),u1_struct_0('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_4095])).

tff(c_4099,plain,
    ( r4_lattice3('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10')
    | ~ m1_subset_1(k15_lattice3('#skF_9','#skF_11'),u1_struct_0('#skF_9'))
    | ~ l3_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_26,c_4096])).

tff(c_4102,plain,
    ( r4_lattice3('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_3946,c_4099])).

tff(c_4104,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_3991,c_4102])).

tff(c_4105,plain,(
    ~ r2_hidden('#skF_1'('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10'),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_4095])).

tff(c_4109,plain,
    ( r4_lattice3('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10')
    | ~ m1_subset_1(k15_lattice3('#skF_9','#skF_11'),u1_struct_0('#skF_9'))
    | ~ l3_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_24,c_4105])).

tff(c_4112,plain,
    ( r4_lattice3('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_3946,c_4109])).

tff(c_4114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_3991,c_4112])).

tff(c_4115,plain,(
    m1_subset_1('#skF_1'('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10'),u1_struct_0('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_4082])).

tff(c_450,plain,(
    ! [A_5,D_238,B_17] :
      ( r1_lattices(A_5,D_238,B_17)
      | ~ m1_subset_1(D_238,u1_struct_0(A_5))
      | ~ r4_lattice3(A_5,B_17,a_2_5_lattice3('#skF_9','#skF_11'))
      | ~ m1_subset_1(B_17,u1_struct_0(A_5))
      | ~ l3_lattices(A_5)
      | v2_struct_0(A_5)
      | ~ r2_hidden(D_238,'#skF_10')
      | ~ m1_subset_1(D_238,u1_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_441,c_20])).

tff(c_4118,plain,(
    ! [B_17] :
      ( r1_lattices('#skF_9','#skF_1'('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10'),B_17)
      | ~ r4_lattice3('#skF_9',B_17,a_2_5_lattice3('#skF_9','#skF_11'))
      | ~ m1_subset_1(B_17,u1_struct_0('#skF_9'))
      | ~ l3_lattices('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ r2_hidden('#skF_1'('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10'),'#skF_10')
      | ~ m1_subset_1('#skF_1'('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10'),u1_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_4115,c_450])).

tff(c_4129,plain,(
    ! [B_17] :
      ( r1_lattices('#skF_9','#skF_1'('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10'),B_17)
      | ~ r4_lattice3('#skF_9',B_17,a_2_5_lattice3('#skF_9','#skF_11'))
      | ~ m1_subset_1(B_17,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9')
      | ~ r2_hidden('#skF_1'('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10'),'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4115,c_86,c_4118])).

tff(c_4130,plain,(
    ! [B_17] :
      ( r1_lattices('#skF_9','#skF_1'('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10'),B_17)
      | ~ r4_lattice3('#skF_9',B_17,a_2_5_lattice3('#skF_9','#skF_11'))
      | ~ m1_subset_1(B_17,u1_struct_0('#skF_9'))
      | ~ r2_hidden('#skF_1'('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10'),'#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_4129])).

tff(c_4181,plain,(
    ~ r2_hidden('#skF_1'('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10'),'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_4130])).

tff(c_4184,plain,
    ( r4_lattice3('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10')
    | ~ m1_subset_1(k15_lattice3('#skF_9','#skF_11'),u1_struct_0('#skF_9'))
    | ~ l3_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_24,c_4181])).

tff(c_4187,plain,
    ( r4_lattice3('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_3946,c_4184])).

tff(c_4189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_3991,c_4187])).

tff(c_4205,plain,(
    ! [B_600] :
      ( r1_lattices('#skF_9','#skF_1'('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10'),B_600)
      | ~ r4_lattice3('#skF_9',B_600,a_2_5_lattice3('#skF_9','#skF_11'))
      | ~ m1_subset_1(B_600,u1_struct_0('#skF_9')) ) ),
    inference(splitRight,[status(thm)],[c_4130])).

tff(c_22,plain,(
    ! [A_5,B_17,C_23] :
      ( ~ r1_lattices(A_5,'#skF_1'(A_5,B_17,C_23),B_17)
      | r4_lattice3(A_5,B_17,C_23)
      | ~ m1_subset_1(B_17,u1_struct_0(A_5))
      | ~ l3_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4220,plain,
    ( r4_lattice3('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10')
    | ~ l3_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ r4_lattice3('#skF_9',k15_lattice3('#skF_9','#skF_11'),a_2_5_lattice3('#skF_9','#skF_11'))
    | ~ m1_subset_1(k15_lattice3('#skF_9','#skF_11'),u1_struct_0('#skF_9')) ),
    inference(resolution,[status(thm)],[c_4205,c_22])).

tff(c_4234,plain,
    ( r4_lattice3('#skF_9',k15_lattice3('#skF_9','#skF_11'),'#skF_10')
    | v2_struct_0('#skF_9')
    | ~ r4_lattice3('#skF_9',k15_lattice3('#skF_9','#skF_11'),a_2_5_lattice3('#skF_9','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3946,c_86,c_4220])).

tff(c_4235,plain,(
    ~ r4_lattice3('#skF_9',k15_lattice3('#skF_9','#skF_11'),a_2_5_lattice3('#skF_9','#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_3991,c_4234])).

tff(c_188,plain,(
    ! [A_97,B_99] :
      ( r4_lattice3(A_97,k15_lattice3(A_97,a_2_5_lattice3(A_97,B_99)),a_2_5_lattice3(A_97,B_99))
      | ~ m1_subset_1(k15_lattice3(A_97,B_99),u1_struct_0(A_97))
      | ~ v4_lattice3(A_97)
      | ~ v10_lattices(A_97)
      | ~ l3_lattices(A_97)
      | v2_struct_0(A_97)
      | ~ l3_lattices(A_97)
      | ~ v4_lattice3(A_97)
      | ~ v10_lattices(A_97)
      | v2_struct_0(A_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_184])).

tff(c_4349,plain,(
    ! [D_615,B_616] :
      ( r1_lattices('#skF_9','#skF_12'(D_615),B_616)
      | ~ r4_lattice3('#skF_9',B_616,a_2_5_lattice3('#skF_9','#skF_11'))
      | ~ m1_subset_1(B_616,u1_struct_0('#skF_9'))
      | ~ r2_hidden('#skF_12'(D_615),'#skF_10')
      | ~ m1_subset_1('#skF_12'(D_615),u1_struct_0('#skF_9'))
      | ~ r2_hidden(D_615,'#skF_10')
      | ~ m1_subset_1(D_615,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_762])).

tff(c_4352,plain,(
    ! [D_615] :
      ( r1_lattices('#skF_9','#skF_12'(D_615),k15_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')))
      | ~ m1_subset_1(k15_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),u1_struct_0('#skF_9'))
      | ~ r2_hidden('#skF_12'(D_615),'#skF_10')
      | ~ m1_subset_1('#skF_12'(D_615),u1_struct_0('#skF_9'))
      | ~ r2_hidden(D_615,'#skF_10')
      | ~ m1_subset_1(D_615,u1_struct_0('#skF_9'))
      | ~ m1_subset_1(k15_lattice3('#skF_9','#skF_11'),u1_struct_0('#skF_9'))
      | ~ l3_lattices('#skF_9')
      | ~ v4_lattice3('#skF_9')
      | ~ v10_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_188,c_4349])).

tff(c_4364,plain,(
    ! [D_615] :
      ( r1_lattices('#skF_9','#skF_12'(D_615),k15_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')))
      | ~ m1_subset_1(k15_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),u1_struct_0('#skF_9'))
      | ~ r2_hidden('#skF_12'(D_615),'#skF_10')
      | ~ m1_subset_1('#skF_12'(D_615),u1_struct_0('#skF_9'))
      | ~ r2_hidden(D_615,'#skF_10')
      | ~ m1_subset_1(D_615,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_3946,c_4352])).

tff(c_4365,plain,(
    ! [D_615] :
      ( r1_lattices('#skF_9','#skF_12'(D_615),k15_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')))
      | ~ m1_subset_1(k15_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),u1_struct_0('#skF_9'))
      | ~ r2_hidden('#skF_12'(D_615),'#skF_10')
      | ~ m1_subset_1('#skF_12'(D_615),u1_struct_0('#skF_9'))
      | ~ r2_hidden(D_615,'#skF_10')
      | ~ m1_subset_1(D_615,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_4364])).

tff(c_4865,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),u1_struct_0('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_4365])).

tff(c_4868,plain,
    ( ~ m1_subset_1(k15_lattice3('#skF_9','#skF_11'),u1_struct_0('#skF_9'))
    | ~ l3_lattices('#skF_9')
    | ~ v4_lattice3('#skF_9')
    | ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_4865])).

tff(c_4870,plain,(
    v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_3946,c_4868])).

tff(c_4872,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_4870])).

tff(c_4874,plain,(
    m1_subset_1(k15_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),u1_struct_0('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_4365])).

tff(c_48,plain,(
    ! [A_53,B_60] :
      ( r4_lattice3(A_53,k15_lattice3(A_53,B_60),B_60)
      | ~ m1_subset_1(k15_lattice3(A_53,B_60),u1_struct_0(A_53))
      | ~ v4_lattice3(A_53)
      | ~ v10_lattices(A_53)
      | ~ l3_lattices(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_4892,plain,
    ( r4_lattice3('#skF_9',k15_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),a_2_5_lattice3('#skF_9','#skF_11'))
    | ~ v4_lattice3('#skF_9')
    | ~ v10_lattices('#skF_9')
    | ~ l3_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_4874,c_48])).

tff(c_4920,plain,
    ( r4_lattice3('#skF_9',k15_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),a_2_5_lattice3('#skF_9','#skF_11'))
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_90,c_88,c_4892])).

tff(c_4921,plain,(
    r4_lattice3('#skF_9',k15_lattice3('#skF_9',a_2_5_lattice3('#skF_9','#skF_11')),a_2_5_lattice3('#skF_9','#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_4920])).

tff(c_4931,plain,
    ( r4_lattice3('#skF_9',k15_lattice3('#skF_9','#skF_11'),a_2_5_lattice3('#skF_9','#skF_11'))
    | ~ l3_lattices('#skF_9')
    | ~ v4_lattice3('#skF_9')
    | ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_4921])).

tff(c_4940,plain,
    ( r4_lattice3('#skF_9',k15_lattice3('#skF_9','#skF_11'),a_2_5_lattice3('#skF_9','#skF_11'))
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_4931])).

tff(c_4942,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_4235,c_4940])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:33:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.60/2.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.60/2.58  
% 7.60/2.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.60/2.59  %$ r4_lattice3 > r3_lattices > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k6_domain_1 > k16_lattice3 > k15_lattice3 > a_2_6_lattice3 > a_2_5_lattice3 > a_2_2_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_11 > #skF_6 > #skF_10 > #skF_5 > #skF_9 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_12 > #skF_4
% 7.60/2.59  
% 7.60/2.59  %Foreground sorts:
% 7.60/2.59  
% 7.60/2.59  
% 7.60/2.59  %Background operators:
% 7.60/2.59  
% 7.60/2.59  
% 7.60/2.59  %Foreground operators:
% 7.60/2.59  tff(l3_lattices, type, l3_lattices: $i > $o).
% 7.60/2.59  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.60/2.59  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.60/2.59  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 7.60/2.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.60/2.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.60/2.59  tff('#skF_11', type, '#skF_11': $i).
% 7.60/2.59  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 7.60/2.59  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 7.60/2.59  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 7.60/2.59  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 7.60/2.59  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 7.60/2.59  tff('#skF_10', type, '#skF_10': $i).
% 7.60/2.59  tff(v4_lattices, type, v4_lattices: $i > $o).
% 7.60/2.59  tff(v6_lattices, type, v6_lattices: $i > $o).
% 7.60/2.59  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 7.60/2.59  tff(v9_lattices, type, v9_lattices: $i > $o).
% 7.60/2.59  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 7.60/2.59  tff(a_2_5_lattice3, type, a_2_5_lattice3: ($i * $i) > $i).
% 7.60/2.59  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 7.60/2.59  tff(v5_lattices, type, v5_lattices: $i > $o).
% 7.60/2.59  tff(v10_lattices, type, v10_lattices: $i > $o).
% 7.60/2.59  tff('#skF_9', type, '#skF_9': $i).
% 7.60/2.59  tff(a_2_2_lattice3, type, a_2_2_lattice3: ($i * $i) > $i).
% 7.60/2.59  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 7.60/2.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.60/2.59  tff('#skF_3', type, '#skF_3': $i > $i).
% 7.60/2.59  tff(v8_lattices, type, v8_lattices: $i > $o).
% 7.60/2.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.60/2.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.60/2.59  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 7.60/2.59  tff('#skF_12', type, '#skF_12': $i > $i).
% 7.60/2.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.60/2.59  tff(a_2_6_lattice3, type, a_2_6_lattice3: ($i * $i) > $i).
% 7.60/2.59  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.60/2.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.60/2.59  tff(v7_lattices, type, v7_lattices: $i > $o).
% 7.60/2.59  
% 7.92/2.62  tff(f_261, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: ((![D]: (m1_subset_1(D, u1_struct_0(A)) => ~(r2_hidden(D, B) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ~(r3_lattices(A, D, E) & r2_hidden(E, C))))))) => r3_lattices(A, k15_lattice3(A, B), k15_lattice3(A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_lattice3)).
% 7.92/2.62  tff(f_185, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (k15_lattice3(A, B) = k16_lattice3(A, a_2_2_lattice3(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_lattice3)).
% 7.92/2.62  tff(f_204, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r2_hidden(B, C) => (r3_lattices(A, B, k15_lattice3(A, C)) & r3_lattices(A, k16_lattice3(A, C), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_lattice3)).
% 7.92/2.62  tff(f_234, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: ((k15_lattice3(A, B) = k15_lattice3(A, a_2_5_lattice3(A, B))) & (k16_lattice3(A, B) = k16_lattice3(A, a_2_6_lattice3(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_lattice3)).
% 7.92/2.62  tff(f_104, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v4_lattice3(A) <=> (![B]: (?[C]: ((m1_subset_1(C, u1_struct_0(A)) & r4_lattice3(A, C, B)) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_lattice3)).
% 7.92/2.62  tff(f_173, axiom, (![A, B, C]: ((((~v2_struct_0(B) & v10_lattices(B)) & v4_lattice3(B)) & l3_lattices(B)) => (r2_hidden(A, a_2_5_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r3_lattices(B, D, E)) & r2_hidden(E, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_5_lattice3)).
% 7.92/2.62  tff(f_84, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 7.92/2.62  tff(f_150, axiom, (![A, B, C]: ((((~v2_struct_0(B) & v10_lattices(B)) & v4_lattice3(B)) & l3_lattices(B)) => (r2_hidden(A, a_2_2_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & r4_lattice3(B, D, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_2_lattice3)).
% 7.92/2.62  tff(f_132, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k15_lattice3(A, B)) <=> (r4_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d21_lattice3)).
% 7.92/2.62  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 7.92/2.62  tff(f_66, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 7.92/2.62  tff(c_92, plain, (~v2_struct_0('#skF_9')), inference(cnfTransformation, [status(thm)], [f_261])).
% 7.92/2.62  tff(c_90, plain, (v10_lattices('#skF_9')), inference(cnfTransformation, [status(thm)], [f_261])).
% 7.92/2.62  tff(c_88, plain, (v4_lattice3('#skF_9')), inference(cnfTransformation, [status(thm)], [f_261])).
% 7.92/2.62  tff(c_86, plain, (l3_lattices('#skF_9')), inference(cnfTransformation, [status(thm)], [f_261])).
% 7.92/2.62  tff(c_70, plain, (![A_84, B_86]: (k16_lattice3(A_84, a_2_2_lattice3(A_84, B_86))=k15_lattice3(A_84, B_86) | ~l3_lattices(A_84) | ~v4_lattice3(A_84) | ~v10_lattices(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_185])).
% 7.92/2.62  tff(c_191, plain, (![A_171, C_172, B_173]: (r3_lattices(A_171, k16_lattice3(A_171, C_172), B_173) | ~r2_hidden(B_173, C_172) | ~m1_subset_1(B_173, u1_struct_0(A_171)) | ~l3_lattices(A_171) | ~v4_lattice3(A_171) | ~v10_lattices(A_171) | v2_struct_0(A_171))), inference(cnfTransformation, [status(thm)], [f_204])).
% 7.92/2.62  tff(c_866, plain, (![A_278, B_279, B_280]: (r3_lattices(A_278, k15_lattice3(A_278, B_279), B_280) | ~r2_hidden(B_280, a_2_2_lattice3(A_278, B_279)) | ~m1_subset_1(B_280, u1_struct_0(A_278)) | ~l3_lattices(A_278) | ~v4_lattice3(A_278) | ~v10_lattices(A_278) | v2_struct_0(A_278) | ~l3_lattices(A_278) | ~v4_lattice3(A_278) | ~v10_lattices(A_278) | v2_struct_0(A_278))), inference(superposition, [status(thm), theory('equality')], [c_70, c_191])).
% 7.92/2.62  tff(c_84, plain, (~r3_lattices('#skF_9', k15_lattice3('#skF_9', '#skF_10'), k15_lattice3('#skF_9', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_261])).
% 7.92/2.62  tff(c_874, plain, (~r2_hidden(k15_lattice3('#skF_9', '#skF_11'), a_2_2_lattice3('#skF_9', '#skF_10')) | ~m1_subset_1(k15_lattice3('#skF_9', '#skF_11'), u1_struct_0('#skF_9')) | ~l3_lattices('#skF_9') | ~v4_lattice3('#skF_9') | ~v10_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_866, c_84])).
% 7.92/2.62  tff(c_885, plain, (~r2_hidden(k15_lattice3('#skF_9', '#skF_11'), a_2_2_lattice3('#skF_9', '#skF_10')) | ~m1_subset_1(k15_lattice3('#skF_9', '#skF_11'), u1_struct_0('#skF_9')) | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_874])).
% 7.92/2.62  tff(c_886, plain, (~r2_hidden(k15_lattice3('#skF_9', '#skF_11'), a_2_2_lattice3('#skF_9', '#skF_10')) | ~m1_subset_1(k15_lattice3('#skF_9', '#skF_11'), u1_struct_0('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_92, c_885])).
% 7.92/2.62  tff(c_887, plain, (~m1_subset_1(k15_lattice3('#skF_9', '#skF_11'), u1_struct_0('#skF_9'))), inference(splitLeft, [status(thm)], [c_886])).
% 7.92/2.62  tff(c_80, plain, (![A_97, B_99]: (k15_lattice3(A_97, a_2_5_lattice3(A_97, B_99))=k15_lattice3(A_97, B_99) | ~l3_lattices(A_97) | ~v4_lattice3(A_97) | ~v10_lattices(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_234])).
% 7.92/2.62  tff(c_38, plain, (![A_27, B_42]: (m1_subset_1('#skF_2'(A_27, B_42), u1_struct_0(A_27)) | ~v4_lattice3(A_27) | ~l3_lattices(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.92/2.62  tff(c_36, plain, (![A_27, B_42]: (r4_lattice3(A_27, '#skF_2'(A_27, B_42), B_42) | ~v4_lattice3(A_27) | ~l3_lattices(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.92/2.62  tff(c_98, plain, (![D_111]: (m1_subset_1('#skF_12'(D_111), u1_struct_0('#skF_9')) | ~r2_hidden(D_111, '#skF_10') | ~m1_subset_1(D_111, u1_struct_0('#skF_9')))), inference(cnfTransformation, [status(thm)], [f_261])).
% 7.92/2.62  tff(c_96, plain, (![D_111]: (r3_lattices('#skF_9', D_111, '#skF_12'(D_111)) | ~r2_hidden(D_111, '#skF_10') | ~m1_subset_1(D_111, u1_struct_0('#skF_9')))), inference(cnfTransformation, [status(thm)], [f_261])).
% 7.92/2.62  tff(c_94, plain, (![D_111]: (r2_hidden('#skF_12'(D_111), '#skF_11') | ~r2_hidden(D_111, '#skF_10') | ~m1_subset_1(D_111, u1_struct_0('#skF_9')))), inference(cnfTransformation, [status(thm)], [f_261])).
% 7.92/2.62  tff(c_374, plain, (![D_219, B_220, C_221, E_222]: (r2_hidden(D_219, a_2_5_lattice3(B_220, C_221)) | ~r2_hidden(E_222, C_221) | ~r3_lattices(B_220, D_219, E_222) | ~m1_subset_1(E_222, u1_struct_0(B_220)) | ~m1_subset_1(D_219, u1_struct_0(B_220)) | ~l3_lattices(B_220) | ~v4_lattice3(B_220) | ~v10_lattices(B_220) | v2_struct_0(B_220))), inference(cnfTransformation, [status(thm)], [f_173])).
% 7.92/2.62  tff(c_419, plain, (![D_234, B_235, D_236]: (r2_hidden(D_234, a_2_5_lattice3(B_235, '#skF_11')) | ~r3_lattices(B_235, D_234, '#skF_12'(D_236)) | ~m1_subset_1('#skF_12'(D_236), u1_struct_0(B_235)) | ~m1_subset_1(D_234, u1_struct_0(B_235)) | ~l3_lattices(B_235) | ~v4_lattice3(B_235) | ~v10_lattices(B_235) | v2_struct_0(B_235) | ~r2_hidden(D_236, '#skF_10') | ~m1_subset_1(D_236, u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_94, c_374])).
% 7.92/2.62  tff(c_426, plain, (![D_111]: (r2_hidden(D_111, a_2_5_lattice3('#skF_9', '#skF_11')) | ~m1_subset_1('#skF_12'(D_111), u1_struct_0('#skF_9')) | ~l3_lattices('#skF_9') | ~v4_lattice3('#skF_9') | ~v10_lattices('#skF_9') | v2_struct_0('#skF_9') | ~r2_hidden(D_111, '#skF_10') | ~m1_subset_1(D_111, u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_96, c_419])).
% 7.92/2.62  tff(c_434, plain, (![D_111]: (r2_hidden(D_111, a_2_5_lattice3('#skF_9', '#skF_11')) | ~m1_subset_1('#skF_12'(D_111), u1_struct_0('#skF_9')) | v2_struct_0('#skF_9') | ~r2_hidden(D_111, '#skF_10') | ~m1_subset_1(D_111, u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_426])).
% 7.92/2.62  tff(c_436, plain, (![D_237]: (r2_hidden(D_237, a_2_5_lattice3('#skF_9', '#skF_11')) | ~m1_subset_1('#skF_12'(D_237), u1_struct_0('#skF_9')) | ~r2_hidden(D_237, '#skF_10') | ~m1_subset_1(D_237, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_92, c_434])).
% 7.92/2.62  tff(c_441, plain, (![D_238]: (r2_hidden(D_238, a_2_5_lattice3('#skF_9', '#skF_11')) | ~r2_hidden(D_238, '#skF_10') | ~m1_subset_1(D_238, u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_98, c_436])).
% 7.92/2.62  tff(c_20, plain, (![A_5, D_26, B_17, C_23]: (r1_lattices(A_5, D_26, B_17) | ~r2_hidden(D_26, C_23) | ~m1_subset_1(D_26, u1_struct_0(A_5)) | ~r4_lattice3(A_5, B_17, C_23) | ~m1_subset_1(B_17, u1_struct_0(A_5)) | ~l3_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.92/2.62  tff(c_736, plain, (![A_268, D_269, B_270]: (r1_lattices(A_268, D_269, B_270) | ~m1_subset_1(D_269, u1_struct_0(A_268)) | ~r4_lattice3(A_268, B_270, a_2_5_lattice3('#skF_9', '#skF_11')) | ~m1_subset_1(B_270, u1_struct_0(A_268)) | ~l3_lattices(A_268) | v2_struct_0(A_268) | ~r2_hidden(D_269, '#skF_10') | ~m1_subset_1(D_269, u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_441, c_20])).
% 7.92/2.62  tff(c_752, plain, (![D_111, B_270]: (r1_lattices('#skF_9', '#skF_12'(D_111), B_270) | ~r4_lattice3('#skF_9', B_270, a_2_5_lattice3('#skF_9', '#skF_11')) | ~m1_subset_1(B_270, u1_struct_0('#skF_9')) | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9') | ~r2_hidden('#skF_12'(D_111), '#skF_10') | ~m1_subset_1('#skF_12'(D_111), u1_struct_0('#skF_9')) | ~r2_hidden(D_111, '#skF_10') | ~m1_subset_1(D_111, u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_98, c_736])).
% 7.92/2.62  tff(c_762, plain, (![D_111, B_270]: (r1_lattices('#skF_9', '#skF_12'(D_111), B_270) | ~r4_lattice3('#skF_9', B_270, a_2_5_lattice3('#skF_9', '#skF_11')) | ~m1_subset_1(B_270, u1_struct_0('#skF_9')) | v2_struct_0('#skF_9') | ~r2_hidden('#skF_12'(D_111), '#skF_10') | ~m1_subset_1('#skF_12'(D_111), u1_struct_0('#skF_9')) | ~r2_hidden(D_111, '#skF_10') | ~m1_subset_1(D_111, u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_752])).
% 7.92/2.62  tff(c_889, plain, (![D_283, B_284]: (r1_lattices('#skF_9', '#skF_12'(D_283), B_284) | ~r4_lattice3('#skF_9', B_284, a_2_5_lattice3('#skF_9', '#skF_11')) | ~m1_subset_1(B_284, u1_struct_0('#skF_9')) | ~r2_hidden('#skF_12'(D_283), '#skF_10') | ~m1_subset_1('#skF_12'(D_283), u1_struct_0('#skF_9')) | ~r2_hidden(D_283, '#skF_10') | ~m1_subset_1(D_283, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_92, c_762])).
% 7.92/2.62  tff(c_898, plain, (![D_283]: (r1_lattices('#skF_9', '#skF_12'(D_283), '#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11'))) | ~m1_subset_1('#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), u1_struct_0('#skF_9')) | ~r2_hidden('#skF_12'(D_283), '#skF_10') | ~m1_subset_1('#skF_12'(D_283), u1_struct_0('#skF_9')) | ~r2_hidden(D_283, '#skF_10') | ~m1_subset_1(D_283, u1_struct_0('#skF_9')) | ~v4_lattice3('#skF_9') | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_36, c_889])).
% 7.92/2.62  tff(c_909, plain, (![D_283]: (r1_lattices('#skF_9', '#skF_12'(D_283), '#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11'))) | ~m1_subset_1('#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), u1_struct_0('#skF_9')) | ~r2_hidden('#skF_12'(D_283), '#skF_10') | ~m1_subset_1('#skF_12'(D_283), u1_struct_0('#skF_9')) | ~r2_hidden(D_283, '#skF_10') | ~m1_subset_1(D_283, u1_struct_0('#skF_9')) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_88, c_898])).
% 7.92/2.62  tff(c_910, plain, (![D_283]: (r1_lattices('#skF_9', '#skF_12'(D_283), '#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11'))) | ~m1_subset_1('#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), u1_struct_0('#skF_9')) | ~r2_hidden('#skF_12'(D_283), '#skF_10') | ~m1_subset_1('#skF_12'(D_283), u1_struct_0('#skF_9')) | ~r2_hidden(D_283, '#skF_10') | ~m1_subset_1(D_283, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_92, c_909])).
% 7.92/2.62  tff(c_1211, plain, (~m1_subset_1('#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), u1_struct_0('#skF_9'))), inference(splitLeft, [status(thm)], [c_910])).
% 7.92/2.62  tff(c_1214, plain, (~v4_lattice3('#skF_9') | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_38, c_1211])).
% 7.92/2.62  tff(c_1217, plain, (v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_88, c_1214])).
% 7.92/2.62  tff(c_1219, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_1217])).
% 7.92/2.62  tff(c_1221, plain, (m1_subset_1('#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), u1_struct_0('#skF_9'))), inference(splitRight, [status(thm)], [c_910])).
% 7.92/2.62  tff(c_201, plain, (![D_174, B_175, C_176]: (r2_hidden(D_174, a_2_2_lattice3(B_175, C_176)) | ~r4_lattice3(B_175, D_174, C_176) | ~m1_subset_1(D_174, u1_struct_0(B_175)) | ~l3_lattices(B_175) | ~v4_lattice3(B_175) | ~v10_lattices(B_175) | v2_struct_0(B_175))), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.92/2.62  tff(c_54, plain, (![A_65, B_66, C_67]: ('#skF_6'(A_65, B_66, C_67)=A_65 | ~r2_hidden(A_65, a_2_2_lattice3(B_66, C_67)) | ~l3_lattices(B_66) | ~v4_lattice3(B_66) | ~v10_lattices(B_66) | v2_struct_0(B_66))), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.92/2.62  tff(c_227, plain, (![D_184, B_185, C_186]: ('#skF_6'(D_184, B_185, C_186)=D_184 | ~r4_lattice3(B_185, D_184, C_186) | ~m1_subset_1(D_184, u1_struct_0(B_185)) | ~l3_lattices(B_185) | ~v4_lattice3(B_185) | ~v10_lattices(B_185) | v2_struct_0(B_185))), inference(resolution, [status(thm)], [c_201, c_54])).
% 7.92/2.62  tff(c_252, plain, (![A_196, B_197]: ('#skF_6'('#skF_2'(A_196, B_197), A_196, B_197)='#skF_2'(A_196, B_197) | ~m1_subset_1('#skF_2'(A_196, B_197), u1_struct_0(A_196)) | ~v10_lattices(A_196) | ~v4_lattice3(A_196) | ~l3_lattices(A_196) | v2_struct_0(A_196))), inference(resolution, [status(thm)], [c_36, c_227])).
% 7.92/2.62  tff(c_255, plain, (![A_27, B_42]: ('#skF_6'('#skF_2'(A_27, B_42), A_27, B_42)='#skF_2'(A_27, B_42) | ~v10_lattices(A_27) | ~v4_lattice3(A_27) | ~l3_lattices(A_27) | v2_struct_0(A_27))), inference(resolution, [status(thm)], [c_38, c_252])).
% 7.92/2.62  tff(c_50, plain, (![D_70, B_66, C_67]: (r2_hidden(D_70, a_2_2_lattice3(B_66, C_67)) | ~r4_lattice3(B_66, D_70, C_67) | ~m1_subset_1(D_70, u1_struct_0(B_66)) | ~l3_lattices(B_66) | ~v4_lattice3(B_66) | ~v10_lattices(B_66) | v2_struct_0(B_66))), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.92/2.62  tff(c_56, plain, (![A_65, B_66, C_67]: (m1_subset_1('#skF_6'(A_65, B_66, C_67), u1_struct_0(B_66)) | ~r2_hidden(A_65, a_2_2_lattice3(B_66, C_67)) | ~l3_lattices(B_66) | ~v4_lattice3(B_66) | ~v10_lattices(B_66) | v2_struct_0(B_66))), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.92/2.62  tff(c_52, plain, (![B_66, A_65, C_67]: (r4_lattice3(B_66, '#skF_6'(A_65, B_66, C_67), C_67) | ~r2_hidden(A_65, a_2_2_lattice3(B_66, C_67)) | ~l3_lattices(B_66) | ~v4_lattice3(B_66) | ~v10_lattices(B_66) | v2_struct_0(B_66))), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.92/2.62  tff(c_911, plain, (![A_285, B_286, C_287]: ('#skF_6'('#skF_6'(A_285, B_286, C_287), B_286, C_287)='#skF_6'(A_285, B_286, C_287) | ~m1_subset_1('#skF_6'(A_285, B_286, C_287), u1_struct_0(B_286)) | ~r2_hidden(A_285, a_2_2_lattice3(B_286, C_287)) | ~l3_lattices(B_286) | ~v4_lattice3(B_286) | ~v10_lattices(B_286) | v2_struct_0(B_286))), inference(resolution, [status(thm)], [c_52, c_227])).
% 7.92/2.62  tff(c_917, plain, (![A_288, B_289, C_290]: ('#skF_6'('#skF_6'(A_288, B_289, C_290), B_289, C_290)='#skF_6'(A_288, B_289, C_290) | ~r2_hidden(A_288, a_2_2_lattice3(B_289, C_290)) | ~l3_lattices(B_289) | ~v4_lattice3(B_289) | ~v10_lattices(B_289) | v2_struct_0(B_289))), inference(resolution, [status(thm)], [c_56, c_911])).
% 7.92/2.62  tff(c_926, plain, (![D_70, B_66, C_67]: ('#skF_6'('#skF_6'(D_70, B_66, C_67), B_66, C_67)='#skF_6'(D_70, B_66, C_67) | ~r4_lattice3(B_66, D_70, C_67) | ~m1_subset_1(D_70, u1_struct_0(B_66)) | ~l3_lattices(B_66) | ~v4_lattice3(B_66) | ~v10_lattices(B_66) | v2_struct_0(B_66))), inference(resolution, [status(thm)], [c_50, c_917])).
% 7.92/2.62  tff(c_1223, plain, (![C_67]: ('#skF_6'('#skF_6'('#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), '#skF_9', C_67), '#skF_9', C_67)='#skF_6'('#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), '#skF_9', C_67) | ~r4_lattice3('#skF_9', '#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), C_67) | ~l3_lattices('#skF_9') | ~v4_lattice3('#skF_9') | ~v10_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_1221, c_926])).
% 7.92/2.62  tff(c_1236, plain, (![C_67]: ('#skF_6'('#skF_6'('#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), '#skF_9', C_67), '#skF_9', C_67)='#skF_6'('#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), '#skF_9', C_67) | ~r4_lattice3('#skF_9', '#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), C_67) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_1223])).
% 7.92/2.62  tff(c_1268, plain, (![C_328]: ('#skF_6'('#skF_6'('#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), '#skF_9', C_328), '#skF_9', C_328)='#skF_6'('#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), '#skF_9', C_328) | ~r4_lattice3('#skF_9', '#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), C_328))), inference(negUnitSimplification, [status(thm)], [c_92, c_1236])).
% 7.92/2.62  tff(c_1286, plain, (![C_328]: (m1_subset_1('#skF_6'('#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), '#skF_9', C_328), u1_struct_0('#skF_9')) | ~r2_hidden('#skF_6'('#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), '#skF_9', C_328), a_2_2_lattice3('#skF_9', C_328)) | ~l3_lattices('#skF_9') | ~v4_lattice3('#skF_9') | ~v10_lattices('#skF_9') | v2_struct_0('#skF_9') | ~r4_lattice3('#skF_9', '#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), C_328))), inference(superposition, [status(thm), theory('equality')], [c_1268, c_56])).
% 7.92/2.62  tff(c_1307, plain, (![C_328]: (m1_subset_1('#skF_6'('#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), '#skF_9', C_328), u1_struct_0('#skF_9')) | ~r2_hidden('#skF_6'('#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), '#skF_9', C_328), a_2_2_lattice3('#skF_9', C_328)) | v2_struct_0('#skF_9') | ~r4_lattice3('#skF_9', '#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), C_328))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_1286])).
% 7.92/2.62  tff(c_1334, plain, (![C_330]: (m1_subset_1('#skF_6'('#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), '#skF_9', C_330), u1_struct_0('#skF_9')) | ~r2_hidden('#skF_6'('#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), '#skF_9', C_330), a_2_2_lattice3('#skF_9', C_330)) | ~r4_lattice3('#skF_9', '#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), C_330))), inference(negUnitSimplification, [status(thm)], [c_92, c_1307])).
% 7.92/2.62  tff(c_1338, plain, (m1_subset_1('#skF_6'('#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), '#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), u1_struct_0('#skF_9')) | ~r2_hidden('#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), a_2_2_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11'))) | ~r4_lattice3('#skF_9', '#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), a_2_5_lattice3('#skF_9', '#skF_11')) | ~v10_lattices('#skF_9') | ~v4_lattice3('#skF_9') | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_255, c_1334])).
% 7.92/2.62  tff(c_1344, plain, (m1_subset_1('#skF_6'('#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), '#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), u1_struct_0('#skF_9')) | ~r2_hidden('#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), a_2_2_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11'))) | ~r4_lattice3('#skF_9', '#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), a_2_5_lattice3('#skF_9', '#skF_11')) | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_88, c_90, c_1338])).
% 7.92/2.62  tff(c_1345, plain, (m1_subset_1('#skF_6'('#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), '#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), u1_struct_0('#skF_9')) | ~r2_hidden('#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), a_2_2_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11'))) | ~r4_lattice3('#skF_9', '#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), a_2_5_lattice3('#skF_9', '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_92, c_1344])).
% 7.92/2.62  tff(c_1560, plain, (~r4_lattice3('#skF_9', '#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), a_2_5_lattice3('#skF_9', '#skF_11'))), inference(splitLeft, [status(thm)], [c_1345])).
% 7.92/2.62  tff(c_1563, plain, (~v4_lattice3('#skF_9') | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_36, c_1560])).
% 7.92/2.62  tff(c_1566, plain, (v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_88, c_1563])).
% 7.92/2.62  tff(c_1568, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_1566])).
% 7.92/2.62  tff(c_1570, plain, (r4_lattice3('#skF_9', '#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), a_2_5_lattice3('#skF_9', '#skF_11'))), inference(splitRight, [status(thm)], [c_1345])).
% 7.92/2.62  tff(c_44, plain, (![A_53, B_60, C_61]: (m1_subset_1('#skF_5'(A_53, B_60, C_61), u1_struct_0(A_53)) | k15_lattice3(A_53, B_60)=C_61 | ~r4_lattice3(A_53, C_61, B_60) | ~m1_subset_1(C_61, u1_struct_0(A_53)) | ~v4_lattice3(A_53) | ~v10_lattices(A_53) | ~l3_lattices(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.92/2.62  tff(c_42, plain, (![A_53, B_60, C_61]: (r4_lattice3(A_53, '#skF_5'(A_53, B_60, C_61), B_60) | k15_lattice3(A_53, B_60)=C_61 | ~r4_lattice3(A_53, C_61, B_60) | ~m1_subset_1(C_61, u1_struct_0(A_53)) | ~v4_lattice3(A_53) | ~v10_lattices(A_53) | ~l3_lattices(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.92/2.62  tff(c_34, plain, (![A_27, B_42, D_47]: (r1_lattices(A_27, '#skF_2'(A_27, B_42), D_47) | ~r4_lattice3(A_27, D_47, B_42) | ~m1_subset_1(D_47, u1_struct_0(A_27)) | ~v4_lattice3(A_27) | ~l3_lattices(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.92/2.62  tff(c_364, plain, (![A_213, C_214, B_215]: (~r1_lattices(A_213, C_214, '#skF_5'(A_213, B_215, C_214)) | k15_lattice3(A_213, B_215)=C_214 | ~r4_lattice3(A_213, C_214, B_215) | ~m1_subset_1(C_214, u1_struct_0(A_213)) | ~v4_lattice3(A_213) | ~v10_lattices(A_213) | ~l3_lattices(A_213) | v2_struct_0(A_213))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.92/2.62  tff(c_3821, plain, (![A_579, B_580, B_581]: (k15_lattice3(A_579, B_580)='#skF_2'(A_579, B_581) | ~r4_lattice3(A_579, '#skF_2'(A_579, B_581), B_580) | ~m1_subset_1('#skF_2'(A_579, B_581), u1_struct_0(A_579)) | ~v10_lattices(A_579) | ~r4_lattice3(A_579, '#skF_5'(A_579, B_580, '#skF_2'(A_579, B_581)), B_581) | ~m1_subset_1('#skF_5'(A_579, B_580, '#skF_2'(A_579, B_581)), u1_struct_0(A_579)) | ~v4_lattice3(A_579) | ~l3_lattices(A_579) | v2_struct_0(A_579))), inference(resolution, [status(thm)], [c_34, c_364])).
% 7.92/2.62  tff(c_3827, plain, (![A_583, B_584]: (~m1_subset_1('#skF_5'(A_583, B_584, '#skF_2'(A_583, B_584)), u1_struct_0(A_583)) | k15_lattice3(A_583, B_584)='#skF_2'(A_583, B_584) | ~r4_lattice3(A_583, '#skF_2'(A_583, B_584), B_584) | ~m1_subset_1('#skF_2'(A_583, B_584), u1_struct_0(A_583)) | ~v4_lattice3(A_583) | ~v10_lattices(A_583) | ~l3_lattices(A_583) | v2_struct_0(A_583))), inference(resolution, [status(thm)], [c_42, c_3821])).
% 7.92/2.62  tff(c_3833, plain, (![A_585, B_586]: (k15_lattice3(A_585, B_586)='#skF_2'(A_585, B_586) | ~r4_lattice3(A_585, '#skF_2'(A_585, B_586), B_586) | ~m1_subset_1('#skF_2'(A_585, B_586), u1_struct_0(A_585)) | ~v4_lattice3(A_585) | ~v10_lattices(A_585) | ~l3_lattices(A_585) | v2_struct_0(A_585))), inference(resolution, [status(thm)], [c_44, c_3827])).
% 7.92/2.62  tff(c_3835, plain, (k15_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11'))='#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')) | ~m1_subset_1('#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), u1_struct_0('#skF_9')) | ~v4_lattice3('#skF_9') | ~v10_lattices('#skF_9') | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_1570, c_3833])).
% 7.92/2.62  tff(c_3840, plain, (k15_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11'))='#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')) | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_90, c_88, c_1221, c_3835])).
% 7.92/2.62  tff(c_3841, plain, (k15_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11'))='#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_92, c_3840])).
% 7.92/2.62  tff(c_184, plain, (![A_163, B_164]: (r4_lattice3(A_163, k15_lattice3(A_163, B_164), B_164) | ~m1_subset_1(k15_lattice3(A_163, B_164), u1_struct_0(A_163)) | ~v4_lattice3(A_163) | ~v10_lattices(A_163) | ~l3_lattices(A_163) | v2_struct_0(A_163))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.92/2.62  tff(c_1017, plain, (![A_299, B_300]: (r4_lattice3(A_299, k15_lattice3(A_299, a_2_5_lattice3(A_299, B_300)), a_2_5_lattice3(A_299, B_300)) | ~m1_subset_1(k15_lattice3(A_299, B_300), u1_struct_0(A_299)) | ~v4_lattice3(A_299) | ~v10_lattices(A_299) | ~l3_lattices(A_299) | v2_struct_0(A_299) | ~l3_lattices(A_299) | ~v4_lattice3(A_299) | ~v10_lattices(A_299) | v2_struct_0(A_299))), inference(superposition, [status(thm), theory('equality')], [c_80, c_184])).
% 7.92/2.62  tff(c_2786, plain, (![A_481, B_482]: (r4_lattice3(A_481, k15_lattice3(A_481, B_482), a_2_5_lattice3(A_481, B_482)) | ~m1_subset_1(k15_lattice3(A_481, B_482), u1_struct_0(A_481)) | ~v4_lattice3(A_481) | ~v10_lattices(A_481) | ~l3_lattices(A_481) | v2_struct_0(A_481) | ~l3_lattices(A_481) | ~v4_lattice3(A_481) | ~v10_lattices(A_481) | v2_struct_0(A_481) | ~l3_lattices(A_481) | ~v4_lattice3(A_481) | ~v10_lattices(A_481) | v2_struct_0(A_481))), inference(superposition, [status(thm), theory('equality')], [c_80, c_1017])).
% 7.92/2.62  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.92/2.62  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.92/2.62  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.92/2.62  tff(c_296, plain, (![A_203, B_204, C_205]: (r1_lattices(A_203, B_204, C_205) | ~r3_lattices(A_203, B_204, C_205) | ~m1_subset_1(C_205, u1_struct_0(A_203)) | ~m1_subset_1(B_204, u1_struct_0(A_203)) | ~l3_lattices(A_203) | ~v9_lattices(A_203) | ~v8_lattices(A_203) | ~v6_lattices(A_203) | v2_struct_0(A_203))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.92/2.62  tff(c_304, plain, (![D_111]: (r1_lattices('#skF_9', D_111, '#skF_12'(D_111)) | ~m1_subset_1('#skF_12'(D_111), u1_struct_0('#skF_9')) | ~l3_lattices('#skF_9') | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9') | ~v6_lattices('#skF_9') | v2_struct_0('#skF_9') | ~r2_hidden(D_111, '#skF_10') | ~m1_subset_1(D_111, u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_96, c_296])).
% 7.92/2.62  tff(c_310, plain, (![D_111]: (r1_lattices('#skF_9', D_111, '#skF_12'(D_111)) | ~m1_subset_1('#skF_12'(D_111), u1_struct_0('#skF_9')) | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9') | ~v6_lattices('#skF_9') | v2_struct_0('#skF_9') | ~r2_hidden(D_111, '#skF_10') | ~m1_subset_1(D_111, u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_304])).
% 7.92/2.62  tff(c_311, plain, (![D_111]: (r1_lattices('#skF_9', D_111, '#skF_12'(D_111)) | ~m1_subset_1('#skF_12'(D_111), u1_struct_0('#skF_9')) | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9') | ~v6_lattices('#skF_9') | ~r2_hidden(D_111, '#skF_10') | ~m1_subset_1(D_111, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_92, c_310])).
% 7.92/2.62  tff(c_312, plain, (~v6_lattices('#skF_9')), inference(splitLeft, [status(thm)], [c_311])).
% 7.92/2.62  tff(c_316, plain, (~v10_lattices('#skF_9') | v2_struct_0('#skF_9') | ~l3_lattices('#skF_9')), inference(resolution, [status(thm)], [c_8, c_312])).
% 7.92/2.62  tff(c_319, plain, (v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_90, c_316])).
% 7.92/2.62  tff(c_321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_319])).
% 7.92/2.62  tff(c_322, plain, (![D_111]: (~v8_lattices('#skF_9') | ~v9_lattices('#skF_9') | r1_lattices('#skF_9', D_111, '#skF_12'(D_111)) | ~m1_subset_1('#skF_12'(D_111), u1_struct_0('#skF_9')) | ~r2_hidden(D_111, '#skF_10') | ~m1_subset_1(D_111, u1_struct_0('#skF_9')))), inference(splitRight, [status(thm)], [c_311])).
% 7.92/2.62  tff(c_324, plain, (~v9_lattices('#skF_9')), inference(splitLeft, [status(thm)], [c_322])).
% 7.92/2.62  tff(c_327, plain, (~v10_lattices('#skF_9') | v2_struct_0('#skF_9') | ~l3_lattices('#skF_9')), inference(resolution, [status(thm)], [c_2, c_324])).
% 7.92/2.62  tff(c_330, plain, (v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_90, c_327])).
% 7.92/2.62  tff(c_332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_330])).
% 7.92/2.62  tff(c_333, plain, (![D_111]: (~v8_lattices('#skF_9') | r1_lattices('#skF_9', D_111, '#skF_12'(D_111)) | ~m1_subset_1('#skF_12'(D_111), u1_struct_0('#skF_9')) | ~r2_hidden(D_111, '#skF_10') | ~m1_subset_1(D_111, u1_struct_0('#skF_9')))), inference(splitRight, [status(thm)], [c_322])).
% 7.92/2.62  tff(c_339, plain, (~v8_lattices('#skF_9')), inference(splitLeft, [status(thm)], [c_333])).
% 7.92/2.62  tff(c_342, plain, (~v10_lattices('#skF_9') | v2_struct_0('#skF_9') | ~l3_lattices('#skF_9')), inference(resolution, [status(thm)], [c_4, c_339])).
% 7.92/2.62  tff(c_345, plain, (v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_90, c_342])).
% 7.92/2.62  tff(c_347, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_345])).
% 7.92/2.62  tff(c_359, plain, (![D_211]: (r1_lattices('#skF_9', D_211, '#skF_12'(D_211)) | ~m1_subset_1('#skF_12'(D_211), u1_struct_0('#skF_9')) | ~r2_hidden(D_211, '#skF_10') | ~m1_subset_1(D_211, u1_struct_0('#skF_9')))), inference(splitRight, [status(thm)], [c_333])).
% 7.92/2.62  tff(c_362, plain, (![D_111]: (r1_lattices('#skF_9', D_111, '#skF_12'(D_111)) | ~r2_hidden(D_111, '#skF_10') | ~m1_subset_1(D_111, u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_98, c_359])).
% 7.92/2.62  tff(c_323, plain, (v6_lattices('#skF_9')), inference(splitRight, [status(thm)], [c_311])).
% 7.92/2.62  tff(c_349, plain, (v8_lattices('#skF_9')), inference(splitRight, [status(thm)], [c_333])).
% 7.92/2.62  tff(c_334, plain, (v9_lattices('#skF_9')), inference(splitRight, [status(thm)], [c_322])).
% 7.92/2.62  tff(c_256, plain, (![A_198, B_199, C_200]: (r3_lattices(A_198, B_199, C_200) | ~r1_lattices(A_198, B_199, C_200) | ~m1_subset_1(C_200, u1_struct_0(A_198)) | ~m1_subset_1(B_199, u1_struct_0(A_198)) | ~l3_lattices(A_198) | ~v9_lattices(A_198) | ~v8_lattices(A_198) | ~v6_lattices(A_198) | v2_struct_0(A_198))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.92/2.62  tff(c_270, plain, (![B_199, D_111]: (r3_lattices('#skF_9', B_199, '#skF_12'(D_111)) | ~r1_lattices('#skF_9', B_199, '#skF_12'(D_111)) | ~m1_subset_1(B_199, u1_struct_0('#skF_9')) | ~l3_lattices('#skF_9') | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9') | ~v6_lattices('#skF_9') | v2_struct_0('#skF_9') | ~r2_hidden(D_111, '#skF_10') | ~m1_subset_1(D_111, u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_98, c_256])).
% 7.92/2.62  tff(c_279, plain, (![B_199, D_111]: (r3_lattices('#skF_9', B_199, '#skF_12'(D_111)) | ~r1_lattices('#skF_9', B_199, '#skF_12'(D_111)) | ~m1_subset_1(B_199, u1_struct_0('#skF_9')) | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9') | ~v6_lattices('#skF_9') | v2_struct_0('#skF_9') | ~r2_hidden(D_111, '#skF_10') | ~m1_subset_1(D_111, u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_270])).
% 7.92/2.62  tff(c_280, plain, (![B_199, D_111]: (r3_lattices('#skF_9', B_199, '#skF_12'(D_111)) | ~r1_lattices('#skF_9', B_199, '#skF_12'(D_111)) | ~m1_subset_1(B_199, u1_struct_0('#skF_9')) | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9') | ~v6_lattices('#skF_9') | ~r2_hidden(D_111, '#skF_10') | ~m1_subset_1(D_111, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_92, c_279])).
% 7.92/2.62  tff(c_351, plain, (![B_199, D_111]: (r3_lattices('#skF_9', B_199, '#skF_12'(D_111)) | ~r1_lattices('#skF_9', B_199, '#skF_12'(D_111)) | ~m1_subset_1(B_199, u1_struct_0('#skF_9')) | ~r2_hidden(D_111, '#skF_10') | ~m1_subset_1(D_111, u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_323, c_349, c_334, c_280])).
% 7.92/2.62  tff(c_58, plain, (![D_81, B_72, C_73, E_83]: (r2_hidden(D_81, a_2_5_lattice3(B_72, C_73)) | ~r2_hidden(E_83, C_73) | ~r3_lattices(B_72, D_81, E_83) | ~m1_subset_1(E_83, u1_struct_0(B_72)) | ~m1_subset_1(D_81, u1_struct_0(B_72)) | ~l3_lattices(B_72) | ~v4_lattice3(B_72) | ~v10_lattices(B_72) | v2_struct_0(B_72))), inference(cnfTransformation, [status(thm)], [f_173])).
% 7.92/2.62  tff(c_1428, plain, (![D_345, B_346, D_347]: (r2_hidden(D_345, a_2_5_lattice3(B_346, a_2_5_lattice3('#skF_9', '#skF_11'))) | ~r3_lattices(B_346, D_345, D_347) | ~m1_subset_1(D_347, u1_struct_0(B_346)) | ~m1_subset_1(D_345, u1_struct_0(B_346)) | ~l3_lattices(B_346) | ~v4_lattice3(B_346) | ~v10_lattices(B_346) | v2_struct_0(B_346) | ~r2_hidden(D_347, '#skF_10') | ~m1_subset_1(D_347, u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_441, c_58])).
% 7.92/2.62  tff(c_1444, plain, (![B_199, D_111]: (r2_hidden(B_199, a_2_5_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11'))) | ~l3_lattices('#skF_9') | ~v4_lattice3('#skF_9') | ~v10_lattices('#skF_9') | v2_struct_0('#skF_9') | ~r2_hidden('#skF_12'(D_111), '#skF_10') | ~m1_subset_1('#skF_12'(D_111), u1_struct_0('#skF_9')) | ~r1_lattices('#skF_9', B_199, '#skF_12'(D_111)) | ~m1_subset_1(B_199, u1_struct_0('#skF_9')) | ~r2_hidden(D_111, '#skF_10') | ~m1_subset_1(D_111, u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_351, c_1428])).
% 7.92/2.62  tff(c_1468, plain, (![B_199, D_111]: (r2_hidden(B_199, a_2_5_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11'))) | v2_struct_0('#skF_9') | ~r2_hidden('#skF_12'(D_111), '#skF_10') | ~m1_subset_1('#skF_12'(D_111), u1_struct_0('#skF_9')) | ~r1_lattices('#skF_9', B_199, '#skF_12'(D_111)) | ~m1_subset_1(B_199, u1_struct_0('#skF_9')) | ~r2_hidden(D_111, '#skF_10') | ~m1_subset_1(D_111, u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_1444])).
% 7.92/2.62  tff(c_1497, plain, (![B_351, D_352]: (r2_hidden(B_351, a_2_5_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11'))) | ~r2_hidden('#skF_12'(D_352), '#skF_10') | ~m1_subset_1('#skF_12'(D_352), u1_struct_0('#skF_9')) | ~r1_lattices('#skF_9', B_351, '#skF_12'(D_352)) | ~m1_subset_1(B_351, u1_struct_0('#skF_9')) | ~r2_hidden(D_352, '#skF_10') | ~m1_subset_1(D_352, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_92, c_1468])).
% 7.92/2.62  tff(c_1501, plain, (![B_353, D_354]: (r2_hidden(B_353, a_2_5_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11'))) | ~r2_hidden('#skF_12'(D_354), '#skF_10') | ~r1_lattices('#skF_9', B_353, '#skF_12'(D_354)) | ~m1_subset_1(B_353, u1_struct_0('#skF_9')) | ~r2_hidden(D_354, '#skF_10') | ~m1_subset_1(D_354, u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_98, c_1497])).
% 7.92/2.62  tff(c_1516, plain, (![D_355]: (r2_hidden(D_355, a_2_5_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11'))) | ~r2_hidden('#skF_12'(D_355), '#skF_10') | ~r2_hidden(D_355, '#skF_10') | ~m1_subset_1(D_355, u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_362, c_1501])).
% 7.92/2.62  tff(c_1735, plain, (![A_382, D_383, B_384]: (r1_lattices(A_382, D_383, B_384) | ~m1_subset_1(D_383, u1_struct_0(A_382)) | ~r4_lattice3(A_382, B_384, a_2_5_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11'))) | ~m1_subset_1(B_384, u1_struct_0(A_382)) | ~l3_lattices(A_382) | v2_struct_0(A_382) | ~r2_hidden('#skF_12'(D_383), '#skF_10') | ~r2_hidden(D_383, '#skF_10') | ~m1_subset_1(D_383, u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_1516, c_20])).
% 7.92/2.62  tff(c_1755, plain, (![D_111, B_384]: (r1_lattices('#skF_9', '#skF_12'(D_111), B_384) | ~r4_lattice3('#skF_9', B_384, a_2_5_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11'))) | ~m1_subset_1(B_384, u1_struct_0('#skF_9')) | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9') | ~r2_hidden('#skF_12'('#skF_12'(D_111)), '#skF_10') | ~r2_hidden('#skF_12'(D_111), '#skF_10') | ~m1_subset_1('#skF_12'(D_111), u1_struct_0('#skF_9')) | ~r2_hidden(D_111, '#skF_10') | ~m1_subset_1(D_111, u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_98, c_1735])).
% 7.92/2.62  tff(c_1773, plain, (![D_111, B_384]: (r1_lattices('#skF_9', '#skF_12'(D_111), B_384) | ~r4_lattice3('#skF_9', B_384, a_2_5_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11'))) | ~m1_subset_1(B_384, u1_struct_0('#skF_9')) | v2_struct_0('#skF_9') | ~r2_hidden('#skF_12'('#skF_12'(D_111)), '#skF_10') | ~r2_hidden('#skF_12'(D_111), '#skF_10') | ~m1_subset_1('#skF_12'(D_111), u1_struct_0('#skF_9')) | ~r2_hidden(D_111, '#skF_10') | ~m1_subset_1(D_111, u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1755])).
% 7.92/2.62  tff(c_1774, plain, (![D_111, B_384]: (r1_lattices('#skF_9', '#skF_12'(D_111), B_384) | ~r4_lattice3('#skF_9', B_384, a_2_5_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11'))) | ~m1_subset_1(B_384, u1_struct_0('#skF_9')) | ~r2_hidden('#skF_12'('#skF_12'(D_111)), '#skF_10') | ~r2_hidden('#skF_12'(D_111), '#skF_10') | ~m1_subset_1('#skF_12'(D_111), u1_struct_0('#skF_9')) | ~r2_hidden(D_111, '#skF_10') | ~m1_subset_1(D_111, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_92, c_1773])).
% 7.92/2.62  tff(c_2789, plain, (![D_111]: (r1_lattices('#skF_9', '#skF_12'(D_111), k15_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11'))) | ~r2_hidden('#skF_12'('#skF_12'(D_111)), '#skF_10') | ~r2_hidden('#skF_12'(D_111), '#skF_10') | ~m1_subset_1('#skF_12'(D_111), u1_struct_0('#skF_9')) | ~r2_hidden(D_111, '#skF_10') | ~m1_subset_1(D_111, u1_struct_0('#skF_9')) | ~m1_subset_1(k15_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), u1_struct_0('#skF_9')) | ~l3_lattices('#skF_9') | ~v4_lattice3('#skF_9') | ~v10_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_2786, c_1774])).
% 7.92/2.62  tff(c_2806, plain, (![D_111]: (r1_lattices('#skF_9', '#skF_12'(D_111), k15_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11'))) | ~r2_hidden('#skF_12'('#skF_12'(D_111)), '#skF_10') | ~r2_hidden('#skF_12'(D_111), '#skF_10') | ~m1_subset_1('#skF_12'(D_111), u1_struct_0('#skF_9')) | ~r2_hidden(D_111, '#skF_10') | ~m1_subset_1(D_111, u1_struct_0('#skF_9')) | ~m1_subset_1(k15_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), u1_struct_0('#skF_9')) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_2789])).
% 7.92/2.62  tff(c_2807, plain, (![D_111]: (r1_lattices('#skF_9', '#skF_12'(D_111), k15_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11'))) | ~r2_hidden('#skF_12'('#skF_12'(D_111)), '#skF_10') | ~r2_hidden('#skF_12'(D_111), '#skF_10') | ~m1_subset_1('#skF_12'(D_111), u1_struct_0('#skF_9')) | ~r2_hidden(D_111, '#skF_10') | ~m1_subset_1(D_111, u1_struct_0('#skF_9')) | ~m1_subset_1(k15_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_92, c_2806])).
% 7.92/2.62  tff(c_3302, plain, (~m1_subset_1(k15_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), u1_struct_0('#skF_9'))), inference(splitLeft, [status(thm)], [c_2807])).
% 7.92/2.62  tff(c_3843, plain, (~m1_subset_1('#skF_2'('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), u1_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_3841, c_3302])).
% 7.92/2.62  tff(c_3846, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1221, c_3843])).
% 7.92/2.62  tff(c_3848, plain, (m1_subset_1(k15_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), u1_struct_0('#skF_9'))), inference(splitRight, [status(thm)], [c_2807])).
% 7.92/2.62  tff(c_3885, plain, (m1_subset_1(k15_lattice3('#skF_9', '#skF_11'), u1_struct_0('#skF_9')) | ~l3_lattices('#skF_9') | ~v4_lattice3('#skF_9') | ~v10_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_80, c_3848])).
% 7.92/2.62  tff(c_3942, plain, (m1_subset_1(k15_lattice3('#skF_9', '#skF_11'), u1_struct_0('#skF_9')) | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_3885])).
% 7.92/2.62  tff(c_3944, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_887, c_3942])).
% 7.92/2.62  tff(c_3946, plain, (m1_subset_1(k15_lattice3('#skF_9', '#skF_11'), u1_struct_0('#skF_9'))), inference(splitRight, [status(thm)], [c_886])).
% 7.92/2.62  tff(c_3945, plain, (~r2_hidden(k15_lattice3('#skF_9', '#skF_11'), a_2_2_lattice3('#skF_9', '#skF_10'))), inference(splitRight, [status(thm)], [c_886])).
% 7.92/2.62  tff(c_3987, plain, (~r4_lattice3('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10') | ~m1_subset_1(k15_lattice3('#skF_9', '#skF_11'), u1_struct_0('#skF_9')) | ~l3_lattices('#skF_9') | ~v4_lattice3('#skF_9') | ~v10_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_50, c_3945])).
% 7.92/2.62  tff(c_3990, plain, (~r4_lattice3('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_3946, c_3987])).
% 7.92/2.62  tff(c_3991, plain, (~r4_lattice3('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_92, c_3990])).
% 7.92/2.62  tff(c_24, plain, (![A_5, B_17, C_23]: (r2_hidden('#skF_1'(A_5, B_17, C_23), C_23) | r4_lattice3(A_5, B_17, C_23) | ~m1_subset_1(B_17, u1_struct_0(A_5)) | ~l3_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.92/2.62  tff(c_26, plain, (![A_5, B_17, C_23]: (m1_subset_1('#skF_1'(A_5, B_17, C_23), u1_struct_0(A_5)) | r4_lattice3(A_5, B_17, C_23) | ~m1_subset_1(B_17, u1_struct_0(A_5)) | ~l3_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.92/2.62  tff(c_440, plain, (![D_111]: (r2_hidden(D_111, a_2_5_lattice3('#skF_9', '#skF_11')) | ~r2_hidden(D_111, '#skF_10') | ~m1_subset_1(D_111, u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_98, c_436])).
% 7.92/2.62  tff(c_66, plain, (![A_71, B_72, C_73]: ('#skF_7'(A_71, B_72, C_73)=A_71 | ~r2_hidden(A_71, a_2_5_lattice3(B_72, C_73)) | ~l3_lattices(B_72) | ~v4_lattice3(B_72) | ~v10_lattices(B_72) | v2_struct_0(B_72))), inference(cnfTransformation, [status(thm)], [f_173])).
% 7.92/2.62  tff(c_448, plain, (![D_238]: ('#skF_7'(D_238, '#skF_9', '#skF_11')=D_238 | ~l3_lattices('#skF_9') | ~v4_lattice3('#skF_9') | ~v10_lattices('#skF_9') | v2_struct_0('#skF_9') | ~r2_hidden(D_238, '#skF_10') | ~m1_subset_1(D_238, u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_441, c_66])).
% 7.92/2.62  tff(c_453, plain, (![D_238]: ('#skF_7'(D_238, '#skF_9', '#skF_11')=D_238 | v2_struct_0('#skF_9') | ~r2_hidden(D_238, '#skF_10') | ~m1_subset_1(D_238, u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_448])).
% 7.92/2.62  tff(c_455, plain, (![D_239]: ('#skF_7'(D_239, '#skF_9', '#skF_11')=D_239 | ~r2_hidden(D_239, '#skF_10') | ~m1_subset_1(D_239, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_92, c_453])).
% 7.92/2.62  tff(c_479, plain, (![B_17, C_23]: ('#skF_7'('#skF_1'('#skF_9', B_17, C_23), '#skF_9', '#skF_11')='#skF_1'('#skF_9', B_17, C_23) | ~r2_hidden('#skF_1'('#skF_9', B_17, C_23), '#skF_10') | r4_lattice3('#skF_9', B_17, C_23) | ~m1_subset_1(B_17, u1_struct_0('#skF_9')) | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_26, c_455])).
% 7.92/2.62  tff(c_509, plain, (![B_17, C_23]: ('#skF_7'('#skF_1'('#skF_9', B_17, C_23), '#skF_9', '#skF_11')='#skF_1'('#skF_9', B_17, C_23) | ~r2_hidden('#skF_1'('#skF_9', B_17, C_23), '#skF_10') | r4_lattice3('#skF_9', B_17, C_23) | ~m1_subset_1(B_17, u1_struct_0('#skF_9')) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_479])).
% 7.92/2.62  tff(c_564, plain, (![B_252, C_253]: ('#skF_7'('#skF_1'('#skF_9', B_252, C_253), '#skF_9', '#skF_11')='#skF_1'('#skF_9', B_252, C_253) | ~r2_hidden('#skF_1'('#skF_9', B_252, C_253), '#skF_10') | r4_lattice3('#skF_9', B_252, C_253) | ~m1_subset_1(B_252, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_92, c_509])).
% 7.92/2.62  tff(c_568, plain, (![B_17]: ('#skF_7'('#skF_1'('#skF_9', B_17, '#skF_10'), '#skF_9', '#skF_11')='#skF_1'('#skF_9', B_17, '#skF_10') | r4_lattice3('#skF_9', B_17, '#skF_10') | ~m1_subset_1(B_17, u1_struct_0('#skF_9')) | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_24, c_564])).
% 7.92/2.62  tff(c_571, plain, (![B_17]: ('#skF_7'('#skF_1'('#skF_9', B_17, '#skF_10'), '#skF_9', '#skF_11')='#skF_1'('#skF_9', B_17, '#skF_10') | r4_lattice3('#skF_9', B_17, '#skF_10') | ~m1_subset_1(B_17, u1_struct_0('#skF_9')) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_568])).
% 7.92/2.62  tff(c_572, plain, (![B_17]: ('#skF_7'('#skF_1'('#skF_9', B_17, '#skF_10'), '#skF_9', '#skF_11')='#skF_1'('#skF_9', B_17, '#skF_10') | r4_lattice3('#skF_9', B_17, '#skF_10') | ~m1_subset_1(B_17, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_92, c_571])).
% 7.92/2.62  tff(c_3965, plain, ('#skF_7'('#skF_1'('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10'), '#skF_9', '#skF_11')='#skF_1'('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10') | r4_lattice3('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10')), inference(resolution, [status(thm)], [c_3946, c_572])).
% 7.92/2.62  tff(c_4059, plain, ('#skF_7'('#skF_1'('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10'), '#skF_9', '#skF_11')='#skF_1'('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_3991, c_3965])).
% 7.92/2.62  tff(c_68, plain, (![A_71, B_72, C_73]: (m1_subset_1('#skF_7'(A_71, B_72, C_73), u1_struct_0(B_72)) | ~r2_hidden(A_71, a_2_5_lattice3(B_72, C_73)) | ~l3_lattices(B_72) | ~v4_lattice3(B_72) | ~v10_lattices(B_72) | v2_struct_0(B_72))), inference(cnfTransformation, [status(thm)], [f_173])).
% 7.92/2.62  tff(c_4072, plain, (m1_subset_1('#skF_1'('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10'), u1_struct_0('#skF_9')) | ~r2_hidden('#skF_1'('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10'), a_2_5_lattice3('#skF_9', '#skF_11')) | ~l3_lattices('#skF_9') | ~v4_lattice3('#skF_9') | ~v10_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_4059, c_68])).
% 7.92/2.62  tff(c_4081, plain, (m1_subset_1('#skF_1'('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10'), u1_struct_0('#skF_9')) | ~r2_hidden('#skF_1'('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10'), a_2_5_lattice3('#skF_9', '#skF_11')) | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_4072])).
% 7.92/2.62  tff(c_4082, plain, (m1_subset_1('#skF_1'('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10'), u1_struct_0('#skF_9')) | ~r2_hidden('#skF_1'('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10'), a_2_5_lattice3('#skF_9', '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_92, c_4081])).
% 7.92/2.62  tff(c_4084, plain, (~r2_hidden('#skF_1'('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10'), a_2_5_lattice3('#skF_9', '#skF_11'))), inference(splitLeft, [status(thm)], [c_4082])).
% 7.92/2.62  tff(c_4095, plain, (~r2_hidden('#skF_1'('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10'), '#skF_10') | ~m1_subset_1('#skF_1'('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10'), u1_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_440, c_4084])).
% 7.92/2.62  tff(c_4096, plain, (~m1_subset_1('#skF_1'('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10'), u1_struct_0('#skF_9'))), inference(splitLeft, [status(thm)], [c_4095])).
% 7.92/2.62  tff(c_4099, plain, (r4_lattice3('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10') | ~m1_subset_1(k15_lattice3('#skF_9', '#skF_11'), u1_struct_0('#skF_9')) | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_26, c_4096])).
% 7.92/2.62  tff(c_4102, plain, (r4_lattice3('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_3946, c_4099])).
% 7.92/2.62  tff(c_4104, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_3991, c_4102])).
% 7.92/2.62  tff(c_4105, plain, (~r2_hidden('#skF_1'('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10'), '#skF_10')), inference(splitRight, [status(thm)], [c_4095])).
% 7.92/2.62  tff(c_4109, plain, (r4_lattice3('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10') | ~m1_subset_1(k15_lattice3('#skF_9', '#skF_11'), u1_struct_0('#skF_9')) | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_24, c_4105])).
% 7.92/2.62  tff(c_4112, plain, (r4_lattice3('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_3946, c_4109])).
% 7.92/2.62  tff(c_4114, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_3991, c_4112])).
% 7.92/2.62  tff(c_4115, plain, (m1_subset_1('#skF_1'('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10'), u1_struct_0('#skF_9'))), inference(splitRight, [status(thm)], [c_4082])).
% 7.92/2.62  tff(c_450, plain, (![A_5, D_238, B_17]: (r1_lattices(A_5, D_238, B_17) | ~m1_subset_1(D_238, u1_struct_0(A_5)) | ~r4_lattice3(A_5, B_17, a_2_5_lattice3('#skF_9', '#skF_11')) | ~m1_subset_1(B_17, u1_struct_0(A_5)) | ~l3_lattices(A_5) | v2_struct_0(A_5) | ~r2_hidden(D_238, '#skF_10') | ~m1_subset_1(D_238, u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_441, c_20])).
% 7.92/2.62  tff(c_4118, plain, (![B_17]: (r1_lattices('#skF_9', '#skF_1'('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10'), B_17) | ~r4_lattice3('#skF_9', B_17, a_2_5_lattice3('#skF_9', '#skF_11')) | ~m1_subset_1(B_17, u1_struct_0('#skF_9')) | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9') | ~r2_hidden('#skF_1'('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10'), '#skF_10') | ~m1_subset_1('#skF_1'('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10'), u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_4115, c_450])).
% 7.92/2.62  tff(c_4129, plain, (![B_17]: (r1_lattices('#skF_9', '#skF_1'('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10'), B_17) | ~r4_lattice3('#skF_9', B_17, a_2_5_lattice3('#skF_9', '#skF_11')) | ~m1_subset_1(B_17, u1_struct_0('#skF_9')) | v2_struct_0('#skF_9') | ~r2_hidden('#skF_1'('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10'), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_4115, c_86, c_4118])).
% 7.92/2.62  tff(c_4130, plain, (![B_17]: (r1_lattices('#skF_9', '#skF_1'('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10'), B_17) | ~r4_lattice3('#skF_9', B_17, a_2_5_lattice3('#skF_9', '#skF_11')) | ~m1_subset_1(B_17, u1_struct_0('#skF_9')) | ~r2_hidden('#skF_1'('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10'), '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_92, c_4129])).
% 7.92/2.62  tff(c_4181, plain, (~r2_hidden('#skF_1'('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10'), '#skF_10')), inference(splitLeft, [status(thm)], [c_4130])).
% 7.92/2.62  tff(c_4184, plain, (r4_lattice3('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10') | ~m1_subset_1(k15_lattice3('#skF_9', '#skF_11'), u1_struct_0('#skF_9')) | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_24, c_4181])).
% 7.92/2.62  tff(c_4187, plain, (r4_lattice3('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_3946, c_4184])).
% 7.92/2.62  tff(c_4189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_3991, c_4187])).
% 7.92/2.62  tff(c_4205, plain, (![B_600]: (r1_lattices('#skF_9', '#skF_1'('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10'), B_600) | ~r4_lattice3('#skF_9', B_600, a_2_5_lattice3('#skF_9', '#skF_11')) | ~m1_subset_1(B_600, u1_struct_0('#skF_9')))), inference(splitRight, [status(thm)], [c_4130])).
% 7.92/2.62  tff(c_22, plain, (![A_5, B_17, C_23]: (~r1_lattices(A_5, '#skF_1'(A_5, B_17, C_23), B_17) | r4_lattice3(A_5, B_17, C_23) | ~m1_subset_1(B_17, u1_struct_0(A_5)) | ~l3_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.92/2.62  tff(c_4220, plain, (r4_lattice3('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10') | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9') | ~r4_lattice3('#skF_9', k15_lattice3('#skF_9', '#skF_11'), a_2_5_lattice3('#skF_9', '#skF_11')) | ~m1_subset_1(k15_lattice3('#skF_9', '#skF_11'), u1_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_4205, c_22])).
% 7.92/2.62  tff(c_4234, plain, (r4_lattice3('#skF_9', k15_lattice3('#skF_9', '#skF_11'), '#skF_10') | v2_struct_0('#skF_9') | ~r4_lattice3('#skF_9', k15_lattice3('#skF_9', '#skF_11'), a_2_5_lattice3('#skF_9', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_3946, c_86, c_4220])).
% 7.92/2.62  tff(c_4235, plain, (~r4_lattice3('#skF_9', k15_lattice3('#skF_9', '#skF_11'), a_2_5_lattice3('#skF_9', '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_92, c_3991, c_4234])).
% 7.92/2.62  tff(c_188, plain, (![A_97, B_99]: (r4_lattice3(A_97, k15_lattice3(A_97, a_2_5_lattice3(A_97, B_99)), a_2_5_lattice3(A_97, B_99)) | ~m1_subset_1(k15_lattice3(A_97, B_99), u1_struct_0(A_97)) | ~v4_lattice3(A_97) | ~v10_lattices(A_97) | ~l3_lattices(A_97) | v2_struct_0(A_97) | ~l3_lattices(A_97) | ~v4_lattice3(A_97) | ~v10_lattices(A_97) | v2_struct_0(A_97))), inference(superposition, [status(thm), theory('equality')], [c_80, c_184])).
% 7.92/2.62  tff(c_4349, plain, (![D_615, B_616]: (r1_lattices('#skF_9', '#skF_12'(D_615), B_616) | ~r4_lattice3('#skF_9', B_616, a_2_5_lattice3('#skF_9', '#skF_11')) | ~m1_subset_1(B_616, u1_struct_0('#skF_9')) | ~r2_hidden('#skF_12'(D_615), '#skF_10') | ~m1_subset_1('#skF_12'(D_615), u1_struct_0('#skF_9')) | ~r2_hidden(D_615, '#skF_10') | ~m1_subset_1(D_615, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_92, c_762])).
% 7.92/2.62  tff(c_4352, plain, (![D_615]: (r1_lattices('#skF_9', '#skF_12'(D_615), k15_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11'))) | ~m1_subset_1(k15_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), u1_struct_0('#skF_9')) | ~r2_hidden('#skF_12'(D_615), '#skF_10') | ~m1_subset_1('#skF_12'(D_615), u1_struct_0('#skF_9')) | ~r2_hidden(D_615, '#skF_10') | ~m1_subset_1(D_615, u1_struct_0('#skF_9')) | ~m1_subset_1(k15_lattice3('#skF_9', '#skF_11'), u1_struct_0('#skF_9')) | ~l3_lattices('#skF_9') | ~v4_lattice3('#skF_9') | ~v10_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_188, c_4349])).
% 7.92/2.62  tff(c_4364, plain, (![D_615]: (r1_lattices('#skF_9', '#skF_12'(D_615), k15_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11'))) | ~m1_subset_1(k15_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), u1_struct_0('#skF_9')) | ~r2_hidden('#skF_12'(D_615), '#skF_10') | ~m1_subset_1('#skF_12'(D_615), u1_struct_0('#skF_9')) | ~r2_hidden(D_615, '#skF_10') | ~m1_subset_1(D_615, u1_struct_0('#skF_9')) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_3946, c_4352])).
% 7.92/2.62  tff(c_4365, plain, (![D_615]: (r1_lattices('#skF_9', '#skF_12'(D_615), k15_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11'))) | ~m1_subset_1(k15_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), u1_struct_0('#skF_9')) | ~r2_hidden('#skF_12'(D_615), '#skF_10') | ~m1_subset_1('#skF_12'(D_615), u1_struct_0('#skF_9')) | ~r2_hidden(D_615, '#skF_10') | ~m1_subset_1(D_615, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_92, c_4364])).
% 7.92/2.62  tff(c_4865, plain, (~m1_subset_1(k15_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), u1_struct_0('#skF_9'))), inference(splitLeft, [status(thm)], [c_4365])).
% 7.92/2.62  tff(c_4868, plain, (~m1_subset_1(k15_lattice3('#skF_9', '#skF_11'), u1_struct_0('#skF_9')) | ~l3_lattices('#skF_9') | ~v4_lattice3('#skF_9') | ~v10_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_80, c_4865])).
% 7.92/2.62  tff(c_4870, plain, (v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_3946, c_4868])).
% 7.92/2.62  tff(c_4872, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_4870])).
% 7.92/2.62  tff(c_4874, plain, (m1_subset_1(k15_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), u1_struct_0('#skF_9'))), inference(splitRight, [status(thm)], [c_4365])).
% 7.92/2.62  tff(c_48, plain, (![A_53, B_60]: (r4_lattice3(A_53, k15_lattice3(A_53, B_60), B_60) | ~m1_subset_1(k15_lattice3(A_53, B_60), u1_struct_0(A_53)) | ~v4_lattice3(A_53) | ~v10_lattices(A_53) | ~l3_lattices(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.92/2.62  tff(c_4892, plain, (r4_lattice3('#skF_9', k15_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), a_2_5_lattice3('#skF_9', '#skF_11')) | ~v4_lattice3('#skF_9') | ~v10_lattices('#skF_9') | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_4874, c_48])).
% 7.92/2.62  tff(c_4920, plain, (r4_lattice3('#skF_9', k15_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), a_2_5_lattice3('#skF_9', '#skF_11')) | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_90, c_88, c_4892])).
% 7.92/2.62  tff(c_4921, plain, (r4_lattice3('#skF_9', k15_lattice3('#skF_9', a_2_5_lattice3('#skF_9', '#skF_11')), a_2_5_lattice3('#skF_9', '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_92, c_4920])).
% 7.92/2.62  tff(c_4931, plain, (r4_lattice3('#skF_9', k15_lattice3('#skF_9', '#skF_11'), a_2_5_lattice3('#skF_9', '#skF_11')) | ~l3_lattices('#skF_9') | ~v4_lattice3('#skF_9') | ~v10_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_80, c_4921])).
% 7.92/2.62  tff(c_4940, plain, (r4_lattice3('#skF_9', k15_lattice3('#skF_9', '#skF_11'), a_2_5_lattice3('#skF_9', '#skF_11')) | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_4931])).
% 7.92/2.62  tff(c_4942, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_4235, c_4940])).
% 7.92/2.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.92/2.62  
% 7.92/2.62  Inference rules
% 7.92/2.62  ----------------------
% 7.92/2.62  #Ref     : 0
% 7.92/2.62  #Sup     : 940
% 7.92/2.62  #Fact    : 0
% 7.92/2.62  #Define  : 0
% 7.92/2.62  #Split   : 20
% 7.92/2.62  #Chain   : 0
% 7.92/2.62  #Close   : 0
% 7.92/2.62  
% 7.92/2.62  Ordering : KBO
% 7.92/2.62  
% 7.92/2.62  Simplification rules
% 7.92/2.62  ----------------------
% 7.92/2.62  #Subsume      : 78
% 7.92/2.62  #Demod        : 1367
% 7.92/2.62  #Tautology    : 186
% 7.92/2.62  #SimpNegUnit  : 412
% 7.92/2.62  #BackRed      : 1
% 7.92/2.62  
% 7.92/2.62  #Partial instantiations: 0
% 7.92/2.62  #Strategies tried      : 1
% 7.92/2.62  
% 7.92/2.62  Timing (in seconds)
% 7.92/2.62  ----------------------
% 7.92/2.62  Preprocessing        : 0.37
% 7.92/2.62  Parsing              : 0.20
% 7.92/2.62  CNF conversion       : 0.03
% 7.92/2.62  Main loop            : 1.40
% 7.92/2.62  Inferencing          : 0.54
% 7.92/2.62  Reduction            : 0.40
% 7.92/2.63  Demodulation         : 0.26
% 7.92/2.63  BG Simplification    : 0.07
% 7.92/2.63  Subsumption          : 0.28
% 7.92/2.63  Abstraction          : 0.10
% 7.92/2.63  MUC search           : 0.00
% 7.92/2.63  Cooper               : 0.00
% 7.92/2.63  Total                : 1.83
% 7.92/2.63  Index Insertion      : 0.00
% 7.92/2.63  Index Deletion       : 0.00
% 7.92/2.63  Index Matching       : 0.00
% 7.92/2.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
