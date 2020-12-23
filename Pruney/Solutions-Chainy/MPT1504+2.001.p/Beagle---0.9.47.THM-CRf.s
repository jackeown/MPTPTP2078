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
% DateTime   : Thu Dec  3 10:24:44 EST 2020

% Result     : Theorem 9.64s
% Output     : CNFRefutation 9.64s
% Verified   : 
% Statistics : Number of formulae       :  146 (1309 expanded)
%              Number of leaves         :   40 ( 494 expanded)
%              Depth                    :   49
%              Number of atoms          :  635 (6414 expanded)
%              Number of equality atoms :   48 ( 684 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_2_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_6 > #skF_5 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_4

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

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k16_lattice3,type,(
    k16_lattice3: ( $i * $i ) > $i )).

tff(k15_lattice3,type,(
    k15_lattice3: ( $i * $i ) > $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r3_lattice3,type,(
    r3_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_187,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B] : k15_lattice3(A,B) = k16_lattice3(A,a_2_2_lattice3(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).

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

tff(f_174,axiom,(
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

tff(c_76,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_70,plain,(
    l3_lattices('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_72,plain,(
    v4_lattice3('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_38,plain,(
    ! [A_27,B_42] :
      ( m1_subset_1('#skF_2'(A_27,B_42),u1_struct_0(A_27))
      | ~ v4_lattice3(A_27)
      | ~ l3_lattices(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_74,plain,(
    v10_lattices('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_36,plain,(
    ! [A_27,B_42] :
      ( r4_lattice3(A_27,'#skF_2'(A_27,B_42),B_42)
      | ~ v4_lattice3(A_27)
      | ~ l3_lattices(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

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

tff(c_170,plain,(
    ! [A_158,C_159,B_160] :
      ( ~ r1_lattices(A_158,C_159,'#skF_5'(A_158,B_160,C_159))
      | k15_lattice3(A_158,B_160) = C_159
      | ~ r4_lattice3(A_158,C_159,B_160)
      | ~ m1_subset_1(C_159,u1_struct_0(A_158))
      | ~ v4_lattice3(A_158)
      | ~ v10_lattices(A_158)
      | ~ l3_lattices(A_158)
      | v2_struct_0(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_527,plain,(
    ! [A_262,B_263,B_264] :
      ( k15_lattice3(A_262,B_263) = '#skF_2'(A_262,B_264)
      | ~ r4_lattice3(A_262,'#skF_2'(A_262,B_264),B_263)
      | ~ m1_subset_1('#skF_2'(A_262,B_264),u1_struct_0(A_262))
      | ~ v10_lattices(A_262)
      | ~ r4_lattice3(A_262,'#skF_5'(A_262,B_263,'#skF_2'(A_262,B_264)),B_264)
      | ~ m1_subset_1('#skF_5'(A_262,B_263,'#skF_2'(A_262,B_264)),u1_struct_0(A_262))
      | ~ v4_lattice3(A_262)
      | ~ l3_lattices(A_262)
      | v2_struct_0(A_262) ) ),
    inference(resolution,[status(thm)],[c_34,c_170])).

tff(c_532,plain,(
    ! [A_265,B_266] :
      ( ~ m1_subset_1('#skF_5'(A_265,B_266,'#skF_2'(A_265,B_266)),u1_struct_0(A_265))
      | k15_lattice3(A_265,B_266) = '#skF_2'(A_265,B_266)
      | ~ r4_lattice3(A_265,'#skF_2'(A_265,B_266),B_266)
      | ~ m1_subset_1('#skF_2'(A_265,B_266),u1_struct_0(A_265))
      | ~ v4_lattice3(A_265)
      | ~ v10_lattices(A_265)
      | ~ l3_lattices(A_265)
      | v2_struct_0(A_265) ) ),
    inference(resolution,[status(thm)],[c_42,c_527])).

tff(c_547,plain,(
    ! [A_271,B_272] :
      ( k15_lattice3(A_271,B_272) = '#skF_2'(A_271,B_272)
      | ~ r4_lattice3(A_271,'#skF_2'(A_271,B_272),B_272)
      | ~ m1_subset_1('#skF_2'(A_271,B_272),u1_struct_0(A_271))
      | ~ v4_lattice3(A_271)
      | ~ v10_lattices(A_271)
      | ~ l3_lattices(A_271)
      | v2_struct_0(A_271) ) ),
    inference(resolution,[status(thm)],[c_44,c_532])).

tff(c_551,plain,(
    ! [A_273,B_274] :
      ( k15_lattice3(A_273,B_274) = '#skF_2'(A_273,B_274)
      | ~ m1_subset_1('#skF_2'(A_273,B_274),u1_struct_0(A_273))
      | ~ v10_lattices(A_273)
      | ~ v4_lattice3(A_273)
      | ~ l3_lattices(A_273)
      | v2_struct_0(A_273) ) ),
    inference(resolution,[status(thm)],[c_36,c_547])).

tff(c_556,plain,(
    ! [A_275,B_276] :
      ( k15_lattice3(A_275,B_276) = '#skF_2'(A_275,B_276)
      | ~ v10_lattices(A_275)
      | ~ v4_lattice3(A_275)
      | ~ l3_lattices(A_275)
      | v2_struct_0(A_275) ) ),
    inference(resolution,[status(thm)],[c_38,c_551])).

tff(c_558,plain,(
    ! [B_276] :
      ( k15_lattice3('#skF_8',B_276) = '#skF_2'('#skF_8',B_276)
      | ~ v10_lattices('#skF_8')
      | ~ l3_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_72,c_556])).

tff(c_561,plain,(
    ! [B_276] :
      ( k15_lattice3('#skF_8',B_276) = '#skF_2'('#skF_8',B_276)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_74,c_558])).

tff(c_562,plain,(
    ! [B_276] : k15_lattice3('#skF_8',B_276) = '#skF_2'('#skF_8',B_276) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_561])).

tff(c_564,plain,(
    ! [B_277] : k15_lattice3('#skF_8',B_277) = '#skF_2'('#skF_8',B_277) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_561])).

tff(c_48,plain,(
    ! [A_53,B_60] :
      ( r4_lattice3(A_53,k15_lattice3(A_53,B_60),B_60)
      | ~ m1_subset_1(k15_lattice3(A_53,B_60),u1_struct_0(A_53))
      | ~ v4_lattice3(A_53)
      | ~ v10_lattices(A_53)
      | ~ l3_lattices(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_571,plain,(
    ! [B_277] :
      ( r4_lattice3('#skF_8',k15_lattice3('#skF_8',B_277),B_277)
      | ~ m1_subset_1('#skF_2'('#skF_8',B_277),u1_struct_0('#skF_8'))
      | ~ v4_lattice3('#skF_8')
      | ~ v10_lattices('#skF_8')
      | ~ l3_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_564,c_48])).

tff(c_580,plain,(
    ! [B_277] :
      ( r4_lattice3('#skF_8','#skF_2'('#skF_8',B_277),B_277)
      | ~ m1_subset_1('#skF_2'('#skF_8',B_277),u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_74,c_72,c_562,c_571])).

tff(c_583,plain,(
    ! [B_278] :
      ( r4_lattice3('#skF_8','#skF_2'('#skF_8',B_278),B_278)
      | ~ m1_subset_1('#skF_2'('#skF_8',B_278),u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_580])).

tff(c_586,plain,(
    ! [B_42] :
      ( r4_lattice3('#skF_8','#skF_2'('#skF_8',B_42),B_42)
      | ~ v4_lattice3('#skF_8')
      | ~ l3_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_38,c_583])).

tff(c_589,plain,(
    ! [B_42] :
      ( r4_lattice3('#skF_8','#skF_2'('#skF_8',B_42),B_42)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_72,c_586])).

tff(c_590,plain,(
    ! [B_42] : r4_lattice3('#skF_8','#skF_2'('#skF_8',B_42),B_42) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_589])).

tff(c_24,plain,(
    ! [A_5,B_17,C_23] :
      ( r2_hidden('#skF_1'(A_5,B_17,C_23),C_23)
      | r3_lattice3(A_5,B_17,C_23)
      | ~ m1_subset_1(B_17,u1_struct_0(A_5))
      | ~ l3_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_86,plain,(
    ! [A_107,B_108,C_109] :
      ( '#skF_6'(A_107,B_108,C_109) = A_107
      | ~ r2_hidden(A_107,a_2_2_lattice3(B_108,C_109))
      | ~ l3_lattices(B_108)
      | ~ v4_lattice3(B_108)
      | ~ v10_lattices(B_108)
      | v2_struct_0(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_259,plain,(
    ! [A_201,B_202,B_203,C_204] :
      ( '#skF_6'('#skF_1'(A_201,B_202,a_2_2_lattice3(B_203,C_204)),B_203,C_204) = '#skF_1'(A_201,B_202,a_2_2_lattice3(B_203,C_204))
      | ~ l3_lattices(B_203)
      | ~ v4_lattice3(B_203)
      | ~ v10_lattices(B_203)
      | v2_struct_0(B_203)
      | r3_lattice3(A_201,B_202,a_2_2_lattice3(B_203,C_204))
      | ~ m1_subset_1(B_202,u1_struct_0(A_201))
      | ~ l3_lattices(A_201)
      | v2_struct_0(A_201) ) ),
    inference(resolution,[status(thm)],[c_24,c_86])).

tff(c_56,plain,(
    ! [A_65,B_66,C_67] :
      ( m1_subset_1('#skF_6'(A_65,B_66,C_67),u1_struct_0(B_66))
      | ~ r2_hidden(A_65,a_2_2_lattice3(B_66,C_67))
      | ~ l3_lattices(B_66)
      | ~ v4_lattice3(B_66)
      | ~ v10_lattices(B_66)
      | v2_struct_0(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_901,plain,(
    ! [A_306,B_307,B_308,C_309] :
      ( m1_subset_1('#skF_1'(A_306,B_307,a_2_2_lattice3(B_308,C_309)),u1_struct_0(B_308))
      | ~ r2_hidden('#skF_1'(A_306,B_307,a_2_2_lattice3(B_308,C_309)),a_2_2_lattice3(B_308,C_309))
      | ~ l3_lattices(B_308)
      | ~ v4_lattice3(B_308)
      | ~ v10_lattices(B_308)
      | v2_struct_0(B_308)
      | ~ l3_lattices(B_308)
      | ~ v4_lattice3(B_308)
      | ~ v10_lattices(B_308)
      | v2_struct_0(B_308)
      | r3_lattice3(A_306,B_307,a_2_2_lattice3(B_308,C_309))
      | ~ m1_subset_1(B_307,u1_struct_0(A_306))
      | ~ l3_lattices(A_306)
      | v2_struct_0(A_306) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_56])).

tff(c_911,plain,(
    ! [A_5,B_17,B_308,C_309] :
      ( m1_subset_1('#skF_1'(A_5,B_17,a_2_2_lattice3(B_308,C_309)),u1_struct_0(B_308))
      | ~ l3_lattices(B_308)
      | ~ v4_lattice3(B_308)
      | ~ v10_lattices(B_308)
      | v2_struct_0(B_308)
      | r3_lattice3(A_5,B_17,a_2_2_lattice3(B_308,C_309))
      | ~ m1_subset_1(B_17,u1_struct_0(A_5))
      | ~ l3_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_24,c_901])).

tff(c_52,plain,(
    ! [B_66,A_65,C_67] :
      ( r4_lattice3(B_66,'#skF_6'(A_65,B_66,C_67),C_67)
      | ~ r2_hidden(A_65,a_2_2_lattice3(B_66,C_67))
      | ~ l3_lattices(B_66)
      | ~ v4_lattice3(B_66)
      | ~ v10_lattices(B_66)
      | v2_struct_0(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_856,plain,(
    ! [B_300,A_301,B_302,C_303] :
      ( r4_lattice3(B_300,'#skF_1'(A_301,B_302,a_2_2_lattice3(B_300,C_303)),C_303)
      | ~ r2_hidden('#skF_1'(A_301,B_302,a_2_2_lattice3(B_300,C_303)),a_2_2_lattice3(B_300,C_303))
      | ~ l3_lattices(B_300)
      | ~ v4_lattice3(B_300)
      | ~ v10_lattices(B_300)
      | v2_struct_0(B_300)
      | ~ l3_lattices(B_300)
      | ~ v4_lattice3(B_300)
      | ~ v10_lattices(B_300)
      | v2_struct_0(B_300)
      | r3_lattice3(A_301,B_302,a_2_2_lattice3(B_300,C_303))
      | ~ m1_subset_1(B_302,u1_struct_0(A_301))
      | ~ l3_lattices(A_301)
      | v2_struct_0(A_301) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_52])).

tff(c_959,plain,(
    ! [B_320,A_321,B_322,C_323] :
      ( r4_lattice3(B_320,'#skF_1'(A_321,B_322,a_2_2_lattice3(B_320,C_323)),C_323)
      | ~ l3_lattices(B_320)
      | ~ v4_lattice3(B_320)
      | ~ v10_lattices(B_320)
      | v2_struct_0(B_320)
      | r3_lattice3(A_321,B_322,a_2_2_lattice3(B_320,C_323))
      | ~ m1_subset_1(B_322,u1_struct_0(A_321))
      | ~ l3_lattices(A_321)
      | v2_struct_0(A_321) ) ),
    inference(resolution,[status(thm)],[c_24,c_856])).

tff(c_98,plain,(
    ! [A_126,B_127,D_128] :
      ( r1_lattices(A_126,'#skF_2'(A_126,B_127),D_128)
      | ~ r4_lattice3(A_126,D_128,B_127)
      | ~ m1_subset_1(D_128,u1_struct_0(A_126))
      | ~ v4_lattice3(A_126)
      | ~ l3_lattices(A_126)
      | v2_struct_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_22,plain,(
    ! [A_5,B_17,C_23] :
      ( ~ r1_lattices(A_5,B_17,'#skF_1'(A_5,B_17,C_23))
      | r3_lattice3(A_5,B_17,C_23)
      | ~ m1_subset_1(B_17,u1_struct_0(A_5))
      | ~ l3_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_103,plain,(
    ! [A_126,B_127,C_23] :
      ( r3_lattice3(A_126,'#skF_2'(A_126,B_127),C_23)
      | ~ m1_subset_1('#skF_2'(A_126,B_127),u1_struct_0(A_126))
      | ~ r4_lattice3(A_126,'#skF_1'(A_126,'#skF_2'(A_126,B_127),C_23),B_127)
      | ~ m1_subset_1('#skF_1'(A_126,'#skF_2'(A_126,B_127),C_23),u1_struct_0(A_126))
      | ~ v4_lattice3(A_126)
      | ~ l3_lattices(A_126)
      | v2_struct_0(A_126) ) ),
    inference(resolution,[status(thm)],[c_98,c_22])).

tff(c_1012,plain,(
    ! [A_331,C_332] :
      ( ~ m1_subset_1('#skF_1'(A_331,'#skF_2'(A_331,C_332),a_2_2_lattice3(A_331,C_332)),u1_struct_0(A_331))
      | ~ v4_lattice3(A_331)
      | ~ v10_lattices(A_331)
      | r3_lattice3(A_331,'#skF_2'(A_331,C_332),a_2_2_lattice3(A_331,C_332))
      | ~ m1_subset_1('#skF_2'(A_331,C_332),u1_struct_0(A_331))
      | ~ l3_lattices(A_331)
      | v2_struct_0(A_331) ) ),
    inference(resolution,[status(thm)],[c_959,c_103])).

tff(c_1021,plain,(
    ! [B_308,C_309] :
      ( ~ v4_lattice3(B_308)
      | ~ v10_lattices(B_308)
      | r3_lattice3(B_308,'#skF_2'(B_308,C_309),a_2_2_lattice3(B_308,C_309))
      | ~ m1_subset_1('#skF_2'(B_308,C_309),u1_struct_0(B_308))
      | ~ l3_lattices(B_308)
      | v2_struct_0(B_308) ) ),
    inference(resolution,[status(thm)],[c_911,c_1012])).

tff(c_66,plain,(
    ! [A_71,B_83,C_89] :
      ( m1_subset_1('#skF_7'(A_71,B_83,C_89),u1_struct_0(A_71))
      | k16_lattice3(A_71,C_89) = B_83
      | ~ r3_lattice3(A_71,B_83,C_89)
      | ~ m1_subset_1(B_83,u1_struct_0(A_71))
      | ~ l3_lattices(A_71)
      | ~ v4_lattice3(A_71)
      | ~ v10_lattices(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_64,plain,(
    ! [A_71,B_83,C_89] :
      ( r3_lattice3(A_71,'#skF_7'(A_71,B_83,C_89),C_89)
      | k16_lattice3(A_71,C_89) = B_83
      | ~ r3_lattice3(A_71,B_83,C_89)
      | ~ m1_subset_1(B_83,u1_struct_0(A_71))
      | ~ l3_lattices(A_71)
      | ~ v4_lattice3(A_71)
      | ~ v10_lattices(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

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

tff(c_126,plain,(
    ! [A_141,B_142,D_143,C_144] :
      ( r1_lattices(A_141,B_142,D_143)
      | ~ r2_hidden(D_143,C_144)
      | ~ m1_subset_1(D_143,u1_struct_0(A_141))
      | ~ r3_lattice3(A_141,B_142,C_144)
      | ~ m1_subset_1(B_142,u1_struct_0(A_141))
      | ~ l3_lattices(A_141)
      | v2_struct_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_353,plain,(
    ! [D_220,C_217,B_216,B_218,A_219] :
      ( r1_lattices(A_219,B_216,D_220)
      | ~ m1_subset_1(D_220,u1_struct_0(A_219))
      | ~ r3_lattice3(A_219,B_216,a_2_2_lattice3(B_218,C_217))
      | ~ m1_subset_1(B_216,u1_struct_0(A_219))
      | ~ l3_lattices(A_219)
      | v2_struct_0(A_219)
      | ~ r4_lattice3(B_218,D_220,C_217)
      | ~ m1_subset_1(D_220,u1_struct_0(B_218))
      | ~ l3_lattices(B_218)
      | ~ v4_lattice3(B_218)
      | ~ v10_lattices(B_218)
      | v2_struct_0(B_218) ) ),
    inference(resolution,[status(thm)],[c_50,c_126])).

tff(c_483,plain,(
    ! [A_257,C_256,B_255,B_254,B_253] :
      ( r1_lattices(A_257,B_253,'#skF_2'(A_257,B_255))
      | ~ r3_lattice3(A_257,B_253,a_2_2_lattice3(B_254,C_256))
      | ~ m1_subset_1(B_253,u1_struct_0(A_257))
      | ~ r4_lattice3(B_254,'#skF_2'(A_257,B_255),C_256)
      | ~ m1_subset_1('#skF_2'(A_257,B_255),u1_struct_0(B_254))
      | ~ l3_lattices(B_254)
      | ~ v4_lattice3(B_254)
      | ~ v10_lattices(B_254)
      | v2_struct_0(B_254)
      | ~ v4_lattice3(A_257)
      | ~ l3_lattices(A_257)
      | v2_struct_0(A_257) ) ),
    inference(resolution,[status(thm)],[c_38,c_353])).

tff(c_4188,plain,(
    ! [A_620,B_622,B_621,B_618,C_619] :
      ( r1_lattices(A_620,'#skF_7'(A_620,B_622,a_2_2_lattice3(B_618,C_619)),'#skF_2'(A_620,B_621))
      | ~ m1_subset_1('#skF_7'(A_620,B_622,a_2_2_lattice3(B_618,C_619)),u1_struct_0(A_620))
      | ~ r4_lattice3(B_618,'#skF_2'(A_620,B_621),C_619)
      | ~ m1_subset_1('#skF_2'(A_620,B_621),u1_struct_0(B_618))
      | ~ l3_lattices(B_618)
      | ~ v4_lattice3(B_618)
      | ~ v10_lattices(B_618)
      | v2_struct_0(B_618)
      | k16_lattice3(A_620,a_2_2_lattice3(B_618,C_619)) = B_622
      | ~ r3_lattice3(A_620,B_622,a_2_2_lattice3(B_618,C_619))
      | ~ m1_subset_1(B_622,u1_struct_0(A_620))
      | ~ l3_lattices(A_620)
      | ~ v4_lattice3(A_620)
      | ~ v10_lattices(A_620)
      | v2_struct_0(A_620) ) ),
    inference(resolution,[status(thm)],[c_64,c_483])).

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

tff(c_592,plain,(
    ! [B_279] : r4_lattice3('#skF_8','#skF_2'('#skF_8',B_279),B_279) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_589])).

tff(c_105,plain,(
    ! [D_131,B_132,C_133] :
      ( r2_hidden(D_131,a_2_2_lattice3(B_132,C_133))
      | ~ r4_lattice3(B_132,D_131,C_133)
      | ~ m1_subset_1(D_131,u1_struct_0(B_132))
      | ~ l3_lattices(B_132)
      | ~ v4_lattice3(B_132)
      | ~ v10_lattices(B_132)
      | v2_struct_0(B_132) ) ),
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

tff(c_109,plain,(
    ! [D_131,B_132,C_133] :
      ( '#skF_6'(D_131,B_132,C_133) = D_131
      | ~ r4_lattice3(B_132,D_131,C_133)
      | ~ m1_subset_1(D_131,u1_struct_0(B_132))
      | ~ l3_lattices(B_132)
      | ~ v4_lattice3(B_132)
      | ~ v10_lattices(B_132)
      | v2_struct_0(B_132) ) ),
    inference(resolution,[status(thm)],[c_105,c_54])).

tff(c_597,plain,(
    ! [B_279] :
      ( '#skF_6'('#skF_2'('#skF_8',B_279),'#skF_8',B_279) = '#skF_2'('#skF_8',B_279)
      | ~ m1_subset_1('#skF_2'('#skF_8',B_279),u1_struct_0('#skF_8'))
      | ~ l3_lattices('#skF_8')
      | ~ v4_lattice3('#skF_8')
      | ~ v10_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_592,c_109])).

tff(c_604,plain,(
    ! [B_279] :
      ( '#skF_6'('#skF_2'('#skF_8',B_279),'#skF_8',B_279) = '#skF_2'('#skF_8',B_279)
      | ~ m1_subset_1('#skF_2'('#skF_8',B_279),u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_597])).

tff(c_606,plain,(
    ! [B_280] :
      ( '#skF_6'('#skF_2'('#skF_8',B_280),'#skF_8',B_280) = '#skF_2'('#skF_8',B_280)
      | ~ m1_subset_1('#skF_2'('#skF_8',B_280),u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_604])).

tff(c_609,plain,(
    ! [B_42] :
      ( '#skF_6'('#skF_2'('#skF_8',B_42),'#skF_8',B_42) = '#skF_2'('#skF_8',B_42)
      | ~ v4_lattice3('#skF_8')
      | ~ l3_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_38,c_606])).

tff(c_612,plain,(
    ! [B_42] :
      ( '#skF_6'('#skF_2'('#skF_8',B_42),'#skF_8',B_42) = '#skF_2'('#skF_8',B_42)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_72,c_609])).

tff(c_613,plain,(
    ! [B_42] : '#skF_6'('#skF_2'('#skF_8',B_42),'#skF_8',B_42) = '#skF_2'('#skF_8',B_42) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_612])).

tff(c_615,plain,(
    ! [B_281] : '#skF_6'('#skF_2'('#skF_8',B_281),'#skF_8',B_281) = '#skF_2'('#skF_8',B_281) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_612])).

tff(c_137,plain,(
    ! [A_147,B_148,C_149] :
      ( r3_lattices(A_147,B_148,C_149)
      | ~ r1_lattices(A_147,B_148,C_149)
      | ~ m1_subset_1(C_149,u1_struct_0(A_147))
      | ~ m1_subset_1(B_148,u1_struct_0(A_147))
      | ~ l3_lattices(A_147)
      | ~ v9_lattices(A_147)
      | ~ v8_lattices(A_147)
      | ~ v6_lattices(A_147)
      | v2_struct_0(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_147,plain,(
    ! [B_66,B_148,A_65,C_67] :
      ( r3_lattices(B_66,B_148,'#skF_6'(A_65,B_66,C_67))
      | ~ r1_lattices(B_66,B_148,'#skF_6'(A_65,B_66,C_67))
      | ~ m1_subset_1(B_148,u1_struct_0(B_66))
      | ~ v9_lattices(B_66)
      | ~ v8_lattices(B_66)
      | ~ v6_lattices(B_66)
      | ~ r2_hidden(A_65,a_2_2_lattice3(B_66,C_67))
      | ~ l3_lattices(B_66)
      | ~ v4_lattice3(B_66)
      | ~ v10_lattices(B_66)
      | v2_struct_0(B_66) ) ),
    inference(resolution,[status(thm)],[c_56,c_137])).

tff(c_630,plain,(
    ! [B_148,B_281] :
      ( r3_lattices('#skF_8',B_148,'#skF_2'('#skF_8',B_281))
      | ~ r1_lattices('#skF_8',B_148,'#skF_6'('#skF_2'('#skF_8',B_281),'#skF_8',B_281))
      | ~ m1_subset_1(B_148,u1_struct_0('#skF_8'))
      | ~ v9_lattices('#skF_8')
      | ~ v8_lattices('#skF_8')
      | ~ v6_lattices('#skF_8')
      | ~ r2_hidden('#skF_2'('#skF_8',B_281),a_2_2_lattice3('#skF_8',B_281))
      | ~ l3_lattices('#skF_8')
      | ~ v4_lattice3('#skF_8')
      | ~ v10_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_615,c_147])).

tff(c_661,plain,(
    ! [B_148,B_281] :
      ( r3_lattices('#skF_8',B_148,'#skF_2'('#skF_8',B_281))
      | ~ r1_lattices('#skF_8',B_148,'#skF_2'('#skF_8',B_281))
      | ~ m1_subset_1(B_148,u1_struct_0('#skF_8'))
      | ~ v9_lattices('#skF_8')
      | ~ v8_lattices('#skF_8')
      | ~ v6_lattices('#skF_8')
      | ~ r2_hidden('#skF_2'('#skF_8',B_281),a_2_2_lattice3('#skF_8',B_281))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_613,c_630])).

tff(c_662,plain,(
    ! [B_148,B_281] :
      ( r3_lattices('#skF_8',B_148,'#skF_2'('#skF_8',B_281))
      | ~ r1_lattices('#skF_8',B_148,'#skF_2'('#skF_8',B_281))
      | ~ m1_subset_1(B_148,u1_struct_0('#skF_8'))
      | ~ v9_lattices('#skF_8')
      | ~ v8_lattices('#skF_8')
      | ~ v6_lattices('#skF_8')
      | ~ r2_hidden('#skF_2'('#skF_8',B_281),a_2_2_lattice3('#skF_8',B_281)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_661])).

tff(c_867,plain,(
    ~ v6_lattices('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_662])).

tff(c_870,plain,
    ( ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ l3_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_8,c_867])).

tff(c_873,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_74,c_870])).

tff(c_875,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_873])).

tff(c_876,plain,(
    ! [B_148,B_281] :
      ( ~ v8_lattices('#skF_8')
      | ~ v9_lattices('#skF_8')
      | r3_lattices('#skF_8',B_148,'#skF_2'('#skF_8',B_281))
      | ~ r1_lattices('#skF_8',B_148,'#skF_2'('#skF_8',B_281))
      | ~ m1_subset_1(B_148,u1_struct_0('#skF_8'))
      | ~ r2_hidden('#skF_2'('#skF_8',B_281),a_2_2_lattice3('#skF_8',B_281)) ) ),
    inference(splitRight,[status(thm)],[c_662])).

tff(c_879,plain,(
    ~ v9_lattices('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_876])).

tff(c_882,plain,
    ( ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ l3_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_2,c_879])).

tff(c_885,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_74,c_882])).

tff(c_887,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_885])).

tff(c_888,plain,(
    ! [B_148,B_281] :
      ( ~ v8_lattices('#skF_8')
      | r3_lattices('#skF_8',B_148,'#skF_2'('#skF_8',B_281))
      | ~ r1_lattices('#skF_8',B_148,'#skF_2'('#skF_8',B_281))
      | ~ m1_subset_1(B_148,u1_struct_0('#skF_8'))
      | ~ r2_hidden('#skF_2'('#skF_8',B_281),a_2_2_lattice3('#skF_8',B_281)) ) ),
    inference(splitRight,[status(thm)],[c_876])).

tff(c_890,plain,(
    ~ v8_lattices('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_888])).

tff(c_893,plain,
    ( ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ l3_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_890])).

tff(c_896,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_74,c_893])).

tff(c_898,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_896])).

tff(c_912,plain,(
    ! [B_310,B_311] :
      ( r3_lattices('#skF_8',B_310,'#skF_2'('#skF_8',B_311))
      | ~ r1_lattices('#skF_8',B_310,'#skF_2'('#skF_8',B_311))
      | ~ m1_subset_1(B_310,u1_struct_0('#skF_8'))
      | ~ r2_hidden('#skF_2'('#skF_8',B_311),a_2_2_lattice3('#skF_8',B_311)) ) ),
    inference(splitRight,[status(thm)],[c_888])).

tff(c_915,plain,(
    ! [B_310,C_67] :
      ( r3_lattices('#skF_8',B_310,'#skF_2'('#skF_8',C_67))
      | ~ r1_lattices('#skF_8',B_310,'#skF_2'('#skF_8',C_67))
      | ~ m1_subset_1(B_310,u1_struct_0('#skF_8'))
      | ~ r4_lattice3('#skF_8','#skF_2'('#skF_8',C_67),C_67)
      | ~ m1_subset_1('#skF_2'('#skF_8',C_67),u1_struct_0('#skF_8'))
      | ~ l3_lattices('#skF_8')
      | ~ v4_lattice3('#skF_8')
      | ~ v10_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_50,c_912])).

tff(c_918,plain,(
    ! [B_310,C_67] :
      ( r3_lattices('#skF_8',B_310,'#skF_2'('#skF_8',C_67))
      | ~ r1_lattices('#skF_8',B_310,'#skF_2'('#skF_8',C_67))
      | ~ m1_subset_1(B_310,u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_2'('#skF_8',C_67),u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_590,c_915])).

tff(c_920,plain,(
    ! [B_312,C_313] :
      ( r3_lattices('#skF_8',B_312,'#skF_2'('#skF_8',C_313))
      | ~ r1_lattices('#skF_8',B_312,'#skF_2'('#skF_8',C_313))
      | ~ m1_subset_1(B_312,u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_2'('#skF_8',C_313),u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_918])).

tff(c_923,plain,(
    ! [B_312,B_42] :
      ( r3_lattices('#skF_8',B_312,'#skF_2'('#skF_8',B_42))
      | ~ r1_lattices('#skF_8',B_312,'#skF_2'('#skF_8',B_42))
      | ~ m1_subset_1(B_312,u1_struct_0('#skF_8'))
      | ~ v4_lattice3('#skF_8')
      | ~ l3_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_38,c_920])).

tff(c_926,plain,(
    ! [B_312,B_42] :
      ( r3_lattices('#skF_8',B_312,'#skF_2'('#skF_8',B_42))
      | ~ r1_lattices('#skF_8',B_312,'#skF_2'('#skF_8',B_42))
      | ~ m1_subset_1(B_312,u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_72,c_923])).

tff(c_928,plain,(
    ! [B_314,B_315] :
      ( r3_lattices('#skF_8',B_314,'#skF_2'('#skF_8',B_315))
      | ~ r1_lattices('#skF_8',B_314,'#skF_2'('#skF_8',B_315))
      | ~ m1_subset_1(B_314,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_926])).

tff(c_62,plain,(
    ! [A_71,B_83,C_89] :
      ( ~ r3_lattices(A_71,'#skF_7'(A_71,B_83,C_89),B_83)
      | k16_lattice3(A_71,C_89) = B_83
      | ~ r3_lattice3(A_71,B_83,C_89)
      | ~ m1_subset_1(B_83,u1_struct_0(A_71))
      | ~ l3_lattices(A_71)
      | ~ v4_lattice3(A_71)
      | ~ v10_lattices(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_932,plain,(
    ! [C_89,B_315] :
      ( k16_lattice3('#skF_8',C_89) = '#skF_2'('#skF_8',B_315)
      | ~ r3_lattice3('#skF_8','#skF_2'('#skF_8',B_315),C_89)
      | ~ m1_subset_1('#skF_2'('#skF_8',B_315),u1_struct_0('#skF_8'))
      | ~ l3_lattices('#skF_8')
      | ~ v4_lattice3('#skF_8')
      | ~ v10_lattices('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ r1_lattices('#skF_8','#skF_7'('#skF_8','#skF_2'('#skF_8',B_315),C_89),'#skF_2'('#skF_8',B_315))
      | ~ m1_subset_1('#skF_7'('#skF_8','#skF_2'('#skF_8',B_315),C_89),u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_928,c_62])).

tff(c_937,plain,(
    ! [C_89,B_315] :
      ( k16_lattice3('#skF_8',C_89) = '#skF_2'('#skF_8',B_315)
      | ~ r3_lattice3('#skF_8','#skF_2'('#skF_8',B_315),C_89)
      | ~ m1_subset_1('#skF_2'('#skF_8',B_315),u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8')
      | ~ r1_lattices('#skF_8','#skF_7'('#skF_8','#skF_2'('#skF_8',B_315),C_89),'#skF_2'('#skF_8',B_315))
      | ~ m1_subset_1('#skF_7'('#skF_8','#skF_2'('#skF_8',B_315),C_89),u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_932])).

tff(c_938,plain,(
    ! [C_89,B_315] :
      ( k16_lattice3('#skF_8',C_89) = '#skF_2'('#skF_8',B_315)
      | ~ r3_lattice3('#skF_8','#skF_2'('#skF_8',B_315),C_89)
      | ~ m1_subset_1('#skF_2'('#skF_8',B_315),u1_struct_0('#skF_8'))
      | ~ r1_lattices('#skF_8','#skF_7'('#skF_8','#skF_2'('#skF_8',B_315),C_89),'#skF_2'('#skF_8',B_315))
      | ~ m1_subset_1('#skF_7'('#skF_8','#skF_2'('#skF_8',B_315),C_89),u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_937])).

tff(c_4196,plain,(
    ! [B_621,B_618,C_619] :
      ( ~ m1_subset_1('#skF_7'('#skF_8','#skF_2'('#skF_8',B_621),a_2_2_lattice3(B_618,C_619)),u1_struct_0('#skF_8'))
      | ~ r4_lattice3(B_618,'#skF_2'('#skF_8',B_621),C_619)
      | ~ m1_subset_1('#skF_2'('#skF_8',B_621),u1_struct_0(B_618))
      | ~ l3_lattices(B_618)
      | ~ v4_lattice3(B_618)
      | ~ v10_lattices(B_618)
      | v2_struct_0(B_618)
      | k16_lattice3('#skF_8',a_2_2_lattice3(B_618,C_619)) = '#skF_2'('#skF_8',B_621)
      | ~ r3_lattice3('#skF_8','#skF_2'('#skF_8',B_621),a_2_2_lattice3(B_618,C_619))
      | ~ m1_subset_1('#skF_2'('#skF_8',B_621),u1_struct_0('#skF_8'))
      | ~ l3_lattices('#skF_8')
      | ~ v4_lattice3('#skF_8')
      | ~ v10_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_4188,c_938])).

tff(c_4200,plain,(
    ! [B_621,B_618,C_619] :
      ( ~ m1_subset_1('#skF_7'('#skF_8','#skF_2'('#skF_8',B_621),a_2_2_lattice3(B_618,C_619)),u1_struct_0('#skF_8'))
      | ~ r4_lattice3(B_618,'#skF_2'('#skF_8',B_621),C_619)
      | ~ m1_subset_1('#skF_2'('#skF_8',B_621),u1_struct_0(B_618))
      | ~ l3_lattices(B_618)
      | ~ v4_lattice3(B_618)
      | ~ v10_lattices(B_618)
      | v2_struct_0(B_618)
      | k16_lattice3('#skF_8',a_2_2_lattice3(B_618,C_619)) = '#skF_2'('#skF_8',B_621)
      | ~ r3_lattice3('#skF_8','#skF_2'('#skF_8',B_621),a_2_2_lattice3(B_618,C_619))
      | ~ m1_subset_1('#skF_2'('#skF_8',B_621),u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_4196])).

tff(c_9103,plain,(
    ! [B_857,B_858,C_859] :
      ( ~ m1_subset_1('#skF_7'('#skF_8','#skF_2'('#skF_8',B_857),a_2_2_lattice3(B_858,C_859)),u1_struct_0('#skF_8'))
      | ~ r4_lattice3(B_858,'#skF_2'('#skF_8',B_857),C_859)
      | ~ m1_subset_1('#skF_2'('#skF_8',B_857),u1_struct_0(B_858))
      | ~ l3_lattices(B_858)
      | ~ v4_lattice3(B_858)
      | ~ v10_lattices(B_858)
      | v2_struct_0(B_858)
      | k16_lattice3('#skF_8',a_2_2_lattice3(B_858,C_859)) = '#skF_2'('#skF_8',B_857)
      | ~ r3_lattice3('#skF_8','#skF_2'('#skF_8',B_857),a_2_2_lattice3(B_858,C_859))
      | ~ m1_subset_1('#skF_2'('#skF_8',B_857),u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_4200])).

tff(c_9106,plain,(
    ! [B_858,B_857,C_859] :
      ( ~ r4_lattice3(B_858,'#skF_2'('#skF_8',B_857),C_859)
      | ~ m1_subset_1('#skF_2'('#skF_8',B_857),u1_struct_0(B_858))
      | ~ l3_lattices(B_858)
      | ~ v4_lattice3(B_858)
      | ~ v10_lattices(B_858)
      | v2_struct_0(B_858)
      | k16_lattice3('#skF_8',a_2_2_lattice3(B_858,C_859)) = '#skF_2'('#skF_8',B_857)
      | ~ r3_lattice3('#skF_8','#skF_2'('#skF_8',B_857),a_2_2_lattice3(B_858,C_859))
      | ~ m1_subset_1('#skF_2'('#skF_8',B_857),u1_struct_0('#skF_8'))
      | ~ l3_lattices('#skF_8')
      | ~ v4_lattice3('#skF_8')
      | ~ v10_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_66,c_9103])).

tff(c_9109,plain,(
    ! [B_858,B_857,C_859] :
      ( ~ r4_lattice3(B_858,'#skF_2'('#skF_8',B_857),C_859)
      | ~ m1_subset_1('#skF_2'('#skF_8',B_857),u1_struct_0(B_858))
      | ~ l3_lattices(B_858)
      | ~ v4_lattice3(B_858)
      | ~ v10_lattices(B_858)
      | v2_struct_0(B_858)
      | k16_lattice3('#skF_8',a_2_2_lattice3(B_858,C_859)) = '#skF_2'('#skF_8',B_857)
      | ~ r3_lattice3('#skF_8','#skF_2'('#skF_8',B_857),a_2_2_lattice3(B_858,C_859))
      | ~ m1_subset_1('#skF_2'('#skF_8',B_857),u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_9106])).

tff(c_9111,plain,(
    ! [B_860,B_861,C_862] :
      ( ~ r4_lattice3(B_860,'#skF_2'('#skF_8',B_861),C_862)
      | ~ m1_subset_1('#skF_2'('#skF_8',B_861),u1_struct_0(B_860))
      | ~ l3_lattices(B_860)
      | ~ v4_lattice3(B_860)
      | ~ v10_lattices(B_860)
      | v2_struct_0(B_860)
      | k16_lattice3('#skF_8',a_2_2_lattice3(B_860,C_862)) = '#skF_2'('#skF_8',B_861)
      | ~ r3_lattice3('#skF_8','#skF_2'('#skF_8',B_861),a_2_2_lattice3(B_860,C_862))
      | ~ m1_subset_1('#skF_2'('#skF_8',B_861),u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_9109])).

tff(c_9115,plain,(
    ! [C_309] :
      ( ~ r4_lattice3('#skF_8','#skF_2'('#skF_8',C_309),C_309)
      | k16_lattice3('#skF_8',a_2_2_lattice3('#skF_8',C_309)) = '#skF_2'('#skF_8',C_309)
      | ~ v4_lattice3('#skF_8')
      | ~ v10_lattices('#skF_8')
      | ~ m1_subset_1('#skF_2'('#skF_8',C_309),u1_struct_0('#skF_8'))
      | ~ l3_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1021,c_9111])).

tff(c_9121,plain,(
    ! [C_309] :
      ( k16_lattice3('#skF_8',a_2_2_lattice3('#skF_8',C_309)) = '#skF_2'('#skF_8',C_309)
      | ~ m1_subset_1('#skF_2'('#skF_8',C_309),u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_74,c_72,c_590,c_9115])).

tff(c_9132,plain,(
    ! [C_868] :
      ( k16_lattice3('#skF_8',a_2_2_lattice3('#skF_8',C_868)) = '#skF_2'('#skF_8',C_868)
      | ~ m1_subset_1('#skF_2'('#skF_8',C_868),u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_9121])).

tff(c_9136,plain,(
    ! [B_42] :
      ( k16_lattice3('#skF_8',a_2_2_lattice3('#skF_8',B_42)) = '#skF_2'('#skF_8',B_42)
      | ~ v4_lattice3('#skF_8')
      | ~ l3_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_38,c_9132])).

tff(c_9139,plain,(
    ! [B_42] :
      ( k16_lattice3('#skF_8',a_2_2_lattice3('#skF_8',B_42)) = '#skF_2'('#skF_8',B_42)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_72,c_9136])).

tff(c_9140,plain,(
    ! [B_42] : k16_lattice3('#skF_8',a_2_2_lattice3('#skF_8',B_42)) = '#skF_2'('#skF_8',B_42) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_9139])).

tff(c_68,plain,(
    k16_lattice3('#skF_8',a_2_2_lattice3('#skF_8','#skF_9')) != k15_lattice3('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_563,plain,(
    k16_lattice3('#skF_8',a_2_2_lattice3('#skF_8','#skF_9')) != '#skF_2'('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_562,c_68])).

tff(c_9144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9140,c_563])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:50:25 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.64/3.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.64/3.44  
% 9.64/3.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.64/3.44  %$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_2_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_6 > #skF_5 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_4
% 9.64/3.44  
% 9.64/3.44  %Foreground sorts:
% 9.64/3.44  
% 9.64/3.44  
% 9.64/3.44  %Background operators:
% 9.64/3.44  
% 9.64/3.44  
% 9.64/3.44  %Foreground operators:
% 9.64/3.44  tff(l3_lattices, type, l3_lattices: $i > $o).
% 9.64/3.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.64/3.44  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.64/3.44  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 9.64/3.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.64/3.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.64/3.44  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 9.64/3.44  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 9.64/3.44  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 9.64/3.44  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 9.64/3.44  tff(v4_lattices, type, v4_lattices: $i > $o).
% 9.64/3.44  tff(v6_lattices, type, v6_lattices: $i > $o).
% 9.64/3.44  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 9.64/3.44  tff(v9_lattices, type, v9_lattices: $i > $o).
% 9.64/3.44  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 9.64/3.44  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 9.64/3.44  tff(v5_lattices, type, v5_lattices: $i > $o).
% 9.64/3.44  tff(v10_lattices, type, v10_lattices: $i > $o).
% 9.64/3.44  tff('#skF_9', type, '#skF_9': $i).
% 9.64/3.44  tff(a_2_2_lattice3, type, a_2_2_lattice3: ($i * $i) > $i).
% 9.64/3.44  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 9.64/3.44  tff('#skF_8', type, '#skF_8': $i).
% 9.64/3.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.64/3.44  tff('#skF_3', type, '#skF_3': $i > $i).
% 9.64/3.44  tff(v8_lattices, type, v8_lattices: $i > $o).
% 9.64/3.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.64/3.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.64/3.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.64/3.44  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 9.64/3.44  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.64/3.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.64/3.44  tff(v7_lattices, type, v7_lattices: $i > $o).
% 9.64/3.44  
% 9.64/3.47  tff(f_187, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (k15_lattice3(A, B) = k16_lattice3(A, a_2_2_lattice3(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_lattice3)).
% 9.64/3.47  tff(f_104, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v4_lattice3(A) <=> (![B]: (?[C]: ((m1_subset_1(C, u1_struct_0(A)) & r4_lattice3(A, C, B)) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_lattice3)).
% 9.64/3.47  tff(f_132, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k15_lattice3(A, B)) <=> (r4_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d21_lattice3)).
% 9.64/3.47  tff(f_84, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattice3)).
% 9.64/3.47  tff(f_150, axiom, (![A, B, C]: ((((~v2_struct_0(B) & v10_lattices(B)) & v4_lattice3(B)) & l3_lattices(B)) => (r2_hidden(A, a_2_2_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & r4_lattice3(B, D, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_2_lattice3)).
% 9.64/3.47  tff(f_174, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((B = k16_lattice3(A, C)) <=> (r3_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_lattice3(A, D, C) => r3_lattices(A, D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_lattice3)).
% 9.64/3.47  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 9.64/3.47  tff(f_66, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 9.64/3.47  tff(c_76, plain, (~v2_struct_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_187])).
% 9.64/3.47  tff(c_70, plain, (l3_lattices('#skF_8')), inference(cnfTransformation, [status(thm)], [f_187])).
% 9.64/3.47  tff(c_72, plain, (v4_lattice3('#skF_8')), inference(cnfTransformation, [status(thm)], [f_187])).
% 9.64/3.47  tff(c_38, plain, (![A_27, B_42]: (m1_subset_1('#skF_2'(A_27, B_42), u1_struct_0(A_27)) | ~v4_lattice3(A_27) | ~l3_lattices(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.64/3.47  tff(c_74, plain, (v10_lattices('#skF_8')), inference(cnfTransformation, [status(thm)], [f_187])).
% 9.64/3.47  tff(c_36, plain, (![A_27, B_42]: (r4_lattice3(A_27, '#skF_2'(A_27, B_42), B_42) | ~v4_lattice3(A_27) | ~l3_lattices(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.64/3.47  tff(c_44, plain, (![A_53, B_60, C_61]: (m1_subset_1('#skF_5'(A_53, B_60, C_61), u1_struct_0(A_53)) | k15_lattice3(A_53, B_60)=C_61 | ~r4_lattice3(A_53, C_61, B_60) | ~m1_subset_1(C_61, u1_struct_0(A_53)) | ~v4_lattice3(A_53) | ~v10_lattices(A_53) | ~l3_lattices(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.64/3.47  tff(c_42, plain, (![A_53, B_60, C_61]: (r4_lattice3(A_53, '#skF_5'(A_53, B_60, C_61), B_60) | k15_lattice3(A_53, B_60)=C_61 | ~r4_lattice3(A_53, C_61, B_60) | ~m1_subset_1(C_61, u1_struct_0(A_53)) | ~v4_lattice3(A_53) | ~v10_lattices(A_53) | ~l3_lattices(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.64/3.47  tff(c_34, plain, (![A_27, B_42, D_47]: (r1_lattices(A_27, '#skF_2'(A_27, B_42), D_47) | ~r4_lattice3(A_27, D_47, B_42) | ~m1_subset_1(D_47, u1_struct_0(A_27)) | ~v4_lattice3(A_27) | ~l3_lattices(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.64/3.47  tff(c_170, plain, (![A_158, C_159, B_160]: (~r1_lattices(A_158, C_159, '#skF_5'(A_158, B_160, C_159)) | k15_lattice3(A_158, B_160)=C_159 | ~r4_lattice3(A_158, C_159, B_160) | ~m1_subset_1(C_159, u1_struct_0(A_158)) | ~v4_lattice3(A_158) | ~v10_lattices(A_158) | ~l3_lattices(A_158) | v2_struct_0(A_158))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.64/3.47  tff(c_527, plain, (![A_262, B_263, B_264]: (k15_lattice3(A_262, B_263)='#skF_2'(A_262, B_264) | ~r4_lattice3(A_262, '#skF_2'(A_262, B_264), B_263) | ~m1_subset_1('#skF_2'(A_262, B_264), u1_struct_0(A_262)) | ~v10_lattices(A_262) | ~r4_lattice3(A_262, '#skF_5'(A_262, B_263, '#skF_2'(A_262, B_264)), B_264) | ~m1_subset_1('#skF_5'(A_262, B_263, '#skF_2'(A_262, B_264)), u1_struct_0(A_262)) | ~v4_lattice3(A_262) | ~l3_lattices(A_262) | v2_struct_0(A_262))), inference(resolution, [status(thm)], [c_34, c_170])).
% 9.64/3.47  tff(c_532, plain, (![A_265, B_266]: (~m1_subset_1('#skF_5'(A_265, B_266, '#skF_2'(A_265, B_266)), u1_struct_0(A_265)) | k15_lattice3(A_265, B_266)='#skF_2'(A_265, B_266) | ~r4_lattice3(A_265, '#skF_2'(A_265, B_266), B_266) | ~m1_subset_1('#skF_2'(A_265, B_266), u1_struct_0(A_265)) | ~v4_lattice3(A_265) | ~v10_lattices(A_265) | ~l3_lattices(A_265) | v2_struct_0(A_265))), inference(resolution, [status(thm)], [c_42, c_527])).
% 9.64/3.47  tff(c_547, plain, (![A_271, B_272]: (k15_lattice3(A_271, B_272)='#skF_2'(A_271, B_272) | ~r4_lattice3(A_271, '#skF_2'(A_271, B_272), B_272) | ~m1_subset_1('#skF_2'(A_271, B_272), u1_struct_0(A_271)) | ~v4_lattice3(A_271) | ~v10_lattices(A_271) | ~l3_lattices(A_271) | v2_struct_0(A_271))), inference(resolution, [status(thm)], [c_44, c_532])).
% 9.64/3.47  tff(c_551, plain, (![A_273, B_274]: (k15_lattice3(A_273, B_274)='#skF_2'(A_273, B_274) | ~m1_subset_1('#skF_2'(A_273, B_274), u1_struct_0(A_273)) | ~v10_lattices(A_273) | ~v4_lattice3(A_273) | ~l3_lattices(A_273) | v2_struct_0(A_273))), inference(resolution, [status(thm)], [c_36, c_547])).
% 9.64/3.47  tff(c_556, plain, (![A_275, B_276]: (k15_lattice3(A_275, B_276)='#skF_2'(A_275, B_276) | ~v10_lattices(A_275) | ~v4_lattice3(A_275) | ~l3_lattices(A_275) | v2_struct_0(A_275))), inference(resolution, [status(thm)], [c_38, c_551])).
% 9.64/3.47  tff(c_558, plain, (![B_276]: (k15_lattice3('#skF_8', B_276)='#skF_2'('#skF_8', B_276) | ~v10_lattices('#skF_8') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_72, c_556])).
% 9.64/3.47  tff(c_561, plain, (![B_276]: (k15_lattice3('#skF_8', B_276)='#skF_2'('#skF_8', B_276) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_74, c_558])).
% 9.64/3.47  tff(c_562, plain, (![B_276]: (k15_lattice3('#skF_8', B_276)='#skF_2'('#skF_8', B_276))), inference(negUnitSimplification, [status(thm)], [c_76, c_561])).
% 9.64/3.47  tff(c_564, plain, (![B_277]: (k15_lattice3('#skF_8', B_277)='#skF_2'('#skF_8', B_277))), inference(negUnitSimplification, [status(thm)], [c_76, c_561])).
% 9.64/3.47  tff(c_48, plain, (![A_53, B_60]: (r4_lattice3(A_53, k15_lattice3(A_53, B_60), B_60) | ~m1_subset_1(k15_lattice3(A_53, B_60), u1_struct_0(A_53)) | ~v4_lattice3(A_53) | ~v10_lattices(A_53) | ~l3_lattices(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.64/3.47  tff(c_571, plain, (![B_277]: (r4_lattice3('#skF_8', k15_lattice3('#skF_8', B_277), B_277) | ~m1_subset_1('#skF_2'('#skF_8', B_277), u1_struct_0('#skF_8')) | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_564, c_48])).
% 9.64/3.47  tff(c_580, plain, (![B_277]: (r4_lattice3('#skF_8', '#skF_2'('#skF_8', B_277), B_277) | ~m1_subset_1('#skF_2'('#skF_8', B_277), u1_struct_0('#skF_8')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_74, c_72, c_562, c_571])).
% 9.64/3.47  tff(c_583, plain, (![B_278]: (r4_lattice3('#skF_8', '#skF_2'('#skF_8', B_278), B_278) | ~m1_subset_1('#skF_2'('#skF_8', B_278), u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_76, c_580])).
% 9.64/3.47  tff(c_586, plain, (![B_42]: (r4_lattice3('#skF_8', '#skF_2'('#skF_8', B_42), B_42) | ~v4_lattice3('#skF_8') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_38, c_583])).
% 9.64/3.47  tff(c_589, plain, (![B_42]: (r4_lattice3('#skF_8', '#skF_2'('#skF_8', B_42), B_42) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_72, c_586])).
% 9.64/3.47  tff(c_590, plain, (![B_42]: (r4_lattice3('#skF_8', '#skF_2'('#skF_8', B_42), B_42))), inference(negUnitSimplification, [status(thm)], [c_76, c_589])).
% 9.64/3.47  tff(c_24, plain, (![A_5, B_17, C_23]: (r2_hidden('#skF_1'(A_5, B_17, C_23), C_23) | r3_lattice3(A_5, B_17, C_23) | ~m1_subset_1(B_17, u1_struct_0(A_5)) | ~l3_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.64/3.47  tff(c_86, plain, (![A_107, B_108, C_109]: ('#skF_6'(A_107, B_108, C_109)=A_107 | ~r2_hidden(A_107, a_2_2_lattice3(B_108, C_109)) | ~l3_lattices(B_108) | ~v4_lattice3(B_108) | ~v10_lattices(B_108) | v2_struct_0(B_108))), inference(cnfTransformation, [status(thm)], [f_150])).
% 9.64/3.47  tff(c_259, plain, (![A_201, B_202, B_203, C_204]: ('#skF_6'('#skF_1'(A_201, B_202, a_2_2_lattice3(B_203, C_204)), B_203, C_204)='#skF_1'(A_201, B_202, a_2_2_lattice3(B_203, C_204)) | ~l3_lattices(B_203) | ~v4_lattice3(B_203) | ~v10_lattices(B_203) | v2_struct_0(B_203) | r3_lattice3(A_201, B_202, a_2_2_lattice3(B_203, C_204)) | ~m1_subset_1(B_202, u1_struct_0(A_201)) | ~l3_lattices(A_201) | v2_struct_0(A_201))), inference(resolution, [status(thm)], [c_24, c_86])).
% 9.64/3.47  tff(c_56, plain, (![A_65, B_66, C_67]: (m1_subset_1('#skF_6'(A_65, B_66, C_67), u1_struct_0(B_66)) | ~r2_hidden(A_65, a_2_2_lattice3(B_66, C_67)) | ~l3_lattices(B_66) | ~v4_lattice3(B_66) | ~v10_lattices(B_66) | v2_struct_0(B_66))), inference(cnfTransformation, [status(thm)], [f_150])).
% 9.64/3.47  tff(c_901, plain, (![A_306, B_307, B_308, C_309]: (m1_subset_1('#skF_1'(A_306, B_307, a_2_2_lattice3(B_308, C_309)), u1_struct_0(B_308)) | ~r2_hidden('#skF_1'(A_306, B_307, a_2_2_lattice3(B_308, C_309)), a_2_2_lattice3(B_308, C_309)) | ~l3_lattices(B_308) | ~v4_lattice3(B_308) | ~v10_lattices(B_308) | v2_struct_0(B_308) | ~l3_lattices(B_308) | ~v4_lattice3(B_308) | ~v10_lattices(B_308) | v2_struct_0(B_308) | r3_lattice3(A_306, B_307, a_2_2_lattice3(B_308, C_309)) | ~m1_subset_1(B_307, u1_struct_0(A_306)) | ~l3_lattices(A_306) | v2_struct_0(A_306))), inference(superposition, [status(thm), theory('equality')], [c_259, c_56])).
% 9.64/3.47  tff(c_911, plain, (![A_5, B_17, B_308, C_309]: (m1_subset_1('#skF_1'(A_5, B_17, a_2_2_lattice3(B_308, C_309)), u1_struct_0(B_308)) | ~l3_lattices(B_308) | ~v4_lattice3(B_308) | ~v10_lattices(B_308) | v2_struct_0(B_308) | r3_lattice3(A_5, B_17, a_2_2_lattice3(B_308, C_309)) | ~m1_subset_1(B_17, u1_struct_0(A_5)) | ~l3_lattices(A_5) | v2_struct_0(A_5))), inference(resolution, [status(thm)], [c_24, c_901])).
% 9.64/3.47  tff(c_52, plain, (![B_66, A_65, C_67]: (r4_lattice3(B_66, '#skF_6'(A_65, B_66, C_67), C_67) | ~r2_hidden(A_65, a_2_2_lattice3(B_66, C_67)) | ~l3_lattices(B_66) | ~v4_lattice3(B_66) | ~v10_lattices(B_66) | v2_struct_0(B_66))), inference(cnfTransformation, [status(thm)], [f_150])).
% 9.64/3.47  tff(c_856, plain, (![B_300, A_301, B_302, C_303]: (r4_lattice3(B_300, '#skF_1'(A_301, B_302, a_2_2_lattice3(B_300, C_303)), C_303) | ~r2_hidden('#skF_1'(A_301, B_302, a_2_2_lattice3(B_300, C_303)), a_2_2_lattice3(B_300, C_303)) | ~l3_lattices(B_300) | ~v4_lattice3(B_300) | ~v10_lattices(B_300) | v2_struct_0(B_300) | ~l3_lattices(B_300) | ~v4_lattice3(B_300) | ~v10_lattices(B_300) | v2_struct_0(B_300) | r3_lattice3(A_301, B_302, a_2_2_lattice3(B_300, C_303)) | ~m1_subset_1(B_302, u1_struct_0(A_301)) | ~l3_lattices(A_301) | v2_struct_0(A_301))), inference(superposition, [status(thm), theory('equality')], [c_259, c_52])).
% 9.64/3.47  tff(c_959, plain, (![B_320, A_321, B_322, C_323]: (r4_lattice3(B_320, '#skF_1'(A_321, B_322, a_2_2_lattice3(B_320, C_323)), C_323) | ~l3_lattices(B_320) | ~v4_lattice3(B_320) | ~v10_lattices(B_320) | v2_struct_0(B_320) | r3_lattice3(A_321, B_322, a_2_2_lattice3(B_320, C_323)) | ~m1_subset_1(B_322, u1_struct_0(A_321)) | ~l3_lattices(A_321) | v2_struct_0(A_321))), inference(resolution, [status(thm)], [c_24, c_856])).
% 9.64/3.47  tff(c_98, plain, (![A_126, B_127, D_128]: (r1_lattices(A_126, '#skF_2'(A_126, B_127), D_128) | ~r4_lattice3(A_126, D_128, B_127) | ~m1_subset_1(D_128, u1_struct_0(A_126)) | ~v4_lattice3(A_126) | ~l3_lattices(A_126) | v2_struct_0(A_126))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.64/3.47  tff(c_22, plain, (![A_5, B_17, C_23]: (~r1_lattices(A_5, B_17, '#skF_1'(A_5, B_17, C_23)) | r3_lattice3(A_5, B_17, C_23) | ~m1_subset_1(B_17, u1_struct_0(A_5)) | ~l3_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.64/3.47  tff(c_103, plain, (![A_126, B_127, C_23]: (r3_lattice3(A_126, '#skF_2'(A_126, B_127), C_23) | ~m1_subset_1('#skF_2'(A_126, B_127), u1_struct_0(A_126)) | ~r4_lattice3(A_126, '#skF_1'(A_126, '#skF_2'(A_126, B_127), C_23), B_127) | ~m1_subset_1('#skF_1'(A_126, '#skF_2'(A_126, B_127), C_23), u1_struct_0(A_126)) | ~v4_lattice3(A_126) | ~l3_lattices(A_126) | v2_struct_0(A_126))), inference(resolution, [status(thm)], [c_98, c_22])).
% 9.64/3.47  tff(c_1012, plain, (![A_331, C_332]: (~m1_subset_1('#skF_1'(A_331, '#skF_2'(A_331, C_332), a_2_2_lattice3(A_331, C_332)), u1_struct_0(A_331)) | ~v4_lattice3(A_331) | ~v10_lattices(A_331) | r3_lattice3(A_331, '#skF_2'(A_331, C_332), a_2_2_lattice3(A_331, C_332)) | ~m1_subset_1('#skF_2'(A_331, C_332), u1_struct_0(A_331)) | ~l3_lattices(A_331) | v2_struct_0(A_331))), inference(resolution, [status(thm)], [c_959, c_103])).
% 9.64/3.47  tff(c_1021, plain, (![B_308, C_309]: (~v4_lattice3(B_308) | ~v10_lattices(B_308) | r3_lattice3(B_308, '#skF_2'(B_308, C_309), a_2_2_lattice3(B_308, C_309)) | ~m1_subset_1('#skF_2'(B_308, C_309), u1_struct_0(B_308)) | ~l3_lattices(B_308) | v2_struct_0(B_308))), inference(resolution, [status(thm)], [c_911, c_1012])).
% 9.64/3.47  tff(c_66, plain, (![A_71, B_83, C_89]: (m1_subset_1('#skF_7'(A_71, B_83, C_89), u1_struct_0(A_71)) | k16_lattice3(A_71, C_89)=B_83 | ~r3_lattice3(A_71, B_83, C_89) | ~m1_subset_1(B_83, u1_struct_0(A_71)) | ~l3_lattices(A_71) | ~v4_lattice3(A_71) | ~v10_lattices(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_174])).
% 9.64/3.47  tff(c_64, plain, (![A_71, B_83, C_89]: (r3_lattice3(A_71, '#skF_7'(A_71, B_83, C_89), C_89) | k16_lattice3(A_71, C_89)=B_83 | ~r3_lattice3(A_71, B_83, C_89) | ~m1_subset_1(B_83, u1_struct_0(A_71)) | ~l3_lattices(A_71) | ~v4_lattice3(A_71) | ~v10_lattices(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_174])).
% 9.64/3.47  tff(c_50, plain, (![D_70, B_66, C_67]: (r2_hidden(D_70, a_2_2_lattice3(B_66, C_67)) | ~r4_lattice3(B_66, D_70, C_67) | ~m1_subset_1(D_70, u1_struct_0(B_66)) | ~l3_lattices(B_66) | ~v4_lattice3(B_66) | ~v10_lattices(B_66) | v2_struct_0(B_66))), inference(cnfTransformation, [status(thm)], [f_150])).
% 9.64/3.47  tff(c_126, plain, (![A_141, B_142, D_143, C_144]: (r1_lattices(A_141, B_142, D_143) | ~r2_hidden(D_143, C_144) | ~m1_subset_1(D_143, u1_struct_0(A_141)) | ~r3_lattice3(A_141, B_142, C_144) | ~m1_subset_1(B_142, u1_struct_0(A_141)) | ~l3_lattices(A_141) | v2_struct_0(A_141))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.64/3.47  tff(c_353, plain, (![D_220, C_217, B_216, B_218, A_219]: (r1_lattices(A_219, B_216, D_220) | ~m1_subset_1(D_220, u1_struct_0(A_219)) | ~r3_lattice3(A_219, B_216, a_2_2_lattice3(B_218, C_217)) | ~m1_subset_1(B_216, u1_struct_0(A_219)) | ~l3_lattices(A_219) | v2_struct_0(A_219) | ~r4_lattice3(B_218, D_220, C_217) | ~m1_subset_1(D_220, u1_struct_0(B_218)) | ~l3_lattices(B_218) | ~v4_lattice3(B_218) | ~v10_lattices(B_218) | v2_struct_0(B_218))), inference(resolution, [status(thm)], [c_50, c_126])).
% 9.64/3.47  tff(c_483, plain, (![A_257, C_256, B_255, B_254, B_253]: (r1_lattices(A_257, B_253, '#skF_2'(A_257, B_255)) | ~r3_lattice3(A_257, B_253, a_2_2_lattice3(B_254, C_256)) | ~m1_subset_1(B_253, u1_struct_0(A_257)) | ~r4_lattice3(B_254, '#skF_2'(A_257, B_255), C_256) | ~m1_subset_1('#skF_2'(A_257, B_255), u1_struct_0(B_254)) | ~l3_lattices(B_254) | ~v4_lattice3(B_254) | ~v10_lattices(B_254) | v2_struct_0(B_254) | ~v4_lattice3(A_257) | ~l3_lattices(A_257) | v2_struct_0(A_257))), inference(resolution, [status(thm)], [c_38, c_353])).
% 9.64/3.47  tff(c_4188, plain, (![A_620, B_622, B_621, B_618, C_619]: (r1_lattices(A_620, '#skF_7'(A_620, B_622, a_2_2_lattice3(B_618, C_619)), '#skF_2'(A_620, B_621)) | ~m1_subset_1('#skF_7'(A_620, B_622, a_2_2_lattice3(B_618, C_619)), u1_struct_0(A_620)) | ~r4_lattice3(B_618, '#skF_2'(A_620, B_621), C_619) | ~m1_subset_1('#skF_2'(A_620, B_621), u1_struct_0(B_618)) | ~l3_lattices(B_618) | ~v4_lattice3(B_618) | ~v10_lattices(B_618) | v2_struct_0(B_618) | k16_lattice3(A_620, a_2_2_lattice3(B_618, C_619))=B_622 | ~r3_lattice3(A_620, B_622, a_2_2_lattice3(B_618, C_619)) | ~m1_subset_1(B_622, u1_struct_0(A_620)) | ~l3_lattices(A_620) | ~v4_lattice3(A_620) | ~v10_lattices(A_620) | v2_struct_0(A_620))), inference(resolution, [status(thm)], [c_64, c_483])).
% 9.64/3.47  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.64/3.47  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.64/3.47  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.64/3.47  tff(c_592, plain, (![B_279]: (r4_lattice3('#skF_8', '#skF_2'('#skF_8', B_279), B_279))), inference(negUnitSimplification, [status(thm)], [c_76, c_589])).
% 9.64/3.47  tff(c_105, plain, (![D_131, B_132, C_133]: (r2_hidden(D_131, a_2_2_lattice3(B_132, C_133)) | ~r4_lattice3(B_132, D_131, C_133) | ~m1_subset_1(D_131, u1_struct_0(B_132)) | ~l3_lattices(B_132) | ~v4_lattice3(B_132) | ~v10_lattices(B_132) | v2_struct_0(B_132))), inference(cnfTransformation, [status(thm)], [f_150])).
% 9.64/3.47  tff(c_54, plain, (![A_65, B_66, C_67]: ('#skF_6'(A_65, B_66, C_67)=A_65 | ~r2_hidden(A_65, a_2_2_lattice3(B_66, C_67)) | ~l3_lattices(B_66) | ~v4_lattice3(B_66) | ~v10_lattices(B_66) | v2_struct_0(B_66))), inference(cnfTransformation, [status(thm)], [f_150])).
% 9.64/3.47  tff(c_109, plain, (![D_131, B_132, C_133]: ('#skF_6'(D_131, B_132, C_133)=D_131 | ~r4_lattice3(B_132, D_131, C_133) | ~m1_subset_1(D_131, u1_struct_0(B_132)) | ~l3_lattices(B_132) | ~v4_lattice3(B_132) | ~v10_lattices(B_132) | v2_struct_0(B_132))), inference(resolution, [status(thm)], [c_105, c_54])).
% 9.64/3.47  tff(c_597, plain, (![B_279]: ('#skF_6'('#skF_2'('#skF_8', B_279), '#skF_8', B_279)='#skF_2'('#skF_8', B_279) | ~m1_subset_1('#skF_2'('#skF_8', B_279), u1_struct_0('#skF_8')) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_592, c_109])).
% 9.64/3.47  tff(c_604, plain, (![B_279]: ('#skF_6'('#skF_2'('#skF_8', B_279), '#skF_8', B_279)='#skF_2'('#skF_8', B_279) | ~m1_subset_1('#skF_2'('#skF_8', B_279), u1_struct_0('#skF_8')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_597])).
% 9.64/3.47  tff(c_606, plain, (![B_280]: ('#skF_6'('#skF_2'('#skF_8', B_280), '#skF_8', B_280)='#skF_2'('#skF_8', B_280) | ~m1_subset_1('#skF_2'('#skF_8', B_280), u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_76, c_604])).
% 9.64/3.47  tff(c_609, plain, (![B_42]: ('#skF_6'('#skF_2'('#skF_8', B_42), '#skF_8', B_42)='#skF_2'('#skF_8', B_42) | ~v4_lattice3('#skF_8') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_38, c_606])).
% 9.64/3.47  tff(c_612, plain, (![B_42]: ('#skF_6'('#skF_2'('#skF_8', B_42), '#skF_8', B_42)='#skF_2'('#skF_8', B_42) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_72, c_609])).
% 9.64/3.47  tff(c_613, plain, (![B_42]: ('#skF_6'('#skF_2'('#skF_8', B_42), '#skF_8', B_42)='#skF_2'('#skF_8', B_42))), inference(negUnitSimplification, [status(thm)], [c_76, c_612])).
% 9.64/3.47  tff(c_615, plain, (![B_281]: ('#skF_6'('#skF_2'('#skF_8', B_281), '#skF_8', B_281)='#skF_2'('#skF_8', B_281))), inference(negUnitSimplification, [status(thm)], [c_76, c_612])).
% 9.64/3.47  tff(c_137, plain, (![A_147, B_148, C_149]: (r3_lattices(A_147, B_148, C_149) | ~r1_lattices(A_147, B_148, C_149) | ~m1_subset_1(C_149, u1_struct_0(A_147)) | ~m1_subset_1(B_148, u1_struct_0(A_147)) | ~l3_lattices(A_147) | ~v9_lattices(A_147) | ~v8_lattices(A_147) | ~v6_lattices(A_147) | v2_struct_0(A_147))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.64/3.47  tff(c_147, plain, (![B_66, B_148, A_65, C_67]: (r3_lattices(B_66, B_148, '#skF_6'(A_65, B_66, C_67)) | ~r1_lattices(B_66, B_148, '#skF_6'(A_65, B_66, C_67)) | ~m1_subset_1(B_148, u1_struct_0(B_66)) | ~v9_lattices(B_66) | ~v8_lattices(B_66) | ~v6_lattices(B_66) | ~r2_hidden(A_65, a_2_2_lattice3(B_66, C_67)) | ~l3_lattices(B_66) | ~v4_lattice3(B_66) | ~v10_lattices(B_66) | v2_struct_0(B_66))), inference(resolution, [status(thm)], [c_56, c_137])).
% 9.64/3.47  tff(c_630, plain, (![B_148, B_281]: (r3_lattices('#skF_8', B_148, '#skF_2'('#skF_8', B_281)) | ~r1_lattices('#skF_8', B_148, '#skF_6'('#skF_2'('#skF_8', B_281), '#skF_8', B_281)) | ~m1_subset_1(B_148, u1_struct_0('#skF_8')) | ~v9_lattices('#skF_8') | ~v8_lattices('#skF_8') | ~v6_lattices('#skF_8') | ~r2_hidden('#skF_2'('#skF_8', B_281), a_2_2_lattice3('#skF_8', B_281)) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_615, c_147])).
% 9.64/3.47  tff(c_661, plain, (![B_148, B_281]: (r3_lattices('#skF_8', B_148, '#skF_2'('#skF_8', B_281)) | ~r1_lattices('#skF_8', B_148, '#skF_2'('#skF_8', B_281)) | ~m1_subset_1(B_148, u1_struct_0('#skF_8')) | ~v9_lattices('#skF_8') | ~v8_lattices('#skF_8') | ~v6_lattices('#skF_8') | ~r2_hidden('#skF_2'('#skF_8', B_281), a_2_2_lattice3('#skF_8', B_281)) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_613, c_630])).
% 9.64/3.47  tff(c_662, plain, (![B_148, B_281]: (r3_lattices('#skF_8', B_148, '#skF_2'('#skF_8', B_281)) | ~r1_lattices('#skF_8', B_148, '#skF_2'('#skF_8', B_281)) | ~m1_subset_1(B_148, u1_struct_0('#skF_8')) | ~v9_lattices('#skF_8') | ~v8_lattices('#skF_8') | ~v6_lattices('#skF_8') | ~r2_hidden('#skF_2'('#skF_8', B_281), a_2_2_lattice3('#skF_8', B_281)))), inference(negUnitSimplification, [status(thm)], [c_76, c_661])).
% 9.64/3.47  tff(c_867, plain, (~v6_lattices('#skF_8')), inference(splitLeft, [status(thm)], [c_662])).
% 9.64/3.47  tff(c_870, plain, (~v10_lattices('#skF_8') | v2_struct_0('#skF_8') | ~l3_lattices('#skF_8')), inference(resolution, [status(thm)], [c_8, c_867])).
% 9.64/3.47  tff(c_873, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_74, c_870])).
% 9.64/3.47  tff(c_875, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_873])).
% 9.64/3.47  tff(c_876, plain, (![B_148, B_281]: (~v8_lattices('#skF_8') | ~v9_lattices('#skF_8') | r3_lattices('#skF_8', B_148, '#skF_2'('#skF_8', B_281)) | ~r1_lattices('#skF_8', B_148, '#skF_2'('#skF_8', B_281)) | ~m1_subset_1(B_148, u1_struct_0('#skF_8')) | ~r2_hidden('#skF_2'('#skF_8', B_281), a_2_2_lattice3('#skF_8', B_281)))), inference(splitRight, [status(thm)], [c_662])).
% 9.64/3.47  tff(c_879, plain, (~v9_lattices('#skF_8')), inference(splitLeft, [status(thm)], [c_876])).
% 9.64/3.47  tff(c_882, plain, (~v10_lattices('#skF_8') | v2_struct_0('#skF_8') | ~l3_lattices('#skF_8')), inference(resolution, [status(thm)], [c_2, c_879])).
% 9.64/3.47  tff(c_885, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_74, c_882])).
% 9.64/3.47  tff(c_887, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_885])).
% 9.64/3.47  tff(c_888, plain, (![B_148, B_281]: (~v8_lattices('#skF_8') | r3_lattices('#skF_8', B_148, '#skF_2'('#skF_8', B_281)) | ~r1_lattices('#skF_8', B_148, '#skF_2'('#skF_8', B_281)) | ~m1_subset_1(B_148, u1_struct_0('#skF_8')) | ~r2_hidden('#skF_2'('#skF_8', B_281), a_2_2_lattice3('#skF_8', B_281)))), inference(splitRight, [status(thm)], [c_876])).
% 9.64/3.47  tff(c_890, plain, (~v8_lattices('#skF_8')), inference(splitLeft, [status(thm)], [c_888])).
% 9.64/3.47  tff(c_893, plain, (~v10_lattices('#skF_8') | v2_struct_0('#skF_8') | ~l3_lattices('#skF_8')), inference(resolution, [status(thm)], [c_4, c_890])).
% 9.64/3.47  tff(c_896, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_74, c_893])).
% 9.64/3.47  tff(c_898, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_896])).
% 9.64/3.47  tff(c_912, plain, (![B_310, B_311]: (r3_lattices('#skF_8', B_310, '#skF_2'('#skF_8', B_311)) | ~r1_lattices('#skF_8', B_310, '#skF_2'('#skF_8', B_311)) | ~m1_subset_1(B_310, u1_struct_0('#skF_8')) | ~r2_hidden('#skF_2'('#skF_8', B_311), a_2_2_lattice3('#skF_8', B_311)))), inference(splitRight, [status(thm)], [c_888])).
% 9.64/3.47  tff(c_915, plain, (![B_310, C_67]: (r3_lattices('#skF_8', B_310, '#skF_2'('#skF_8', C_67)) | ~r1_lattices('#skF_8', B_310, '#skF_2'('#skF_8', C_67)) | ~m1_subset_1(B_310, u1_struct_0('#skF_8')) | ~r4_lattice3('#skF_8', '#skF_2'('#skF_8', C_67), C_67) | ~m1_subset_1('#skF_2'('#skF_8', C_67), u1_struct_0('#skF_8')) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_50, c_912])).
% 9.64/3.47  tff(c_918, plain, (![B_310, C_67]: (r3_lattices('#skF_8', B_310, '#skF_2'('#skF_8', C_67)) | ~r1_lattices('#skF_8', B_310, '#skF_2'('#skF_8', C_67)) | ~m1_subset_1(B_310, u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_2'('#skF_8', C_67), u1_struct_0('#skF_8')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_590, c_915])).
% 9.64/3.47  tff(c_920, plain, (![B_312, C_313]: (r3_lattices('#skF_8', B_312, '#skF_2'('#skF_8', C_313)) | ~r1_lattices('#skF_8', B_312, '#skF_2'('#skF_8', C_313)) | ~m1_subset_1(B_312, u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_2'('#skF_8', C_313), u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_76, c_918])).
% 9.64/3.47  tff(c_923, plain, (![B_312, B_42]: (r3_lattices('#skF_8', B_312, '#skF_2'('#skF_8', B_42)) | ~r1_lattices('#skF_8', B_312, '#skF_2'('#skF_8', B_42)) | ~m1_subset_1(B_312, u1_struct_0('#skF_8')) | ~v4_lattice3('#skF_8') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_38, c_920])).
% 9.64/3.47  tff(c_926, plain, (![B_312, B_42]: (r3_lattices('#skF_8', B_312, '#skF_2'('#skF_8', B_42)) | ~r1_lattices('#skF_8', B_312, '#skF_2'('#skF_8', B_42)) | ~m1_subset_1(B_312, u1_struct_0('#skF_8')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_72, c_923])).
% 9.64/3.47  tff(c_928, plain, (![B_314, B_315]: (r3_lattices('#skF_8', B_314, '#skF_2'('#skF_8', B_315)) | ~r1_lattices('#skF_8', B_314, '#skF_2'('#skF_8', B_315)) | ~m1_subset_1(B_314, u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_76, c_926])).
% 9.64/3.47  tff(c_62, plain, (![A_71, B_83, C_89]: (~r3_lattices(A_71, '#skF_7'(A_71, B_83, C_89), B_83) | k16_lattice3(A_71, C_89)=B_83 | ~r3_lattice3(A_71, B_83, C_89) | ~m1_subset_1(B_83, u1_struct_0(A_71)) | ~l3_lattices(A_71) | ~v4_lattice3(A_71) | ~v10_lattices(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_174])).
% 9.64/3.47  tff(c_932, plain, (![C_89, B_315]: (k16_lattice3('#skF_8', C_89)='#skF_2'('#skF_8', B_315) | ~r3_lattice3('#skF_8', '#skF_2'('#skF_8', B_315), C_89) | ~m1_subset_1('#skF_2'('#skF_8', B_315), u1_struct_0('#skF_8')) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8') | ~r1_lattices('#skF_8', '#skF_7'('#skF_8', '#skF_2'('#skF_8', B_315), C_89), '#skF_2'('#skF_8', B_315)) | ~m1_subset_1('#skF_7'('#skF_8', '#skF_2'('#skF_8', B_315), C_89), u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_928, c_62])).
% 9.64/3.47  tff(c_937, plain, (![C_89, B_315]: (k16_lattice3('#skF_8', C_89)='#skF_2'('#skF_8', B_315) | ~r3_lattice3('#skF_8', '#skF_2'('#skF_8', B_315), C_89) | ~m1_subset_1('#skF_2'('#skF_8', B_315), u1_struct_0('#skF_8')) | v2_struct_0('#skF_8') | ~r1_lattices('#skF_8', '#skF_7'('#skF_8', '#skF_2'('#skF_8', B_315), C_89), '#skF_2'('#skF_8', B_315)) | ~m1_subset_1('#skF_7'('#skF_8', '#skF_2'('#skF_8', B_315), C_89), u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_932])).
% 9.64/3.47  tff(c_938, plain, (![C_89, B_315]: (k16_lattice3('#skF_8', C_89)='#skF_2'('#skF_8', B_315) | ~r3_lattice3('#skF_8', '#skF_2'('#skF_8', B_315), C_89) | ~m1_subset_1('#skF_2'('#skF_8', B_315), u1_struct_0('#skF_8')) | ~r1_lattices('#skF_8', '#skF_7'('#skF_8', '#skF_2'('#skF_8', B_315), C_89), '#skF_2'('#skF_8', B_315)) | ~m1_subset_1('#skF_7'('#skF_8', '#skF_2'('#skF_8', B_315), C_89), u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_76, c_937])).
% 9.64/3.47  tff(c_4196, plain, (![B_621, B_618, C_619]: (~m1_subset_1('#skF_7'('#skF_8', '#skF_2'('#skF_8', B_621), a_2_2_lattice3(B_618, C_619)), u1_struct_0('#skF_8')) | ~r4_lattice3(B_618, '#skF_2'('#skF_8', B_621), C_619) | ~m1_subset_1('#skF_2'('#skF_8', B_621), u1_struct_0(B_618)) | ~l3_lattices(B_618) | ~v4_lattice3(B_618) | ~v10_lattices(B_618) | v2_struct_0(B_618) | k16_lattice3('#skF_8', a_2_2_lattice3(B_618, C_619))='#skF_2'('#skF_8', B_621) | ~r3_lattice3('#skF_8', '#skF_2'('#skF_8', B_621), a_2_2_lattice3(B_618, C_619)) | ~m1_subset_1('#skF_2'('#skF_8', B_621), u1_struct_0('#skF_8')) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_4188, c_938])).
% 9.64/3.47  tff(c_4200, plain, (![B_621, B_618, C_619]: (~m1_subset_1('#skF_7'('#skF_8', '#skF_2'('#skF_8', B_621), a_2_2_lattice3(B_618, C_619)), u1_struct_0('#skF_8')) | ~r4_lattice3(B_618, '#skF_2'('#skF_8', B_621), C_619) | ~m1_subset_1('#skF_2'('#skF_8', B_621), u1_struct_0(B_618)) | ~l3_lattices(B_618) | ~v4_lattice3(B_618) | ~v10_lattices(B_618) | v2_struct_0(B_618) | k16_lattice3('#skF_8', a_2_2_lattice3(B_618, C_619))='#skF_2'('#skF_8', B_621) | ~r3_lattice3('#skF_8', '#skF_2'('#skF_8', B_621), a_2_2_lattice3(B_618, C_619)) | ~m1_subset_1('#skF_2'('#skF_8', B_621), u1_struct_0('#skF_8')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_4196])).
% 9.64/3.47  tff(c_9103, plain, (![B_857, B_858, C_859]: (~m1_subset_1('#skF_7'('#skF_8', '#skF_2'('#skF_8', B_857), a_2_2_lattice3(B_858, C_859)), u1_struct_0('#skF_8')) | ~r4_lattice3(B_858, '#skF_2'('#skF_8', B_857), C_859) | ~m1_subset_1('#skF_2'('#skF_8', B_857), u1_struct_0(B_858)) | ~l3_lattices(B_858) | ~v4_lattice3(B_858) | ~v10_lattices(B_858) | v2_struct_0(B_858) | k16_lattice3('#skF_8', a_2_2_lattice3(B_858, C_859))='#skF_2'('#skF_8', B_857) | ~r3_lattice3('#skF_8', '#skF_2'('#skF_8', B_857), a_2_2_lattice3(B_858, C_859)) | ~m1_subset_1('#skF_2'('#skF_8', B_857), u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_76, c_4200])).
% 9.64/3.47  tff(c_9106, plain, (![B_858, B_857, C_859]: (~r4_lattice3(B_858, '#skF_2'('#skF_8', B_857), C_859) | ~m1_subset_1('#skF_2'('#skF_8', B_857), u1_struct_0(B_858)) | ~l3_lattices(B_858) | ~v4_lattice3(B_858) | ~v10_lattices(B_858) | v2_struct_0(B_858) | k16_lattice3('#skF_8', a_2_2_lattice3(B_858, C_859))='#skF_2'('#skF_8', B_857) | ~r3_lattice3('#skF_8', '#skF_2'('#skF_8', B_857), a_2_2_lattice3(B_858, C_859)) | ~m1_subset_1('#skF_2'('#skF_8', B_857), u1_struct_0('#skF_8')) | ~l3_lattices('#skF_8') | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_66, c_9103])).
% 9.64/3.47  tff(c_9109, plain, (![B_858, B_857, C_859]: (~r4_lattice3(B_858, '#skF_2'('#skF_8', B_857), C_859) | ~m1_subset_1('#skF_2'('#skF_8', B_857), u1_struct_0(B_858)) | ~l3_lattices(B_858) | ~v4_lattice3(B_858) | ~v10_lattices(B_858) | v2_struct_0(B_858) | k16_lattice3('#skF_8', a_2_2_lattice3(B_858, C_859))='#skF_2'('#skF_8', B_857) | ~r3_lattice3('#skF_8', '#skF_2'('#skF_8', B_857), a_2_2_lattice3(B_858, C_859)) | ~m1_subset_1('#skF_2'('#skF_8', B_857), u1_struct_0('#skF_8')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_9106])).
% 9.64/3.47  tff(c_9111, plain, (![B_860, B_861, C_862]: (~r4_lattice3(B_860, '#skF_2'('#skF_8', B_861), C_862) | ~m1_subset_1('#skF_2'('#skF_8', B_861), u1_struct_0(B_860)) | ~l3_lattices(B_860) | ~v4_lattice3(B_860) | ~v10_lattices(B_860) | v2_struct_0(B_860) | k16_lattice3('#skF_8', a_2_2_lattice3(B_860, C_862))='#skF_2'('#skF_8', B_861) | ~r3_lattice3('#skF_8', '#skF_2'('#skF_8', B_861), a_2_2_lattice3(B_860, C_862)) | ~m1_subset_1('#skF_2'('#skF_8', B_861), u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_76, c_9109])).
% 9.64/3.47  tff(c_9115, plain, (![C_309]: (~r4_lattice3('#skF_8', '#skF_2'('#skF_8', C_309), C_309) | k16_lattice3('#skF_8', a_2_2_lattice3('#skF_8', C_309))='#skF_2'('#skF_8', C_309) | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | ~m1_subset_1('#skF_2'('#skF_8', C_309), u1_struct_0('#skF_8')) | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_1021, c_9111])).
% 9.64/3.47  tff(c_9121, plain, (![C_309]: (k16_lattice3('#skF_8', a_2_2_lattice3('#skF_8', C_309))='#skF_2'('#skF_8', C_309) | ~m1_subset_1('#skF_2'('#skF_8', C_309), u1_struct_0('#skF_8')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_74, c_72, c_590, c_9115])).
% 9.64/3.47  tff(c_9132, plain, (![C_868]: (k16_lattice3('#skF_8', a_2_2_lattice3('#skF_8', C_868))='#skF_2'('#skF_8', C_868) | ~m1_subset_1('#skF_2'('#skF_8', C_868), u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_76, c_9121])).
% 9.64/3.47  tff(c_9136, plain, (![B_42]: (k16_lattice3('#skF_8', a_2_2_lattice3('#skF_8', B_42))='#skF_2'('#skF_8', B_42) | ~v4_lattice3('#skF_8') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_38, c_9132])).
% 9.64/3.47  tff(c_9139, plain, (![B_42]: (k16_lattice3('#skF_8', a_2_2_lattice3('#skF_8', B_42))='#skF_2'('#skF_8', B_42) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_72, c_9136])).
% 9.64/3.47  tff(c_9140, plain, (![B_42]: (k16_lattice3('#skF_8', a_2_2_lattice3('#skF_8', B_42))='#skF_2'('#skF_8', B_42))), inference(negUnitSimplification, [status(thm)], [c_76, c_9139])).
% 9.64/3.47  tff(c_68, plain, (k16_lattice3('#skF_8', a_2_2_lattice3('#skF_8', '#skF_9'))!=k15_lattice3('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_187])).
% 9.64/3.47  tff(c_563, plain, (k16_lattice3('#skF_8', a_2_2_lattice3('#skF_8', '#skF_9'))!='#skF_2'('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_562, c_68])).
% 9.64/3.47  tff(c_9144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9140, c_563])).
% 9.64/3.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.64/3.47  
% 9.64/3.47  Inference rules
% 9.64/3.47  ----------------------
% 9.64/3.47  #Ref     : 0
% 9.64/3.47  #Sup     : 1740
% 9.64/3.47  #Fact    : 0
% 9.64/3.47  #Define  : 0
% 9.64/3.47  #Split   : 3
% 9.64/3.47  #Chain   : 0
% 9.64/3.47  #Close   : 0
% 9.64/3.47  
% 9.64/3.47  Ordering : KBO
% 9.64/3.47  
% 9.64/3.47  Simplification rules
% 9.64/3.47  ----------------------
% 9.64/3.47  #Subsume      : 669
% 9.64/3.47  #Demod        : 4832
% 9.64/3.47  #Tautology    : 393
% 9.64/3.47  #SimpNegUnit  : 851
% 9.64/3.47  #BackRed      : 2
% 9.64/3.47  
% 9.64/3.47  #Partial instantiations: 0
% 9.64/3.47  #Strategies tried      : 1
% 9.64/3.47  
% 9.64/3.47  Timing (in seconds)
% 9.64/3.47  ----------------------
% 9.64/3.47  Preprocessing        : 0.35
% 9.64/3.47  Parsing              : 0.19
% 9.64/3.47  CNF conversion       : 0.03
% 9.64/3.47  Main loop            : 2.30
% 9.64/3.47  Inferencing          : 0.86
% 9.64/3.47  Reduction            : 0.63
% 9.64/3.47  Demodulation         : 0.43
% 9.64/3.47  BG Simplification    : 0.09
% 9.64/3.47  Subsumption          : 0.60
% 9.64/3.47  Abstraction          : 0.14
% 9.64/3.47  MUC search           : 0.00
% 9.64/3.47  Cooper               : 0.00
% 9.64/3.47  Total                : 2.69
% 9.64/3.47  Index Insertion      : 0.00
% 9.64/3.47  Index Deletion       : 0.00
% 9.64/3.47  Index Matching       : 0.00
% 9.64/3.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
